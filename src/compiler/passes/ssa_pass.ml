(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)

(* SSA pass
 * converts a CFG to SSA form.
 *)


open Wasm
open Source

open Solver_types

open Instr_graph
open Func_types
open Script_types
open State_types
open Proof_types

open Pass_types
open Debug
open Wasm_utils
open Proof_builder

module G = Digraph
module Q = Queue
module Dom = Dominance


type var = Int32.t             (* used to be Ast.var, but that also has extra region information *)
module XSet = Int32Set
module XMap = Int32Map

(* maps a local variable to a set of vertices *)
type var_vertices_map = G.VSet.t XMap.t
type var_defs_map = var_vertices_map
type var_IDF_map = var_vertices_map

(* maps a local variable to a stack of its versions *)
type var_varstack_map = (var list) XMap.t                            

(* maps each vertex to its dominance frontier *)
type vertex_DF_map = G.VSet.t G.VMap.t 
(* maps a vertex to the set of variables that require phi nodes at that vertex *)                       
type vertex_varset_map = XSet.t G.VMap.t

                     
(* Phi assignments are attached as a label "phis" to a graph vertex. 
 * This maps a variable x to an entry (new_x, edge entries)
 * where new_x is the new version created for x for use within the block of the vertex
 * and edge entry (u,x_u) says to use x_u if control enters this vertex from vertex u. 
 * 
 * The root vertex has a special entry (root,x) in its map, 
 * as each variable is implicitly initialized to 0 by the wasm semantics. 
 *)
                                

(* proof information: all we need to keep track of is a map for each edge *)
type var_var_map = var XMap.t
type raw_ssa_proof_entry =  G.vertex * G.vertex * var_var_map (* (u,v,xxmap): local variable map for edge u->v *)
type raw_ssa_proof = raw_ssa_proof_entry list    

module EIn =
  struct
    type t = G.basic_edge
    let compare: t -> t -> int = Stdlib.compare
  end

module EMap = Map.Make(EIn)

type pair_formula_map_t = state_pair_formula EMap.t
    

(* ========== generating new SSA local variables ========= *)

type fresh_local_gen = {
    old_param_and_local_types: Types.value_type list;
    next_local_number: Int32.t;
    new_local_types: Types.value_type list;
  }

let initial_local_gen: Types.value_type list -> fresh_local_gen = 
  fun param_and_local_types ->
  let fresh_local_gen = {
      old_param_and_local_types = param_and_local_types;
      next_local_number = Int32.of_int (List.length param_and_local_types);
      new_local_types = []
    }
  in 

  Debug.if_debug_high
    (fun () ->
      Printf.printf "\nssa/initial_local_gen: new locals numbering starts at %ld"
        fresh_local_gen.next_local_number);

  fresh_local_gen

    
let fresh_local_var: fresh_local_gen -> Int32.t -> Int32.t * fresh_local_gen =
  fun fgen x ->
  (* create a new variable for old variable x *)
  let xtyp = List.nth_int32 x fgen.old_param_and_local_types Types.I32Type in
  let new_x = fgen.next_local_number in
  let fgen1 =
    { fgen with 
      next_local_number = Int32.add new_x 1l;
      new_local_types = fgen.new_local_types@[xtyp];
    }
  in
  (new_x, fgen1)

                                         

(* ========== scan the graph, collect variable definitions ========== *)

let scan_graph:
      ('a,'b) instr_graph
      -> G.vertex                                     (* root vertex *)
      -> ('c -> G.vertex -> Ast.instr list -> 'c)     (* scan the instructions in the block at vertex v, accumulate information *)
      -> 'c                                           (* initial information *)
      -> 'c                 
  =
  fun graph root gather init ->
  (* scans a graph, gathering information from instructions in each block.
   * blocks are visited exactly once in arbitrary order by a BFS search. *)
    
  let rec bfs queue visited acc =
    match Q.dequeue queue with
    | None -> acc 
    | Some(v,queue1) ->
       if G.VSet.mem v visited then (* continue *)
         bfs queue1 visited acc 
       else 
         match G.vertex_label v graph with
         | None ->
            (prerr_endline ("ssa/scan_graph: None lookup at " ^ G.string_of_vertex v);
             acc)
              
         | Some(block, _) ->
            let acc1 = gather acc v block.instrs in
            let visited1 = G.VSet.add v visited in
            let unvisited_succs =
              List.concat
                (List.map
                   (fun (s, _) -> if G.VSet.mem s visited1 then [] else [s])
                   (G.vertex_succs v graph))
          in
          let queue2 = Q.enqueue_list unvisited_succs queue1 in          
          bfs queue2 visited1 acc1
              
  in
  let queue = [root]
  and visited = G.VSet.empty
  and acc = init
  in
  bfs queue visited acc

                                   

let add_def: var_defs_map -> var -> G.vertex -> var_defs_map =
  fun xdefs x v ->
  match XMap.find_opt x xdefs with
  | None -> XMap.add x (G.VSet.singleton v) xdefs 
  | Some vs -> XMap.add x (G.VSet.add v vs) xdefs
                         
             
let rec fold_instrs : var_defs_map -> G.vertex -> Ast.instr list -> var_defs_map =
  fun xdefs v instrs -> 
    match instrs with
    | [] ->
       xdefs
    | instr :: instrs_tl ->
      match instr.it with
      | Ast.LocalSet x
        | Ast.LocalTee x ->
         fold_instrs (add_def xdefs x.Source.it v) v instrs_tl
      | _ ->
         fold_instrs xdefs v instrs_tl


let string_of_vertex_set: G.VSet.t -> string =
  fun vset ->
  "{"
  ^ G.VSet.fold (fun y r -> (G.string_of_vertex y) ^ " " ^ r) vset ""
  ^ "}"
                     

let variable_definitions_map:
      (unit, unit) instr_graph
      -> G.vertex 
      -> var_defs_map
  =
  fun graph root ->
  let xdefs_map0 = scan_graph graph root fold_instrs XMap.empty in 
  (* add in the root vertex as all wasm variables are implicitly initialized *)
  XMap.map (fun vs -> G.VSet.add root vs) xdefs_map0


(* ========== compute iterated dominance frontiers (idfs) ========== *)
    
(* NOTE: this should probably go in dominance.ml *)
                 
let cfg_successors_of:
      G.VSet.t
      -> (unit, unit) instr_graph
      -> G.VSet.t
  =
  fun vs graph ->
  G.VSet.fold
    (fun v acc -> 
      let succs_of_v = List.map fst (G.vertex_succs v graph) in
      G.VSet.union (G.VSet.of_list succs_of_v) acc
    )
    vs
    G.VSet.empty
                 

let dominance_frontier_of_vertex:
      G.vertex
      -> (unit, unit) instr_graph
      -> Dom.dom_data
      -> G.VSet.t
  =
  fun v graph domdata ->

  Debug.if_debug_high (fun () -> Printf.printf "\nssa/dominance_frontier_of_vertex: processing %s"
                                   (G.string_of_vertex v));

  let dom_v =
    (match G.VMap.find_opt v domdata.Dom.doms_map with
     | None ->
        failwith(Printf.sprintf "ssa/dominance_frontier_of_vertex: None lookup at %s" (G.string_of_vertex v))
                
     | Some(vs) -> vs
    )
  in
  (*
  let _ = Printf.printf "\nVertex %s dominates %s" (G.string_of_vertex v) (string_of_vertex_set dom_v) in 
  *)
  let strict_dom_v = G.VSet.remove v dom_v in 
  let dominance_frontier_v = 
    G.VSet.diff
      (cfg_successors_of dom_v graph)
      strict_dom_v
  in
  dominance_frontier_v
                 

                 
let dominance_frontier_map:
      (unit, unit) instr_graph
      -> Dom.dom_data
      -> vertex_DF_map
  = 
  fun graph domdata ->
  G.VSet.fold
    (fun v map ->
      let df_v = dominance_frontier_of_vertex v graph domdata in
      G.VMap.add v df_v map
    )
    graph.G.vertex_set    
    G.VMap.empty

      
let print_df_map: vertex_DF_map -> unit =
  fun vdfs ->
  G.VMap.iter
    (fun v df_v ->
      Printf.printf "\nDF(%s) = %s"
        (G.string_of_vertex v)
        (string_of_vertex_set df_v)
    )
    vdfs
    

let dominance_frontier_of_vertex_set:
      G.VSet.t   (* DF of this set = union of DFs of each vertex in the set *)
      -> vertex_DF_map           
      -> G.VSet.t
  =
  fun vset dfmap ->
  G.VSet.fold
    (fun v acc ->
      match G.VMap.find_opt v dfmap with
      | None ->
         failwith(Printf.sprintf "ssa/dominance_frontier_of_vertex_set: None lookup at %s" (G.string_of_vertex v))
                 
      | Some(vs) ->
         G.VSet.union vs acc
    )
    vset
    G.VSet.empty


    
let iterated_dominance_frontier_of_vertex_set:
      G.VSet.t   (* IDF of this set *)
      -> vertex_DF_map 
      -> G.VSet.t
  =
  fun vset dfmap ->

  let df vs = dominance_frontier_of_vertex_set vs dfmap in

  let rec iterate acc vs =
    (* acc is the accumulated result, vs \subseteq acc is the last value *)
    let vs' = df vs in
    if (G.VSet.subset vs' acc) then acc
    else
      let acc' = G.VSet.union vs' acc in
      iterate acc' vs' 
                 
  in
  let idf_0_vset = df vset in 
  iterate idf_0_vset idf_0_vset 

  
           
let iterated_dominance_frontier_map:
      var_defs_map
      -> vertex_DF_map 
      -> var_IDF_map
  =
  fun xdefs dfmap ->
  XMap.map
    (fun defs_for_x ->
      iterated_dominance_frontier_of_vertex_set defs_for_x dfmap 
    )
    xdefs


     
let print_idf_map: var_IDF_map -> unit =
  fun vidfs ->
  XMap.iter
    (fun x idf_x ->
      Printf.printf "\nIDF(def_vertices(%ld)) = %s"
        x
        (string_of_vertex_set idf_x)
    )
    vidfs
  

(* ========== rewrite instructions to SSA form ========== *)

let phi_variables_map:
      var_IDF_map
      -> vertex_varset_map
  =
  fun xidfs ->
  (* map each vertex v to the set { var x | v \in xidfs(x)}. These variables require a phi entry at v. *)
  XMap.fold
    (fun x idf_x map -> (* add x to the entry for every vertex v in idf_x *)
      G.VSet.fold
        (fun v map ->
          match G.VMap.find_opt v map with
          | None -> G.VMap.add v (XSet.singleton x) map
          | Some(xs) -> G.VMap.add v (XSet.add x xs) map
        )
        idf_x
        map
    )
    xidfs 
    G.VMap.empty

           
let augment_phimap:
      (unit,unit) instr_graph
      -> fresh_local_gen
      -> vertex_varset_map
      -> phi_map
      -> phi_map * fresh_local_gen 
  =
  fun graph fgen vxs_map phimap ->

  let add_phis_to: G.vertex -> phi_vertex_map -> fresh_local_gen -> (phi_vertex_map * fresh_local_gen) = 
    fun v vmap fgen -> 
    match G.VMap.find_opt v vxs_map with
    | None ->  (* no phi-entries to be added *)
       (vmap,fgen)
    | Some(xs) ->  (* add entries for all variables in xs *)


       Debug.if_debug_high
         (fun () ->
           Printf.printf "\nssa/augment_phimap: adding phi definitions at vertex %s\n\t" (G.string_of_vertex v);
           XSet.iter (fun x -> Printf.printf "%ld " x) xs;
         );

       
       XSet.fold
         (fun x (vmap,fgen) ->
           match Int32Map.find_opt x vmap with
           | None ->
              let new_x, fgen1 = fresh_local_var fgen x in
              let vmap1 = Int32Map.add x (new_x, []) vmap in
              (vmap1, fgen1)
           | Some _ ->
              failwith(Printf.sprintf
                         "ssa/add_phis_to: collision! existing entry for local index %ld in phimap for vertex %s"
                         x (G.string_of_vertex v))
         )
         xs
         (vmap, fgen)
  in
  G.VSet.fold
    (fun v (phimap0,fgen0) ->
      let vmap0 = (* extract current vmap at vertex v *)
        match G.VMap.find_opt v phimap0 with
        | None -> Int32Map.empty
        | Some(vmap) -> vmap
      in
      (* augment if necessary *)
      let vmap1,fgen1 = add_phis_to v vmap0 fgen0 in
      (* set up augmented vmap at v *)
      let phimap1 = G.VMap.add v vmap1 phimap0 in
      (phimap1,fgen1)
    )
    graph.G.vertex_set
    (phimap,fgen)
  


let push_xstack:
      var                   (* old *)
      -> var                (* new *)
      -> var_varstack_map
      -> var_varstack_map
  =
  fun old_x new_x xstack -> 
  match XMap.find_opt old_x xstack with
  | None ->
     failwith ("ssa/push_xstack: None lookup")
  | Some(xvars) ->
     XMap.add old_x (new_x::xvars) xstack

              
let topvar:
      var_varstack_map
      -> var
      -> var
  =
  fun xstack x ->
  match XMap.find_opt x xstack with
  | None ->
     failwith ("ssa/topvar_xstack: None lookup")
  | Some([]) ->
     failwith ("ssa/topvar_xstack: empty stack")
  | Some(y::_) -> y
              

let add_phi_assignments:
      G.vertex             (* prior vertex u *)
      -> phi_vertex_map       (* original phi map *)
      -> var_varstack_map  (* stack of new names for variables *)
      -> (phi_vertex_map * var_varstack_map)  (* updated map and stack *)
  =
  fun u vphis xstack -> (* entering edge u->v with xstack *)
  XMap.fold             
    (fun old_x xentry (vphis1, xstack1) ->
      let (new_x, phi_edges_x) = xentry in 
      let top_x = topvar xstack1 old_x in
      let xentry1 = (new_x, (u,top_x)::phi_edges_x) in
      
      let vphis2 = XMap.add old_x xentry1 vphis1 
      and xstack2 = push_xstack old_x new_x xstack1
      in
      (vphis2, xstack2)
    )
    vphis
    (vphis,xstack)


let noregion: 'a -> 'a Source.phrase =
  fun a -> 
  Source.(@@) a Source.no_region 


let rec rewrite_instrs:
          Ast.instr list
          -> var_varstack_map                    
          -> fresh_local_gen
          -> (Ast.instr list * var_varstack_map * fresh_local_gen)
  =
  fun instrs xstack fgen ->
  (* rework LocalGet and LocalSet entries relative to xstack, 
   * producing a rewritten instruction list and a (possibly) extended xstack *)
  match instrs with
  | [] -> ([], xstack, fgen)

  | i::rest ->
     match i.Source.it with
     | Ast.LocalGet x ->
        let old_x = x.Source.it in         
        let top_x = topvar xstack old_x in
        let top_x_var = noregion top_x in 
        let i1 = noregion (Ast.LocalGet top_x_var) in 
        let rest1,xstack1,fgen1 = rewrite_instrs rest xstack fgen in 
        (i1::rest1, xstack1, fgen1)
                  
     | Ast.LocalSet x ->
        let old_x = x.Source.it in 
        let new_x, fgen1 = fresh_local_var fgen old_x in
        let new_x_var = noregion new_x in 
        let i1 = noregion (Ast.LocalSet new_x_var) in 
        let xstack1 = push_xstack old_x new_x xstack in
        let rest1,xstack2,fgen2 = rewrite_instrs rest xstack1 fgen1 in          
        (i1::rest1, xstack2, fgen2)

     | Ast.LocalTee x ->
        let old_x = x.Source.it in 
        let new_x, fgen1 = fresh_local_var fgen old_x in
        let new_x_var = noregion new_x in 
        let i1 = noregion (Ast.LocalTee new_x_var) in 
        let xstack1 = push_xstack old_x new_x xstack in
        let rest1,xstack2,fgen2 = rewrite_instrs rest xstack1 fgen1 in          
        (i1::rest1, xstack2, fgen2)          
          
     | _ ->
        let rest1,xstack1,fgen1 = rewrite_instrs rest xstack fgen in          
        (i::rest1, xstack1, fgen1)         

          
let top_vars_of: var_varstack_map -> var_var_map =
  fun xstack -> 
  XMap.map 
    (fun xs ->
      match xs with
      | [] ->
         failwith("ssa/top_vars: empty entry in xstack?")
      | y::_ ->
         y
    )
    xstack


let phimap_at_vertex: G.vertex -> phi_map -> phi_vertex_map =
  fun v phimap ->
  match G.VMap.find_opt v phimap with
  | None -> Int32Map.empty
  | Some(vmap) -> vmap
                    

let rec rewrite_graph:
          uinstr_graph
          -> pass_config 
          -> phi_map 
          -> fresh_local_gen  
          -> (G.vertex * G.vertex * var_varstack_map) Q.queue (* entry (previous, current, xstack for current) *)
          -> G.VSet.t
          -> raw_ssa_proof
          -> uinstr_graph * phi_map * raw_ssa_proof * fresh_local_gen 
  =
  fun graph config phimap fgen queue visited rawproof ->
  match Q.dequeue queue with
  | None ->
     (graph, phimap, rawproof, fgen)
                
  | Some ((u,v,xstack0), queue1) ->  (* following edge u->v with xstack0 *)
      match G.vertex_label v graph with
      | None ->
         prerr_endline ("ssa/rewrite_graph: None lookup at " ^ G.string_of_vertex v);
         (graph, phimap, rawproof, fgen)
          
      | Some (block, _) ->
         let vphis0 = phimap_at_vertex v phimap in
         (* record top-of-stack values on this edge for proof generation *)
         let rawproof1 =
           if config.gen_proof then (u,v,top_vars_of xstack0)::rawproof else rawproof
         in
         (* extend phimap at vertex v by adding assignment entries for edge u->v *)
         let vphis1, xstack1 = add_phi_assignments u vphis0 xstack0 in
         let phimap1 = G.VMap.add v vphis1 phimap in
         
         if G.VSet.mem v visited then (* continue *)
           rewrite_graph graph config phimap1 fgen queue1 visited rawproof1
         else (* rewrite block, set up successors for processing *)
           let instrs1, xstack2, fgen1 = rewrite_instrs block.instrs xstack1 fgen in
           let block1 = { block with instrs = instrs1 } in
           let graph1 = G.add_vertex_label v (block1, ()) graph in

           (* mark v as visited *)
           let visited1 = G.VSet.add v visited in

           (* process ALL successors w of v *)
           let add_to_queue =
             List.map (fun (w,_) -> (v,w,xstack2)) (G.vertex_succs v graph)   
           in
           let queue2 = Q.enqueue_list add_to_queue queue1 in
           rewrite_graph graph1 config phimap1 fgen1 queue2 visited1 rawproof1 


let rec collect_references: XSet.t-> G.vertex -> Ast.instr list -> XSet.t = 
  fun xs v instrs -> 
    match instrs with
    | [] ->
       xs
    | instr :: instrs_tl ->
      match instr.it with
      | Ast.LocalSet x
        | Ast.LocalGet x
        | Ast.LocalTee x -> 
         collect_references (XSet.add x.Source.it xs) v instrs_tl
      | _ ->
         collect_references xs v instrs_tl
      
let referenced_variables:
      (unit,unit) instr_graph
      -> G.vertex
      -> XSet.t
  =
  fun graph root ->
  scan_graph graph root collect_references XSet.empty


let phi_asgns_to_string:
      phi_edge list -> string
  =
  fun xasgns ->
  List.fold_left
    (fun str (vprev,xprev) ->
      Printf.sprintf "%s (%s,%s) "
        str
        (G.string_of_vertex vprev)
        (Int32.to_string xprev)
    )
    ""
    xasgns
  
             
let phi_vertex_map_to_string:
      phi_vertex_map -> string
  =
  fun vmap ->
  Int32Map.fold
    (fun x (new_x, xasgns) str ->
      Printf.sprintf "%s \n\t lvar %s -> %s := %s"
        str
        (Int32.to_string x)
        (Int32.to_string new_x)        
        (phi_asgns_to_string xasgns)
    )
    vmap
    ""
             

let phi_map_to_string:
      phi_map -> string
  =
  fun phimap ->
  G.VMap.fold
    (fun v vmap str ->
      Printf.sprintf "%s \n at vertex %s: %s "
        str
        (G.string_of_vertex v)
        (phi_vertex_map_to_string vmap)
    )
    phimap
    ""
    

let ssa_on_graph:
      uinstr_graph
      -> pass_config
      -> G.vertex
      -> phi_map
      -> fresh_local_gen 
      -> uinstr_graph * phi_map * raw_ssa_proof * fresh_local_gen 
  =
  fun graph config root phimap fgen ->
  (* Debug.print_debug_high "computing dom info"; *)
  (* 1. compute iterated dominance frontiers *)
  let dom_data = Dom.graph_to_dom_data graph root in

  (* Debug.if_debug_high (fun () -> Printf.printf "\nDom-Tree %s" (G.string_of_graph_simple dom_data.dom_tree)); *)

  (* [total] map each vertex v to DF(v) *)
  let df_map = dominance_frontier_map graph dom_data in
  (* [partial] map each variable x to defined(x) *)
  let xdefs_map = variable_definitions_map graph root in
  (* [partial] map each variable x to IDF(defined(x)) *)

  (* Debug.print_debug_high "computing IDFs"; *)
  let xidfs_map = iterated_dominance_frontier_map xdefs_map df_map in

  (*
  let _ = print_df_map df_map in 
  let _ = print_idf_map xidfs_map in 
  *)

  (* 2. rewrite CFG *)
  (* 2A. [partial] map each vertex v to the set of variables that require phi definitions at v *)
  let vertex_to_phivars_map = phi_variables_map xidfs_map in
  (* 2B. find the set of referenced local variables in the graph *)
  let xrefs = referenced_variables graph root in   
  (* 2C. extend the given phimap with entries x -> (new_x,[]) for every local variable requiring a phi-entry at v . The empty list is filled in during the final graph rewrite step. *)
  let phimap1, fgen1 = augment_phimap graph fgen vertex_to_phivars_map phimap in
  (* 2D. walk the graph, rewriting each block and introducing new copies of variables as necessary. 
   * All locals are initialized in wasm. The initial stack therefore maps x to stack [x]. *)
  let xstack0 = XSet.fold (fun x map -> XMap.add x [x] map) xrefs XMap.empty in
  let queue0 = [(root,root,xstack0)]
  and visited0 = G.VSet.empty
  and rawproof0 = []
  in
  (*
  Debug.if_debug_high (fun () -> Printf.printf "rewriting to target graph: original graph has %d vertices"
                                     (graph.G.free_vertex-1));  
  *)
  rewrite_graph graph config phimap1 fgen1 queue0 visited0 rawproof0

let print_phi_graph: string -> ufunc_ir -> unit =
  fun msg ir ->
  Printf.printf "\n%s" msg;
  Printf.printf "\nRoot %s" (G.string_of_vertex ir.root_vertex);
  Printf.printf "\nGraph  { %s }" (string_of_instr_graph ir.body_graph);
  Printf.printf "\nPhiMap { %s }" (phi_map_to_string ir.phi_map);
  Printf.printf "\n"


(* =============== Proof generation ===================== 

let build_refinement_map: ('a,'b) instr_graph -> raw_ssa_proof -> refinement_map = 
  fun src_graph rawproof ->
  List.fold_left  
    (fun rmap (u,v,xxmap) ->
      let pair_formula = (* for edge (u,v) and var map xxmap , create a state pair function *)
        (fun (src,tgt) ->
          let src_l = locals src
          and tgt_l = locals tgt
          in
          let locals_equality =
            (* local at source index x is equal to local at target index x' for all pairs (x,x') *)
            XMap.fold
              (fun x x' eql ->
                let x_ptr = VarPtr (noregion x)
                and xprime_ptr = VarPtr (noregion x')
                in
                let eq_x_xprime =
                  ValsRelForm(SelectVal (src_l, x_ptr), IntEq, SelectVal (tgt_l, xprime_ptr))
                in
                eq_x_xprime::eql
              )
              xxmap
              []
          in
          AndForm
            [
              ArrsEqForm (values src, values tgt);
              PtrsRelForm (stack_pointer src, IntEq, stack_pointer tgt);
              
              AndForm locals_equality;
              
              ArrsEqForm (globals src, globals tgt);
              ArrsEqForm (uf_memory src, uf_memory tgt)
            ]
        )
      in
      let e = (u,v) in
      let rmap1 = 
        if is_call_vertex v src_graph then 
          SourceEdge_TargetEdgeMap.add (e,e,PreCall) pair_formula rmap
        else if is_call_vertex u src_graph then 
          SourceEdge_TargetEdgeMap.add (e,e,PostCall) pair_formula rmap
        else
          SourceEdge_TargetEdgeMap.add (e,e,Initial) pair_formula
            (SourceEdge_TargetEdgeMap.add (e,e,Final) pair_formula rmap)
      in
      (*
      let _ = (* print proof assertions *)
        Printf.printf "\n proof assertion for edge %d->%d:" (G.vertex_to_int u) (G.vertex_to_int v);
        XMap.iter (fun x x' -> Printf.printf " SL(%ld)=TL(%ld) " x x') xxmap
      in
      *)
      rmap1
    )
    SourceEdge_TargetEdgeMap.empty
    rawproof

    

let generate_ssa_proof: ufunc_ir -> ufunc_ir -> raw_ssa_proof -> proof = 
  fun source_ir target_ir rawproof ->
  let source_graph = source_ir.body_graph in

  (* 1. each edge is related to itself. Thus, the checkpoints are simply pairs (e,e) *)
  let checkpoints =
    List.map (fun (u,v,_) -> ((u,v), (u,v))) rawproof
  in

  (* 2. the refinement map for edge pair (e,e) is as follows
   * - source stack = target stack
   * - source globals = target globals
   * - source local x = target local for x in the raw proof
   *)

  let refinement_map = build_refinement_map source_graph rawproof in

  (* 3. the frontier of an edge e=(u,v) is the set of outgoing edges of vertex v *)
  let frontier_map =
    List.fold_left
      (fun fmap (u,v,_) ->
        let succs_v = List.map fst (G.vertex_succs v source_graph) in
        let succ_edges = List.map (fun w -> (v,w)) succs_v in
        TargetEdgeMap.add (u,v) succ_edges fmap 
      )
      TargetEdgeMap.empty
      rawproof
  in

  (* 4. a target path is thus just a pair of edges of the form (u,v);(v,w). 
   * The corresponding source path is the same. *)
  let path_match_map =
    List.fold_left
      (fun pmap (u,v,_) ->
        let succs_v = List.map fst (G.vertex_succs v source_graph) in

        (* fold over all successors w of vertex v *)
        List.fold_left
          (fun pmap2 w ->
            let u_to_w_via_v = [u;v;w] in 
            SourceEdge_TargetPathMap.add ((u,v), u_to_w_via_v) u_to_w_via_v pmap2
          )
          pmap
          succs_v
      )
      SourceEdge_TargetPathMap.empty
      rawproof
  in
  let proof = {
      func_id = target_ir.func_id;
      checkpoints = checkpoints;
      refinement_map = refinement_map;
      frontier_map = frontier_map;
      path_match_map = path_match_map;
      debugs = []
    }
  in
  proof
 *)


                
(* ================ Proof Generation =================== *)

let pair_formula: G.vertex -> G.vertex -> var_var_map -> state_pair_formula
  = (* for edge (u,v) and var map xxmap , create a state pair function *)
  fun u v xxmap ->
  (* DEBUG
  let _ =
    Printf.printf "\nxxmap for edge (%s, %s)" (G.string_of_vertex u) (G.string_of_vertex v);
    XMap.iter (fun x x' -> Printf.printf "\n\t src %ld = tgt %ld " x x') xxmap
  in
   *)
  (fun (src,tgt) ->
    let src_l = locals src
    and tgt_l = locals tgt
    in
    let locals_equality =
      (* local at source index x is equal to local at target index x' for all pairs (x,x') *)
      XMap.fold
        (fun x x' eql ->
          let x_ptr = VarPtr (noregion x)
          and xprime_ptr = VarPtr (noregion x')
          in
          let eq_x_xprime =
            ValsRelForm(SelectVal (src_l, x_ptr), IntEq, SelectVal (tgt_l, xprime_ptr))
          in
          (* Debug.if_debug_high (fun () -> Printf.printf "src %ld = tgt %ld " x x'); *)
          eq_x_xprime::eql
        )
        xxmap
        []
    in
    let formula = 
      AndForm
        [
          ArrsEqForm (values src, values tgt);
          PtrsRelForm (stack_pointer src, IntEq, stack_pointer tgt);
          
          AndForm locals_equality;
          
          ArrsEqForm (globals src, globals tgt);
          SymEqForm (uf_memory src, uf_memory tgt)
        ]
    in
    (*
    Debug.if_debug_high (fun () ->
        Printf.printf "\n\t pair formula for (%s,%s): %s" (G.string_of_vertex u) (G.string_of_vertex v)
          (string_of_formula formula));
    *)
    formula
  )

                
let add_to_refmap:
      ('a,'b) instr_graph
      -> G.vertex * G.vertex * G.vertex
      -> pair_formula_map_t
      -> refinement_map
      -> refinement_map
  =
  fun src_graph (u,v,w) pfmap refmap ->
  let ein = (u,v)
  and eout = (v,w)
  in
  let pfin = EMap.find ein pfmap
  and pfout = EMap.find eout pfmap 
  in

  let refmap1 = (* PreCall=Initial and PostCall=Final here, as we're not checking paths with multiple vertices *)
    if is_call_vertex v src_graph then
      SourceEdge_TargetEdgeMap.add (ein,ein,PreCall) pfin
        (SourceEdge_TargetEdgeMap.add (ein,ein,Initial) pfin
           (SourceEdge_TargetEdgeMap.add (eout,eout,PostCall) pfout
              (SourceEdge_TargetEdgeMap.add (eout,eout,Final) pfout refmap)))
    else 
      SourceEdge_TargetEdgeMap.add (ein,ein,Initial) pfin
        (SourceEdge_TargetEdgeMap.add (eout,eout,Final) pfout refmap)
  in
  refmap1

  

let generate_ssa_proof: ufunc_ir -> ufunc_ir -> raw_ssa_proof -> proof = 
  fun source_ir target_ir rawproof ->
  let source_graph = source_ir.body_graph in

  let pair_formula_map = (* maps an edge to its pair formula *)
    List.fold_left
      (fun pfmap (u,v,xxmap) ->
        EMap.add (u,v) (pair_formula u v xxmap) pfmap
      )
      EMap.empty
      rawproof
  in
    

  let checkpoints,frontier_map,path_match_map,refinement_map = 
    List.fold_left
      (fun (chks,fmap,pmap,refmap) (u,v,_) ->
        let e = (u,v) in

        (*
        Debug.if_debug_high (fun () -> Printf.printf "\n processing rawproof edge %s -> %s " (G.string_of_vertex u) (G.string_of_vertex v));
        *)
        
        (* each edge is related to itself. Thus, the checkpoints are simply pairs (e,e) *)
        let chks1 = (e,e)::chks in
        
        (* the frontier of an edge e=(u,v) is the set of outgoing edges of vertex v. 
         * a target path is a pair of edges of the form (u,v);(v,w). 
         * The corresponding source path is the same. *)
        
        let succs_v = List.map fst (G.vertex_succs v source_graph) in
        let succ_edges = List.map (fun w -> (v,w)) succs_v in
        
        let fmap1 = TargetEdgeMap.add e succ_edges fmap in
        
        (* fold over all successors w of vertex v *)
        let pmap1, refmap1 = 
          List.fold_left
            (fun (pmap,refmap) w ->
              let u_to_w_via_v = [u;v;w] in
              
              (*
              Debug.if_debug_high (fun () -> Printf.printf "\nSSA: Entering pathmap: edge %s |-> path %s" (G.string_of_basic_edge e) (G.string_of_basic_path u_to_w_via_v));
              *)
              
              let pmap'   = SourceEdge_TargetPathMap.add (e, u_to_w_via_v) u_to_w_via_v pmap
              and refmap' = add_to_refmap source_graph (u,v,w) pair_formula_map refmap in
              (pmap',refmap')
            )
            (pmap,refmap)
            succs_v
        in
        (chks1,fmap1,pmap1,refmap1)
      )
      ([],TargetEdgeMap.empty,SourceEdge_TargetPathMap.empty,SourceEdge_TargetEdgeMap.empty)
      rawproof
  in
  let proof = {
      transform = "SSA";
      interpretation = INone;
      (*
      interpretation = IFull;
      *)
      
      func_id = target_ir.func_id;
      checkpoints = checkpoints;
      refinement_map = refinement_map;
      frontier_map = frontier_map;
      path_match_map = path_match_map;
      debugs = []
    }
  in
  proof
                
                
    
(* ================ Main function =================== *)                

let ssa_pass_fun: ufunc_ir -> pass_config -> ufunc_ir * pass_out =
  fun source_ir config ->
  Debug.if_debug_high (fun () -> print_phi_graph "Source" source_ir);

  (* determine last allocated local index *)
  let Types.FuncType (fty_ins, _) = lookup_func_type source_ir.types_table source_ir.ftype in
  let fgen_init = initial_local_gen (fty_ins @ source_ir.func_locals) in
  (* do SSA conversion *)
  let target_body_graph, target_phimap, rawproof, fgen =    
    ssa_on_graph (source_ir.body_graph) config (source_ir.root_vertex) (source_ir.phi_map) fgen_init
  in

  Debug.if_debug_high (fun () -> Printf.printf "number of new SSA variables: %d:"
                                     (List.length fgen.new_local_types));

  let target_ir = { (* copy over most of source_ir *)
      func_id = source_ir.func_id;
      func_index = source_ir.func_index;
      ftype = source_ir.ftype;
      types_table = source_ir.types_table;
      ftypes = source_ir.ftypes;
      (* This function's graph data *)
      func_locals = source_ir.func_locals @ fgen.new_local_types;
      root_vertex = source_ir.root_vertex;
      sink_vertex = source_ir.sink_vertex;
      phi_map = target_phimap; 
      body_graph = target_body_graph;
      region = source_ir.region;
    }
  in
  Debug.if_debug_high (fun () -> print_phi_graph "Target" target_ir); 

  let pass_out = 
    if config.gen_proof
    then {pass_id = "ssa"; proofs = [generate_ssa_proof source_ir target_ir rawproof]}
    else empty_pass_out
  in
  (target_ir, pass_out)


  
let ssa_pass : upass = 
  init_pass
    "ssa"
    ssa_pass_fun
                          

  
  

    
(* TODOS: 
 * - scan_graph need not be a BFS, simply look up each vertex.
 *)
