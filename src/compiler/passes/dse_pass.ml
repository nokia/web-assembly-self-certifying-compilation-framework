(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)

(* Iterative Dead Store Elimination (DSE) Pass. 
 *
 * Assumes that the program is in SSA form. 
 * 
 * The goal is to remove stores to local memory (i.e., "LocalSet k", for some k) 
 * that are never referenced (i.e., no "LocalGet k"). These are called "dead stores".
 * 
 * NOTE: in wasm, parameters to a function are also treated as local variables. 
 * Those are excluded from the dead-store set. 
 * 
 * SSA considerably simplifies this process, as each local variable is set at most once.
 * 
 * Removing a dead store may result in simplifications that remove references to other 
 * stores. For instance, consider "...; LocalGet 0; LocalGet 1; mul; LocalSet 3; ...". 
 * Removing (LocalSet 3) implies that the multiplication is unnecessary; thus, its arguments 
 * (obtained via LocalGets) are also unnecessary. 
 *
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

module SSA = Ssa_pass


(* store_info keeps track of definitions and uses of local variables *)
type loc_t = G.vertex Int32Map.t  (* maps a local variable to its defining vertex, if any *)
type count_t = int Int32Map.t     (* maps a local variable to the number of uses of that variable *)
               
type store_info_t = {
    loc: loc_t;
    count: count_t; 
  }

type rawproof_t = int32 list      (* list of variables whose definitions are removed  *)


let range: int32 -> int32 -> int32 list =
  fun l h -> (* range: low..high, both inclusive, with small values of l and h *)
  let res = ref [] in
  for k = (Int32.to_int h) downto (Int32.to_int l) do
    res := (Int32.of_int k)::(!res)
  done;
  !res



let find_dead_locals: store_info_t -> Int32Set.t =
  fun smap ->
  let bindings = Int32Map.bindings smap.count in
  let zero_bindings = List.filter (fun (_,c) -> c=0) bindings in 
  Int32Set.of_list (List.map fst zero_bindings)



let print_store_info: store_info_t -> unit =
  fun smap ->
  Printf.printf "\nStore Info";
  Int32Map.iter
    (fun i v ->
      Printf.printf "\n\t local %ld defined at vertex %s" i (G.string_of_vertex v))
    smap.loc;
  Int32Map.iter
    (fun i k -> Printf.printf "\n\t local %ld count = %d" i k)
    smap.count
  
                      

let add_loc: int32 -> G.vertex -> store_info_t -> store_info_t = 
  fun x v smap ->
  match Int32Map.find_opt x smap.loc with
  | None ->
     {smap with loc = Int32Map.add x v smap.loc}
  | Some _ ->
     failwith(Printf.sprintf "dse/add_loc: Not SSA? Found more than one defining location for variable %ld" x)

             
let increment_count: int32 -> store_info_t -> store_info_t = 
  fun x smap ->
  match Int32Map.find_opt x smap.count with
  | None ->
     {smap with count = Int32Map.add x 1 smap.count}
  | Some k ->
     {smap with count = Int32Map.add x (k+1) smap.count}



             
let decrement_count: int32 -> store_info_t -> store_info_t = 
  fun x smap ->
  match Int32Map.find_opt x smap.count with
  | None ->
     failwith(Printf.sprintf "dse/decrement_count: None count entry for variable %ld" x)
  | Some 0 ->
     failwith(Printf.sprintf "dse/decrement_count: zero count entry for variable %ld" x)
  | Some k -> 
     {smap with count = Int32Map.add x (k-1) smap.count}
                            
       

let scan_phis: G.vertex -> phi_vertex_map -> store_info_t -> store_info_t =
  fun v vmap smap ->

  Int32Map.fold       
    (fun _ (x, xrhs) smap0 ->
      (* add definition location for variable x *)
      let smap1 = add_loc x v smap0 in 

      (* increment use count for all variables in the rhs *)      
      List.fold_right 
        (fun (_,y) smap2 -> increment_count y smap2)
        xrhs
        smap1
    )
    vmap
    smap



let scan_instrs: G.vertex -> Ast.instr list -> store_info_t -> store_info_t =
  fun v il smap ->
  List.fold_right
    (fun i smap0 ->
      match i.it with
      | Ast.LocalSet x (* add definition location for variable x *)
        | Ast.LocalTee x -> 
         add_loc x.Source.it v smap0
      | Ast.LocalGet x -> (* increment use count for variable x *)
         increment_count x.Source.it smap0
      | _ ->
         smap0
    )
    il
    smap
      
              
          
                      
let phimap_at_vertex: G.vertex -> phi_map -> phi_vertex_map =
  (* NOTE: duplicate of function in ssa_pass.ml *)
  fun v phimap ->
  match G.VMap.find_opt v phimap with
  | None -> Int32Map.empty
  | Some(vmap) -> vmap
                      
              
let build_store_map:
      ('a,'b) instr_graph
      -> G.vertex
      -> phi_map
      -> store_info_t 
      -> store_info_t
  =
  fun src_graph src_root src_phimap smap0 ->

  let rec bfs queue visited smap = 
    match Q.dequeue queue with
    | None -> smap
    | Some(v,queue1) -> 
       if G.VSet.mem v visited then (* continue *)
         bfs queue1 visited smap
       else 
         match G.vertex_label v src_graph with
         | None ->
            (prerr_endline ("bdse/build_store_map: None lookup at " ^ G.string_of_vertex v);
             smap)
              
         | Some(block, _) ->       
            let v_phis = phimap_at_vertex v src_phimap in
            let smap1 = scan_phis v v_phis smap in
            let smap2 = scan_instrs v block.instrs smap1 in
            let visited1 = G.VSet.add v visited in 
            
            let unvisited_succs_v = 
              List.filter
                (fun w -> not(G.VSet.mem w visited1))
                (List.map fst (G.vertex_succs v src_graph))
            in
            let queue2 = Q.enqueue_list unvisited_succs_v queue1 in 
            bfs queue2 visited1 smap2
                
  in
  let queue0 = [src_root]
  and visited0 = G.VSet.empty
  in
  bfs queue0 visited0 smap0
  

let stack_movement: Ast.instr -> (int * int) option = 
  fun i ->
  (* for each instruction, returns pair (m,n) where m is the number of values popped
   * from the stack as arguments for the instruction, and n is the number of values pushed
   * to the stack as a result. 
   *
   * For call and return instructions we return None to indicate that those quantities are unknown.*)
  
  match i.it with
 
    | Nop    -> Some(0,0)                 (* do nothing *)
    | Drop   -> Some(1,0)                 (* forget a value *)
    | LocalGet _ -> Some(0,1)             (* read local variable *)
    | Unary _ -> Some(1,1)                (* unary numeric operator *)
    | Binary _ -> Some(2,1)               (* binary numeric operator *)
    | Convert _ -> Some(1,1)              (* conversion *)
    | GlobalGet _ -> Some(0,1)            (* read global variable *)
    | Const _ -> Some(0,1)                (* constant *)

    | MemorySize -> Some (0,1)
    | MemoryGrow -> None


    | LocalSet _                          (* write local variable *)
      | LocalTee _                        (* write local variable and keep value *)
      | GlobalSet _                       (* write global variable *)
      | Store    _                        (* write memory at address *)
      | Load     _                        (* read memory at address *)                 

      | Test _                              (* numeric test *)
      | Compare _                           (* numeric comparison *)
                
      | Call _                           (* call function *)
      | CallIndirect _ -> None              (* call function through table *)
                          
                          

    | Unreachable                         (* trap unconditionally *)
      | Return                              (* break from function body *)                       
      | Select                              (* branchless conditional *)
      | Block _                             (* execute in sequence *)
      | Loop _                              (* loop header *)
      | If _                                (* conditional *)
      | Br _                                (* break to n-th surrounding label *)
      | BrIf _                              (* conditional break *)
      | BrTable _                           (* indexed break *)
      -> failwith("unexpected or not-handled operator " ^ string_of_instr_inline i)

 
let rec manydrops: int -> Ast.instr list =
  fun k ->
  if (k <=0) then [] else (noregion Ast.Drop)::(manydrops (k-1))


                                      
let rec drop: Ast.instr list -> int -> Ast.instr list * int32 list =
  fun il k ->
  (* returns a new instruction list that is equivalent to dropping k 
   * entries (k >=0) from the stack after processing il in reverse, 
   * and also reports dropped LocalGets *)
  if k <= 0 then (il,[])
  else 
    match il with
    | [] -> (manydrops k, [])
    | i::rest ->
       match stack_movement i with
       | None -> ((manydrops k)@il, [])
       | Some(m,n) ->
          (* the instruction pops m elements from stack and pushes n. 
           * the n elements are irrelevant iff k>=n AND the instruction has no side effect.
           * In that case, the instruction list is equivalent to one
           * where that instruction is replaced by a drop of (m+(k-n)) 
           * entries; this value is nonnegative as m>=0 and k>=n>=0. 
           *)
          if k < n then ((manydrops k)@il, [])
          else
            let il', lgets' = drop rest (k+m-n) in
            match i.it with
            | Ast.LocalGet x -> (il', x.Source.it::lgets')
            | _ -> (il',lgets')
                     
      

let remove_dead_store_from_phimap:
      int32
      -> phi_vertex_map
      -> (phi_vertex_map * int32 list) option
  =
  fun k vphis ->
  (* find if there is an assignment to k in vphis and extract local references from rhs of phi-assignment *)
  let loc = ref None in
  let _ = 
    Int32Map.iter 
      (fun l (x,xasgns) -> 
        if Int32.equal x k then loc := Some(l, List.map snd xasgns) else ()
      )
      vphis
  in
  (* remove the entry if found *)
  match !loc with
  | None -> None
  | Some(l,lgets) -> Some(Int32Map.remove l vphis, lgets)                   



let rec remove_store_and_propagate_drop: 
          int32                                (* dead variable *)
          -> Ast.instr list                    (* processed tail of instruction list -- to keep*)
          -> Ast.instr list                    (* unprocessed instructions in reverse *)
          -> Ast.instr list * int32 list
  =
  fun k tail rev_il ->
  match rev_il with
  | [] ->
     failwith(Printf.sprintf "dse/remove_store: No store found for dead variable %ld" k)

  | i::rev_rest ->
     match i.it with
     | Ast.LocalSet x when (Int32.equal x.Source.it k) -> (* turn set into drop and propagate further *)
        let modified_rev_rest, removed_lgets = drop rev_rest 1 in
        ((List.rev modified_rev_rest)@tail, removed_lgets)
               
     | Ast.LocalTee x when (Int32.equal x.Source.it k) -> (* turn tee into nop and stop *)
        ((List.rev ((noregion Ast.Nop)::rev_rest))@tail, []) 
          
     | _ -> 
        remove_store_and_propagate_drop k (i::tail) rev_rest



let remove_dead_store_from_instrs:
      int32
      -> Ast.instr list
      -> Ast.instr list * int32 list
  =
  fun k il ->
  remove_store_and_propagate_drop k [] (List.rev il)
        
      

      
let remove_dead_store:
      int32                                                (* store to be removed *)
      -> G.vertex                                          (* at vertex *)
      -> ('a,'b) instr_graph
      -> phi_map
      -> ('a,'b) instr_graph * phi_map * int32 list
  =
  fun k v graph phimap ->
  (* remove entry for k from phi entries *)
  let vphis = phimap_at_vertex v phimap in
  match remove_dead_store_from_phimap k vphis with
  | Some(vphis1, lgets) ->
     let phimap1 = G.VMap.add v vphis1 phimap in 
     (graph, phimap1, lgets)
  | None ->
     (* remove entry for k from instruction list *)
     match G.vertex_label v graph with
     | None ->
        prerr_endline ("dse_pass/remove_dead_store: None lookup at " ^ G.string_of_vertex v);
        (graph, phimap, [])
          
     | Some (block, _) ->
        let instrs1, lgets = remove_dead_store_from_instrs k block.instrs in 
        let block1 = { block with instrs = instrs1 } in
        let graph1 = G.add_vertex_label v (block1, ()) graph in
        (graph1, phimap, lgets)
          


let rec build_target_graph:
      ('a,'b) instr_graph
      -> phi_map
      -> Int32Set.t 
      -> store_info_t
      -> ('a,'b) instr_graph * phi_map * store_info_t
  =
  fun graph phimap old_dead_locals smap ->
  (* For each block containing a dead store, either remove the store from the phimap 
   * or replace the store instruction with (drop). Then iterate on newly dead variables. 
   * Return new graph, new phi map and new store info, containing only live locals and parameters. *)

  let all_dead_locals = find_dead_locals smap in
  let new_dead_locals = Int32Set.diff all_dead_locals old_dead_locals in

  Debug.if_debug_high (fun () ->
      Printf.printf "\nRewriting to Target. Newly dead locals: ";
      Int32Set.iter (fun x -> Printf.printf "%ld " x) new_dead_locals
    );

  if (Int32Set.is_empty new_dead_locals) then
    (graph,phimap,smap)
  else
    (* replace new dead stores with (drop) and simplify, keeping track of newly eliminated LocalGets *)
    let graph1,phimap1,lgets1= 
      Int32Set.fold
        (fun k (graph,phimap,lgets) ->
          match Int32Map.find_opt k smap.loc with
          | None ->
             let _ = Debug.if_debug_high (fun () -> Printf.eprintf "Dead local variable %ld is never defined" k) in
             (graph,phimap,lgets)
               
          | Some(v) -> (* k is defined at vertex v *)
             let graph',phimap',lgets' = remove_dead_store k v graph phimap in
             (graph',phimap',lgets'@lgets)
        )
        new_dead_locals
        (graph,phimap,[])
    in
    (* decrement count for each local get that is newly eliminated *)
    let smap1 =
      List.fold_left
        (fun smap k -> decrement_count k smap)
        smap
        lgets1
    in
    (* go around again *)
    build_target_graph graph1 phimap1 all_dead_locals smap1 

    
let generate_dse_proof: ufunc_ir -> ufunc_ir -> int32 -> int32 -> Int32Set.t -> proof = 
  fun src_ir tgt_ir first_local last_local dead_locals ->

  let source_graph = src_ir.body_graph in
  let bedges = G.edges source_graph in
  let edges = List.map (fun (u,_,v) -> (u,v)) bedges in 

  
  let all_locals = Int32Set.of_list (range 0l last_local) in
  let preserved_locals = Int32Set.diff all_locals dead_locals in
  let preserved_locals_list = Int32Set.elements preserved_locals in 

  Debug.if_debug_high
    (fun () ->
      Printf.printf "\n Proof: Preserved locals: ";
      List.iter (fun x -> Printf.printf "%ld " x) preserved_locals_list
    );
          
  let pair_formula =
    (fun (src,tgt) ->
      let src_l = locals src
      and tgt_l = locals tgt
      in
      let locals_equality =
        List.map
          (fun x ->
            let xptr = VarPtr (noregion x) in
            ValsRelForm(SelectVal (src_l, xptr), IntEq, SelectVal (tgt_l, xptr))
          )
          preserved_locals_list
      in
      AndForm
        [
          ArrsEqForm (values src, values tgt);
          PtrsRelForm (stack_pointer src, IntEq, stack_pointer tgt);
          
          AndForm locals_equality;
          
          ArrsEqForm (globals src, globals tgt);
          SymEqForm (uf_memory src, uf_memory tgt)
        ]
    )
  in
  let checkpoints = List.map (fun e -> (e,e)) edges in
  let refinement_map =
    List.fold_left
      (fun map e -> 
        let (u,v) = e in
        let map1 = 
          if is_call_vertex v source_graph then
            SourceEdge_TargetEdgeMap.add (e,e,PreCall) pair_formula map
          else map
        in 
        let map2 =
          if is_call_vertex u source_graph then
            SourceEdge_TargetEdgeMap.add (e,e,PostCall) pair_formula map1
          else map1
        in 
        SourceEdge_TargetEdgeMap.add (e,e,Initial) pair_formula
          (SourceEdge_TargetEdgeMap.add (e,e,Final) pair_formula map2)
      )
      SourceEdge_TargetEdgeMap.empty
      edges
  in
  (* the frontier of an edge e=(u,v) is the set of outgoing edges of vertex v *)
  let frontier_map =
    List.fold_left
      (fun fmap (u,v) ->
        let succs_v = List.map fst (G.vertex_succs v source_graph) in
        let succ_edges = List.map (fun w -> (v,w)) succs_v in
        TargetEdgeMap.add (u,v) succ_edges fmap 
      )
      TargetEdgeMap.empty
      edges
  in
  (* a target path is thus just a pair of edges of the form (u,v);(v,w). 
   * The corresponding source path is the same. *)
  let path_match_map =
    List.fold_left
      (fun pmap (u,v) ->
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
      edges
  in
  let proof = {
      transform = "DSE";
      interpretation = INone;
      

      func_id = tgt_ir.func_id;
      checkpoints = checkpoints;
      refinement_map = refinement_map;
      frontier_map = frontier_map;
      path_match_map = path_match_map;
      debugs = []
    }
  in
  proof  

                      
(* ================ Main function =================== *)                

let dse_pass_fun: ufunc_ir -> pass_config -> ufunc_ir * pass_out =
  fun source_ir config ->
  Debug.if_debug_high (fun () -> SSA.print_phi_graph "DSE: Source" source_ir); 

  (* determine first local index *)
  let Types.FuncType (parameter_types, _) =
    lookup_func_type source_ir.types_table source_ir.ftype in
  let local_types = source_ir.func_locals in
  let first_local = List.length parameter_types in 
  let last_local = first_local + (List.length local_types) -1 in

  let first_local_i32 = Int32.of_int first_local
  and last_local_i32 = Int32.of_int last_local
  in
  let local_vars = range first_local_i32 last_local_i32 in 

  (* build local uses map: mark uses for each variable as 0 *)
  let smap0: store_info_t = {
      loc = Int32Map.empty;
      count = List.fold_left (fun smap k -> Int32Map.add k 0 smap) Int32Map.empty local_vars;
    }
  in
  let smap1 = build_store_map (source_ir.body_graph) (source_ir.root_vertex) (source_ir.phi_map) smap0 in

  Debug.if_debug_high (fun () -> print_store_info smap1);

  (* find if any NON-parameter variables are dead *)
  let dead_locals = find_dead_locals smap1 in 

  if Int32Set.is_empty dead_locals then
    let _ = Debug.if_debug_high (fun () -> Printf.eprintf "\nNo dead locals found, no change to program") in 
    (source_ir, empty_pass_out)
  else
    let _ = 
      Debug.if_debug_high (fun () -> 
          Printf.printf "\nDead locals: ";
          Int32Set.iter (fun x -> Printf.printf "%ld " x) dead_locals
        )
    in
  
    (* build target graph *)
    let target_body_graph, target_phimap, smap2 = 
      build_target_graph (source_ir.body_graph) source_ir.phi_map Int32Set.empty smap1  in
  
    (* set up the target ir *)
    let target_ir = { (* copy over most of source_ir *)
        func_id = source_ir.func_id;
        func_index = source_ir.func_index;
        ftype = source_ir.ftype;
        types_table = source_ir.types_table;
        ftypes = source_ir.ftypes;
        (* This function's graph data *)
        func_locals = source_ir.func_locals;
        root_vertex = source_ir.root_vertex;
        sink_vertex = source_ir.sink_vertex;
        
        phi_map = target_phimap; (* BUG: source_ir.phi_map; *)
        body_graph = target_body_graph;
        
        region = source_ir.region;
      }
    in
    let _ = Debug.if_debug_high (fun () -> SSA.print_phi_graph "DSE: Target" target_ir) in 
    let pass_out = 
      if config.gen_proof then
        let dead_locals1 = find_dead_locals smap2 in 
        {pass_id = "dse";
         proofs = [generate_dse_proof source_ir target_ir first_local_i32 last_local_i32 dead_locals1]}
      else empty_pass_out
    in
    (target_ir, pass_out)


      
let dse_pass : upass = 
  init_pass
    "dse"
    dse_pass_fun
                          
                      
