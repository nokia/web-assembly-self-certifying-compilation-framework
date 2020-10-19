(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)

(* Compress Locals Pass. 
 *
 * This pass remove locals that are never refered to in the function. 
 * It also renames all locals so that the numbering is contiguous. 
 * Thus it is similar to "defragmentation". 
 * 
 * NOTE: in wasm, function parameters are also treated as local variables. 
 * Those are excluded from consideration. 
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


(* maps a local variable to the number of references (LocalGet or LocalSet) to that variable.
 * Not really necessary -- a map to unit would suffice, but this is interesting debug info. 
 *)
type ref_count_t = int Int32Map.t

(* 1-1 map from referenced variables to a contiguous range *)
type remap_t = int32 Int32Map.t

(* the raw proof is the remapping *)
type rawproof_t = remap_t


let print_refs: ref_count_t -> unit =
  fun refs ->
  Printf.printf "\nRef Count";
  Int32Map.iter
    (fun i k -> Printf.printf "\n\t local %ld count = %d" i k)
    refs
  
             
let increment_count: int32 -> ref_count_t -> ref_count_t = 
  fun x refs ->
  match Int32Map.find_opt x refs with
  | None ->
     Int32Map.add x 1 refs
  | Some k ->
     Int32Map.add x (k+1) refs
                            

let scan_phis: phi_vertex_map -> ref_count_t -> ref_count_t =
  fun vmap refs ->
  Int32Map.fold       
    (fun _ (x, xrhs) refs0 ->
      (* increment def. count for x *)
      let refs1 = increment_count x refs0 in 

      (* increment use count for all variables in the rhs *)      
      List.fold_right 
        (fun (_,y) refs2 -> increment_count y refs2)
        xrhs
        refs1
    )
    vmap
    refs



let scan_instrs: Ast.instr list -> ref_count_t -> ref_count_t =
  fun il refs ->
  List.fold_right
    (fun i refs0 ->
      match i.it with
      | Ast.LocalSet x -> (* increment def count for variable x *)
         increment_count x.Source.it refs0
      | Ast.LocalTee x -> (* increment def count for variable x *)
         increment_count x.Source.it refs0                         
      | Ast.LocalGet x -> (* increment use count for variable x *)
         increment_count x.Source.it refs0
      | _ ->
         refs0
    )
    il
    refs
      
              
                      
let phimap_at_vertex: G.vertex -> phi_map -> phi_vertex_map =
  (* NOTE: duplicate of function in ssa_pass.ml *)
  fun v phimap ->
  match G.VMap.find_opt v phimap with
  | None -> Int32Map.empty
  | Some(vmap) -> vmap
                      
              
let build_refs:
      ('a,'b) instr_graph
      -> G.vertex
      -> phi_map
      -> ref_count_t
  =
  fun src_graph src_root src_phimap ->

  let rec bfs queue visited refs = 
    match Q.dequeue queue with
    | None -> refs
    | Some(v,queue1) ->
       if G.VSet.mem v visited then (* continue *)
         bfs queue1 visited refs
       else 
         match G.vertex_label v src_graph with
         | None ->
            (prerr_endline ("compress-locals/build_refs: None lookup at " ^ G.string_of_vertex v);
             refs)
              
         | Some(block, _) ->       
            let v_phis = phimap_at_vertex v src_phimap in
            let refs1 = scan_phis v_phis refs in
            let refs2 = scan_instrs block.instrs refs1 in
            let visited1 = G.VSet.add v visited in 
            
            let unvisited_succs_v = 
              List.filter
                (fun w -> not(G.VSet.mem w visited1))
                (List.map fst (G.vertex_succs v src_graph))
            in
            let queue2 = Q.enqueue_list unvisited_succs_v queue1 in 
            bfs queue2 visited1 refs2

  in
  let queue = [src_root]
  and visited = G.VSet.empty
  and refs = Int32Map.empty
  in
  bfs queue visited refs
  


let remap_local_index:
      remap_t 
      -> int32
      -> int32
  =
  fun varmap l ->
  match Int32Map.find_opt l varmap with
  | None ->
     failwith(Printf.sprintf "compress-locals/remap_local_index: no mapping found for index %ld" l)
  | Some(k) ->
     k


let remap_var:
      remap_t 
      -> Ast.var
      -> Ast.var
  =
  fun varmap x ->
  noregion (remap_local_index varmap x.Source.it)
              
              
let remap_phis:
      remap_t
      -> phi_vertex_map
      -> phi_vertex_map 
  =
  fun varmap vphis ->
  Int32Map.map
    (fun (l,lrhs) ->
      let l' = remap_local_index varmap l 
      and lrhs' = List.map (fun (u,k) -> (u,remap_local_index varmap k)) lrhs
      in
      (l',lrhs')
    )
    vphis


let remap_instrs:
      remap_t 
      -> Ast.instr list
      -> Ast.instr list
  =
  fun varmap il -> 
  List.map
    (fun i ->
      match i.it with
      | Ast.LocalSet x ->
         let x' = remap_var varmap x in 
         noregion (Ast.LocalSet x')

      | Ast.LocalTee x ->
         let x' = remap_var varmap x in 
         noregion (Ast.LocalTee x')                  
                  
      | Ast.LocalGet x ->
         let x' = remap_var varmap x in 
         noregion (Ast.LocalGet x')
                  
      | _ -> i
    )
    il
    

          

let build_target_graph:
      ('a,'b) instr_graph
      -> G.vertex 
      -> phi_map
      -> remap_t
      -> ('a,'b) instr_graph * phi_map
  =
  fun src_graph src_root src_phimap varmap ->
  (* For each reachable block in the source graph, rename the entries in the phimap 
   * and in the block instructions according to the varmap *)

  let rec bfs queue visited tgt_graph tgt_phimap = 
    match Q.dequeue queue with
    | None -> (tgt_graph, tgt_phimap)
    | Some(v,queue1) -> (* invariant: queue is unvisited *)
       match G.vertex_label v src_graph with
       | None ->
          (prerr_endline ("compress-locals/build_target_graph: None lookup at " ^ G.string_of_vertex v);
           (tgt_graph, tgt_phimap))
            
       | Some(block, _) ->       
          let src_vphis = phimap_at_vertex v src_phimap in
          let tgt_vphis = remap_phis varmap src_vphis in
          let src_instrs = block.instrs in
          let tgt_instrs = remap_instrs varmap src_instrs in
          let tgt_block =  {block with instrs = tgt_instrs} in
          let tgt_graph1 = G.add_vertex_label v (tgt_block, ()) tgt_graph
          and tgt_phimap1 = G.VMap.add v tgt_vphis tgt_phimap
          in
          let visited1 = G.VSet.add v visited in 
          
          let unvisited_succs_v = 
            List.filter
              (fun w -> not(G.VSet.mem w visited1))
              (List.map fst (G.vertex_succs v src_graph))
          in
          let queue2 = Q.enqueue_list unvisited_succs_v queue1 in 
          bfs queue2 visited1 tgt_graph1 tgt_phimap1 

  in
  let queue = [src_root]
  and visited = G.VSet.empty
  in
  bfs queue visited src_graph src_phimap 




let range: int32 -> int32 -> int32 list =
  fun l h -> (* range: low..high, both inclusive, with small values of l and h *)
  let res = ref [] in
  for k = (Int32.to_int h) downto (Int32.to_int l) do
    res := (Int32.of_int k)::(!res)
  done;
  !res
  
          
          
let generate_compress_locals_proof: ufunc_ir -> ufunc_ir -> int32 -> int32 -> remap_t -> proof = 
  fun src_ir tgt_ir first_local last_local varmap ->

  let source_graph = src_ir.body_graph in
  let bedges = G.edges source_graph in
  let edges = List.map (fun (u,_,v) -> (u,v)) bedges in 

  let all_locals = range 0l last_local in

  
  let pair_formula =
    (fun (src,tgt) ->
      let src_l = locals src
      and tgt_l = locals tgt
      in
      let locals_equality =
        List.concat 
          (List.map
             (fun x ->
               if Int32.compare x first_local < 0 then (* this is a parameter, keep unchanged *)
                 let xptr = VarPtr (noregion x) in
                 [ValsRelForm(SelectVal (src_l, xptr), IntEq, SelectVal (tgt_l, xptr))]
               else
                 match Int32Map.find_opt x varmap with
                 | None -> (* x is not referenced in the source and is hence omitted from target *) []
                 | Some(y) -> (* add src-local(x) = tgt-local(y) *)
                    let xptr = VarPtr (noregion x)
                    and yptr = VarPtr (noregion y)
                    in
                    [ValsRelForm(SelectVal (src_l, xptr), IntEq, SelectVal (tgt_l, yptr))]
             )
             all_locals
          )
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
      transform = "CompressLocals";
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

  
let find_used_unused_locals: int32 -> int32 -> ref_count_t -> int32 list * int32 list =
  fun first_local last_local refs ->
  let used_locals = 
    List.filter
      (fun k -> (Int32.compare k first_local >= 0) && (Int32.compare k last_local <= 0))
      (List.map fst (Int32Map.bindings refs))
  in
  let unused_locals =
    List.filter
      (fun k -> not(List.mem k used_locals))
      (range first_local last_local)
  in
  (used_locals, unused_locals)


let build_varmap: int32 -> int32 -> int32 list -> Types.value_type list ->
                  remap_t * Types.value_type list
  = 
  fun first_local last_local used local_types ->

  let map0 = (* remap parameter i to i *)
    List.fold_left 
      (fun map i -> Int32Map.add i i map)
      Int32Map.empty
      (range 0l (Int32.pred first_local))
  in 
  let _,_,varmap,ltypes = 
    List.fold_left
      (fun (k,l,varmap,ltypes) kt ->
        (* k is the current source local, l is the next available local index in the target,
         * kt is the type of k, varmap is the map between current and new local indexes,
         * ltypes is the type list for the locals remapped in the target. 
         *)
        if List.mem k used then
          let k1 = Int32.succ k
          and l1 = Int32.succ l
          and varmap1 = Int32Map.add k l varmap
          and ltypes1 = ltypes@[kt]
          in
          (k1,l1,varmap1,ltypes1)
        else
          let k1 = Int32.succ k in (* move right along *)
          (k1,l,varmap,ltypes)
      )
      (first_local,first_local,map0,[])
      local_types
  in
  (varmap,ltypes)
  
                      
(* ================ Main function =================== *)                

let compress_locals_pass_fun: ufunc_ir -> pass_config -> ufunc_ir * pass_out =
  fun source_ir config ->
  (*
  SSA.print_phi_graph "Basic DSE: Source" source_ir; 
  *)

  (* count number of references to local variables. Map may be partial. *)
  let refs: ref_count_t = 
    build_refs (source_ir.body_graph) (source_ir.root_vertex) (source_ir.phi_map) in

  let _ = print_refs refs in 

  (* determine first local index *)
  let Types.FuncType (parameter_types, _) = lookup_func_type source_ir.types_table source_ir.ftype in
  let local_types = source_ir.func_locals in
  let first_local = List.length parameter_types in 
  let last_local = first_local + (List.length local_types) -1 in

  let first_local_i32 = Int32.of_int first_local
  and last_local_i32 = Int32.of_int last_local
  in

  (* find unused locals *)
  let used_locals, unused_locals = find_used_unused_locals first_local_i32 last_local_i32 refs in 

  if unused_locals = [] then
    (Printf.eprintf "\nNo unused locals found, no change to program";
     (source_ir, empty_pass_out))
  else
    let _ = Printf.printf "\nUnused locals: " in 
    let _ = List.iter (fun x -> Printf.printf "%ld " x) unused_locals in 
  
    (* build the variable renaming map *)
    let varmap, target_local_types = build_varmap first_local_i32 last_local_i32 used_locals local_types in

    (* rewrite source graph to target *)
    let target_body_graph, target_phimap = 
      build_target_graph (source_ir.body_graph) (source_ir.root_vertex) source_ir.phi_map varmap in
  
    (* set up the target ir *)
    let target_ir = { (* copy over most of source_ir *)
        func_id = source_ir.func_id;
        func_index = source_ir.func_index;
        ftype = source_ir.ftype;
        types_table = source_ir.types_table;
        ftypes = source_ir.ftypes;
        (* This function's graph data *)
        
        func_locals = target_local_types;                 (* change *)
          
        root_vertex = source_ir.root_vertex;
        sink_vertex = source_ir.sink_vertex;
        
        phi_map = target_phimap;                          (* change *)
        body_graph = target_body_graph;                   (* change *)
        
        region = source_ir.region;
      }
    in
    (*
    SSA.print_phi_graph "Basic DSE: Target" target_ir; 
    *)
    let pass_out = 
      if config.gen_proof then
        {pass_id = "compress-locals";
         proofs = [generate_compress_locals_proof source_ir target_ir first_local_i32 last_local_i32 varmap]}
      else empty_pass_out
    in
    (target_ir, pass_out)


      
let compress_locals_pass : upass = 
  init_pass
    "compress-locals"
    compress_locals_pass_fun
                          
                      
