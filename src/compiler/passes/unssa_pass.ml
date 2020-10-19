(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)

(* The UnSSA pass removes the phi-functions attached to a vertex, 
 * pushing the phi-updates "up" to each entering edge. 
 * 
 * This is carried out by adding a fresh vertex, denoted [u,v], for each original edge (u,v). 
 * and connecting it up as u->[u,v]->v in the target. The phi-updates for (u,v) are pushed to vertex [u,v].
 * 
 * For the equivalence proof, relate a path u->[u,v]->v->[v,w] in the target with 
 * path u->v->w in the source. The initial and final edges of these paths are related by the identity relation. 
 *)


(* In more detail, the procedure:
 * 
 * 1. scans the source graph, building a map from edge (u,v) to the instructions to be attached to [u,v]. 
 * 
 * 2. builds the target graph from the map, 
 *       + adding vertex [u,v] and the block of instructions it contains
 *       + removing edge (u,v) and introducing the new edges u->[u,v] and [u,v]->v, 
 *       + setting the phimap to empty. 
 * 
 * 3. sets up the proof from the map. 
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

               
module E = struct
  type t = G.basic_edge
  let compare: t -> t -> int = Stdlib.compare
end

module EMap = Map.Make(E)

(* maps an edge (u,v) to its associated phi-instruction list *)
type emap_t = (Ast.instr list) EMap.t

(* maps an edge (u,v) to the newly introduced vertex [u,v] for that edge *)
type rawproof_t = G.vertex EMap.t


let extract_instructions: G.vertex -> phi_vertex_map -> Ast.instr list =
  fun u vphis ->
  Int32Map.fold
    (fun _ (lhs, rhs_phi) il ->
      let rhs = List.assoc u rhs_phi in
      let lhs_v = noregion lhs
      and rhs_v = noregion rhs
      in
      [noregion (Ast.LocalGet rhs_v);
       noregion (Ast.LocalSet lhs_v)
      ]
      @il
    )
    vphis
    []

    

let phimap_at_vertex: G.vertex -> phi_map -> phi_vertex_map =
  (* NOTE: duplicate of function in ssa_pass.ml *)
  fun v phimap ->
  match G.VMap.find_opt v phimap with
  | None -> Int32Map.empty
  | Some(vmap) -> vmap


                    
let build_edge_map:
      ('a,'b) instr_graph
      -> G.vertex
      -> phi_map
      -> emap_t
  =
  fun src_graph src_root src_phimap ->

  let rec bfs queue visited emap = 
    match Q.dequeue queue with
    | None -> emap
    | Some((u,v),queue1) ->
       let v_phis = phimap_at_vertex v src_phimap in
       let uv_instrs = extract_instructions u v_phis in
       let emap1 = EMap.add (u,v) uv_instrs emap in

       if G.VSet.mem v visited then (* continue *)
         bfs queue1 visited emap1
       else 
         let all_edges_from_v =
           List.map (fun (w,_) -> (v,w)) (G.vertex_succs v src_graph) in
         let queue2 = Q.enqueue_list all_edges_from_v queue1 in 
         let visited1 = G.VSet.add v visited in
         bfs queue2 visited1 emap1

  in
  let queue = [(src_root, src_root)]
  and visited = G.VSet.empty
  and emap = EMap.empty
  in
  bfs queue visited emap
  
      

let build_target_graph:
      ('a,'b) instr_graph
      -> G.vertex 
      -> pass_config
      -> emap_t
      -> (('a,'b) instr_graph * rawproof_t)
  =
  fun src_graph src_root config emap ->
  (* fold over edge map, adding a new vertex for each edge and building 
   * the target graph and a raw proof *)
  EMap.fold
    (fun (u,v) uv_instrs (tgt, rawproof)->
      if (u,v) = (src_root,src_root) then (* ignore: don't add intermediate vertex *)
        (tgt,rawproof)
      else (* graph surgery: add intermediate vertex *)
        let uv_src_edge_label =
          (match G.edge_label (u,v) src_graph with
           | None ->
              failwith (Printf.sprintf "No edge label for edge %s -> %s?" (G.string_of_vertex u) (G.string_of_vertex v))
           | Some(l) -> l
          )
        in
        let uv_vertex_label = (init_block uv_instrs, ()) in      
        let uv, tgt1 = G.alloc_vertex uv_vertex_label tgt in
        
        let tgt2 = G.remove_basic_edge (u,v) tgt1 in
        let tgt3 = G.add_edge (u, uv_src_edge_label, uv) tgt2 in
        let tgt4 = G.add_edge (uv, (Jump, ()), v) tgt3 in
        
        let rawproof1 =
          if config.gen_proof then EMap.add (u,v) uv rawproof
          else rawproof
        in 
        (tgt4, rawproof1)
    )
    emap
    (src_graph, EMap.empty)
        
      


    
let generate_unssa_proof:  ufunc_ir -> ufunc_ir -> rawproof_t -> proof = 
  fun src_ir tgt_ir rawproof ->
  let src_graph = src_ir.body_graph
  and tgt_graph = tgt_ir.body_graph
  in
  (* checkpoints are edges (u,v) in source, (u,[u,v]) in target *)
  (* the frontier for (u,[u,v]) is the successors of v in the target, i.e., edges (v,[v,w]) *)
  (* the refinement relation between these pairs is the identity *)  
  (* a target path relates source edge (u,v) and tgt path (u,[u,v],v,[v,w]) to source path (u,v,w) *)

  let checkpoints,
      refinement_map,
      frontier_map,
      path_match_map
    =
    EMap.fold
      (fun (u,v) uv (chks,refs,fronts,paths) ->
        let succs_v_src = List.map fst (G.vertex_succs v src_graph) in        
        let succs_v_tgt = List.map fst (G.vertex_succs v tgt_graph) in

        let succ_edges_v_tgt = List.map (fun w -> (v,w)) succs_v_tgt in
        
        let chks1 = ((u,v), (u,uv))::chks in

        let fronts1 = TargetEdgeMap.add (u,uv) succ_edges_v_tgt fronts in

        let paths1,refs1 = (* build paths and refinement maps together *)
          List.fold_left
            (fun (pmap,rmap) w -> (* consider edge v->w in the source *)
              let vw = EMap.find (v,w) rawproof in 
              let lhs = ((u,v), [u;uv;v;vw]) in
              let rhs = [u;v;w] in
              let pmap1 = SourceEdge_TargetPathMap.add lhs rhs pmap in

              let rmap1 = 
                if is_call_vertex v src_graph then
                  SourceEdge_TargetEdgeMap.add ((u,v),(uv,v),PreCall) uf_state_pair_equiv rmap
                else rmap
              in 
              let rmap2 =
                if is_call_vertex u src_graph then
                  SourceEdge_TargetEdgeMap.add ((u,v),(u,uv),PostCall) uf_state_pair_equiv rmap1
                else rmap1
              in
              let rmap3 =
                SourceEdge_TargetEdgeMap.add ((u,v),(u,uv),Initial) uf_state_pair_equiv
                  (SourceEdge_TargetEdgeMap.add ((v,w),(v,vw),Final) uf_state_pair_equiv rmap2)
              in
              (pmap1, rmap3)
            )
            (paths,refs)
            succs_v_src
        in
        (chks1,refs1,fronts1,paths1)
      )
      rawproof
      ([],
       SourceEdge_TargetEdgeMap.empty,
       TargetEdgeMap.empty,
       SourceEdge_TargetPathMap.empty
      )
  in
  
  let proof = {
      transform = "UnSSA";
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

let unssa_pass_fun: ufunc_ir -> pass_config -> ufunc_ir * pass_out =
  fun source_ir config ->
  Debug.if_debug_high (fun () -> SSA.print_phi_graph "Source" source_ir); 

  (* build edge map *)
  let emap: emap_t =
    build_edge_map (source_ir.body_graph) (source_ir.root_vertex) (source_ir.phi_map) in

  (* build target graph *)
  let target_body_graph, rawproof = 
    build_target_graph (source_ir.body_graph) (source_ir.root_vertex) config emap in
  
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
      
      phi_map = G.VMap.empty;
      body_graph = target_body_graph;
      
      region = source_ir.region;
    }
  in
   Debug.if_debug_high (fun () -> SSA.print_phi_graph "Target" target_ir); 
  let pass_out = 
    if config.gen_proof
    then {pass_id = "unssa";
          proofs = [generate_unssa_proof source_ir target_ir rawproof]}
    else empty_pass_out
  in
  (target_ir, pass_out)


  
let unssa_pass : upass = 
  init_pass
    "unssa"
    unssa_pass_fun
                          
