(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


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

(* This is a very simplified version of a block merging pass:
 *  1: Go over all edges of a graph and check if they're mergeable
 *  2: Find the one that is mergeable, if any
 *  3: Merge that one single edge
 *  4: Return
 *
 *
 *  a   b   c   <- entry edge labels
 *   \  |  /
 *  ---------
 *  | blk a |   <- basic block
 *  ---------
 *      |       <- unconditional (and only) branch
 *  ---------
 *  | blk b |
 *  ---------
 *   /  |  \
 *  d   e   f  <- exit edge labels
 *
 * ... would transform into ...
 *
 *  a   b   c
 *   \  |  /
 *  ---------
 *  | blk c |   <- merged, where blk_c.instrs = blk_a.instrs @ blk_b.instrs
 *  ---------
 *   /  |  \
 *  d   e   f
 *
 * The "proof" / path_relation that is generated from each pass is a list
 * of four-edge pairs that relates every pair:
 *   (a, d); (a, e); (a, f); (b, d); ...; (c, f)
 *)


(* Generate the refinement_map. *)
let adjacents_to_refinement_map
  : (G.vertex list) * G.vertex * G.vertex * (G.vertex list)
  -> refinement_map =
  fun (prevs, src_v, dst_v, succs) ->
    (* The starting states are all the same because we merge into the src_v *)
    let src_state0_kvs =
      List.map
        (fun pv ->
          let src_e0 = (pv, src_v) in
          let tgt_e0 = (pv, src_v) in
          ((src_e0, tgt_e0, Initial), full_state_pair_equiv))
        prevs in

    (* The final states, however, are different. *)
    let tgt_state0_kvs =
      List.map
        (fun sv ->
          let src_ef = (dst_v, sv) in
          let tgt_ef = (src_v, sv) in
          ((src_ef, tgt_ef, Final), full_state_pair_equiv))
        succs in

    SourceEdge_TargetEdgeMap.of_seq
      (List.to_seq (src_state0_kvs @ tgt_state0_kvs))


(* Generate the target_edge_frontier_map *)
let adjacents_to_frontier_map
  : (G.vertex list) * G.vertex * G.vertex * (G.vertex list)
  -> frontier_map =
  fun (prevs, src_v, _, succs) ->
    let tgt_front_kvs =
      List.map
        (fun pv ->
          ((pv, src_v), List.map (fun sv -> (src_v, sv)) succs))
        prevs in

    TargetEdgeMap.of_seq
      (List.to_seq (tgt_front_kvs))

(* Generate the refined_source_path_map *)
let adjacents_to_path_match_map
  : (G.vertex list) * G.vertex * G.vertex * (G.vertex list)
  -> path_match_map =
  fun (prevs, src_v, dst_v, succs) ->
    let path_match_kvs =
      List.concat
        (List.map (fun pv -> 
          (List.map (fun sv ->
              let src_e0 = (pv, src_v) in
              let tgt_path = [pv; src_v; sv] in
              let src_path = [pv; src_v; dst_v; sv] in
              ((src_e0, tgt_path), src_path))
            succs))
          prevs) in

    SourceEdge_TargetPathMap.of_seq (List.to_seq path_match_kvs)

(* Generate the todo_edge_pairs *)
let adjacents_to_checkpoints
  : (G.vertex list) * G.vertex * G.vertex * (G.vertex list)
  -> checkpoints =
  fun (prevs, src_v, _, _) ->
    List.map (fun pv -> ((pv, src_v), (pv, src_v))) prevs

(* Go about generating a proof given what edges got merged *)
let adjacents_to_proof
  : (G.vertex list) * G.vertex * G.vertex * (G.vertex list)
  -> func_id
  -> proof =
  fun adjs func_id ->
    let refinement_map = adjacents_to_refinement_map adjs in
    let frontier_map = adjacents_to_frontier_map adjs in
    let path_match_map = adjacents_to_path_match_map adjs in
    let checkpoints = adjacents_to_checkpoints adjs in

    { empty_proof with
      func_id = func_id;
      refinement_map = refinement_map;
      frontier_map = frontier_map;
      path_match_map = path_match_map;
      checkpoints = checkpoints;
      debugs =
        [ "basic_basic_merge_pass: " ^ func_id ];
    }

(* Calculates the pre- and post-adjacenct vertices of an edge *)
let edge_adjacents
  : G.basic_edge
  -> ufunc_ir
  -> (G.vertex list) * G.vertex * G.vertex * (G.vertex list) =
  fun (src_v, dst_v) func_ir ->
    let prevs = G.vertex_prevs src_v func_ir.body_graph in
    let succs = G.vertex_succs dst_v func_ir.body_graph in
    (List.map fst prevs, src_v, dst_v, List.map fst succs)

(* Actually go about merging the edge; we need to delete the old vertex.
 *  (1) Make all of dst_v's succs into src_v's succs.
 *  (2) Directly delete dst_v from the graph.
 *      Since src_v should be its only prev this should be okay.
 *  (3) Generate proofs *)
let merge_uinstr_edge : G.basic_edge -> ufunc_ir -> (ufunc_ir * proof) =
  fun this_e func_ir0 ->
    (* Debugging *)
    let adjs = edge_adjacents this_e func_ir0 in
    let (_ , src_v, dst_v, succs) = adjs in

    (* Perform graph modifications *)
    let src_blk =
      (match G.vertex_label src_v func_ir0.body_graph with
      | Some (blk , _)-> blk
      | None -> empty_block) in
    let dst_blk = 
      (match G.vertex_label dst_v func_ir0.body_graph with
      | Some (blk, _) -> blk
      | None -> empty_block) in

    (* TODO: update type information too *)
    let merged_blk =
      { src_blk with instrs = src_blk.instrs @ dst_blk.instrs } in

    let graph0 = func_ir0.body_graph in
    let graph1 = G.add_vertex src_v (merged_blk, ()) graph0 in
    let graph2 = G.remove_vertex dst_v graph1 in
    let graph3 =
      List.fold_left
        (fun acc_g sv ->
          let br =
            (* Lookup old information *)
            match G.edge_label (dst_v, sv) graph0 with
            | None ->
              (prerr_endline
                ("merge_uinstr_edge: "
                  ^ G.string_of_basic_edge (dst_v, sv) ^ " label not found");
              (Jump, ()))
            | Some b -> b in
          G.add_edge (src_v, br, sv) acc_g)
        graph2
        succs in
    let func_ir1 = { func_ir0 with body_graph = graph3 } in

    (* Generate the proof *)
    let proof = adjacents_to_proof adjs func_ir1.func_id in

    (* Output *)
    (func_ir1, proof)


(* We can merge when dst_v is the unique successor of src_v and the two
 * are connected by a single Jump *)
let uinstr_edge_mergeable : uinstr_edge -> ufunc_ir -> bool =
  fun (src_v, (br, _), dst_v) func_ir ->
  if (src_v <> func_ir.root_vertex) && (br = Jump) then
    match G.vertex_succs src_v func_ir.body_graph with
    | [(succ_v, (Jump, _))] when
        (succ_v = dst_v) && (succ_v <> G.null_vertex) ->
      (match (G.vertex_label src_v func_ir.body_graph,
              G.vertex_label dst_v func_ir.body_graph) with
      | (Some (src_blk, _), Some (dst_blk, _)) ->
        List.fold_left
          (fun accb ins -> accb && not (is_instr_control_flow ins))
          true
          (src_blk.instrs @ dst_blk.instrs)
      | _ -> false)
    | _ -> false
  else false

  (* Below is a stricter criteria *)
  (*
  match G.vertex_prevs src_v func_ir.body_graph with
  | [] -> false
  | _ ->
    match G.vertex_succs src_v func_ir.body_graph with
    | [(succ_v, (Jump, _))] ->
      (succ_v = dst_v) && (succ_v <> G.null_vertex) && (branch = Jump)
    | _ -> false
  *)

(* Find that one mergeable edge if it exists *)
let find_mergeable_uinstr_edge : ufunc_ir -> uinstr_edge option =
  fun func_ir ->
    let edges = G.edges func_ir.body_graph in
    match (List.filter (fun e -> uinstr_edge_mergeable e func_ir) edges) with
    | [] -> None
    | (e :: _) ->
        Some e

(* AAAAAAAAAAAAAAAAA *)
let merge_func_ir_opt : ufunc_ir -> (ufunc_ir * proof) option =
  fun func_ir0 ->
    match find_mergeable_uinstr_edge func_ir0 with
    | None -> None
    | Some (src_v, _, dst_v) ->
      let (func_ir1, proof) = merge_uinstr_edge (src_v, dst_v) func_ir0 in
      Some (func_ir1, proof)


(* Search over all the edges; take the first mergeable one and merge that *)
let basic_basic_merge_pass_fun
  : ufunc_ir -> pass_config -> ufunc_ir * pass_out =
  fun func_ir0 _ ->
    match merge_func_ir_opt func_ir0 with
    | None -> (func_ir0, empty_pass_out)
    | Some (func_ir1, proof) ->
        (func_ir1, { empty_pass_out with proofs = [proof]; })

(* Put this into the upass object *)
let basic_basic_merge_pass : upass =
  init_pass
    "basic_basic_merge"
    basic_basic_merge_pass_fun



