(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


open Digraph

open Solver_types
open To_smt_ir

open Instr_graph
open Func_types
open Script_types

open Pass_header



(* This is a pass that is meant to merge consecutive unconditional branchs.
 * It's meant to be a very simple optimization and is more or less a
 * preliminary exploration for how much of the backend should be structured
 * to support it.
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
 *
 * We may need post-processing to eliminate no-longer existant edges.
 *)

(*









(* Given a particular vertex labeled as a basic block,
 * provided it has only one successor that happens to be a basic block,
 * which also only has one predecessor,
 * then that's grounds for removal.
 * We track in a singleton list the edge that ends up removed.
 *)
let merge_succs
  : vertex -> uinstr_graph -> uinstr_graph * (source_edge list) =
  fun this_v graph ->
    match vertex_label this_v graph with
    (* We only consider cases where it's a basic block *)
    | Some (this_blk, ()) ->
      (match vertex_succs this_v graph with
      (* Only care about the case where there is one successor *)
      | [(next_v, (Jump, ()))] ->
        (match vertex_prevs next_v graph with
        | [(_, (Jump, ()))] ->
          (match vertex_label next_v graph with
          (* We have found our match! *)
          | Some (next_blk, ()) ->
            (* Now we'll append u_instrs into v,
             * as well as make u's successors into v's successors,
             * followed by deleting u from the graph *)
            let succs1 = vertex_succs next_v graph in
            let label1 =
              (init_block (this_blk.instrs @ next_blk.instrs), ()) in
            let graph1 = remove_vertex next_v graph in
            ({ graph1 with
              label_map = VMap.add this_v label1 graph1.label_map;
              succs_map = VMap.add this_v succs1 graph1.succs_map },
            [(this_v, (Jump, ()), next_v)])

          (* This can only be merged if u is also a basic block *)
          | _ -> (graph, []))
        (* As stated, we only care about the case where u would have v as
         * a predecessor *)
        | _ -> (graph, []))
      (* All other cases can be ignored *)
      | _ -> (graph, []))
    (* All other options are not considered *)
    | _ -> (graph, [])

(* Since the merge process involves deleting the "next_v",
 * it is possible during folding that some of the old "this_v" will
 * no longer exist in the graph as it keeps getting iteratively updated.
 * Thus, to filter down information we need to track which edges are still
 * "relevant" by noting if the head (this_v) still exists
 * at the end of all the update iterations.
 *)
let edge_relevant : source_edge -> uinstr_graph -> bool =
  fun (this_v, _, _) graph -> vertex_exists this_v graph
  
(* Find all the merged edges, accounting for no longer relevant ones. *)
let merge_graph_succs : uinstr_graph -> uinstr_graph * (source_edge list) =
  fun graph ->
    let (graph1, all_merged_es) =
      List.fold_left
        (fun (g, acc_es) v ->
          let (g1, m_e) = merge_succs v graph in (g1, m_e @ acc_es))
        (graph, [])
        (vertices graph) in
    (graph1, List.filter (fun e -> edge_relevant e graph1) all_merged_es)

(* The relation we care about here is that the states are equal.
 * In other words, for each:
 *    src_start_edge.state  =  tgt_start_edge.state
 *    src_final_edge.state  =  tgt_final_edge.state
 *)

let edges_equiv_formulas : source_edge -> target_edge -> formula list =
  fun src_e tgt_e ->
    let src_state = tag_state (uinstr_edge_to_state src_e) "src" in
    let tgt_state = tag_state (uinstr_edge_to_state tgt_e) "tgt" in
    states_eq_formulas src_state tgt_state

(* Given merged edge we can infer a lot of information.
 * For one, we can generate a list of frontiers for every single one
 * of the predecessor edges. *)
let merged_edge_frontiers : source_edge -> uinstr_graph -> target_frontiers =
  fun merged_e src_graph ->
    []

(* We are also able to generate the relations for all the in- and out-adjacent
 * edges provided the merged_edge.
 * In particular, these will assert the equivalence of the states over
 * the source and target edges *)
let merged_edge_relations : source_edge -> uinstr_graph -> edge_relations =
  fun merged_e src_graph ->
    []

(* Given a merged edge we can also find all the relevant start pairs that
 * would arise from it -- and note that this can be optimized away later *)
let merged_edge_start_pairs : source_edge -> uinstr_graph -> start_pairs =
  fun merged_e src_graph ->
    []

(* We can also get all the path pairings given the merged edge.
 * Note that having four separate functions is highly un-optimized,
 * but we keep this here for now in order to sketch designs *)
let merged_edge_path_pairs : source_edge -> uinstr_graph -> path_pairs =
  fun merged_e src_graph ->
    []

(* With the auxillary functions that allow us to generate components of
 * the proof from a single merged edge, we can fold over a list of
 * merged edges to aggregate together a proof.
 * We expect that the source graph and target graph share the same id*)
let merged_edges_to_proof : source_edge list -> uinstr_graph -> ugraph_proof =
  fun merged_es src_graph ->
    let (edge_rels, tgt_fronts, path_pairs, start_pairs) =
      List.fold_left
        (fun (acc_rels, acc_fronts, acc_paths, acc_starts) merged_e ->
          (acc_rels @ merged_edge_relations merged_e src_graph,
          acc_fronts @ merged_edge_frontiers merged_e src_graph,
          acc_paths @ merged_edge_path_pairs merged_e src_graph,
          acc_starts @ merged_edge_start_pairs merged_e src_graph))
        ([], [], [], [])
        merged_es in
    { empty_ugraph_proof with
      source_id = src_graph.graph_id;
      target_id = src_graph.graph_id;
      edge_relations = edge_rels;
      target_frontiers = tgt_fronts;
      path_pairs = path_pairs;
      start_pairs = start_pairs }


(* We need to run this on the entire graph:
 *  (1) we merge the edges via merge_graph_succs to get relevant ones
 *  (2) run merged_edges_to_proof on the result.
 *  (3) return the merged graph and the proof *)
let graph_to_merged_proof : uinstr_graph -> (uinstr_graph * ugraph_proof) =
  fun src_graph ->
    let (tgt_graph, merged_es) = merge_graph_succs src_graph in
      (tgt_graph, merged_edges_to_proof merged_es src_graph)

*)

(*
let block_merge_pass
  : umodule_ir -> upass_config -> umodule_ir * (upass_out list) =
  fun mod_ conf ->
    (mod_, [])
*)


