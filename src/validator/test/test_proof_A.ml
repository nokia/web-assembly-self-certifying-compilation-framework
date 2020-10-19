(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


open Wasm
open Source
open Wasm_utils
open Instr_graph
open Func_types
open State_types
open Proof_types
open Solver_types
open Worklist

open Digraph

open Cfg_builder
open Proof_builder

module List = List_utils

(* The goal of this test is to check block merging without alterations *)

(* We hard-code the following optimization of block merging:
 * Source graph:
 *        [v1]
 *        /  \
 *    [v2]    [v7]
 *     |        |
 *    [v3]    [v8]
 *     |        |
 *    [v4]    [v9]
 *     |        |
 *    [v5]    [v10]
 *     |        |
 *      \     [v11]
 *       \    /
 *        [v6]
 *
 * Target graph:
 *        [v1]
 *        /  \
 *    [v2]    [v7]
 *     |        |
 *    [v3']   [v8']
 *     |        |
 *    [v5]    [v11]
 *       \    /
 *        [v6]
 *
 * The merge that happened are:
 *  v3' = v3 @ v4
 *  v8' = v8 @ v9 @ v10
 *
 * For simplicity of implementation we just do v3 = v3' and v8 = v8'.
 *
 * NOTE: We intentionally introduce an error in this process.
 * Observe below in the adjacency lists, source graph's v8 has the label
 *  Const 88888
 *
 * However this is not the case in the target graph's adjacency list.
 * The intent here is that the v3 @ v4 optimization is done correctly,
 * and will thus give a SAT result,
 * while the v8 @ v9 @ v10 is errnoneous and yields UNSAT. *)

let src_adjs
  : (G.vertex * (Ast.instr list) * ((G.vertex * branch) list)) list =
  [ (1, [const 1], [(2, JumpIf true); (7, JumpIf false)]);
    (2, [local_get 2], [(3, Jump)]);
    (3, [local_get 3], [(4, Jump)]);
    (4, [global_get 4], [(5, Jump)]);
    (5, [const 5], [(6, Jump)]);
    (6, [local_tee 6], []);
    (7, [local_set 7], [(8, Jump)]);
    (8, [const 88888], [(9, Jump)]);
    (9, [const 9], [(10, Jump)]);
    (10, [const 10], [(11, Jump)]);
    (11, [global_get 11], [(6, Jump)]);
  ]

let src_cfg_data : cfg_data =
  { empty_cfg_data with
    cfg_id = "test_proof_A_src";
    root_vertex = 1;
    sink_vertex = 6;
    adjacency_list = src_adjs;
  }

let tgt_adjs
  : (G.vertex * (Ast.instr list) * ((G.vertex * branch) list)) list =
  [ (1, [const 1], [(2, JumpIf true); (7, JumpIf false)]);
    (2, [local_get 2], [(3, Jump)]);
    (3, [local_get 3; global_get 4], [(5, Jump)]);  (* MODIFIED *)
    (5, [const 5], [(6, Jump)]);
    (6, [local_tee 6], []);
    (7, [local_set 7], [(8, Jump)]);
    (8, [const 8; const 9; const 10], [(11, Jump)]);  (* MODIFIED *)
    (11, [global_get 11], [(6, Jump)]);
  ]

let tgt_cfg_data : cfg_data =
  { empty_cfg_data with
    cfg_id = "test_proof_A_tgt";
    root_vertex = 1;
    sink_vertex = 6;
    adjacency_list = tgt_adjs;
  }

(* We want to generate proofs to check whether
 *  src { v3-v4 } == tgt { v3' }
 *  src { v8-v9-v10} == tgt { v8' }
 *
 * Of course, we know that the v8-v9-v10 merge is incorrect
 * due to our explicitly introduced error on vertex 8.
 *
 * We construct the proof objects that should be returned by a pass
 * in a few of the variables defined below *)

(* The edge_pair_relations_adjs are a pair-list representation of a function
 * for the formulaic relationship between a source_edge and target_edge.
 * The thing that we want to encode here are that:
 *  1: the source path start and target path start states are equivalent
 *  2: the source path final and target path final states are equivalent
 *
 * where equivalent means that the
 *  values, pointer, locals, globals, and memory
 * are all equal.
 *
 * For the starts these are
 *  src_(2, 3) --- tgt_(2, 3)
 *  src_(7, 8) --- tgt_(7, 8)
 *
 * For the finals these are
 *  src_(4, 5) --- tgt_(3, 5)
 *  src_(10, 11) --- tgt_(8, 11)
 *)

(*
let refinement_adjs
  : ((source_edge * target_edge * state_status * callx) * formula) list =
  let src_2_3 = init_state0 (2,3) source_tag in
  let tgt_2_3 = init_state0 (2,3) target_tag in

  let src_4_5 = init_statef (4,5) source_tag in
  let tgt_3_5 = init_statef (3,5) target_tag in

  let src_7_8 = init_state0 (7,8) source_tag in
  let tgt_7_8 = init_state0 (7,8) target_tag in

  let src_10_11 = init_statef (10,11) source_tag in
  let tgt_8_11 = init_statef (8,11) target_tag in

  [ (((2,3), (2,3), Active, 0), states_equiv src_2_3 tgt_2_3);
    (((4,5), (3,5), Final, 0), states_equiv src_4_5 tgt_3_5);

    (((7,8), (7,8), Active, 0), states_equiv src_7_8 tgt_7_8);
    (((10,11), (8,11), Final, 0), states_equiv src_10_11 tgt_8_11);
  ]
*)

let refinement_adjs
  : ((source_edge * target_edge * state_status_flag) * state_pair_formula) list =

  [ (((2,3), (2,3), Initial), full_state_pair_equiv);
    (((4,5), (3,5), Final), full_state_pair_equiv);

    (((7,8), (7,8), Initial), full_state_pair_equiv);
    (((10,11), (8,11), Final), full_state_pair_equiv);
  ]

(* Generate the frontiers adjacency list.
 * These would just be mapping, within the target:
 *    (2, 3) \mapsto (3, 5)
 *    (7, 8) \mapsto (8, 11)
 *
 * since these are the terminal edges (states) of each contracted path *)

let frontier_adjs : (target_edge * (target_edge list)) list =
  [ ((2,3), [(3,5)]);
    ((7,8), [(8,11)]); ]

(* Match paths.
 * We map the following:
 *  (src_2_3, tgt_2_3_5) \mapsto (src_2_3_4_5)        (should SAT)
 *  (src_7_8, tgt_7_8_11) \mapsto (src_7_8_9_10_11)   (should UNSAT) *)
let path_match_adjs : ((source_edge * target_path) * source_path) list =
  [ (((2,3), [2;3;5]), [2;3;4;5]);          (* Correct *)
    (((7,8), [7;8;11]), [7;8;9;10;11])      (* Wrong *)
  ]

let checkpts : ((source_edge * target_edge) * (unit -> unit)) list =
  [ (((2,3), (2,3)),
      (fun _ ->
        prerr_endline "should be valid"));
    (((7,8), (7,8)),
      (fun _ ->
        prerr_endline "should be invalid: v8 now 88888 instead of 8"));
  ]


(* We've defined a few helper functions in proofs/proof_types.ml
 * that help convert from pair-lists into key-value stores *)
let the_proof : proof =
  { empty_proof with
    func_id = "test_proof_A";
    refinement_map =
      SourceEdge_TargetEdgeMap.of_seq (List.to_seq refinement_adjs);
    frontier_map =
      TargetEdgeMap.of_seq (List.to_seq frontier_adjs);
    path_match_map =
      SourceEdge_TargetPathMap.of_seq (List.to_seq path_match_adjs);
    checkpoints = List.map fst checkpts
  }

(* It helps streamline the process a bit if every test/test*.ml file
 * has its own custom unit -> unit function named the same as the file *)
let test_proof_A : unit -> unit =
  fun _ ->
    let _ =
      refinement_check_inject
        (cfg_data_to_ufunc_ir src_cfg_data)
        (cfg_data_to_ufunc_ir tgt_cfg_data)
        the_proof
        checkpts
        default_checker_config in
    ()

