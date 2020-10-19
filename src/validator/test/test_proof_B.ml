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

(* The goal of this particular optimization is to test
 *  block merging with altered instructions
 *  enabled/disabled paths
 *)


(* Here we attempt the following optimization, which is also block-merge based
 * Source graph:
 *
 *         [v0]
 *          |
 *         [v1]
 *       /  |   \
 *   [v2]  [v5]  [v8]
 *    |     |     |
 *   [v3]  [v6]  [v9]
 *    |     |     |
 *   [v4]  [v7]  [v10]
 *       \  |   /
 *         [v11]
 *          |
 *         [v12]
 *
 * Target graph:
 * 
 *         [v0]
 *           |
 *         [v1]
 *       /   |   \
 *  [v2']  [v5']  [v8']
 *       \   |   /
 *         [v11]
 *           |
 *         [v12]
 *
 * where the goal is to merge
 *  v2' = v2 @ v3 @ v4
 *  v5' = v5 @ v6 @ v7
 *  v8' = v8 @ v9 @ v10
 *
 * NOTE: the only way in WASM to naturally introduce a three-way branch
 * is via a BrTable command; in our case we set it up so that:
 *  v2-v3-v4 is disabled and has no optimization error
 *  v5-v6-v7 is enabled and has no optimization error
 *  v8-v9-v10 is disabled and has no optimization error
 *
 * These will also be more complicated than those of test_proof_A.
 *)

(* The optimization is such that we begin at (null_vertex, v1) -- the root;
 * and conclude at (v11, null_vertex) -- the sink.
 *
 * The optimizations taken for each path are:
 *  ---
 *  src_2_3_4:
 *    Const 222
 *    Const 333
 *    Binary Add
 *
 *  NOTE: This one fails because shiftign down stack pointer is not the
 *  same as popping 333 off the top of the stack.
 *  tgt_2':
 *    Const 555
 *  ---
 *  src_5_6_7:
 *    Const 16
 *    Const 555
 *    Store 80 ; stores the value 555 at memory addr 16 offset 80
 *    Const 16
 *    Load ; loads the value at memory addr 16, 555 now on top of values
 *    Const 0
 *    Const 16
 *    Store 80 ; stores 0 at addr 16 offset 80, 555 is on top of values
 *
 *  tgt_5':
 *    Const 555
 *    Const 16
 *    Const 0
 *    Store 80 ; stores 0 at addr 16 offset 80, 555 top of values
 *  ---  
 *  src_8_9_10:
 *    Const 888
 *    GlobalSet 20 ; stores 888 in global addr 20
 *    GlobalGet 20 ; retrieves 888 to top of values from global addr 20;
 *    Const 0;
 *    GlobalSet 20 ; overwrites global addr 20 to 0
 *
 *  tgt_8':
 *    Const 888
 *    Const 0
 *    GlobalSet 20 ; writes 0 to global addr 20
 *)

let src_adjs
  : (G.vertex * (Ast.instr list) * ((G.vertex * branch) list)) list =
  [ (0, [], [(1, Jump)]);
    (1, [const 1],
      [ (2, JumpIndex 0l);
        (5, JumpIndex 1l);
        (8, JumpDefault 2l) ]);

    (2, [const 222], [(3, Jump)]);
    (3, [const 333], [(4, Jump)]);
    (4, [binary Ast.IntOp.Add], [(11, Jump)]);

    (5, [const 16; const 555; store 80], [(6, Jump)]);
    (6, [const 16; load 80], [(7, Jump)]);
    (7, [const 16; const 0; store 80], [(11, Jump)]);

    (8, [const 888; global_set 20; global_get 20], [(9, Jump)]);
    (9, [], [(10, Jump)]);
    (10, [const 0; global_set 20], [(11, Jump)]);

    (11, [const 4], [(12, Jump)]);
    (12, [], [])
  ]

let src_cfg_data : cfg_data =
  { empty_cfg_data with
    cfg_id = "test_proof_B_src";
    root_vertex = 0;
    sink_vertex = 12;
    adjacency_list = src_adjs;
  }

let tgt_adjs
  : (G.vertex * (Ast.instr list) * ((G.vertex * branch) list)) list =
  [ (0, [], [(1, Jump)]);
    (1, [const 1],
      [ (2, JumpIndex 0l);
        (5, JumpIndex 1l);
        (8, JumpDefault 2l) ]);

    (2, [const 555], [(11, Jump)]);

    (5, [const 555; const 16; const 0; store 80], [(11, Jump)]);

    (8, [const 888; const 0; global_set 20], [(11, Jump)]);

    (11, [const 4], [(12, Jump)]);
    (12, [], [])
  ]

let tgt_cfg_data : cfg_data =
  { empty_cfg_data with
    cfg_id = "test_proof_B_tgt";
    root_vertex = 0;
    sink_vertex = 12;
    adjacency_list = tgt_adjs;
  }


(* Begin constructing the proofs *)

let refinement_adjs
  : ((source_edge * target_edge * state_status_flag) * state_pair_formula) list =
  [ (((0,1), (0,1), Initial), full_state_pair_equiv);

    (* Left paths *)
    (((1,2), (1,2), Final), full_state_pair_equiv);
    (((1,2), (1,2), Initial), full_state_pair_equiv);

    (* Middle paths *)
    (((1,5), (1,5), Final), full_state_pair_equiv);
    (((1,5), (1,5), Initial), full_state_pair_equiv);

    (* Right paths *)
    (((1,8), (1,8), Final), full_state_pair_equiv);
    (((1,8), (1,8), Initial), full_state_pair_equiv);

    (* Final edge *)
    (((11,12), (11,12), Final), full_state_pair_equiv); ]


(* Frontiers for the target.
 * There is only one for (null, 1) to (11, null) *)
let frontier_adjs : (target_edge * (target_edge list)) list =
  [ ((0,1), [(1,2); (1,5); (1,8)]);
    ((1,2), [(11,12)]);
    ((1,5), [(11,12)]);
    ((1,8), [(11,12)]); ]


(* Match paths, where we map the following:
 *  (e_0_1, tgt_0_1_2_11_12) \mapsto src_0_1_2_3_4_11_12
 *  (e_0_1, tgt_0_1_5_11_12) \mapsto src_0_1_5_6_7_11_12
 *  (e_0_1, tgt_0_1_8_11_12) \mapsto src_0_1_8_9_10_11_12
 *)
let path_match_adjs : ((source_edge * target_path) * source_path) list =
  [ (((0,1), [0;1;2]), [0;1;2]);
    (((0,1), [0;1;5]), [0;1;5]);
    (((0,1), [0;1;8]), [0;1;8]);

    (((1,2), [1;2;11;12]), [1;2;3;4;11;12]);
    (((1,5), [1;5;11;12]), [1;5;6;7;11;12]);
    (((1,8), [1;8;11;12]), [1;8;9;10;11;12]);
  ]

let checkpts : ((source_edge * target_edge) * (unit -> unit)) list =
  [ (((0,1), (0,1)),
      (fun _ -> prerr_endline "should be valid"));
    
    (((1,2), (1,2)),
      (fun _ -> prerr_endline "should be valid"));  

    (((1,5), (1,5)),
      (fun _ -> prerr_endline "should be valid"));

    (((1,8), (1,8)),
      (fun _ -> prerr_endline "should be valid"));
  ]

(* Construct the proof object *)
let proof_B : proof =
  { empty_proof with
    func_id = "test_proof_B";
    refinement_map =
      SourceEdge_TargetEdgeMap.of_seq (List.to_seq refinement_adjs);
    frontier_map =
      TargetEdgeMap.of_seq (List.to_seq frontier_adjs);
    path_match_map =
      SourceEdge_TargetPathMap.of_seq (List.to_seq path_match_adjs);
    checkpoints = List.map fst checkpts
  }

let test_proof_B : unit -> unit =
  fun _ ->
    let _ =
      refinement_check_inject
        (cfg_data_to_ufunc_ir src_cfg_data)
        (cfg_data_to_ufunc_ir tgt_cfg_data)
        proof_B
        checkpts
        default_checker_config in
    ()


