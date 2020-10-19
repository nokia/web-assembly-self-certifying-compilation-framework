(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)



open Wasm
open Wasm_utils
open Instr_graph
open Func_types
open State_types
open Proof_types

open Worklist
open Cfg_builder
open Proof_builder

module G = Digraph


(* Loop unrolling (Fig 12) *)

let src_adjs
  : (G.vertex * (Ast.instr list) * ((G.vertex * branch) list)) list =
  [ (1, [],
      [(2, Jump)]);

    (2, [const 0; local_set 0],
      [(3, Jump)]);

    (3, [local_get 0; const 99; compare Ast.IntOp.Eq],
      [(4, JumpIf false); (8, JumpIf true)]);

    (4, [const 1; local_get 0; binary Ast.IntOp.Add; local_set 0],
      [(3, Jump)]);

    (8, [],
      [(9, Jump)]);

    (9, [], []) ]

let src_cfg_data: cfg_data =
  { empty_cfg_data with
    cfg_id = "loop_unroll_src";
    root_vertex = 1;
    sink_vertex = 9;
    adjacency_list = src_adjs
  }

let tgt_adjs
  : (G.vertex * (Ast.instr list) * ((G.vertex * branch) list)) list =
  [ (1, [],
      [(2, Jump)]);

    (2, [const 0; local_set 0],
      [(3, Jump)]);

    (3, [const 1; local_get 0; binary Ast.IntOp.Add; local_set 0],
      [(4, Jump)]);

    (4, [local_get 0; const 99; compare Ast.IntOp.Eq],
      [(5, JumpIf false); (8, JumpIf true)]);

    (5, [const 1; local_get 0; binary Ast.IntOp.Add; local_set 0],
      [(3, Jump)]);

    (8, [],
      [(9, Jump)]);

    (9, [], []) ]

let tgt_cfg_data: cfg_data =
  { empty_cfg_data with
    cfg_id = "loop_unroll_tgt";
    root_vertex = 1;
    sink_vertex = 9;
    adjacency_list = tgt_adjs
  }


(* We mark a few traces explicitly via vertex sequences (basic_path).
 * Based on how we define things, instruction execution begins on the second
 * vertex; the last action is the branch to the last vertex.
 *
 * Note that mathematical convention differs from programming convention
 * (i.e. the code lists source/target rather than target/source in the math)
 *
 *  The very start of the execution:
 *    T1: tgt [1;2;3] --> src [1;2;3]
 *
 *  The first step into the loop body (even); source has redundant check
 *    T2: tgt[2;3;4] --> src [2;3;4;3]
 *
 *  The odd iteration of the loop body (condition false)
 *    T3: tgt [3;4;5;3] --> src [4;3;4;3]
 *
 *  The odd iteration of the loop body (condition true)
 *    T4: tgt [3;4;8] --> src [4;3;8]
 *
 *  The even iteration of the loop body
 *    T5: tgt [5;3;4] --> src [4;3;4;3]
 *)

(* Generate the proofs *)

(* Refinements *)
let refinement_adjs
  : ((source_edge * target_edge * state_status_flag) * state_pair_formula) list =
  [ (* Trace T1 start / end *)
    (((1,2), (1,2), Initial), full_state_pair_equiv);
    (((2,3), (2,3), Final), full_state_pair_equiv);

    (* Trace T2 start / end *)
    (((2,3), (2,3), Initial),
      (fun (src, tgt) ->
        AndForm
          [ full_state_pair_equiv (src, tgt);
            even_int32_value
              (SelectVal (locals src, Int32Ptr 0l)) ]));

    (((4,3), (3,4), Final), full_state_pair_equiv);

    (* Trace T3 and T4 start / end *)
    (((4,3), (3,4), Initial),
      (fun (src, tgt) ->
        AndForm
          [ full_state_pair_equiv (src, tgt);
            even_int32_value
              (SelectVal (locals src, Int32Ptr 0l))]));
    (((4,3), (5,3), Final), full_state_pair_equiv);
    (((3,8), (4,8), Final), full_state_pair_equiv);

    (* Trace T5 start / end *)
    (((4,3), (5,3), Initial),
      (fun (src, tgt) ->
        AndForm
          [ full_state_pair_equiv (src, tgt);
            even_int32_value
              (SelectVal (locals src, Int32Ptr 0l))]));
    (((4,3), (3,4), Final), full_state_pair_equiv);
]

(* Frontiers *)
let frontier_adjs : (target_edge * (target_edge list)) list =
  [ (* T1 *)
    ((1,2), [(2,3)]);

    (* T2 *)
    ((2,3), [(3,4)]);

    (* T3 / T4 *)
    ((3,4), [(5,3); (4,8)]);

    (* T5 *)
    ((5,3), [(3,4)])
  ]

(* Path matching *)
let path_match_adjs : ((source_edge * target_path) * source_path) list =
  [ (* T1 *)
    (((1,2), [1;2;3]), [1;2;3]);

    (* T2 *)
    (((2,3), [2;3;4]), [2;3;4;3]);

    (* T3 *)
    (((4,3), [3;4;5;3]), [4;3;4;3]);

    (* T4 *)
    (((4,3), [3;4;8]), [4;3;8]);

    (* T5 *)
    (((4,3), [5;3;4]), [4;3;4;3])
  ]

(* Proof *)
let the_proof : proof =
  { empty_proof with
    func_id = "test_loop_unroll";
    refinement_map =
      SourceEdge_TargetEdgeMap.of_seq (List.to_seq refinement_adjs);
    frontier_map =
      TargetEdgeMap.of_seq (List.to_seq frontier_adjs);
    path_match_map =
      SourceEdge_TargetPathMap.of_seq (List.to_seq path_match_adjs);
    checkpoints =
      [ ((1,2), (1,2));
        ((2,3), (2,3));
        ((4,3), (3,4));
        ((4,3), (5,3));
      ]
    }

let test_loop_unroll : unit -> unit =
  fun _ ->
    let _ =
      refinement_check_inject
        (cfg_data_to_ufunc_ir src_cfg_data)
        (cfg_data_to_ufunc_ir tgt_cfg_data)
        the_proof
        [ (((1,2), (1,2)),
            (fun _ -> prerr_endline "*****"; print_endline "******"));
          (((2,3), (2,3)),
            (fun _ -> prerr_endline "*****"; print_endline "******"));
          (((4,3), (3,4)),
            (fun _ -> prerr_endline "*****"; print_endline "******"));
          (((4,3), (5,3)),
            (fun _ -> prerr_endline "*****"; print_endline "******")); ]
        default_checker_config in
    ()



