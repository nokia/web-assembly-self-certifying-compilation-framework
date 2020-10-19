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

(* Dead code elimination *)

let src_adjs
  : (G.vertex * (Ast.instr list) * ((G.vertex * branch) list)) list =
  [ (1, [], [(2, Jump)]);
    (2, [const 617; local_set 1; const 212; local_set 2], [(3, Jump)]);
    (3, [const 781; local_set 3; const 267; local_set 2], [(4, Jump)]);
    (4, [local_get 1; local_get 2; binary Ast.IntOp.Add], [(5, Jump)]);
    (5, [], []);
  ]

let src_cfg_data : cfg_data =
  { empty_cfg_data with
    cfg_id = "test_dce_src";
    root_vertex = 1;
    sink_vertex = 5;
    adjacency_list = src_adjs;
  }

let tgt_adjs
  : (G.vertex * (Ast.instr list) * ((G.vertex * branch) list)) list =
  [ (1, [], [(2, Jump)]);
    (2, [const 617; local_set 1;], [(3, Jump)]);
    (3, [const 781; local_set 3; const 267; local_set 2], [(4, Jump)]);
    (4, [local_get 1; local_get 2; binary Ast.IntOp.Add], [(5, Jump)]);
    (5, [], []);
  ]

let tgt_cfg_data : cfg_data =
  { empty_cfg_data with
    cfg_id = "test_dce_tgt";
    root_vertex = 1;
    sink_vertex = 5;
    adjacency_list = tgt_adjs;
  }


let refinement_adjs
  : ((source_edge * target_edge * state_status_flag) * state_pair_formula) list =
  [ (((1,2), (1,2), Initial), full_state_pair_equiv);
    
    (((2,3), (2,3), Final),
      (fun (src, tgt) ->
        AndForm
          [ ArrsEqForm (values src, values tgt);
            PtrsRelForm
              (stack_pointer src,
                AstRelOp(Values.I32 Ast.IntOp.Eq),
                stack_pointer tgt);
            int32_vals_eq
              (SelectVal (locals src, Int32Ptr 1l))
              (SelectVal (locals tgt, Int32Ptr 1l));
            ArrsEqForm (globals src, globals tgt);
            SymEqForm (uf_memory src, uf_memory tgt); ]));

    (((2,3), (2,3), Initial),
      (fun (src, tgt) ->
        AndForm
          [ ArrsEqForm (values src, values tgt);
            PtrsRelForm
              (stack_pointer src,
                AstRelOp(Values.I32 Ast.IntOp.Eq),
                stack_pointer tgt);
            int32_vals_eq
              (SelectVal (locals src, Int32Ptr 1l))
              (SelectVal (locals tgt, Int32Ptr 1l));
            ArrsEqForm (globals src, globals tgt);
            SymEqForm (uf_memory src, uf_memory tgt); ]));

    (((3,4), (3,4), Final), full_state_pair_equiv);
    (((3,4), (3,4), Initial), full_state_pair_equiv);
    (((4,5), (4,5), Final), full_state_pair_equiv);
  ]


(* Generate the frontiers adjacency list. *)
let frontier_adjs : (target_edge * (target_edge list)) list =
  [ ((1,2), [(2,3)]);
    ((2,3), [(3,4)]);
    ((3,4), [(4,5)]);
  ]
    
(* Match paths. *)
let path_match_adjs : ((source_edge * target_path) * source_path) list =
  [ (((1,2), [1;2;3]), [1;2;3]);
    (((2,3), [2;3;4]), [2;3;4]);
    (((3,4), [3;4;5]), [3;4;5]);
  ]

let checkpts : ((source_edge * target_edge) * (unit -> unit)) list =
  [ (((1,2), (1,2)),
      (fun _ ->
        prerr_endline "should be valid"));
    (((2,3), (2,3)),
      (fun _ ->
        prerr_endline "should be valid"));
    (((3,4), (3,4)),
      (fun _ ->
        prerr_endline "should be valid"));
  ]


(* We've defined a few helper functions in proofs/proof_types.ml
 * that help convert from pair-lists into key-value stores *)
let the_proof : proof =
  { empty_proof with
    func_id = "test_dce";
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
let test_dce : unit -> unit =
  fun _ ->
    let _ =
      refinement_check_inject
        (cfg_data_to_ufunc_ir src_cfg_data)
        (cfg_data_to_ufunc_ir tgt_cfg_data)
        the_proof
        checkpts
        default_checker_config in
    ()

