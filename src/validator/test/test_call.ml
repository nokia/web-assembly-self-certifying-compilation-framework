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
open Type_inference

module G = Digraph


(* Test function calls *)

let src_adjs
  : (G.vertex * (Ast.instr list) * ((G.vertex * branch) list)) list =
  [ (1, [], [(2, Jump)]);

    (2, [const 100; const 100; binary Ast.IntOp.Add],
        [(3, JumpIf true); (4, JumpIf false)]);

    (3, [call 1],
        [(5, Jump)]);

    (4, [call 2],
        [(5, Jump)]);

    (5, [const 250; const 2; binary Ast.IntOp.Mul],
        [(6, Jump)]);

    (6, [], []) ]


let types_table : Ast.type_ list =
  [ noregion (Types.FuncType ([i32ty], [i32ty]));
    noregion (Types.FuncType ([i32ty; i32ty], [i32ty]));
    noregion (Types.FuncType ([i32ty], [i32ty; i32ty]));
    noregion (Types.FuncType ([i32ty; i32ty], [i32ty; i32ty]))
  ]

let ftypes : Ast.var list =
  List.map int_to_var
    [ 0; 1; 2; 3; 0; 1; 2; 3 ]

let src_cfg_data : cfg_data =
  { cfg_id = "test_call_src";
    root_vertex = 1;
    sink_vertex = 6;
    adjacency_list = src_adjs;
    types_table = types_table;
    ftypes = ftypes;
  }

let tgt_adjs
  : (G.vertex * (Ast.instr list) * ((G.vertex * branch) list)) list =
  [ (1, [], [(2, Jump)]);

    (2, [const 200],
        [(3, JumpIf true); (4, JumpIf false)]);

    (3, [call 1],
        [(5, Jump)]);

    (4, [call 2],
        [(5, Jump)]);

    (5, [const 500],
        [(6, Jump)]);

    (6, [], []) ]

let tgt_cfg_data : cfg_data =
  { cfg_id = "test_call_tgt";
    root_vertex = 1;
    sink_vertex = 6;
    adjacency_list = tgt_adjs;
    types_table = types_table;
    ftypes = ftypes;
  }


(* Start making the proof *)
let refinement_adjs
  : ((source_edge * target_edge * state_status_flag) * state_pair_formula) list =
  [ 
    (* Pre opt *)
    (((1,2), (1,2), Initial), full_state_pair_equiv);
    (* Pre-Left *)
    (((2,3), (2,3), Final), full_state_pair_equiv);
    (* Pre-Right *)
    (((2,4), (2,4), Final), full_state_pair_equiv);

    (* Middle-Left *)
    (((2,3), (2,3), Initial), full_state_pair_equiv);
    (((2,3), (2,3), PreCall),
      (fun (src, tgt) ->
        AndForm
          [ full_state_pair_equiv (src, tgt);
            int32_vals_eq
              (SelectVal (locals src, Int32Ptr 1l))
              (Int32Val 100l) ]));
    
    (((3,5), (3,5), PostCall), full_state_pair_equiv);
    (((3,5), (3,5), Final), full_state_pair_equiv);
    (* Middle-right *)
    (((2,4), (2,4), Initial), full_state_pair_equiv);
    (((2,4), (2,4), PreCall),
      (fun (src, tgt) ->
        AndForm
          [ full_state_pair_equiv (src, tgt);
            int32_vals_eq
              (SelectVal (locals src, Int32Ptr 1l))
              (Int32Val 100l) ]));
    
    (((4,5), (4,5), PostCall), full_state_pair_equiv);
    (((4,5), (4,5), Final), full_state_pair_equiv);


    (* Bottom-left *)
    (((3,5), (3,5), Initial), full_state_pair_equiv);
    (* Bottom-right *)
    (((4,5), (4,5), Initial), full_state_pair_equiv);

    (((5,6), (5,6), Final), full_state_pair_equiv); ]


let frontier_adjs : (target_edge * (target_edge list)) list =
  [ ((1,2), [(2,3); (2,4)]);
    ((2,3), [(3,5)]);
    ((2,4), [(4,5)]);
    ((3,5), [(5,6)]);
    ((4,5), [(5,6)]);
  ]

let path_match_adjs : ((source_edge * target_path) * source_path) list =
  [ (((1,2), [1;2;3]), [1;2;3]);
    (((1,2), [1;2;4]), [1;2;4]);

    (* The function calls *)
    (((2,3), [2;3;5]), [2;3;5]);
    (((2,4), [2;4;5]), [2;4;5]);

    (* After function calls *)
    (((3,5), [3;5;6]), [3;5;6]);
    (((4,5), [4;5;6]), [4;5;6]);
    ]

let checkpts : ((source_edge * target_edge) * (unit -> unit)) list =
  [ (((1,2), (1,2)), (fun _ -> prerr_endline ("should be valid")));
    (((2,3), (2,3)), (fun _ -> prerr_endline ("should be valid")));
    (((2,4), (2,4)), (fun _ -> prerr_endline ("should be valid")));
    (((3,5), (3,5)), (fun _ -> prerr_endline ("should be valid")));
    (((4,5), (4,5)), (fun _ -> prerr_endline ("should be valid")));
  ]


let the_proof : proof =
  { empty_proof with
    func_id = "test_call";
    
    refinement_map =
      SourceEdge_TargetEdgeMap.of_seq (List.to_seq refinement_adjs);
    frontier_map =
      TargetEdgeMap.of_seq (List.to_seq frontier_adjs);
    path_match_map =
      SourceEdge_TargetPathMap.of_seq (List.to_seq path_match_adjs);
    checkpoints =
      List.map fst checkpts
  }

let test_call : unit -> unit =
  fun _ ->
    let _ =
      refinement_check_inject
        (cfg_data_to_ufunc_ir src_cfg_data)
        (cfg_data_to_ufunc_ir tgt_cfg_data)
        the_proof
        checkpts
        default_checker_config in
    ()



