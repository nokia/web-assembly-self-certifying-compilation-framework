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


(* Constant hoisting optimization hard-coded
 *
 *  entry                                       entry           ; v1
 *                -------- all equal ---------
 *  local.get 2                               i32.const 100000  ; v2
 *                                            local.set 1
 *                                            local.get 2
 *                -- L'[1] == 100; all equal -
 *  if i32                                      if i32
 *    i32.const 100000                            local.get 1   ; v3
 *    i32.const 3                                 i32.const 3
 *    i32.mul                                     i32.mul
 *  else                                        else
 *    i32.const 2                                 i32.const 2   ; v4
 *    i32.const 100000                            local.get 1
 *    i32.add                                     i32.add
 *  fi                                          fi
 *  local.set 2                                 local.set 2     ; v5
 *                -------- all equal ---------
 *  sink                                        sink            ; v6
 *
 *)

let src_adjs
  : (G.vertex * (Ast.instr list) * ((G.vertex * branch) list)) list =
  [ (1, [], [(2, Jump)]);
    
    (2, [local_get 2],
        [(3, JumpIf true); (4, JumpIf false)]);

    (3, [const 100000; const 3; binary Ast.IntOp.Mul],
        [(5, Jump)]);

    (4, [const 2; const 100000; binary Ast.IntOp.Add],
        [(5, Jump)]);

    (5, [local_set 2],
        [(6, Jump)]);

    (6, [], []) ]

let src_cfg_data : cfg_data =
  { empty_cfg_data with
    cfg_id = "test_const_hoist_src";
    root_vertex = 1;
    sink_vertex = 6;
    adjacency_list = src_adjs;
  }

let tgt_adjs
  : (G.vertex * (Ast.instr list) * ((G.vertex * branch) list)) list =
  [ (1, [], [(2, Jump)]);
    
    (2, [const 100000; local_set 1; local_get 2],
        [(3, JumpIf true); (4, JumpIf false)]);

    (3, [local_get 1; const 3; binary Ast.IntOp.Mul],
        [(5, Jump)]);

    (4, [const 2; local_get 1; binary Ast.IntOp.Add],
        [(5, Jump)]);

    (5, [local_set 2],
        [(6, Jump)]);

    (6, [], []) ]

let tgt_cfg_data : cfg_data =
  { empty_cfg_data with
    cfg_id = "test_const_hoist_tgt";
    root_vertex = 1;
    sink_vertex = 6;
    adjacency_list = tgt_adjs;
  }


(* Start making the proof *)

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
              (SelectVal (locals tgt, Int32Ptr 1l))
              (Int32Val 100000l);
            ArrsEqForm (globals src, globals tgt);
            SymEqForm (uf_memory src, uf_memory tgt);
          ]));
    
    (((2,3), (2,3), Initial),
      (fun (src, tgt) ->
        AndForm
          [ ArrsEqForm (values src, values tgt);
            PtrsRelForm
              (stack_pointer src,
                AstRelOp(Values.I32 Ast.IntOp.Eq),
                stack_pointer tgt);
            int32_vals_eq
              (SelectVal (locals tgt, Int32Ptr 1l))
              (Int32Val 100000l);
            ArrsEqForm (globals src, globals tgt);
            SymEqForm (uf_memory src, uf_memory tgt);
          ]));

    (((2,4), (2,4), Final),
      (fun (src, tgt) ->
        AndForm
          [ ArrsEqForm (values src, values tgt);
            PtrsRelForm
              (stack_pointer src,
                AstRelOp(Values.I32 Ast.IntOp.Eq),
                stack_pointer tgt);
            int32_vals_eq
              (SelectVal (locals tgt, Int32Ptr 1l))
              (Int32Val 100000l);
            ArrsEqForm (globals src, globals tgt);
            SymEqForm (uf_memory src, uf_memory tgt);
          ]));
    
    (((2,4), (2,4), Initial),
      (fun (src, tgt) ->
        AndForm
          [ ArrsEqForm (values src, values tgt);
            PtrsRelForm
              (stack_pointer src,
                AstRelOp(Values.I32 Ast.IntOp.Eq),
                stack_pointer tgt);
            int32_vals_eq
              (SelectVal (locals tgt, Int32Ptr 1l))
              (Int32Val 100000l);
            ArrsEqForm (globals src, globals tgt);
            SymEqForm (uf_memory src, uf_memory tgt);
          ]));

    (* On the final state, everything equal except for the locals *)
    (((5,6), (5,6), Final),
      (fun (src, tgt) ->
        AndForm
          [ ArrsEqForm (values src, values tgt);
            PtrsRelForm
              (stack_pointer src,
                AstRelOp (Values.I32 Ast.IntOp.Eq),
                stack_pointer tgt);
            ArrsEqForm (globals src, globals tgt);
            SymEqForm (uf_memory src, uf_memory tgt);
          ])); ]

let frontier_adjs : (target_edge * (target_edge list)) list =
  [ ((1,2), [(2,3); (2,4)]);
    ((2,3), [(5,6)]);
    ((2,4), [(5,6)]); ]


let path_match_adjs : ((source_edge * target_path) * source_path) list =
  [ (((1,2), [1;2;3]), [1;2;3]);
    (((1,2), [1;2;4]), [1;2;4]);

    (((2,3), [2;3;5;6]), [2;3;5;6]);
    (((2,4), [2;4;5;6]), [2;4;5;6]); ]

let checkpts : ((source_edge * target_edge) * (unit -> unit)) list =
  [ (((1,2), (1,2)), (fun _ -> prerr_endline ("should be valid")));
    (((2,3), (2,3)), (fun _ -> prerr_endline ("should be valid")));
    (((2,4), (2,4)), (fun _ -> prerr_endline ("should be valid")));
  ]


let the_proof : proof =
  { empty_proof with
    func_id = "test_const_hoist";
    refinement_map =
      SourceEdge_TargetEdgeMap.of_seq (List.to_seq refinement_adjs);
    frontier_map =
      TargetEdgeMap.of_seq (List.to_seq frontier_adjs);
    path_match_map =
      SourceEdge_TargetPathMap.of_seq (List.to_seq path_match_adjs);
    checkpoints =
      List.map fst checkpts
  }

let test_const_hoist : unit -> unit =
  fun _ ->
    let _ =
      refinement_check_inject
        (cfg_data_to_ufunc_ir src_cfg_data)
        (cfg_data_to_ufunc_ir tgt_cfg_data)
        the_proof
        checkpts
        default_checker_config in
    ()



