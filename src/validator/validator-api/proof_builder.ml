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

open Cfg_builder

open Worklist

module Full = Full_sym_eval.Eval
module UF = Uf_sym_eval.Eval

(* Build proofs more easier *)
let int32_vals_eq : value -> value -> formula =
  fun x y ->
    ValsRelForm (x, AstRelOp(Values.I32 Ast.IntOp.Eq), y)

let post_call_state : state -> Ast.var -> state =
  fun state0 x ->
    next_state state0 (CallAct x)

let uf_state_pair_equiv : (state * state) -> formula =
  fun (state0, state1) ->
  UF.states_equiv state0 state1

let full_state_pair_equiv : (state * state) -> formula =
  fun (state0, state1) ->
  Full.states_equiv state0 state1


