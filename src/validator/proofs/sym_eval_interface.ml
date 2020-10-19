(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)

(* abstrated symbolic evaluator interface *)

open Wasm
open Wasm_utils
open Instr_graph
open State_types
open Proof_types
open Func_types
open Debug

open Smt_ir

(* Some configurations for symbolic evaluation *)
type sym_config =
  {
    (* Number of states allowed *)
    max_states : int;

    (* Pointer ranges *)
    values_min : int32;
    values_max : int32;

    locals_min : int32;
    locals_max : int32;

    globals_min : int32;
    globals_max : int32;

    memory_min : int32;
    memory_max : int32;
  }

let default_sym_config =
  {
    max_states = 2500;
  
    values_min = 4l;
    (* values_max = 2147483647l; *)
    values_max = 65535l;

    locals_min = 0l;
    (* locals_max = 2147483647l; *)
    locals_max = 65535l;

    globals_min = 0l;
    (* globals_max = 2147483647l; *)
    globals_max = 65535l;

    memory_min = 0l;
    (* memory_max = 2147483647l; *)
    memory_max = 65535l;
  }

(* Shortcuts *)
let eq_int32 : relop = AstRelOp (Values.I32 Ast.IntOp.Eq)
let ne_int32 : relop = AstRelOp (Values.I32 Ast.IntOp.Ne)
let leu_int32: relop = AstRelOp (Values.I32 Ast.IntOp.LeU)
    
module type EvalT =
  sig

    val states_equiv : state -> state -> formula

    val exec_state_actions:
      state -> action list -> phi_map -> sym_config -> string (* tag *) -> formula

    val enabled_upto_state_actions:
        state -> action list -> sym_config -> (state * formula)

    val blocked_at_state_actions:
      state -> action list -> sym_config -> formula
                                              
    val trapped_at_state_actions:
      state -> action list -> sym_config -> formula
                                              
    val source_target_calls_synced:
      (state * action list * ufunc_ir)
      -> (state * action list * ufunc_ir)
      -> proof
      -> sym_config
      -> (formula * formula) list

    val smt_operator_decls: action list -> smt_decl list

    val smt_const_decls: unit -> smt_decl list

    val smt_int_value: int32 -> value
                         
  end
