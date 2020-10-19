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
open Script_types
open Debug

module String = String_utils

(* ****************** *)
type smtlib = string

(* The backend with how the solver is run, do we use:
 *  - Strings that are dumped into a file on which Z3 is called
 *  - Z3 bridge mode using Z3's OCaml bridge
 *)
type solver_mode = SmtLibStringMode | Z3BridgeMode

(* Tells whether we are Sat or Unsat, or unknown if the search failed.
 * At the moment we do not support returning models because this implies
 * the ability to parse solver output, which would require hooking
 * up against an actual back-end bridge or writer own own parser.
 * So we keep things simple for now :) *)
type solver_status = Sat | Unsat | Unknown | Error | NotCalled

(* Some configurations to feed into the SMT solver.
 *  smt_headers is used for smtlib instructions before the main body
 *  smt_footers is used for smtlib instructions after the main body *)
type solver_config =
  { solver_mode : solver_mode;
    debugs : string list
  }

let default_solver_config : solver_config =
  { solver_mode = SmtLibStringMode;
    (*
    solver_mode = Z3BridgeMode;
    *)
    debugs = [];
  }

(* When querying an smt solver we track the stdout and stderr and use some
 * minor functionalities to search for Sat / Unsat / Unknown results *)
type solver_result =
  { solver_status : solver_status;
    debug_strings : string list
  }

let empty_solver_result : solver_result =
  { solver_status = NotCalled;
    debug_strings = [];
  }

(* Mild parsing functionalities *)

(* Lines that have "(error " *)
let parse_error_lines : string -> string list =
  fun str ->
    List.filter (fun l -> String.contains l "(error ")
      (String.lines (String.lowercase_ascii str))

let parse_solver_call : solver_config -> (string * string) -> solver_result =
  fun solv_conf (out_str, err_str) ->
    (* Some things go into the stdout for some reason *)
    let err_lines = parse_error_lines out_str in
    let debug_outs = if List.length err_lines > 1 then [List.hd err_lines] else [] in
    let debug_err = "solver stderr: " ^ err_str in
    { empty_solver_result with
      debug_strings = debug_err :: debug_outs;
      solver_status =
        (if String.contains (String.lowercase_ascii out_str) "unsat" then
          Unsat
        else if String.contains (String.lowercase_ascii out_str) "sat" then
          Sat
        else if String.contains (String.lowercase_ascii out_str) "(error " then
          Error
        else
          Unknown) }

let string_of_solver_status : solver_status -> string = function
  | Sat -> "Sat"
  | Unsat -> "Unsat"
  | Unknown -> "Unknown"
  | Error -> "Error"
  | NotCalled -> "NotCalled"

