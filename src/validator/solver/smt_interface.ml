(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)

open Proof_types
       
open Solver_types
open Smt_ir
open String_bridge
open Z3_bridge

let run_smt_query : interpretation -> smt_query -> solver_config -> solver_result =
  fun interp query solv_conf ->

    let solv_res =
      (if solv_conf.solver_mode = SmtLibStringMode then
        let smt = smt_query_to_smtlib interp query in
        let solv_res = query_smtlib smt solv_conf in
        solv_res
      else
        let solv_res = run_z3_query query solv_conf in
        solv_res) in

    if solv_res.solver_status == Sat then
      let _ = prerr_endline ("FOUND SAT!") in
      (*
      let _ = exit 0 in
      *)
      solv_res
    else
      (*
      let _ = prerr_endline ("*UNSAT!") in
      *)
      solv_res



