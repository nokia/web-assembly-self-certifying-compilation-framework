(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


open Wasm
open Source
open Script_types
open Func_types
open Proof_types
open Solver_types
open Worklist
open Instr_graph
open Wasm_utils

open Pass_types
open Pass_master

open Either
open File_reader
open File_writer
open System
open Debug

open Benchmark_types
open System
open Filename

(* A lot of this would be a re-implementation of what is in passes, but with timing marks *)

(* Run passes on a single file *)
let query_pass_summary : upass_summary -> checker_config -> solver_result list * float =
  fun sum check_conf ->
  if check_conf.enabled then
    let smt_tm0 = Unix.gettimeofday () in
    let _ = print_debug_none ("\t proof checking " ^ sum.source_func_ir.func_id) in
    let results =
      List.concat
        (List.map
          (fun pf ->
            let qs = List.map (fun ep -> (ep, fun _ -> ())) pf.checkpoints in
            refinement_check_inject
              sum.source_func_ir sum.target_func_ir pf qs check_conf)
          sum.pass_out.proofs) in
    let smt_tm1 = Unix.gettimeofday () in
    let _ = print_debug_none ("\t done checking " ^ sum.source_func_ir.func_id) in
    (results, smt_tm1 -. smt_tm0)
  else
    (print_debug_none ("\t proof checking not enabled"); ([], 0.0))


(* Run pass on a single func, timed *)
let run_func_timed
  : Ast.func * ufunc_ir
  -> pass_config * checker_config
  -> upass list
  -> (ufunc_ir * (upass_summary list) * ufunc_ir * Ast.func) * func_stat =
  fun (func0, func_ir0) (pass_conf, checker_conf) passes ->
    let total_tm0 = Unix.gettimeofday () in
    (* Run the passes *)
    let (func_ir1, sums_rev) =
      List.fold_left
        (fun (f0, acc_sums) pass ->
          let sum = run_upass f0 pass_conf pass in
          (sum.target_func_ir, sum :: acc_sums))
        (func_ir0, [])
        passes in
    let opt_tm = (Unix.gettimeofday ()) -. total_tm0 in
    let sums = List.rev sums_rev in
    
    (* If the instr graphs are different, we do something about it *)
    let graph_modified = instr_graphs_differ func_ir0.body_graph func_ir1.body_graph in

    (* Do some querying of the SMT *)
    let query_res =
      List.map
        (fun sum ->
          if graph_modified
            then query_pass_summary sum checker_conf
            else ([], 0.0))
        sums in
    let smt_tm = List.fold_left (+.) 0.0 (List.map snd query_res) in

    (* Convert if applicable *)
    let (func1, cfg2wast_tm) =
      if graph_modified && pass_conf.gen_wast
        then
          let gen_tm0 = Unix.gettimeofday () in
          let f1 = func_ir_to_func func_ir1 in
          let gen_tm1 = Unix.gettimeofday () in
          (f1, gen_tm1 -. gen_tm0)
        else (func0, 0.0) in

    let total_tm1 = Unix.gettimeofday () in

    ((func_ir0, [], func_ir1, func1),
      { empty_func_stat with
        func_id = func_ir0.func_id;
        func_good = true;
        func_modified = graph_modified;
        total_checks = -1;
        good_checks = -1;
        total_time = total_tm1 -. total_tm0;
        opt_time = opt_tm;
        smt_time = smt_tm;
        cfg2wast_time = cfg2wast_tm;
      })

(* Run passes on a single module, timed *)
let run_module_timed
  : umodule_ir
  -> pass_config * checker_config
  -> upass list
  -> (umodule_ir * (upass_summary list) * umodule_ir) * func_stat list =
  fun mod_ir0 confs passes ->
    let (md0, mdty0) = mod_ir0 in
    let funcs0 = md0.it.funcs in
    let func_irs0 = mdty0.func_irs in
    let func_count = List.length func_irs0 in

    let pass_conf, checker_conf = confs in 
    
    let passes_res =
      List.mapi (fun i ((func0 : Ast.func), (fir0 : ufunc_ir)) ->
        (* If the func_ir is good we run it, otherwise no *)
          let (bad, reason) =
            if (pass_conf.filter) then is_instrs_bad func0.it.body else (false,"NO REASON")
          in
        if bad then
          let _ = print_debug_none ("\t function "
            ^ string_of_fraction (i+1, func_count) ^ ": skipping because " ^ reason) in
          ((fir0, [], fir0, func0), { empty_func_stat with func_id = fir0.func_id })
        else
          let _ = print_debug_none ("\t function "
            ^ string_of_fraction (i+1, func_count) ^ ": optimizing") in
          run_func_timed (func0, fir0) confs passes)
        (List.zip funcs0 func_irs0) in

    let sums = List.concat (List.map (fun ((_, s, _, _), _) -> s) passes_res) in
    let func_irs1 = List.map (fun ((_, _, fir1, _), _) -> fir1) passes_res in
    let funcs1 = List.map (fun ((_, _, _, f1), _) -> f1) passes_res in
    let func_stats = List.map snd passes_res in
    
    let md1 = { md0.it with funcs = funcs1 } @@ md0.at in
    let mdty1 = { mdty0 with func_irs = func_irs1 } in
    (((md0, mdty0), sums, (md1, mdty1)), func_stats)

(* Run passes on a single definition, timed *)
let run_definition_timed
  : udefinition_ir
  -> pass_config * checker_config
  -> upass list
  -> (udefinition_ir * (upass_summary list) * udefinition_ir) * func_stat list =
  fun def_ir0 confs passes ->
    match def_ir0.it with
    | Textual md_ir0 ->
      let ((_, sums, md_ir1), func_stats) = run_module_timed md_ir0 confs passes in
      let def_ir1 = (Textual md_ir1) @@ def_ir0.at in
      ((def_ir0, sums, def_ir1), func_stats)
    | _ -> ((def_ir0, [], def_ir0), [])

(* Run passes on a single command, timed *)
let rec run_command_timed
  : ucommand_ir
  -> pass_config * checker_config
  -> upass list
  -> (ucommand_ir * (upass_summary list) * ucommand_ir) * func_stat list =
  fun cmd_ir0 confs passes ->
    match cmd_ir0.it with
    | Module (x_opt, def_ir0) ->
      let ((_, sums, def_ir1), func_stats) = run_definition_timed def_ir0 confs passes in
      let cmd_ir1 = (Module (x_opt, def_ir1)) @@ cmd_ir0.at in
      ((cmd_ir0, sums, cmd_ir1), func_stats)
    | Meta meta_ir0 ->
      let ((_, sums, meta_ir1), func_stats) = run_meta_timed meta_ir0 confs passes in
      let cmd_ir1 = (Meta meta_ir1) @@ cmd_ir0.at in
      ((cmd_ir0, sums, cmd_ir1), func_stats)
    | _ -> ((cmd_ir0, [], cmd_ir0), [])

(* Run on a single meta, timed *)
and run_meta_timed
  : umeta_ir
  -> pass_config * checker_config
  -> upass list
  -> (umeta_ir * (upass_summary list) * umeta_ir) * func_stat list =
  fun meta_ir0 confs passes ->
    match meta_ir0.it with
    | Script (x_opt, script_ir0) ->
      let ((_, sums, script_ir1), func_stats) =
        run_script_timed script_ir0 confs passes in
      let meta_ir1 = (Script (x_opt, script_ir1)) @@ meta_ir0.at in
      ((meta_ir0, sums, meta_ir1), func_stats)
    | _ -> ((meta_ir0, [], meta_ir0), [])

(* Run on a single script, timed *)
and run_script_timed
  : uscript_ir
  -> pass_config * checker_config
  -> upass list
  -> (uscript_ir * (upass_summary list) * uscript_ir) * func_stat list =
  fun cmd_irs0 confs passes ->
    let passes_res =
      List.map (fun c -> run_command_timed c confs passes) cmd_irs0 in
    let pass_trips = List.map fst passes_res in
    let func_stats = List.concat (List.map snd passes_res) in
    let sums = List.concat (List.map (fun (_, s, _) -> s) pass_trips) in
    let cmd_irs1 = List.map (fun (_, _, cmd1) -> cmd1) pass_trips in
    ((cmd_irs0, sums, cmd_irs1), func_stats)

(* Run on a single file, timed *)
let run_file_timed : string -> (pass_config * checker_config) -> upass list -> file_stat =
  fun file confs passes ->
    let _ = print_debug_none (" <<<<< Beginning file " ^ file ^ "") in
    let (pass_conf, _) = confs in
    let _ = print_debug_none ("\t converting to ir " ^ file) in
    let script_ir0 = script_to_uscript_ir (wast_file_to_script file) in

    let ((_, _, script_ir1), func_stats) = run_script_timed script_ir0 confs passes in
    let _ = print_debug_none ("\t finished run_script_timed") in

    let file_stat = func_stats_to_file_stat file passes func_stats in

    let out_file = (remove_extension file) ^ ".out.wast" in

    let _ =
      if pass_conf.gen_wast then
        (* The func_ir_to_func handles the CFG conversion already earlier *)
        let script1 = script_ir_to_script script_ir1 in
        script_to_file script1 out_file 
      else
        ()
      in

    let _ = print_debug_none (" >>>>> Completed file " ^ file ^ "") in
    let _ = flush stdout in
    let _ = flush stderr in
    file_stat

let run_spec_timed : (pass_config * checker_config) -> upass list -> file_stat list =
  fun confs passes ->
    let _ = print_debug_none ("### Beginning Specs Benchmarks ########################") in
    let stats = List.map (fun f -> run_file_timed f confs passes) (spec_wasts ()) in
    let _ = print_debug_none ("### Completed Specs Benchmarks ########################") in
    let _ = flush stdout in
    let _ = flush stderr in
    stats

