(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


(* This is where all the passes are added *)

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

open Do_nothing_pass
open Basic_basic_merge_pass
open Const_fold_pass
open Const_hoist_pass
open Debug

open Either

open File_reader
open File_writer
open System

(* Register all the func-to-func passes here *)
let upasses : upass list =
  [ do_nothing_pass;
    basic_basic_merge_pass;
    const_fold_pass
  ]

(* Apply a upass to a ufunc_ir *)
let run_upass : ufunc_ir -> pass_config -> upass -> upass_summary =
  fun func_ir0 pass_conf pass ->
    let (func_ir1, pass_out) = pass.pass_fun func_ir0 pass_conf in
    init_pass_summary
      func_ir0
      pass_out
      func_ir1



(* Check the summary of a pass against an SMT solver *)
let query_pass_summary : upass_summary -> checker_config -> solver_result list =
  fun sum check_conf ->
  if check_conf.enabled then 
    print_debug_none (Printf.sprintf "\t checking proof for pass %s on function %s" sum.pass_out.pass_id sum.source_func_ir.func_id);
    let result = 
      List.concat
        (List.map
           (fun pf ->
             let qs = List.map (fun ep -> (ep, fun _ -> ())) pf.checkpoints in
             refinement_check_inject
               sum.source_func_ir sum.target_func_ir pf qs check_conf)
           sum.pass_out.proofs)
    in
    print_debug_none (Printf.sprintf "\t done checking proof for pass %s on function %s" sum.pass_out.pass_id sum.source_func_ir.func_id);
    result

      

(* Run all passes and check the summary at the end -- ie blocking behavior *)
let run_func_b
  : ufunc_ir
  -> pass_config * checker_config
  -> upass list
  -> ufunc_ir * (upass_summary list) * ufunc_ir =
  fun func_ir0 (pass_conf, checker_conf) passes ->
  let _ = print_debug_none (Printf.sprintf "\t transforming function %s" func_ir0.func_id) in
  let (func_ir1, sums_rev) =
      List.fold_left
        (fun (f0, acc_sums) pass ->
          let _ = print_debug_none (Printf.sprintf "\t\t via pass %s" pass.pass_id) in
          let sum = run_upass f0 pass_conf pass in
          (sum.target_func_ir, sum :: acc_sums))
        (func_ir0, [])
        passes in
    let sums = List.rev sums_rev in 
    let _ = List.map (fun sum -> query_pass_summary sum checker_conf) sums in
    (func_ir0, sums, func_ir1)

(* Run passes on a module.
 * Need to convert the func_ir back to Ast.func for the module funcs *)
let run_module_b
  : umodule_ir
  -> pass_config * checker_config
  -> upass list
  -> umodule_ir * (upass_summary list) * umodule_ir =
  fun (md0, mdty0) (pass_conf, checker_conf) passes ->

    let funcs0 = md0.it.funcs in
    let func_irs0 = mdty0.func_irs in
    let func_count = List.length func_irs0 in

    (* Dumping code *)
    let _ =
      if pass_conf.dump_init_cfgs
        then print_debug_none ("no longer dumping initial CFGs")
        else () in

    let passes_res =
      List.mapi (fun i ((func0 : Ast.func), (fir0 : ufunc_ir)) ->
        let _ = print_debug_none ("\t pass on function "
                ^ string_of_fraction (i + 1, func_count) ^ ": "
                ^ fir0.func_id) in
        let (bad, reason) =
          if (pass_conf.filter) then is_instrs_bad func0.it.body else (false,"NO REASON")
        in
        if bad 
          then (print_debug_none ("\t skipping because " ^ reason); (fir0, [], fir0))
          else run_func_b fir0 (pass_conf, checker_conf) passes)
        (List.zip funcs0 func_irs0) in
    let sums = List.concat (List.map (fun (_, s, _) -> s) passes_res) in
    let func_irs1 = List.map (fun (_, _, fn1) -> fn1) passes_res in

    (* Dumping code *)
    let _ =
      if pass_conf.dump_final_cfgs
        then print_debug_none ("no longer dumping final CFGs")
        else () in

    let funcs1 =
      if pass_conf.gen_wast
        then List.map func_ir_to_func func_irs1
        else md0.it.funcs in

    let md1 = { md0.it with funcs = funcs1 } @@ md0.at in
    let mdty1 = { mdty0 with func_irs = func_irs1 } in
    ((md0, mdty0), sums, (md1, mdty1))
      
(* Run passes on a definition *)
let run_definition_b
  : udefinition_ir
  -> pass_config * checker_config
  -> upass list
  -> udefinition_ir * (upass_summary list) * udefinition_ir =
  fun def_ir0 confs passes ->
    match def_ir0.it with
    | Textual md_ir0 ->
      let (_, sums, md_ir1) = run_module_b md_ir0 confs passes in
      let def_ir1 = (Textual md_ir1) @@ def_ir0.at in
      (def_ir0, sums, def_ir1)
    | _ -> (def_ir0, [], def_ir0)

(* Run passes on a command, which recursively calls definition *)
let rec run_command_b
  : ucommand_ir
  -> pass_config * checker_config
  -> upass list
  -> ucommand_ir * (upass_summary list) * ucommand_ir =
  fun cmd_ir0 confs passes ->
    match cmd_ir0.it with
    | Module (x_opt, def_ir0) ->
      let (_, sums, def_ir1) =
        run_definition_b def_ir0 confs passes in
      let cmd_ir1 = (Module (x_opt, def_ir1)) @@ cmd_ir0.at in
      (cmd_ir0, sums, cmd_ir1)
    | Meta meta_ir0 ->
      let (_, sums, meta_ir1) =
        run_meta_b meta_ir0 confs passes in
      let cmd_ir1 = (Meta meta_ir1) @@ cmd_ir0.at in
      (cmd_ir0, sums, cmd_ir1)
    | _ -> (cmd_ir0, [], cmd_ir0)

(* Run passes on a meta *)
and run_meta_b
  : umeta_ir
  -> pass_config * checker_config
  -> upass list
  -> umeta_ir * (upass_summary list) * umeta_ir =
  fun meta_ir0 confs passes ->
    match meta_ir0.it with
    | Script (x_opt, script_ir0) ->
      let (_, sums, script_ir1) =
        run_script_b script_ir0 confs passes in
      let meta_ir1 = (Script (x_opt, script_ir1)) @@ meta_ir0.at in
      (meta_ir0, sums, meta_ir1)
    | _ -> (meta_ir0, [], meta_ir0)

(* Run passes on a script, recalling that Script.script = Script.cmd list *)
and run_script_b
  : uscript_ir
  -> pass_config * checker_config
  -> upass list
  -> uscript_ir * (upass_summary list) * uscript_ir =
  fun cmd_irs0 confs passes ->
    let passes_res =
      List.map (fun c -> run_command_b c confs passes) cmd_irs0 in
    let sums = List.concat (List.map (fun (_, s, _) -> s) passes_res) in
    let cmd_irs1 = List.map (fun (_, _, cmd1) -> cmd1) passes_res in
    (cmd_irs0, sums, cmd_irs1)

(* I/O operations such as SMT calls and reading from file;
 * things to do after we have done with the passes *)

    
(* Run passes on a file, check the pass summary proofs,
 * and write the optimized script (file) to the new destination after 
let run_file_passes_block
  : string -> string -> pass_config -> upass list -> checker_config -> unit =
  fun in_file out_file pass_conf passes check_conf ->
    (* Extract script_ir and run the passes *)
    let script0 = wast_file_to_script in_file in
    let script_ir0 = script_to_uscript_ir script0 in
    let (_, sums, script_ir1) =
      run_script_b script_ir0 pass_conf passes in

    (* Do Smt checks *)
    let _ = List.map (fun sum -> query_pass_summary sum check_conf) sums in

    (* Convert and write out to file *)
    let script1 = script_ir_to_script script_ir1 in
    script_to_file script1 out_file

*)
