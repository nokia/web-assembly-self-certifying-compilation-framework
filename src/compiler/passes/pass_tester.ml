(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


(* We go through the pass process but do not bother converting the
 * the func_ir back to the actual func type -- the purpose of this is
 * to make sure that our annotated passes are working correctly *)

open Func_types
open Proof_types
open Script_types
open Pass_types
open Pass_master

(* Extract upass_summaries from module *)
let run_module_test
  : umodule_ir
  -> pass_config
  -> upass list
  -> upass_summary list =
  fun (md0, mdty0) pass_conf passes ->
    List.concat (List.map
      (fun fn -> let (_, sums, _) = run_func_b fn pass_conf passes in sums)
      mdty0.func_irs)

(* Extract upass_summaries from definition *)
let run_definition_test
  : udefinition_ir
  -> pass_config
  -> upass list
  -> upass_summary list =
  fun def_ir0 pass_conf passes ->
    match def_ir0.it with
    | Textual md_ir0 -> run_module_test md_ir0 pass_conf passes
    | _ -> []

(* Extract upass_summaries from command *)
let rec run_command_test
  : ucommand_ir
  -> pass_config
  -> upass list
  -> upass_summary list =
  fun cmd_ir0 pass_conf passes ->
    match cmd_ir0.it with
    | Module (x_opt, def_ir0) -> run_definition_test def_ir0 pass_conf passes
    | Meta meta_ir0 -> run_meta_test meta_ir0 pass_conf passes
    | _ -> []

(* Extract upass_summaries from meta *)
and run_meta_test
  : umeta_ir
  -> pass_config
  -> upass list
  -> upass_summary list =
  fun meta_ir0 pass_conf passes ->
    match meta_ir0.it with
    | Script (x_opt, script_ir0) -> run_script_test script_ir0 pass_conf passes
    | _ -> []

(* Extract upass_summaries from script *)
and run_script_test
  : uscript_ir
  -> pass_config
  -> upass list
  -> upass_summary list =
  fun cmd_irs0 pass_conf passes ->
    List.concat (List.map
      (fun cmd_ir -> run_command_test cmd_ir pass_conf passes) cmd_irs0)


