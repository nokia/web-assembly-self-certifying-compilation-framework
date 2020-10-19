(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


open Sys
open Filename
open File_reader
open Script_types
open Solver_types
open Pass_header
open Pass_master
open Pass_tester

open System

let spec_core_dir : string = "test/spec-core"
(* let spec_core_dir : string = "test/tpec-core" *)

let is_wast_file : string -> bool =
  fun file -> ".wast" = (extension file)

let spec_core_wasts : unit -> string list =
  fun _ ->
    let files = Array.to_list (readdir spec_core_dir) in
    let path_files = List.map (fun f -> spec_core_dir ^ "/" ^ f) files in
    List.filter is_wast_file path_files

let spec_core_script_irs : unit -> uscript_ir list =
  fun _ ->
    let wasts = spec_core_wasts () in
    let scripts = List.map wast_file_to_script wasts in
    let script_irs = List.map script_to_uscript_ir scripts in
    script_irs

let test_pass_tester : unit -> unit =
  fun _ ->
    let _ = prerr_endline ("test_pass_tester: start") in
    let script_irs = spec_core_script_irs () in
    let pass_conf = empty_upass_config in
    let passes = upasses in
    let smt_conf = empty_smt_config in
    let sums =
      List.concat (List.map
        (fun sir -> run_script_test sir pass_conf passes) script_irs) in
    let _ = prerr_endline ("test_pass_tester: running summary checks") in
    let _ = check_summaries sums smt_conf in
    let _ = prerr_endline ("test_pass_tester: done") in

    ()


