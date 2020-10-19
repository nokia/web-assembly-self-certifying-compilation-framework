(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


open Sys
open Filename
open Wasm
open Source
open Wasm_utils
open Instr_graph
open Func_types
open Script_types
open State_types
open Proof_types
open Solver_types
open Worklist

open Digraph
open File_reader
open Pass_types
open Pass_master

open Cfg_builder
open Proof_builder

open File_writer

module List = List_utils


(* Make sure that the identity transformation works on specs core tests
 * ... that are found in the test/tmp file currently *)

let pass_conf = default_pass_config

let check_conf = default_pass_config.checker_config

let spec_core_dir : string = "test/tmp"

let is_wast_file : string -> bool =
  fun file ->
    (extension file) = ".wast"

let spec_core_wasts : string list =
  let files = Array.to_list (readdir spec_core_dir) in
  List.filter is_wast_file (List.map (fun f -> spec_core_dir ^ "/" ^ f) files)

(* (1) extract the func_irs
 * (2) run_upass on each one
 * (3) check_summary *)
let run_file : upass list -> string -> unit =
  fun passes file ->
    let script_ir = script_to_uscript_ir (wast_file_to_script file) in
    let (_, sums, script_ir1) = run_script_b script_ir (pass_conf,check_conf) passes in
    let _ = List.map (fun sum -> query_pass_summary sum check_conf) sums in
    let script1 = script_ir_to_script script_ir1 in
    let _ = script_to_file script1 "/home/taro/Desktop/hello.wast" in
    ()

let run_passes_tmp : upass list -> unit =
  fun passes ->
    List.iter (run_file passes) spec_core_wasts


