(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)

open Sys
open Filename
open File_reader
open File_writer
open Pass_header
open Pass_master
open Script_types

open System

(* Makes sure that we can do the following do nothing pass:
 *  WAST file
 *  -> Script.script
 *  -> Script_types.script_ir
 *  -> run_script_blocked with [do_nothing_pass]
 *  -> Script.script
 *  -> WAST
 *
 * That is, the functionalities converting to and from IR is an identity.
 * Assumes that /usr/bin/wasm or equivalent is present,
 * which is the executable from the make install of spec *)

(* Directory relative to starting at wasm-certified/checker *)
let spec_core_dir : string = "test/spec-core"

(* Is .wast file? *)
let is_wast_file : string -> bool =
  fun file ->
    (* String.lowercase_ascii (extension file) = "wast" *)
    (extension file) = ".wast"

(* Assume there is no nested directories since this only looks at top-level *)
let spec_core_wasts : string list =
  let files = Array.to_list (readdir spec_core_dir) in
  let path_files = List.map (fun f -> spec_core_dir ^ "/" ^ f) files in
  List.filter is_wast_file path_files

(* Runs the do_nothing_pass; puts results in a new file. *)
let run_do_nothing_pass : string -> string -> unit =
  fun in_file out_file ->
    (* Extract script ir *)
    let script0 = wast_file_to_script in_file in
    let script_ir0 = script_to_uscript_ir script0 in

    (* Run the pass *)
    let (_, _, script_ir1) =
      run_script_blocked
        script_ir0 empty_upass_config [Do_nothing_pass.do_nothing_pass] in
    
    (* Convert to script and write to file *)
    let script1 = script_ir_to_script script_ir1 in
    script_to_file script1 out_file

(* The system pipeline consists of:
 *  (1) creating a temp file
 *  (2) using the temp file as a target for the original WAST File
 *  (3) comparing differences of /usr/bin/wasm on the temp and original
 *  (4) report whatever necessary *)
let test_file_do_nothing_pass : string -> unit =
  fun file ->
    (* let _ = print_endline ("test_file_wast: " ^ file) in *)
    let temp_file = temp_file (remove_extension (basename file)) ".wast" in
    let _ = run_do_nothing_pass file temp_file in


    let _ = prerr_endline temp_file in
    ()

  (*
    let (old_out, old_err) = unix_command_stdout_stderr ("wasm " ^ file) in
    let (new_out, new_err)
      = unix_command_stdout_stderr ("wasm " ^ temp_file) in
    if (String.trim old_out = String.trim new_out)
        && (String.trim new_err = String.trim new_err) then
      let _ = prerr_endline new_err in
      print_endline
        ("test_file_do_nothing_pass: Okay [" ^ file ^ "]")
    else
      let _ = prerr_endline new_err in
      print_endline
        ("test_file_do_nothing_pass: Errs [" ^ file ^ "]"
          ^ "; Check [" ^ temp_file ^ "]")
    *)

let test_spec_core_do_nothing_pass : unit -> unit =
  fun _ ->
    let wasts = spec_core_wasts in
    let _ = print_int (List.length wasts) in
    List.iter test_file_do_nothing_pass wasts


