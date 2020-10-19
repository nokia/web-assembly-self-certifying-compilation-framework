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
open Debug
open System

open Test_call

module List = List_utils

module SSA = Ssa_pass
module UnSSA = Unssa_pass
module BDSE = Bdse_pass
module DSE = Dse_pass
module CompressLocals = Compress_locals_pass
module Unroll = Unroll_pass

open Benchmark_types
open Benchmark_runner
                

open Z3_bridge

let is_wast_file : string -> bool =
  fun file ->
  (extension file) = ".wast"


(* add a new pass here *)
let supported_passes: (string * upass) list = 
  [
    "const-fold",      Const_fold_pass.const_fold_pass;
    "ssa",             SSA.ssa_pass;
    "unssa",           UnSSA.unssa_pass;
    "basic-dse",       BDSE.bdse_pass;
    "dse",             DSE.dse_pass;
    "compress-locals", CompressLocals.compress_locals_pass;
    "unroll",          Unroll.unroll_pass;
  ]

    

(* globals used to record external arguments *)
let r_debug: int ref = ref Debug.none
let r_passes: upass list ref = ref []
let r_source_file: string option ref = ref None
let r_output_file: string option ref = ref None
let r_nowast : bool ref = ref false
let r_proof_chk: bool ref = ref false
let r_proof_gen: bool ref = ref false
let r_dump_init_cfgs : bool ref = ref false
let r_dump_final_cfgs : bool ref = ref false
let r_list_passes: bool ref = ref false
let r_spec_bench : bool ref = ref false
let r_filter : bool ref = ref false
(* end globals *)

                        
let usage =
  "WebAssembly optimizer 
      run as whisk -pass <pass> source.wast
      run as whisk --help for more options
   "

let run_file_passes_block
  : string -> string -> pass_config -> upass list -> checker_config -> unit =
  fun in_file out_file pass_conf passes check_conf ->
    (* Extract script_ir and run the passes *)
    let _ = print_debug_none (Printf.sprintf "\t init loading %s" in_file) in
    let script0 = wast_file_to_script in_file in
    let script_ir0 = script_to_uscript_ir script0 in

    let _ = print_debug_none (Printf.sprintf "\t done loading %s" in_file) in

    let (_, sums, script_ir1) =
      run_script_b script_ir0 (pass_conf,check_conf) passes in

    (* Convert and write out to file *)
    if not (!r_nowast) then
      let script1 = script_ir_to_script script_ir1 in
      script_to_file script1 out_file
    else
      ()        

    
let register_pass p =
  try
    let pass = List.assoc p supported_passes in 
    r_passes := (!r_passes)@[pass]
  with
    Not_found ->
     Printf.eprintf "Unknown pass %s -- ignored" p
        

let register_source_file f =
  if (not (is_wast_file f)) then
    failwith(Printf.sprintf "Source file %s does not have a .wast extension" f)
  else
    r_source_file := Some(f)

let register_output_file f =
  if (not (is_wast_file f)) then
    failwith(Printf.sprintf "Output file %s does not have a .wast extension" f)
  else
    r_output_file := Some(f)                       


let arg_spec =
  [
    "-debug",           Arg.Set_int r_debug,              "set debug level (default none)";
    "-o",               Arg.String register_output_file,  "<output file> (default is <source>.out.wast)";
    "-list-passes",     Arg.Set r_list_passes,            "list available passes";
    "-pass",            Arg.String register_pass,         "<pass name>";
    "-proofgen",        Arg.Set r_proof_gen,              "turn on proof generation";        
    "-proofchk",        Arg.Set r_proof_chk,              "turn on proof generation and checking";
    "-nowast",          Arg.Set r_nowast,                 "do not generate a file";
    "-dump-init-cfgs",  Arg.Set r_dump_init_cfgs,         "dump the initial CFGs";
    "-dump-final-cfgs", Arg.Set r_dump_final_cfgs,        "dump the initial CFGs";
    "-spec-bench",      Arg.Set r_spec_bench,             "run spec benchmarks";
    "-filter",          Arg.Set r_filter,                 "filter out certain source files";
  ]

  
let bench_check_config : checker_config =
  { default_checker_config with
    enabled = true;
  }

let bench_pass_config =
  { default_pass_config with
    gen_proof = true;
    gen_wast = false;
  }

let run_spec_benchmark : upass list -> unit =
  fun passes ->
    let spec_file_stats = run_spec_timed (bench_pass_config, bench_check_config) passes in
    let spec_bench_stat = file_stats_to_bench_stat spec_file_stats in

    let _ = flush stdout in
    let _ = flush stderr in
    let _ = print_debug_none (string_of_bench_stat spec_bench_stat "spec dump") in
    exit 0


let compile() =
  Printexc.record_backtrace true;

  Arg.parse arg_spec register_source_file usage;

  Debug.set_debug_level (!r_debug);

  if !r_list_passes then
    (Printf.printf "\n Available passes:";
     List.iter (fun (p,_) -> Printf.printf "\n\t%s" p) supported_passes;
     Printf.printf "\n";
     exit 0;
    )
  else ();
  
  let _ = if !r_spec_bench then run_spec_benchmark !r_passes else () in

  (* check arguments *)
  let source_file_name =
    match !r_source_file with
    | None ->
       Printf.printf "%s" usage;
       failwith("No source file provided")
    | Some(inf) -> inf
  in

  let output_file_name =
    match !r_output_file with
    | None ->  Printf.sprintf "%s.out.wast" (remove_extension source_file_name)
    | Some(outf) -> outf
  in

  (* make consistent choices for proof generation and checking *)
  if (!r_proof_chk) then r_proof_gen := true;

  let check_config =
    { default_checker_config with
      enabled = !r_proof_chk
    }
  in
  let pass_config =
    { default_pass_config with
        gen_proof = !r_proof_gen;
        gen_wast = not (!r_nowast);
        dump_init_cfgs = !r_dump_init_cfgs;
        dump_final_cfgs = !r_dump_final_cfgs;
        checker_config = check_config;
        filter = !r_filter
    }
  in
  run_file_passes_block source_file_name output_file_name pass_config (!r_passes) check_config
  ;;

compile();;

