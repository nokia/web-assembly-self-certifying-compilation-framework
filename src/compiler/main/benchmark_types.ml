(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


open Sys
open Filename
open File_reader
open Pass_types
open Func_types
open Func_types
open Script_types
open Wasm_utils
open Debug

module String = String_utils

(* File information relative to checker/ *)
let spec_bench_dir : string = "spec/test/core"

let spec_wasts : unit -> string list =
  fun _ ->
    let files = Array.to_list (readdir spec_bench_dir) in
    let path_files = List.map (fun f -> spec_bench_dir ^ "/" ^ f) files in
    List.filter is_wast_file path_files

let spec_script_irs : unit -> uscript_ir list =
  fun _ ->
    let wasts = spec_wasts () in
    let scripts = List.map wast_file_to_script wasts in
    let script_irs = List.map script_to_uscript_ir scripts in
    script_irs


(* Statitics for a single function
 * Assumption:
 *  - if func_good = false, then func_modified = false
 *  - if func_good = true, but func_modified = false, then all times are zero
 *  - if func_good = false, then all times are zero
 *)
type func_stat =
  { func_id : func_id;

    func_good : bool;
    func_modified : bool;

    total_checks : int;
    good_checks : int;

    total_time : float;
    opt_time : float;
    smt_time : float;
    cfg2wast_time : float;
  }

let empty_func_stat : func_stat =
  { func_id = "";
    func_good = false;
    func_modified = false;
    total_checks = 0;
    good_checks = 0;
    total_time = 0.0;
    opt_time = 0.0;
    smt_time = 0.0;
    cfg2wast_time = 0.0;
  }

(* Statistics over a file *)
type file_stat =
  { file : string;
    pass_ids : pass_id list;

    (* total - good = # bailed funcs due to non-Int32 or non-SMT instrs *)
    total_funcs : int;
    good_funcs : int;
    modified_funcs : int;

    (* total - good = # checks that returned UNKNOWN *)
    total_checks : int;
    good_checks : int;

    (* Total time spent doing these passes on this *)
    total_time : float;

    (* Time spent doing optimizations *)
    opt_time : float;

    (* Time spent doing SMT converions *)
    smt_time : float;

    (* Time spent folding CFG back into instruction sequences *)
    cfg2wast_time : float;
  }


(* Functions for computing file_stat from a func_stat list *)

let func_total_time : func_stat -> float =
  fun stat -> if stat.func_good && stat.func_modified then stat.total_time else 0.0

let func_opt_time : func_stat -> float =
  fun stat -> if stat.func_good && stat.func_modified then stat.opt_time else 0.0

let func_smt_time : func_stat -> float =
  fun stat -> if stat.func_good && stat.func_modified then stat.smt_time else 0.0

let func_cfg2wast_time : func_stat -> float =
  fun stat -> if stat.func_good && stat.func_modified then stat.cfg2wast_time else 0.0

let sumfs : float list -> float =
  fun fs -> List.fold_left (+.) 0.0 fs

let sumis : int list -> int =
  fun is -> List.fold_left (+) 0 is

let func_stats_to_file_stat
  : string
  -> upass list
  -> func_stat list
  -> file_stat =
  fun file passes fun_stats ->
    let pass_ids = List.map (fun (p : upass) -> p.pass_id) passes in

    let total_funcs = List.length fun_stats in
    let good_funcs = List.length (List.filter (fun s -> s.func_good) fun_stats) in
    let modified_funcs = List.length (List.filter (fun s -> s.func_modified) fun_stats) in

    let total_checks = sumis (List.map (fun (s : func_stat) -> s.total_checks) fun_stats) in
    let good_checks = sumis (List.map (fun (s : func_stat) -> s.good_checks) fun_stats) in

    let total_time = sumfs (List.map func_total_time fun_stats) in
    let opt_time = sumfs (List.map func_opt_time fun_stats) in
    let smt_time = sumfs (List.map func_smt_time fun_stats) in
    let cfg2wast_time = sumfs (List.map func_cfg2wast_time fun_stats) in
 
    { file = file;
      pass_ids = pass_ids;

      (* total - good = # bailed funcs due to non-Int32 or non-SMT instrs *)
      total_funcs = total_funcs;
      good_funcs = good_funcs;
      modified_funcs = modified_funcs;

      (* total - good = # checks that returned UNKNOWN *)
      total_checks = total_checks;
      good_checks = good_checks;

      (* Total time spent doing these passes on this *)
      total_time = total_time;
      opt_time = opt_time;
      smt_time = smt_time;
      cfg2wast_time = cfg2wast_time;
    }   


(* Print data *)
let string_of_file_stat : file_stat -> string =
  fun stat ->
    "[" ^ stat.file ^ "]"
      ^ (String.unlines
          ["  passes: " ^ String.concat_as_list stat.pass_ids;
           "  good/total funcs: " ^ string_of_fraction (stat.good_funcs, stat.total_funcs);
           "  total time: " ^ string_of_float stat.total_time;
           "  opt time:   " ^ string_of_float stat.opt_time;
           "  smt time:   " ^ string_of_float stat.smt_time;
           "  gen time:   " ^ string_of_float stat.cfg2wast_time;
           ])

(* Statistics of a "benchmark run" over a list of files *)
type bench_stat =
  { file_passes : (string * pass_id list) list;

    (* total - good = # bailed funcs due to non-Int32 or non-SMT instrs *)
    total_funcs : int;
    good_funcs : int;
    modified_funcs : int;

    (* total - good = # checks that returned UNKNOWN *)
    total_checks : int;
    good_checks : int;

    (* Total time spent doing these passes on this *)
    total_time : float;

    (* Time spent doing optimizations *)
    opt_time : float;

    (* Time spent doing SMT converions *)
    smt_time : float;

    (* Time spent folding CFG back into instruction sequences *)
    cfg2wast_time : float;
  }

let file_stats_to_bench_stat : file_stat list -> bench_stat =
  fun stats ->
    let file_passes = List.map (fun (s : file_stat) -> (s.file, s.pass_ids)) stats in
    let total_funcs = sumis (List.map (fun (s : file_stat) -> s.total_funcs) stats) in
    let good_funcs = sumis (List.map (fun (s : file_stat) -> s.good_funcs) stats) in
    let modified_funcs = sumis (List.map (fun (s : file_stat) -> s.modified_funcs) stats) in

    let total_checks = sumis (List.map (fun (s : file_stat) -> s.total_checks) stats) in
    let good_checks = sumis (List.map (fun (s : file_stat) -> s.good_checks) stats) in

    let total_time = sumfs (List.map (fun (s : file_stat) -> s.total_time) stats) in
    let opt_time = sumfs (List.map (fun (s : file_stat) -> s.opt_time) stats) in
    let smt_time = sumfs (List.map (fun (s : file_stat) -> s.smt_time) stats) in
    let cfg2wast_time = sumfs (List.map (fun (s : file_stat) -> s.cfg2wast_time) stats) in

    { file_passes = file_passes;
      total_funcs = total_funcs;
      good_funcs = good_funcs;
      modified_funcs = modified_funcs;
      total_checks = total_checks;
      good_checks = good_checks;
      total_time = total_time;
      opt_time = opt_time;
      smt_time = smt_time;
      cfg2wast_time = cfg2wast_time;
    }


(* Print data *)
let string_of_bench_stat : bench_stat -> string -> string =
  fun stat msg ->
    let pass_ids =
      (match stat.file_passes with
        | [] -> []
        | (_, ids) :: _ -> ids) in
    "Benchmark Statistics"
      ^ (String.unlines
          ["  msg: " ^ msg;
           "  passes: " ^ String.concat_as_list pass_ids;
           "  good/total funcs: " ^ string_of_fraction (stat.good_funcs, stat.total_funcs);
           "  total time: " ^ string_of_float stat.total_time;
           "  opt time:   " ^ string_of_float stat.opt_time;
           "  smt time:   " ^ string_of_float stat.smt_time;
           "  gen time:   " ^ string_of_float stat.cfg2wast_time;
           ])
