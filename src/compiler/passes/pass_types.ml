(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


open Digraph
open Instr_graph
open Func_types
open Script_types
open Worklist

open Proof_types
open Solver_types

(* Passes operate at a per-function (graph) level;
 * maybe one day there will be module-level multi-CFG passes.
 * For now each pass modifies one function (graph) *)

(* Flags that we may need *)
type pass_flag = PassFlag

(* Input configuration for passes. *)
type pass_config =
  { flags : pass_flag list;
    checker_config : checker_config;
    gen_proof: bool;                   (* true = proof generation is switched on *)
    gen_wast : bool;                   (* toggle generating WAST files via cfg folding *)
    dump_init_cfgs : bool;
    dump_final_cfgs : bool;
    verbose : bool;
    filter: bool;                      (* if on, filter source files *)
  }

let default_pass_config : pass_config =
  { flags = [];
    checker_config = default_checker_config;
    gen_proof = false;
    gen_wast = false;
    dump_init_cfgs = false;
    dump_final_cfgs = false;
    verbose = true;
    filter = false;
  }

(* The type of a pass *)
type pass_id = string

(* Each pass should track the old func_ir, new func_ir, and proofs *)
type pass_out =
  { pass_id: pass_id;
    proofs : proof list;
  }

let empty_pass_out : pass_out =
  { pass_id = "NONE";
    proofs = [];
  }

(* A pass consists of its id (string / name) and the function applying it *)
type ('a, 'b, 'c, 'd) pass_fun =
  ('a, 'b) func_ir -> pass_config -> ('c, 'd) func_ir * pass_out

type ('a, 'b, 'c, 'd) pass = 
  { pass_id : pass_id;
    pass_fun : ('a, 'b, 'c, 'd) pass_fun;
  }

(* upass stands for "unit"; the type of the func_ir *)
type upass = (unit, unit, unit, unit) pass
                                      

let init_pass : pass_id -> ('a, 'b, 'c, 'd) pass_fun -> ('a, 'b, 'c, 'd) pass =
  fun pass_id pass_fun ->
    { pass_id = pass_id;
      pass_fun = pass_fun
    }

(* Applying one pass yields a summary of what happened *)
type ('a, 'b, 'c, 'd) pass_summary =
  { source_func_ir : ('a, 'b) func_ir;
    pass_out : pass_out;
    target_func_ir : ('c, 'd) func_ir;
  }

type upass_summary = (unit, unit, unit, unit) pass_summary

let init_pass_summary
  : ('a, 'b) func_ir
  -> pass_out
  -> ('c, 'd) func_ir
  -> ('a, 'b, 'c, 'd) pass_summary =
  fun func_ir0 pass_out func_ir1 ->
    { source_func_ir = func_ir0;
      pass_out = pass_out;
      target_func_ir = func_ir1
    }

