(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


open Wasm
open Wasm_utils
open Instr_graph
open Func_types
open State_types
open Proof_types
open Script_types
open Debug

open Z3
open Z3.Boolean
open Z3.Z3Array

open Solver_types

module String = String_utils

(* IR components *)
type smt_top =
  | SmtTop

type smt_decl =
  | StateDecl of state
  | SmtDecls of string list
                 
type smt_stmt =
  | AssertStmt of formula

type smt_meta =
  | CheckSatMeta


(* An SMT query consists of several components:
 *  - Top-level initialization (eg setting logic, unimplemented)
 *  - Declarations
 *  - "headers" that may prepend the main formula body
 *  - "statements" of the body
 *  - "footers" that may append hte main formula body, (eg check-sat)
 *)
type smt_query =
  { (* Some meta information that can be used in printing *)
    smt_meta : string list;
    smt_tops : smt_top list;
    smt_decls : smt_decl list;
    smt_headers : smt_stmt list;
    smt_stmts : smt_stmt list;
    smt_footers : smt_meta list;
  }

let default_smt_query : smt_query =
  { smt_meta = [];
    smt_tops = [];
    smt_decls = [];
    smt_headers = [];
    smt_stmts = [];
    smt_footers = [CheckSatMeta];
  }

(* Utility functions *)
let append_decls : smt_query -> smt_decl list -> smt_query =
  fun query decls ->
  { query with smt_decls = query.smt_decls @ decls }

let prepend_decls : smt_decl list -> smt_query -> smt_query =
  fun decls query ->
    { query with smt_decls = decls @ query.smt_decls }    

let append_headers : smt_query -> smt_stmt list -> smt_query =
  fun query stmts ->
    { query with smt_headers = query.smt_headers @ stmts }

let append_stmts : smt_query -> smt_stmt list -> smt_query =
  fun query stmts ->
    { query with smt_stmts = query.smt_stmts @ stmts }

let append_footers : smt_query -> smt_meta list -> smt_query =
  fun query metas ->
    { query with smt_footers = query.smt_footers @ metas }

(* Shortcut functions *)
let declare_states : state list -> smt_decl list =
  fun states -> List.map (fun s -> StateDecl s) states

let assert_formulas : formula list -> smt_stmt list =
  fun forms -> List.map (fun f -> AssertStmt f) forms


let string_of_smt_query : smt_query -> string =
  fun query ->
    ""

