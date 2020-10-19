(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


open Wasm
open Ast
open Solver_types
open State_types
open Proof_types
open Smt_ir

open Z3

(* There are several sequences we need to do per-Z3 run:
 *
 *  (1) Instantiate a fresh context via mk_context
 *
 *  (2) Declare all the variables; we need an smtid_map : smtid -> expr.
 *      This is because the formula type constructs from smtid,
 *      and this is integral to the string_bridge
 *
 *  (3) Only after declaring the variables can we use the correspondingly
 *      populated smt_id_map to fully convert formulas into Z3 exprs.
 *
 *  (4) Call the Z3 solver and return the results
 *
 *)

module SmtId = struct
  type t = smtid
  let compare : t -> t -> int = Stdlib.compare
end

module SmtIdMap = Map.Make(SmtId)

type z3_expr = Z3.Expr.expr

type expr_map = z3_expr SmtIdMap.t

type z3_context = Z3.context

type z3_sort = Z3.Sort.sort

type z3_solver = Solver.solver

let fresh_context : unit -> z3_context = fun () -> mk_context []

let fresh_solver : z3_context -> z3_solver = fun ctx -> Solver.mk_solver ctx None

let mk_bv32_sort = fun ctx -> BitVector.mk_sort ctx 32

let mk_bv32_zero = fun ctx -> Expr.mk_numeral_int ctx 0 (mk_bv32_sort ctx)

let mk_bv32_one = fun ctx -> Expr.mk_numeral_int ctx 1 (mk_bv32_sort ctx)

(* We don't declare functions just yet ... *)
let decl_const : z3_context -> smtid -> z3_sort -> expr_map -> expr_map =
  fun ctx smtid sort emap ->
    let expr = Expr.mk_const_s ctx smtid sort in
    SmtIdMap.add smtid expr emap

let decl_arr : z3_context -> smtid -> z3_sort -> z3_sort -> expr_map -> expr_map =
  fun ctx smtid sort0 sort1 emap  ->
    let expr = Z3Array.mk_const_s ctx smtid sort0 sort1 in
    SmtIdMap.add smtid expr emap

(* Converting smtid to expr *)
let smtid_to_expr : z3_context -> smtid -> expr_map -> z3_expr =
  fun ctx smtid emap ->
    match SmtIdMap.find_opt smtid emap with
    | Some e -> e
    | None ->
      (prerr_endline ("smt_id_to_expr: could not find " ^ smtid);
      mk_bv32_zero ctx)

let boolean_to_bitvector : z3_context -> z3_expr -> z3_expr =
  fun ctx boole ->
    Boolean.mk_ite ctx boole (mk_bv32_one ctx) (mk_bv32_zero ctx)

let bitvector_to_boolean : z3_context -> z3_expr -> z3_expr =
  fun ctx bve ->
    Boolean.mk_not ctx (Boolean.mk_eq ctx (mk_bv32_zero ctx) bve)

(* testop *)
let testop_to_expr : z3_context -> Ast.testop -> z3_expr -> expr_map -> z3_expr =
  fun ctx testop expr emap ->
    match testop with
    | Values.I32 op ->
      (match op with
      | IntOp.Eqz -> boolean_to_bitvector ctx (Boolean.mk_eq ctx expr (mk_bv32_zero ctx)))
    | _ ->
    (prerr_endline ("testop_to_expr: received non-int32");
      mk_bv32_zero ctx)

(* relop *)
let relop_to_expr : z3_context -> z3_expr -> Ast.relop -> z3_expr -> expr_map -> z3_expr =
  fun ctx lhs relop rhs emap ->
    match relop with
    | Values.I32 op ->
      let boole = (match op with
        | IntOp.Eq -> Boolean.mk_eq ctx lhs rhs
        | IntOp.Ne -> Boolean.mk_not ctx (Boolean.mk_eq ctx lhs rhs)
        | IntOp.LtS -> BitVector.mk_slt ctx lhs rhs
        | IntOp.LtU -> BitVector.mk_ult ctx lhs rhs
        | IntOp.GtS -> BitVector.mk_sgt ctx lhs rhs
        | IntOp.GtU -> BitVector.mk_ugt ctx lhs rhs
        | IntOp.LeS -> BitVector.mk_sle ctx lhs rhs
        | IntOp.LeU -> BitVector.mk_ule ctx lhs rhs
        | IntOp.GeS -> BitVector.mk_sge ctx lhs rhs
        | IntOp.GeU -> BitVector.mk_uge ctx lhs rhs) in
      boolean_to_bitvector ctx boole
    | _ ->
    (prerr_endline ("relop_to_expr: received non-int32");
      mk_bv32_zero ctx)

(* unop *)
let unop_to_expr : z3_context -> Ast.unop -> z3_expr -> expr_map -> z3_expr =
  fun ctx unop expr emap ->
    match unop with
    | _ -> (prerr_endline ("unop_to_expr: no valid unops available"); mk_bv32_zero ctx)


(* binop *)
let binop_to_expr : z3_context -> z3_expr -> Ast.binop -> z3_expr -> expr_map -> z3_expr =
  fun ctx lhs binop rhs emap ->
    match binop with
    | Values.I32 op ->
      (match op with
      | IntOp.Add -> BitVector.mk_add ctx lhs rhs
      | IntOp.Sub -> BitVector.mk_sub ctx lhs rhs
      | IntOp.Mul -> BitVector.mk_mul ctx lhs rhs
      | IntOp.DivS -> BitVector.mk_sdiv ctx lhs rhs
      | IntOp.DivU -> BitVector.mk_udiv ctx lhs rhs
      | IntOp.RemS -> BitVector.mk_srem ctx lhs rhs
      | IntOp.RemU -> BitVector.mk_urem ctx lhs rhs
      | IntOp.And -> BitVector.mk_and ctx lhs rhs
      | IntOp.Or -> BitVector.mk_or ctx lhs rhs
      | IntOp.Xor -> BitVector.mk_xor ctx lhs rhs
      | IntOp.Shl -> BitVector.mk_shl ctx lhs rhs
      | IntOp.ShrS -> BitVector.mk_ashr ctx lhs rhs
      | IntOp.ShrU -> BitVector.mk_lshr ctx lhs rhs
      | IntOp.Rotl -> BitVector.mk_ext_rotate_left ctx lhs rhs
      | IntOp.Rotr -> BitVector.mk_ext_rotate_right ctx lhs rhs
      )
    | _ -> (prerr_endline ("unop_to_expr: received non-int32"); mk_bv32_zero ctx)

(* cvtop *)
let cvtop_to_expr : z3_context -> Ast.cvtop -> z3_expr -> expr_map -> z3_expr =
  fun ctx cvtop expr emap ->
    match cvtop with
    | _ -> (prerr_endline ("cvtop_to_expr: no valid cvtops available"); mk_bv32_zero ctx)


let rec pointer_to_expr : z3_context -> pointer -> expr_map -> z3_expr =
  fun ctx ptr emap ->
    match ptr with
    | IntPtr n -> Expr.mk_numeral_int ctx (n) (mk_bv32_sort ctx)
    | Int32Ptr n -> Expr.mk_numeral_int ctx (Int32.to_int n) (mk_bv32_sort ctx)
    | IdPtr smtid -> smtid_to_expr ctx smtid emap
    | VarPtr x -> Expr.mk_numeral_int ctx (Int32.to_int x.it) (mk_bv32_sort ctx)
    | OffsetPtr (ptr1, n)->
        let ptr1e = pointer_to_expr ctx ptr1 emap in
        let offe = Expr.mk_numeral_int ctx (Int32.to_int n) (mk_bv32_sort ctx) in
        BitVector.mk_add ctx ptr1e offe
    | IntOffsetPtr (ptr1, n)->
        let ptr1e = pointer_to_expr ctx ptr1 emap in
        let offe = Expr.mk_numeral_int ctx (n) (mk_bv32_sort ctx) in
        BitVector.mk_add ctx ptr1e offe
    | CastedPtr wal -> value_to_expr ctx wal emap
    | NullPtr -> mk_bv32_zero ctx

and value_to_expr : z3_context -> value -> expr_map -> z3_expr =
  fun ctx wal_ emap ->
    match wal_ with
    | IntVal n -> Expr.mk_numeral_int ctx (n) (mk_bv32_sort ctx)
    | Int32Val n -> Expr.mk_numeral_int ctx (Int32.to_int n) (mk_bv32_sort ctx)
    | WasmVal wal ->
      (match wal.it with
      | I32 n -> Expr.mk_numeral_int ctx (Int32.to_int n) (mk_bv32_sort ctx)
      | _ -> (prerr_endline ("value_to_expr: non-int32")); mk_bv32_zero ctx)
    | TestOpVal (test, wal0) ->
      let wal0e = value_to_expr ctx wal0 emap in
      testop_to_expr ctx test wal0e emap
    | RelOpVal (wal0, rel, wal1) ->
      let wal0e = value_to_expr ctx wal0 emap in
      let wal1e = value_to_expr ctx wal1 emap in
      relop_to_expr ctx wal0e rel wal1e emap
    | UnOpVal (unop, wal0) ->
      let wal0e = value_to_expr ctx wal0 emap in
      unop_to_expr ctx unop wal0e emap
    | BinOpVal (wal0, binop, wal1) ->
      let wal0e = value_to_expr ctx wal0 emap in
      let wal1e = value_to_expr ctx wal1 emap in
      binop_to_expr ctx wal0e binop wal1e emap
    | CvtOpVal (cvtop, wal0) ->
      let wal0e = value_to_expr ctx wal0 emap in
      cvtop_to_expr ctx cvtop wal0e emap
    | SelectVal (arr, ptr) ->
      let arre = array_to_expr ctx arr emap in
      let ptre = pointer_to_expr ctx ptr emap in
      Z3Array.mk_select ctx arre ptre

    | UFVal _ ->
      let _ = prerr_endline ("value_to_expr: unsupported UFVal") in
      mk_bv32_zero ctx

    | ArrayVal _ ->
      let _ = prerr_endline ("value_to_expr: unsupported ArrayVal") in
      mk_bv32_zero ctx


and array_to_expr : z3_context -> array_ -> expr_map -> z3_expr =
  fun ctx arr_ emap ->
    match arr_ with
    | IdArr aid -> smtid_to_expr ctx aid emap
    | StoreArr (arr1, ptr, wal) ->
      let arr1e = array_to_expr ctx arr1 emap in
      let ptre = pointer_to_expr ctx ptr emap in
      let wale = value_to_expr ctx wal emap in
      Z3Array.mk_store ctx arr1e ptre wale


(* Formula conversion *)
let rec formula_to_expr : z3_context -> formula -> expr_map -> z3_expr =
  fun ctx form_ emap ->
    match form_ with
    | PtrsRelForm (ptr0, AstRelOp (I32 Ast.IntOp.Eq), ptr1) ->
      let ptr0e = pointer_to_expr ctx ptr0 emap in
      let ptr1e = pointer_to_expr ctx ptr1 emap in     
      Boolean.mk_eq ctx ptr0e ptr1e

    | PtrsRelForm (ptr0, AstRelOp rel, ptr1) ->
      let ptr0e = pointer_to_expr ctx ptr0 emap in
      let ptr1e = pointer_to_expr ctx ptr1 emap in
      bitvector_to_boolean ctx (relop_to_expr ctx ptr0e rel ptr1e emap)

    | PtrsRelForm (ptr0, _, ptr1) ->
      let _ = prerr_endline ("formula_to_expr: not implemented uninterpreted relop") in
      mk_bv32_zero ctx

    | ValsRelForm (wal0, AstRelOp (I32 Ast.IntOp.Eq), wal1) ->
      let wal0e = value_to_expr ctx wal0 emap in
      let wal1e = value_to_expr ctx wal1 emap in
      Boolean.mk_eq ctx wal0e wal1e

    | ValsRelForm (wal0, AstRelOp relop, wal1) ->
      let wal0e = value_to_expr ctx wal0 emap in
      let wal1e = value_to_expr ctx wal1 emap in
      bitvector_to_boolean ctx (relop_to_expr ctx wal0e relop wal1e emap)

    | ValsRelForm (wal0, _, wal1) ->
      let _ = prerr_endline ("formula_to_expr: not implemented uninterpreted relop") in
      mk_bv32_zero ctx

    | ArrsEqForm (arr0, arr1) ->
      let arr0e = array_to_expr ctx arr0 emap in
      let arr1e = array_to_expr ctx arr1 emap in
      Boolean.mk_eq ctx arr0e arr1e

    | ArrZeroAfterForm (arr0, ptr0,_) -> (* FIXME: ignores value *)
      (* mk_forall_const vs mk_forall: https://github.com/Z3Prover/z3/issues/1871 *)
      let arr = array_to_expr ctx arr0 emap in
      let ptr = pointer_to_expr ctx ptr0 emap in
      let ptr2 = Expr.mk_const_s ctx "ptr2" (mk_bv32_sort ctx) in
      let ante = BitVector.mk_slt ctx ptr ptr2 in
      let conseq = Boolean.mk_eq ctx (Z3Array.mk_select ctx arr ptr2) (mk_bv32_zero ctx) in
      let impl = Boolean.mk_implies ctx ante conseq in
      Z3.Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [ptr2] impl None [] [] None None)

    | BoolForm b ->
      Boolean.mk_val ctx b

    | AndForm ands ->
      let andes = List.map (fun f -> formula_to_expr ctx f emap) ands in
      Boolean.mk_and ctx andes

    | OrForm ors ->
      let ores = List.map (fun f -> formula_to_expr ctx f emap) ors in
      Boolean.mk_or ctx ores

    | ImplForm (form0, form1) ->
      let form0e = formula_to_expr ctx form0 emap in
      let form1e = formula_to_expr ctx form1 emap in
      Boolean.mk_implies ctx form0e form1e
    
    | NotForm form0 ->
      let form0e = formula_to_expr ctx form0 emap in
      Boolean.mk_not ctx form0e

    | CommentForm (msg, form0) ->
      formula_to_expr ctx form0 emap

    | _ -> failwith("rel has wrong type now: TO BE FIXED")


(* Functions for takig an SMT ir and doing some declarations from it *)
let decl_state : z3_context -> state -> expr_map -> expr_map =
  fun ctx state emap ->
    let vals_id = values_smtid state in
    let vals_expr = Z3Array.mk_const_s ctx vals_id (mk_bv32_sort ctx) (mk_bv32_sort ctx) in

    let ptr_id = stack_pointer_smtid state in
    let ptr_expr = Expr.mk_const_s ctx ptr_id (mk_bv32_sort ctx) in

    let loc_id = locals_smtid state in
    let loc_expr = Z3Array.mk_const_s ctx loc_id (mk_bv32_sort ctx) (mk_bv32_sort ctx) in

    let glb_id = globals_smtid state in
    let glb_expr = Z3Array.mk_const_s ctx glb_id (mk_bv32_sort ctx) (mk_bv32_sort ctx) in

    let mem_id = memory_smtid state in
    let mem_expr = Z3Array.mk_const_s ctx mem_id (mk_bv32_sort ctx) (mk_bv32_sort ctx) in
    
    let emap1 = SmtIdMap.add vals_id vals_expr emap in
    let emap2 = SmtIdMap.add ptr_id ptr_expr emap1 in
    let emap3 = SmtIdMap.add loc_id loc_expr emap2 in
    let emap4 = SmtIdMap.add glb_id glb_expr emap3 in
    let emap5 = SmtIdMap.add mem_id mem_expr emap4 in

    emap5

let z3_decl : z3_context -> smt_decl -> expr_map -> expr_map =
  fun ctx decl emap ->
    match decl with
    | StateDecl state -> decl_state ctx state emap
    | SmtDecls _ -> prerr_endline ("z3_decl: unsupported SmtDecl"); emap

let rec z3_decls : z3_context -> smt_decl list -> expr_map -> expr_map =
  fun ctx decls emap0 ->
    match decls with
    | [] -> emap0
    | (decl0 :: decls_tl) ->
      let emap1 = z3_decl ctx decl0 emap0 in
      z3_decls ctx decls_tl emap1

(* Statements *)

let z3_stmt : z3_context -> z3_solver -> smt_stmt -> expr_map -> expr_map =
  fun ctx solv stmt emap ->
    match stmt with
    | AssertStmt form ->
      let forme = formula_to_expr ctx form emap in
      let _ = Solver.add solv [forme] in
      emap

let rec z3_stmts : z3_context -> z3_solver -> smt_stmt list -> expr_map -> expr_map =
  fun ctx solv stmts emap0 ->
    match stmts with
    | [] -> emap0
    | (stmt0 :: stmts_tl) ->
      let emap1 = z3_stmt ctx solv stmt0 emap0 in
      z3_stmts ctx solv stmts_tl emap1

(* Meta *)

let check_sat : z3_solver -> Solver.status =
  fun solv ->
    (* debugging *)
    (*
    let asserts = Solver.get_assertions solv in
    let _ = prerr_endline ("assertion: " ^ string_of_int (List.length asserts)) in
    *)

    Solver.check solv []

let z3_meta : z3_context -> z3_solver -> smt_meta -> Solver.status =
  fun ctx solv meta ->
    match meta with
    | CheckSatMeta -> check_sat solv


(* Put everything together *)
let run_z3_query : smt_query -> solver_config -> solver_result =
  fun query solv_conf ->
    let emap0 = SmtIdMap.empty in
    let ctx = fresh_context () in
    let solv = fresh_solver ctx in
    
    (* Declare things *)
    let emap1 = z3_decls ctx query.smt_decls emap0 in

    (* Do all the formula assertions *)
    let emap2 = z3_stmts ctx solv query.smt_headers emap1 in
    let _ = z3_stmts ctx solv query.smt_stmts emap2 in
    
    (* hacky *)
    let status = z3_meta ctx solv (List.hd query.smt_footers) in

    let solv_status = 
      { empty_solver_result with
        solver_status =
          (if status == UNSATISFIABLE then
            Unsat
          else if status == UNKNOWN then
            Unknown
          else
            let _ = prerr_endline "SAT" in
            let asserts = Solver.get_assertions solv in
            let _ = List.iter (fun e -> prerr_endline (Expr.to_string e)) asserts in
            Sat )} in

    solv_status



