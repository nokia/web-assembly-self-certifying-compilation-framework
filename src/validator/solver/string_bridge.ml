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
open Wasm_utils
open Smt_ir

open Debug

module String = String_utils

(* Initialization: find full path name to Z3 executable *)
let find_file: string -> string option =
  fun fname -> 
  let ic = Unix.open_process_in (Printf.sprintf "which %s" fname) in
  let result = try Some(input_line ic)  with _ -> None in
  close_in ic;
  result
           
let z3_executable =
  (let z3exec_opt = find_file "z3" in
   match z3exec_opt with
   | None -> failwith("Z3 not found")
   | Some(z3exec) ->
    print_debug_high ("found Z3 executable at " ^ z3exec); z3exec)

(* let z3_flags = (* "-memory:4000 -T:100 " *) "-v:2"  *)
let z3_flags = "-memory:4000 -t:2000 -v:2" 

(* Convert the proof types into SMTLIB string representation.
 * We leverage the theory of arrays for bitvectors to do this *)

(* ******************** *)
(* Some utility declarations *)
let bv32_sort_smt : smtlib = "(_ BitVec 32)"
let bv64_sort_smt : smtlib = "(_ BitVec 64)"

let int_sort_smt  : smtlib = "Int"
let value_sort_smt  : smtlib = "Val"
let mem_sort_smt  : smtlib = "Mem"                                 

let array_sort_smt : smtlib -> smtlib -> smtlib =
  fun key wal ->
    "(Array " ^ key ^ " " ^ wal ^ ")"

let declare_const_smt : smtlib -> smtlib -> smtlib =
  fun const sort ->
    "(declare-const " ^ const ^ " " ^ sort ^ ")"

let declare_function_smt : smtlib -> smtlib list -> smtlib -> smtlib =
  fun func params ret ->
    "(declare-fun "
      ^ func ^ " "
      ^ "(" ^ String.concat " " params ^ ") "
      ^ ret ^ ")"

let assert_smt : smtlib -> smtlib =
  fun smt ->
    "(assert\n" ^ (String.indent2 smt) ^ ")"

let assert_smts : smtlib list -> smtlib list =
  fun smts ->
    List.map assert_smt smts

let comment_smt : string -> smtlib =
  fun str ->
    "; " ^ str

let neg_smt : smtlib -> smtlib =
  fun smt ->
    "(not " ^ smt ^ ")"

let int32_to_bv32_smt : int32 -> smtlib =
  fun n ->
    if n < 0l then
      "(bvneg (_ bv" ^ Int32.to_string (Int32.neg n) ^ " 32))"
    else
      "(_ bv" ^ Int32.to_string n ^ " 32)"

let int64_to_bv64_smt : int64 -> smtlib =
  fun n ->
    if n < 0L then
      "(bvneg (_ bv" ^ Int64.to_string (Int64.neg n) ^ " 64))"
    else
      "(_ bv" ^ Int64.to_string n ^ " 64)"

let bv32_zero_smt : smtlib = int32_to_bv32_smt 0l
let bv32_one_smt: smtlib = int32_to_bv32_smt 1l
let bv64_zero_smt : smtlib = int64_to_bv64_smt Int64.zero
let bv64_one_smt : smtlib = int64_to_bv64_smt Int64.one

let select_array_smt : smtlib -> smtlib -> smtlib =
  fun arr ind ->
    "(select " ^ arr ^ " " ^ ind ^ ")"

let store_array_smt :  smtlib -> smtlib -> smtlib -> smtlib =
  fun arr ind va ->
    "(store " ^ arr ^ " " ^ ind ^ " " ^ va ^ ")"

let wasm_value_smt : wasm_value -> smtlib =
  fun wal ->
    match wal.it with
    (* Only handle int32 and int64 for now *)
    | I32 i -> int32_to_bv32_smt i
    | I64 i -> int64_to_bv64_smt i
    (* Doing this should cause smt solvers to raise an error.
     * Although we can probably just output the float's string form *)
    | F32 f -> F32.to_string f
    | F64 f -> F64.to_string f

(* When doing relational comparisons we need to implement things as returning a
 * bv32 one or bv32 zero instead of true and false *)
let bool_to_bv32_smt : smtlib -> smtlib =
  fun b ->
    "(ite " ^ b ^ " " ^ bv32_one_smt ^ " " ^ bv32_zero_smt ^ ")"
    
let bv32_to_bool_smt : smtlib -> smtlib =
  fun x ->
    "(not (= " ^ x ^ " " ^ bv32_zero_smt ^ "))"

(* Result is a boolean *)
let eq_bv32_smt : smtlib -> smtlib -> smtlib =
  fun x y ->
    "(= " ^ x ^ " " ^ y ^ ")"
    (* bv32_to_bool_smt (int32op_relop_smt (Ast.IntOp.Eq) x y) *)

let eq_bv32_zero_smt : smtlib -> smtlib =
  fun x ->
    eq_bv32_smt x bv32_zero_smt

let zero_bv32_array_smt : smtlib -> smtlib =
  fun arr ->
    "(forall ((ind (_ BitVec 32))) "
      ^ (eq_bv32_zero_smt (select_array_smt arr "ind"))
      ^ ")"

(* For all *)
let forall_smt : smtlib -> smtlib -> smtlib -> smtlib =
  fun x sort body ->
    "(forall ((" ^ x ^ " " ^ sort ^ ")) " ^ body ^ ")"

let implies_smt : smtlib -> smtlib -> smtlib =
  fun ante conseq ->
    "(=> " ^ ante ^ " " ^ conseq ^ ")"

(* ******************** *)
(* testop *)

(* Since we only implement bv32 for now; return type conforms with WASM *)
let intop_testop_smt : smtlib -> IntOp.testop -> smtlib -> smtlib =
  fun zero testop wal ->
    match testop with
    | IntOp.Eqz -> bool_to_bv32_smt ("(= " ^ zero ^ " " ^ wal ^ ")")

let int32op_testop_smt : IntOp.testop -> smtlib -> smtlib =
  fun testop wal ->
    intop_testop_smt bv32_zero_smt testop wal

let int64op_testop_smt : IntOp.testop -> smtlib -> smtlib =
  fun testop wal ->
    intop_testop_smt bv64_zero_smt testop wal

let floatop_testop_smt : FloatOp.testop -> smtlib -> smtlib =
  fun _ wal -> "(floatop_testop_smt " ^ wal ^ ")"

let float32op_testop_smt : FloatOp.testop -> smtlib -> smtlib =
  floatop_testop_smt

let float64op_testop_smt : FloatOp.testop -> smtlib -> smtlib =
  floatop_testop_smt

let testop_smt : testop -> smtlib -> smtlib =
  fun testop wal ->
    match testop with
    | I32 op -> int32op_testop_smt op wal
    | I64 op -> int64op_testop_smt op wal
    | F32 op -> float32op_testop_smt op wal
    | F64 op -> float64op_testop_smt op wal

(* ******************** *)
(* relop *)

(* Since we only implement bv32 for now; return type conforms with WASM *)
let intop_relop_smt
  : smtlib -> smtlib -> IntOp.relop -> smtlib -> smtlib -> smtlib =
  fun zero one relop wal0 wal1 ->
  match relop with 
  (* We need to return bit vectors for boolean comparisons things
   * when doing equality and inequality comparisons *)
  | IntOp.Eq -> bool_to_bv32_smt ("(= " ^ wal0 ^ " " ^ wal1 ^ ")")
  | IntOp.Ne -> bool_to_bv32_smt ("(not (=" ^ wal0 ^ " " ^ wal1 ^ "))")
  | IntOp.LtS -> bool_to_bv32_smt ("(bvslt " ^ wal0 ^ " " ^ wal1 ^ ")")
  | IntOp.LtU -> bool_to_bv32_smt ("(bvult " ^ wal0 ^ " " ^ wal1 ^ ")")
  | IntOp.GtS -> bool_to_bv32_smt ("(bvsgt " ^ wal0 ^ " " ^ wal1 ^ ")")
  | IntOp.GtU -> bool_to_bv32_smt ("(bvugt " ^ wal0 ^ " " ^ wal1 ^ ")")
  | IntOp.LeS -> bool_to_bv32_smt ("(bvsle " ^ wal0 ^ " " ^ wal1 ^ ")")
  | IntOp.LeU -> bool_to_bv32_smt ("(bvule " ^ wal0 ^ " " ^ wal1 ^ ")")
  | IntOp.GeS -> bool_to_bv32_smt ("(bvsge " ^ wal0 ^ " " ^ wal1 ^ ")")
  | IntOp.GeU -> bool_to_bv32_smt ("(bvuge " ^ wal0 ^ " " ^ wal1 ^ ")")

let int32op_relop_smt : IntOp.relop -> smtlib -> smtlib -> smtlib =
  fun relop wal0 wal1 ->
    intop_relop_smt bv32_zero_smt bv32_one_smt relop wal0 wal1

let int64op_relop_smt : IntOp.relop -> smtlib -> smtlib -> smtlib =
  fun relop wal0 wal1 ->
    intop_relop_smt bv64_zero_smt bv64_one_smt relop wal0 wal1

(* Since we only implement bv32 for now; return type conforms with WASM *)
let floatop_relop_smt : FloatOp.relop -> smtlib -> smtlib -> smtlib =
  fun relop wal0 wal1 ->
    match relop with
    | FloatOp.Eq -> bool_to_bv32_smt ("(= " ^ wal0 ^ " " ^ wal1 ^ ")")
    | FloatOp.Ne -> bool_to_bv32_smt ("(not (= " ^ wal0 ^ " " ^ wal1 ^ "))")
    | FloatOp.Lt -> bool_to_bv32_smt ("(< " ^ wal0 ^ " " ^ wal1 ^ ")")
    | FloatOp.Gt -> bool_to_bv32_smt ("(> " ^ wal0 ^ " " ^ wal1 ^ ")")
    | FloatOp.Le -> bool_to_bv32_smt ("(<= " ^ wal0 ^ " " ^ wal1 ^ ")")
    | FloatOp.Ge -> bool_to_bv32_smt ("(>= " ^ wal0 ^ " " ^ wal1 ^ ")")

let float32op_relop_smt : FloatOp.relop -> smtlib -> smtlib -> smtlib =
  floatop_relop_smt

let float64op_relop_smt : FloatOp.relop -> smtlib -> smtlib -> smtlib =
  floatop_relop_smt

let relop_smt : relop -> smtlib -> smtlib -> smtlib =
  fun relop wal0 wal1 ->
  match relop with
  | IntEq -> ("(= " ^ wal0 ^ " " ^ wal1 ^ ")")
  | IntNeq -> ("(not (= " ^ wal0 ^ " " ^ wal1 ^ "))")
  | IntLeq -> ("(<= " ^ wal0 ^ " " ^ wal1 ^ ")")
  | AstRelOp rop ->
    match rop with
    | I32 op -> int32op_relop_smt op wal0 wal1
    | I64 op -> int64op_relop_smt op wal0 wal1
    | F32 op -> float32op_relop_smt op wal0 wal1
    | F64 op -> float64op_relop_smt op wal0 wal1

(* ******************** *)
(* UnaryOp *)
let intop_unop_smt : IntOp.unop -> smtlib -> smtlib =
  fun unop wal ->
    match unop with
    | IntOp.Clz -> "(Clz " ^ wal ^ ")"
    | IntOp.Ctz -> "(Ctz " ^ wal ^ ")"
    | IntOp.Popcnt -> "(Popcnt " ^ wal ^ ")"

let int32op_unop_smt : IntOp.unop -> smtlib -> smtlib =
  intop_unop_smt

let int64op_unop_smt : IntOp.unop -> smtlib -> smtlib =
  intop_unop_smt

let floatop_unop_smt : FloatOp.unop -> smtlib -> smtlib =
  fun unop wal ->
    match unop with
    | FloatOp.Neg -> "(bvneg " ^ wal ^ ")"
    | FloatOp.Abs -> 
      let cond = "(> " ^ wal ^ " 0" in
      let t = "wal" in
      let f = "(* " ^ wal ^ " (- 1))" in
      "(ite " ^ cond ^ " " ^ t ^ " " ^ f ^ ")"
    | FloatOp.Ceil -> "(Ceil " ^ wal ^ ")"
    | FloatOp.Floor -> "(Floor " ^ wal ^ ")"
    | FloatOp.Trunc -> "(Trunc " ^ wal ^ ")"
    | FloatOp.Nearest -> "(Nearest " ^ wal ^ ")"
    | FloatOp.Sqrt -> "(Sqrt " ^ wal ^ " 0.5)"

let float32op_unop_smt : FloatOp.unop -> smtlib -> smtlib =
  floatop_unop_smt

let float64op_unop_smt : FloatOp.unop -> smtlib -> smtlib =
  floatop_unop_smt

let unop_smt : unop -> smtlib -> smtlib =
  fun unop wal ->
    match unop with
    | I32 op -> int32op_unop_smt op wal
    | I64 op -> int64op_unop_smt op wal
    | F32 op -> float32op_unop_smt op wal
    | F64 op -> float64op_unop_smt op wal

(* ******************** *)
(* BinaryOp *)

(* Since we only implement bv32 for now; return type conforms with WASM *)
let intop_binop_smt : IntOp.binop -> smtlib -> smtlib -> smtlib =
  fun binop wal0 wal1 ->
    match binop with
    | IntOp.Add -> "(bvadd " ^ wal0 ^ " " ^ wal1 ^ ")"
    | IntOp.Sub -> "(bvsub " ^ wal0 ^ " " ^ wal1 ^ ")"
    | IntOp.Mul -> "(bvmul " ^ wal0 ^ " " ^ wal1 ^ ")"
    | IntOp.DivS -> "(bvsdiv " ^ wal0 ^ " " ^ wal1 ^ ")"
    | IntOp.DivU -> "(bvudiv " ^ wal0 ^ " " ^ wal1 ^ ")"
    | IntOp.RemS -> "(bvsrem " ^ wal0 ^ " " ^ wal1 ^ ")"
    | IntOp.RemU -> "(bvurem " ^ wal0 ^ " " ^ wal1 ^ ")"
    | IntOp.And -> "(bvand " ^ wal0 ^ " " ^ wal1 ^ ")"
    | IntOp.Or -> "(bvor " ^ wal0 ^ " " ^ wal1 ^ ")"
    | IntOp.Xor -> "(bvxor " ^ " " ^ wal0 ^ " " ^ wal1 ^ ")"
    | IntOp.Shl -> "(bvshl " ^ wal0 ^ " " ^ wal1 ^ ")"
    | IntOp.ShrS -> "(bvashr " ^ wal0 ^ " " ^ wal1 ^ ")"
    | IntOp.ShrU -> "(bvlshr " ^ wal0 ^ " " ^ wal1 ^ ")"
    | IntOp.Rotl ->  "(bvrotl " ^ wal0 ^ " " ^ wal1 ^ ")"
    | IntOp.Rotr ->  "(bvrotr " ^ wal0 ^ " " ^ wal1 ^ ")"

let int32op_binop_smt : IntOp.binop -> smtlib -> smtlib -> smtlib =
  intop_binop_smt

let int64op_binop_smt : IntOp.binop -> smtlib -> smtlib -> smtlib =
  intop_binop_smt

let floatop_binop_smt : FloatOp.binop -> smtlib -> smtlib -> smtlib =
  fun binop wal0 wal1 ->
    match binop with
    | FloatOp.Add -> "(+ " ^ wal0 ^ " " ^ wal1 ^ ")"
    | FloatOp.Sub -> "(- "  ^ wal0 ^ " " ^ wal1 ^ ")"
    | FloatOp.Mul -> "(* " ^ wal0 ^ " " ^ wal1 ^ ")"
    | FloatOp.Div -> "(/" ^ wal0 ^ " " ^ wal1 ^ ")"
    | FloatOp.Min ->
      let cond = "(< " ^ wal0 ^ " " ^ wal1 ^ ")" in
      "(ite " ^ cond ^ " " ^ wal0 ^ " " ^ wal1 ^ ")"
    | FloatOp.Max ->
      let cond = "(> " ^ wal0 ^ " " ^ wal1 ^ ")" in
      "(ite " ^ cond ^ " " ^ wal0 ^ " " ^ wal1 ^ ")"
    | FloatOp.CopySign ->
      let absw0 = "(ite (> " ^ wal0 ^ " 0) " ^ wal0 ^ " (* " ^ wal0 ^ " (- 1)))" in
      let sign = "(ite (> " ^ wal1 ^ " 0) 1 (- 1))" in
      "(* " ^ absw0 ^ " " ^ sign ^ ")"

let float32op_binop_smt : FloatOp.binop -> smtlib -> smtlib -> smtlib =
  floatop_binop_smt

let float64op_binop_smt : FloatOp.binop -> smtlib -> smtlib -> smtlib =
  floatop_binop_smt

let binop_smt : binop -> smtlib -> smtlib -> smtlib =
  fun binop wal0 wal1 ->
    match binop with
    | I32 op -> int32op_binop_smt op wal0 wal1
    | I64 op -> int64op_binop_smt op wal0 wal1
    | F32 op -> float32op_binop_smt op wal0 wal1
    | F64 op -> float64op_binop_smt op wal0 wal1

(* ******************** *)
(* cvtop *)
let intop_cvtop_smt : IntOp.cvtop -> smtlib -> smtlib =
  fun cvtop wal ->
    match cvtop with
    | IntOp.ExtendSI32 -> "(ExtendSI32 " ^ wal ^ ")"
    | IntOp.ExtendUI32 -> "(ExtendUI32 " ^ wal ^ ")"
    | IntOp.WrapI64 -> "(WrapI64 " ^ wal ^ ")"
    | IntOp.TruncSF32 -> "(TruncSF32 " ^ wal ^ ")"
    | IntOp.TruncUF32 -> "(TruncUF32 " ^ wal ^ ")"
    | IntOp.TruncSF64 -> "(TruncSF64 " ^ wal ^ ")"
    | IntOp.TruncUF64 -> "(TruncUF64 " ^ wal ^ ")"
    | IntOp.ReinterpretFloat -> "(ReinterpretFloat " ^ wal ^ ")"

let floatop_cvtop_smt : FloatOp.cvtop -> smtlib -> smtlib =
  fun cvtop wal ->
    match cvtop with
    | FloatOp.ConvertSI32 -> "(ConvertSI32 " ^ wal ^ ")"
    | FloatOp.ConvertUI32 -> "ConvertUI32 " ^ wal ^ ")"
    | FloatOp.ConvertSI64 -> "(ConvertSI64 " ^ wal ^ ")"
    | FloatOp.ConvertUI64 -> "(ConvertUI64 " ^ wal ^ ")"
    | FloatOp.PromoteF32 -> "(PromoteF32 " ^ wal ^ ")"
    | FloatOp.DemoteF64 -> "(DemoteF64 " ^ wal ^ ")"
    | FloatOp.ReinterpretInt -> "(ReinterpretInt " ^ wal ^ ")"

let cvtop_smt : cvtop -> smtlib -> smtlib =
  fun cvtop wal ->
    match cvtop with
    | I32 op -> intop_cvtop_smt op wal
    | I64 op -> intop_cvtop_smt op wal
    | F32 op -> floatop_cvtop_smt op wal
    | F64 op -> floatop_cvtop_smt op wal

let ufval_smt: smtid -> smtlib list -> smtlib =
  fun funid args ->
  match args with
  | [] -> funid
  | _ -> 
     "(" ^ funid ^ " " ^
       (List.fold_left (fun r a -> r^" "^a) "" args) ^ ")"


    
(* ******************** *)
(* We treat pointers as int32's, a convention that appears to be
 * supported by the reference implementation *)
let rec pointer_smt : interpretation -> pointer -> smtlib =
  fun interp ptr ->
  match ptr with
  | IntPtr i ->
    if interp = IFull then
      int32_to_bv32_smt (Int32.of_int i)
    else
      Printf.sprintf "%d" i
  | Int32Ptr i -> int32_to_bv32_smt i
  | IdPtr pid -> pid
  | VarPtr x ->
    if interp = IFull then
      int32_to_bv32_smt x.it
    else
      Printf.sprintf "%d" (Int32.to_int x.it)
  | IntOffsetPtr (ptr, x) ->
     if (x >= 0) then 
       "(+ " ^ pointer_smt interp ptr ^ " " ^ (Printf.sprintf "%d)" x)
     else
       "(- " ^ pointer_smt interp ptr ^ " " ^ (Printf.sprintf "%d)" (-x))       
  | OffsetPtr (ptr, x) ->
    if x >= 0l then
      "(bvadd " ^ pointer_smt interp ptr ^ " " ^ int32_to_bv32_smt x ^ ")"
    else
      "(bvsub "
        ^ pointer_smt interp ptr ^ " "
        ^ int32_to_bv32_smt (Int32.mul x Int32.minus_one) ^ ")"
  | CastedPtr wal -> value_smt interp wal
  | NullPtr -> bv32_zero_smt

(* Since we only implement bv32 for now; return type conforms with WASM.
 * The return type of value_smt ought to be a bv32, while the return type
 * of formula is a boolean value. *)
and value_smt : interpretation -> value -> smtlib =
  fun interp walue ->
  match walue with
  | IntVal i ->
    if interp = IFull then
      int32_to_bv32_smt (Int32.of_int i)
    else
      Printf.sprintf "%d" i
  | Int32Val i ->
    int32_to_bv32_smt i
  | WasmVal wal ->
    wasm_value_smt wal
  | TestOpVal (testop, wal) ->
    testop_smt testop (value_smt interp wal)
  | RelOpVal (wal0, relop, wal1) ->
    relop_smt (AstRelOp relop) (value_smt interp wal0) (value_smt interp wal1)
  | UnOpVal (unop, wal) ->
    unop_smt unop (value_smt interp wal)
  | BinOpVal (wal0, binop, wal1) ->
    binop_smt binop (value_smt interp wal0) (value_smt interp wal1)
  | CvtOpVal (cvtop, wal) ->
    cvtop_smt cvtop (value_smt interp wal)
  | SelectVal (aid, ptr) ->
     select_array_smt (array_smt interp aid) (pointer_smt interp ptr)
  | UFVal (funid, args) ->
     let args_smt = List.map (value_smt interp) args in
     ufval_smt funid args_smt
  | ArrayVal aid ->
     array_smt interp aid
             
and array_smt : interpretation -> array_ -> smtlib =
  fun interp array_ ->
  match array_ with
  | IdArr aid -> aid
  | StoreArr (arr, ptr, wal) ->
    store_array_smt (array_smt interp arr) (pointer_smt interp ptr) (value_smt interp wal)

(* ******************** *)
(* The return value of this call should be a formula that represents
 * a boolean value rather than a BitVec one.
 * The rationale is that the one and zero-ness of these calls is sometimes
 * then hacked together with WASM code.
 * The rationale is that formulas are either true or false -- even though
 * constructivism is the only truth *)
let rec formula_smt : interpretation -> formula -> smtlib =
  fun interp form ->
  match form with
  | PtrsRelForm (ptr0, AstRelOp (I32 Ast.IntOp.Eq), ptr1) ->
    eq_bv32_smt (pointer_smt interp ptr0) (pointer_smt interp ptr1)

  | PtrsRelForm (ptr0, relop, ptr1) ->
     let s = relop_smt relop (pointer_smt interp ptr0) (pointer_smt interp ptr1) in 
     (match relop with | AstRelOp _ -> bv32_to_bool_smt s | _ -> s)

  | ValsRelForm (wal0, AstRelOp (I32 Ast.IntOp.Eq), wal1) ->
    eq_bv32_smt (value_smt interp wal0) (value_smt interp wal1)

  | ValsRelForm (wal0, relop, wal1) ->
     let s = relop_smt relop (value_smt interp wal0) (value_smt interp wal1) in
     (match relop with | AstRelOp _ -> bv32_to_bool_smt s | _ -> s)

  | ArrsEqForm (arr0, arr1) ->
    "(= " ^ array_smt interp arr0 ^ " " ^ array_smt interp arr1 ^ ")"

  | ArrZeroAfterForm (arr, ptr, val0) ->
    let arr_smt = array_smt interp arr in
    let ptr_smt = pointer_smt interp ptr in
    let ptr2_smt = "ptr2" in
    let sort2_smt = if interp = IFull then bv32_sort_smt else "Int" in
    let body =
      if interp = IFull then (* FIXME: assumes val0 is 0 *)
        implies_smt
          ("(bvslt " ^ ptr_smt ^ " " ^ ptr2_smt ^ ")")
          (eq_bv32_zero_smt (select_array_smt arr_smt ptr2_smt))
      else
        implies_smt
          ("(< " ^ ptr_smt ^ " " ^ ptr2_smt ^ ")")
          ("(= " ^ (select_array_smt arr_smt ptr2_smt) ^ (value_smt interp val0) ^ ")") in
    forall_smt ptr2_smt sort2_smt body

  | UFBoolForm (funid, args) -> 
     let args_smt = List.map (value_smt interp) args in
     ufval_smt funid args_smt

  | SymEqForm (v0, v1) ->
     let v0_smt = value_smt interp v0 and
         v1_smt = value_smt interp v1 in
     "(= " ^ v0_smt ^ " " ^ v1_smt ^ ")"

  | BoolForm b -> if b then "true" else "false"
  | AndForm [] -> "true"
  | AndForm (form :: []) -> formula_smt interp form
  | AndForm forms ->
    "(and\n"
      ^ String.indent2 (String.unlines (List.map (formula_smt interp) forms)) ^ ")"
  | OrForm [] -> "false"
  | OrForm (form :: []) -> formula_smt interp form
  | OrForm forms ->
    "(or\n"
      ^ String.indent2 (String.unlines (List.map (formula_smt interp) forms)) ^ ")"
  | ImplForm (form0, form1) ->
    "(implies\n"
      ^ (String.indent2 (formula_smt interp form0)) ^ "\n"
      ^ (String.indent2 (formula_smt interp form1)) ^ ")"
  | NotForm form ->
    "(not\n" ^ (String.indent2 (formula_smt interp form)) ^ ")"
  | CommentForm (msg, form) -> "; " ^ msg ^ "\n" ^ (formula_smt interp form)

(* ******************** *)

let assert_formula_smt : interpretation -> formula -> smtlib =
  fun interp form ->
    assert_smt (formula_smt interp form)

let assert_formulas_smts : interpretation -> formula list -> smtlib list =
  fun interp forms ->
    List.map (assert_formula_smt interp) forms

(* The variable declarations needed for a state *)
let declare_state_smt : state -> smtlib =
  fun state ->
    String.unlines
      [ declare_const_smt
          (values_smtid state)
          (array_sort_smt bv32_sort_smt bv32_sort_smt);

        declare_const_smt
          (stack_pointer_smtid state)
          bv32_sort_smt;

        declare_const_smt
          (locals_smtid state)
          (array_sort_smt bv32_sort_smt bv32_sort_smt);

        declare_const_smt
          (globals_smtid state)
          (array_sort_smt bv32_sort_smt bv32_sort_smt);

        declare_const_smt
          (memory_smtid state)
          (array_sort_smt bv32_sort_smt bv32_sort_smt); ]

let uf_declare_state_smt : state -> smtlib =
  fun state ->
    String.unlines
      [ declare_const_smt
          (values_smtid state)
          (array_sort_smt int_sort_smt value_sort_smt);

        declare_const_smt
          (stack_pointer_smtid state)
          int_sort_smt;

        declare_const_smt
          (locals_smtid state)
          (array_sort_smt int_sort_smt value_sort_smt);

        declare_const_smt
          (globals_smtid state)
          (array_sort_smt int_sort_smt value_sort_smt);

        declare_const_smt
          (memory_smtid state)
          mem_sort_smt;]

      
(* Assert that all the contents of an array (bv32 to bv32) is zero *)

(* Result is a boolean *)
let eq_bv32_smt : smtlib -> smtlib -> smtlib =
  fun x y ->
    bv32_to_bool_smt (int32op_relop_smt (Ast.IntOp.Eq) x y)

let eq_bv32_zero_smt : smtlib -> smtlib =
  fun x ->
    eq_bv32_smt x bv32_zero_smt

let zero_bv32_array_smt : smtlib -> smtlib =
  fun arr  ->
    "(forall ((ind (_ BitVec 32))) "
      ^ (eq_bv32_zero_smt (select_array_smt arr "ind"))
      ^ ")"

let even_bv32_smt : smtlib -> smtlib =
  fun x ->
    eq_bv32_zero_smt (intop_binop_smt Ast.IntOp.DivS x (int32_to_bv32_smt 2l))

(* ******************** *)
let smt_decl_to_smtlib : smt_decl -> smtlib = function
  | StateDecl state -> declare_state_smt state
  | SmtDecls ds -> String.unlines ds

let smt_stmt_to_smtlib : interpretation -> smt_stmt -> smtlib =
  fun interp stmt ->
    match stmt with
    | AssertStmt form -> assert_smt (formula_smt interp form)

let smt_meta_to_smtlib : smt_meta -> smtlib = function
  | CheckSatMeta -> "(check-sat)"

let uf_smt_decl_to_smtlib : smt_decl -> smtlib = function
  | StateDecl state -> uf_declare_state_smt state
  | SmtDecls ds -> String.unlines ds
                      
let smt_query_to_smtlib : interpretation -> smt_query -> smtlib =
  fun interp query ->
  let decl_smts =
    (match interp with
     | IFull -> List.map smt_decl_to_smtlib query.smt_decls
     | INone -> List.map uf_smt_decl_to_smtlib query.smt_decls
    ) in 
    let header_smts = List.map (smt_stmt_to_smtlib interp) query.smt_headers in
    let stmt_smts = List.map (smt_stmt_to_smtlib interp) query.smt_stmts in
    let footer_smts = List.map smt_meta_to_smtlib query.smt_footers in
    String.unlines (decl_smts @ header_smts @ stmt_smts @ footer_smts)

(* ******************** *)

let print_info : smtlib -> solver_config -> unit =
  fun query_smt solv_conf ->
    let _ = flush stdout in
    let _ = flush stderr in
    let _ = print_debug_high "-------------------------" in
    let _ = List.iter print_debug_high solv_conf.debugs in
    let _ = print_debug_high "query_smtlib_hack: dumping" in
    let _ = print_debug_high "----------" in

    (* The massive query we dump to STDERR *)
    let _ = Debug.print_debug_high ("\n\n" ^ query_smt ^ "\n\n") in 
    let _ = Debug.print_debug_high  "----------" in
    let _ = Debug.print_debug_high  "query_smtlib_hack: done\n\n" in
    let _ = Debug.print_debug_high "-------------------------" in
    let _ = flush stdout in
    let _ = flush stderr in
    ()

(* functions lines_from and run_command are adapted from example code at 
 * http://pleac.sourceforge.net/pleac_ocaml/processmanagementetc.html *)
      
let lines_from : in_channel -> string list =
  fun inch ->
  let lines = ref [] in 
  (try
     while true do
       lines := input_line inch :: !lines
     done;
   with End_of_file -> ());
  List.rev !lines

let run_command : string -> (string list) * (string list) =
  fun cmd -> 
  let channels = Unix.open_process_full cmd (Array.make 0 "") in
  let outch,_,errch = channels in 
  let outs = lines_from outch
  and errs = lines_from errch
  in
  ignore(Unix.close_process_full channels);
  (outs,errs)

      
let query_smtlib_hack : smtlib -> solver_config -> (string * string) =
  fun query_smt solv_conf ->
  (* Dump the smtlib2 file so we can debug it easier *)
  let outfp = open_out "__query.smt2" in
  let _ = Printf.fprintf outfp "%s" query_smt in
  let _ = close_out outfp in
  let _ = print_info query_smt solv_conf in
  let z3_cmd = z3_executable ^ " " ^ z3_flags in  
  let outs,errs = run_command (z3_cmd ^ " __query.smt2") in
  (String.unlines outs, String.unlines errs)


let query_formula_hack : interpretation -> formula -> solver_config -> (string * string) =
  fun interp form solv_conf ->
    query_smtlib_hack (assert_formula_smt interp form) solv_conf

    
let query_smtlib : smtlib -> solver_config -> solver_result =
  fun smt solv_conf ->
  let output = query_smtlib_hack smt solv_conf in
  let result = parse_solver_call solv_conf output in
  result

let query_formula : interpretation -> formula -> solver_config -> solver_result =
  fun interp form solv_conf ->
    query_smtlib (assert_formula_smt interp form) solv_conf


