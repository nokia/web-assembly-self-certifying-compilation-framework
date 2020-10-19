(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


open Wasm
open Ast
open Types
open Memory
open Values
open Source
open Debug

module String = String_utils
module List = List_utils

(* Useful module and typing declarations *)

module WasmValue = struct
  type t = Values.value
  let compare : t -> t -> int = Stdlib.compare
end

module WasmValueMap = Map.Make(WasmValue)

module Int32Map = Map.Make(Int32)
module Int32Set = Set.Make(Int32)

(* Wasm regions *)
let noregion: 'a -> 'a Source.phrase =
  fun a -> Source.(@@) a Source.no_region

(* Conversion functions *)
let bool_to_literal : bool -> literal =
  fun b ->
    noregion (if b then (I32 1l) else (I32 0l))

let int32_to_literal : int32 -> literal =
  fun n -> noregion (I32 n)

let int32_to_var : int32 -> var =
  fun n -> noregion n

let int_to_var : int -> var =
  fun n -> noregion (Int32.of_int n)

let int_to_literal : int -> literal =
  fun n -> noregion (I32 (Int32.of_int n))

let zero_var : var = noregion 0l

(* Function type lookup *)
let empty_func_type : Ast.type_ = noregion (Types.FuncType ([], []))

type type_map_type = Ast.var -> Types.func_type

let lookup_func_type : Ast.type_ list -> Ast.var -> Types.func_type =
  fun types_table x ->
    let func_type = List.nth_int32 x.it types_table empty_func_type in
    func_type.it

(* Check that the instructions contain only i32 *)
let is_value_type_i32 : value_type -> bool = function
  | I32Type -> true
  | _ -> false

let is_literal_i32 : literal -> bool =
  fun lit ->
    match lit.it with
    | I32 _ -> true
    | _ -> false

let is_op_i32 : ('a, 'b, 'c, 'd) op -> bool = function
  | I32 _ -> true
  | _ -> false

let rec is_instr_i32 : instr -> bool =
  fun instr ->
    match instr.it with
    | Block (_, instrs) -> List.all is_instr_i32 instrs
    | Loop (_, instrs) -> List.all is_instr_i32 instrs
    | If (_, true_instrs, false_instrs) ->
      List.all is_instr_i32 (true_instrs @ false_instrs)
    | Const lit -> is_literal_i32 lit
    | Test op -> is_op_i32 op
    | Compare op -> is_op_i32 op
    | Unary op -> is_op_i32 op
    | Binary op -> is_op_i32 op
    | _ -> true

let is_func_i32 : func -> bool =
  fun func ->
    (List.all is_value_type_i32 func.it.locals)
      && (List.all is_instr_i32 func.it.body)

(* *************************** *)

(* Flatten instructions in order to count them *)
let rec unroll_instrs : instr list -> instr list -> instr list =
  fun instrs acc0 ->
    match instrs with
    | [] -> acc0
    | instr :: instrs_tl ->
      match instr.it with
      | Block (_, block_instrs) ->
        let acc1 = unroll_instrs block_instrs acc0 in
        (unroll_instrs[@tailcall]) instrs_tl acc1

      | Loop (_, loop_instrs) ->
        let acc1 = unroll_instrs loop_instrs acc0 in
        (unroll_instrs[@tailcall]) instrs_tl acc1

      | If (_, true_instrs, false_instrs) ->
        let acc1 = unroll_instrs true_instrs acc0 in
        let acc2 = unroll_instrs false_instrs acc1 in
        (unroll_instrs[@tailcall]) instrs_tl acc2

      | _ -> (unroll_instrs[@tailcall]) instrs_tl (instr :: acc0)


(* Figure out whether there exists an instruction that matches a predicate *)
let rec exists_instr : (instr -> bool) -> instr list -> bool =
  fun pred instrs ->
  match instrs with
  | [] -> false
  | (instr :: instrs_tl) ->
    match instr.it with
    | Block (_, block_instrs) ->
      pred instr
      || exists_instr pred block_instrs
      || exists_instr pred instrs_tl 
    | Loop (_, loop_instrs) ->
      pred instr
      || exists_instr pred loop_instrs
      || exists_instr pred instrs_tl
    | If (_, true_instrs, false_instrs) ->
      pred instr
      || exists_instr pred true_instrs
      || exists_instr pred false_instrs
      || exists_instr pred instrs_tl
    | _ -> pred instr || exists_instr pred instrs_tl

let is_instr_return : instr -> bool =
  fun instr ->
    match instr.it with
    | Return -> true
    | _ -> false

let is_bad_const : instr -> bool =
  fun instr ->
    match instr.it with
    | Const lit ->
      (match lit.it with
      | I32 x -> (x = Int32.max_int) || (x = Int32.min_int)
      | _ -> true)
    | _ -> false

(* Instructions that are supported with respsect to i32 encodings *)
let is_instr_unsupported : instr -> bool =
  fun instr ->
    match instr.it with
    | BrTable _ | CallIndirect _ -> true
    | _ -> false

let is_bad_binop : binop -> bool =
  fun binop ->
    match binop with
    | I32 op -> op = IntOp.Rotl || op = IntOp.Rotr
    | _ -> true

(* Find which instructions can be handled under i32 encodings *)
let is_instr_bad_op : instr -> bool =
  fun instr ->
    match instr.it with
    | Unary unop -> true
    | Binary binop -> is_bad_binop binop
    | Compare relop -> type_of relop <> Types.I32Type
    | Test testop -> type_of testop <> Types.I32Type
    | Convert cvtop -> true
    | _ -> false

(* Run the overall check for i32 fully interpreted compatibility *)

let rec is_instrs_bad : instr list -> (bool * string) =
  fun instrs ->
    if (exists_instr is_instr_unsupported instrs)
      then (true, "unsupported instruction exists")
    else if (exists_instr is_bad_const instrs)
      then (true, "non-i32 constant exists")
    else if (exists_instr is_instr_bad_op instrs)
      then (true, "bad bin/un/cvt/rel/testop instruction exists")
    else (false, "")

(*  *********************** *)

(* Web Assembly related printing *)

let string_of_var : var -> string =
  fun x -> Int32.to_string x.it

let string_of_pack_size : pack_size -> string =
  fun mem ->
    match mem with
    | Pack8 -> "Pack8"
    | Pack16 -> "Pack16"
    | Pack32 -> "Pack32"

let string_of_extension : extension -> string =
  fun ext ->
    match ext with
    | SX -> "SX"
    | ZX -> "ZX"

let string_of_memop : string -> 'a memop -> ('a -> string) -> string =
  fun opname memop string_of_a ->
    let sz_str =
      match memop.sz with
      | None -> "None"
      | Some sz -> string_of_a sz in
    (opname
     ^ "_"
     ^ string_of_value_type memop.ty ^ "_"
     ^ string_of_int memop.align ^ "_"
     ^ Int32.to_string memop.offset ^ "_"
     ^ sz_str)


let string_of_loadop : loadop -> string =
  fun loadop ->
  string_of_memop
    "load"
    loadop
    (fun (mem, ext) ->
      string_of_pack_size mem ^ "_"
      ^ string_of_extension ext)
    
let string_of_storeop : storeop -> string =
  fun storeop ->
    string_of_memop "store" storeop string_of_pack_size


(* IntOp *)
let string_of_intop_unop : IntOp.unop -> string = function
  | IntOp.Clz -> "Clz"
  | IntOp.Ctz -> "Ctz"
  | IntOp.Popcnt -> "Popcnt"

let string_of_intop_binop : IntOp.binop -> string = function
  | IntOp.Add -> "Add"
  | IntOp.Sub -> "Sub"
  | IntOp.Mul -> "Mul"
  | IntOp.DivS -> "DivS"
  | IntOp.DivU -> "DivU"
  | IntOp.RemS -> "RemS"
  | IntOp.RemU -> "RemU"
  | IntOp.And -> "And"
  | IntOp.Or -> "Or"
  | IntOp.Xor -> "Xor"
  | IntOp.Shl -> "Shl"
  | IntOp.ShrS -> "ShrS"
  | IntOp.ShrU -> "SrU"
  | IntOp.Rotl -> "Rotl"
  | IntOp.Rotr -> "Rotr"

let string_of_intop_testop : IntOp.testop -> string = function
  | IntOp.Eqz -> "Eqz"

let string_of_intop_relop : IntOp.relop -> string = function
  | IntOp.Eq -> "Eq"
  | IntOp.Ne -> "Ne"
  | IntOp.LtS -> "LtS"
  | IntOp.LtU -> "LtU"
  | IntOp.GtS -> "GtS"
  | IntOp.GtU -> "GtU"
  | IntOp.LeS -> "LeS"
  | IntOp.LeU -> "LeU"
  | IntOp.GeS -> "GeS"
  | IntOp.GeU -> "GeU"

let string_of_intop_cvtop : IntOp.cvtop -> string = function
  | IntOp.ExtendSI32 -> "ExtendSI32"
  | IntOp.ExtendUI32 -> "ExtendUI32"
  | IntOp.WrapI64 -> "WrapI64"
  | IntOp.TruncSF32 -> "TruncSF32"
  | IntOp.TruncUF32 -> "TruncUF32"
  | IntOp.TruncSF64 -> "TruncSF64"
  | IntOp.TruncUF64 -> "TruncUF64"
  | IntOp.ReinterpretFloat -> "ReinterpretFloat"

(* FloatOp *)
let string_of_floatop_unop : FloatOp.unop -> string = function
  | FloatOp.Neg -> "Neg"
  | FloatOp.Abs -> "Abs"
  | FloatOp.Ceil -> "Ceil"
  | FloatOp.Floor -> "Floor"
  | FloatOp.Trunc -> "Trunc"
  | FloatOp.Nearest -> "Nearest"
  | FloatOp.Sqrt -> "Sqrt"

let string_of_floatop_binop : FloatOp.binop -> string = function
  | FloatOp.Add -> "Add"
  | FloatOp.Sub -> "Sub"
  | FloatOp.Mul -> "Mul"
  | FloatOp.Div -> "Div"
  | FloatOp.Min -> "Min"
  | FloatOp.Max -> "Max"
  | FloatOp.CopySign -> "CopySign"

(* This is an uninhabited type *)
let string_of_floatop_testop : FloatOp.testop -> string =
  fun _ -> "FloatOp.testop"

let string_of_floatop_relop : FloatOp.relop -> string = function
  | FloatOp.Eq -> "Eq"
  | FloatOp.Ne -> "Ne"
  | FloatOp.Lt -> "Lt"
  | FloatOp.Gt -> "Gt"
  | FloatOp.Le -> "Le"
  | FloatOp.Ge -> "Ge"

let string_of_floatop_cvtop : FloatOp.cvtop -> string = function
  | FloatOp.ConvertSI32 -> "ConvertSI32"
  | FloatOp.ConvertUI32 -> "ConvertUI32"
  | FloatOp.ConvertSI64 -> "ConvertSI64"
  | FloatOp.ConvertUI64 -> "ConvertUI64"
  | FloatOp.PromoteF32 -> "PromoteF32"
  | FloatOp.DemoteF64 -> "DemoteF64"
  | FloatOp.ReinterpretInt -> "ReinterpretInt"

(* Print the stuff *)
let string_of_unop : unop -> string = function
  | I32 unop -> "I32_" ^ (string_of_intop_unop unop)
  | I64 unop -> "I64_" ^ (string_of_intop_unop unop)
  | F32 unop -> "F32_" ^ (string_of_floatop_unop unop)
  | F64 unop -> "F64_" ^ (string_of_floatop_unop unop)

let string_of_binop : binop -> string = function
  | I32 op -> "I32_" ^ (string_of_intop_binop op)
  | I64 op -> "I64_" ^ (string_of_intop_binop op)
  | F32 op -> "F32_" ^ (string_of_floatop_binop op)
  | F64 op -> "F64_" ^ (string_of_floatop_binop op)

let string_of_testop : testop -> string = function
  | I32 op -> "I32_" ^ (string_of_intop_testop op)
  | I64 op -> "I64_" ^ (string_of_intop_testop op)
  | F32 op -> "F32_" ^ (string_of_floatop_testop op)
  | F64 op -> "F64_" ^ (string_of_floatop_testop op)

let string_of_relop : relop -> string = function
  | I32 op -> "I32_" ^ (string_of_intop_relop op)
  | I64 op -> "I64_" ^ (string_of_intop_relop op)
  | F32 op -> "F32_" ^ (string_of_floatop_relop op)
  | F64 op -> "F64_" ^ (string_of_floatop_relop op)

let string_of_cvtop : cvtop -> string = function
  | I32 op -> "I32_" ^ (string_of_intop_cvtop op)
  | I64 op -> "I64_" ^ (string_of_intop_cvtop op)
  | F32 op -> "F32_" ^ (string_of_floatop_cvtop op)
  | F64 op -> "F64_" ^ (string_of_floatop_cvtop op)

let string_of_literal : literal -> string =
  fun lit ->
    string_of_value lit.it

let rec string_of_instr_inline : instr -> string =
  fun instr ->
    match instr.it with
    | Unreachable -> "Unreachable"
    | Nop -> "Nop"
    | Drop -> "Drop"
    | Select -> "Select"

    | Block (stack_type, instrs) ->
      "Block ("
        ^ string_of_stack_type stack_type ^ ", "
        ^ String.string_of_list_inline instrs string_of_instr_inline ^ ")"
        
    | Loop (stack_type, instrs) ->
      "Loop ("
        ^ string_of_stack_type stack_type ^ ", "
        ^ String.string_of_list_inline instrs string_of_instr_inline ^ ")"

    | If (stack_type, true_instrs, false_instrs) ->
      "If ("
        ^ string_of_stack_type stack_type ^ ", "
        ^ String.string_of_list_inline
            true_instrs string_of_instr_inline ^ ", "
        ^ String.string_of_list_inline
            false_instrs string_of_instr_inline ^ ")"

    | Br x -> "Br " ^ string_of_var x
    | BrIf x -> "BrIf " ^ string_of_var x
    | BrTable (xs, x) ->
      "BrTable ("
        ^ String.string_of_list_inline xs string_of_var ^ ", "
        ^ string_of_var x ^ ")"

    | Return -> "Return"
    | Call f -> "Call " ^ string_of_var f
    | CallIndirect f -> "CallIndirect " ^ string_of_var f

    | LocalGet x -> "LocalGet " ^ string_of_var x
    | LocalSet x -> "LocalSet " ^ string_of_var x
    | LocalTee x -> "LocalTee " ^ string_of_var x
    | GlobalGet x -> "GlobalGet " ^ string_of_var x
    | GlobalSet x -> "GlobalSet " ^ string_of_var x

    | Load loadop -> "Load " ^ string_of_loadop loadop
    | Store storeop -> "Store " ^ string_of_storeop storeop
    | MemorySize -> "MemorySize"
    | MemoryGrow -> "MemoryGrow"

    | Const literal -> "Const " ^ string_of_literal literal

    | Test testop -> "Test " ^ string_of_testop testop
    | Compare relop -> "Compare " ^ string_of_relop relop
    | Unary unop -> "Unary " ^ string_of_unop unop
    | Binary binop -> "Binary " ^ string_of_binop binop
    | Convert cvtop -> "Convert " ^ string_of_cvtop cvtop

let string_of_instrs_inline : instr list -> string =
  fun instrs ->
    String.string_of_list_inline instrs string_of_instr_inline

(* Endlines and indents *)
let rec string_of_instr_indent : int -> instr -> string =
  fun ind instr ->
    match instr.it with
    | Block (stack_type, block_instrs) ->
      (* let stack_type_str = string_of_stack_type stack_type in *)
      let block_strs = List.map (string_of_instr_indent ind) block_instrs in
      String.unlines
        [ "Block";
          (String.unlines block_strs);
          "EndBlock" ]
             
    | Loop (stack_type, loop_instrs) ->
      let loop_strs = List.map (string_of_instr_indent ind) loop_instrs in
      String.unlines
        [ "Loop";
          (String.unlines loop_strs);
          "EndLoop" ]

    | If (stack_type, true_instrs, false_instrs) ->
      (* let stack_type_str = string_of_stack_type stack_type in *)
      let true_strs = List.map (string_of_instr_indent ind) true_instrs in
      let false_strs = List.map (string_of_instr_indent ind) false_instrs in
      String.unlines
        [ "If testop Then";
          (String.unlines true_strs);
          "Else";
          (String.unlines false_strs);
          "EndIf" ]

    | _ -> (string_of_instr_inline instr)


(* For printing functions *)
let string_of_func : func -> string =
  fun func ->
    let f = func.it in
    let ftype_str = string_of_var f.ftype in
    let local_str = string_of_value_types f.locals in
    let body_str =
      String.string_of_list_endline 1 3 f.body (string_of_instr_indent 2) in
    String.unlines
      [ "{ func with ";
        String.indent2 "ftype =";
          String.indent4 ftype_str ^ ";";
        String.indent2 "locals ="; 
          String.indent4 local_str ^ ";";
        String.indent2 "body =";
          String.indent4 body_str ^ ";";
        "}"]


(* For printing a module_ *)
let string_of_module_ : module_ -> string =
  fun mod_ ->
    let m = mod_.it in
    let types_str = "TODO" in
    let globals_str = "TODO" in
    let tables_str = "TODO" in
    let memories_str = "TODO" in
    let funcs_str =
      String.string_of_list_endline 2 3 m.funcs string_of_func in
    let start_str = String.string_of_option m.start string_of_var in
    let elems_str = "TODO" in
    let data_str = "TODO" in
    let imports_str = "TODO" in
    let exports_str = "TODO" in
    String.unlines
      [ "{ module_ with";
        String.indent2 "types_str =";
          String.indent4 types_str ^ ";\n";
        String.indent2 "globals_str =";
          String.indent4 globals_str ^ ";\n";
        String.indent2 "tables_str =" ^
          String.indent4 tables_str ^ ";\n";
        String.indent2 "memories_str =";
          String.indent4 memories_str ^ ";\n";
        String.indent2 "funcs_str =";
          String.indent4 funcs_str ^ ";\n";
        String.indent2 "start_str =";
          String.indent4 start_str ^ ";\n";
        String.indent2 "elems_str =";
          String.indent4 elems_str ^ ";\n";
        String.indent2 "data_str =";
          String.indent4 data_str ^ ";\n";
        String.indent2 "imports_str =";
          String.indent4 imports_str ^ ";\n";
        String.indent2 "exports_str =";
          String.indent4 exports_str ^ ";";
        "}"]

let string_of_definition : Script.definition -> string =
  fun def ->
    match def.it with
    | Textual md -> "Textual " ^ string_of_module_ md
    | Encoded (str1, str2) -> "Encoded (" ^ str1 ^ ", " ^ str2 ^ ")"
    | Quoted (str1, str2) -> "Quoted (" ^ str1 ^ ", " ^ str2 ^ ")"

let string_of_action : Script.action -> string =
  fun act ->
    match act.it with
    | Invoke (x_opt, name, lits) ->
      "Invoke ("
        ^ (String.string_of_option x_opt (fun s -> s.it)) ^ ", "
        ^ (string_of_name name) ^ ", "
        ^ (String.string_of_list_inline lits string_of_literal) ^ ")"
    | Get (x_opt, name) ->
      "Get ("
        ^ (String.string_of_option x_opt (fun s -> s.it)) ^ ", "
        ^ string_of_name name ^ ")"

let string_of_command : Script.command -> string =
  fun cmd ->
    match cmd.it with
    | Module (x_opt, def) ->
      "Module ("
        ^ (String.string_of_option x_opt (fun s -> s.it)) ^ ", "
        ^ string_of_definition def ^ ")"
    | Register _ -> "Command Register"
    | Action _ -> "Command Action"
    | Assertion _ -> "Command Assertion"
    | Meta _ -> "Command Meta"


(* sets of instructions *)
module InstrOpSetIn =
  struct
    type t = instr'
    let compare = Stdlib.compare
  end

module InstrOpSet = Set.Make(InstrOpSetIn)

