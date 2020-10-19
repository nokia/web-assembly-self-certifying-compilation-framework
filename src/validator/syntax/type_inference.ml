(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


(* Do type inference on WASM instructions.
 * The main purpose of this is to correctly generate type annotations
 * when we go form CFG to WAST files. *)

open Wasm
open Wasm_utils
open Either
open Debug

module S = Stack
open String_utils

(* Some defaults *)
let i32ty : Types.value_type = Types.I32Type

(* Let's implement a simple stack-based type simulator *)
type walue_type =
  | Int32Type
  | Int64Type
  | Float32Type
  | Float64Type
  | UnknownType

let string_of_walue_type : walue_type -> string = function
  | Int32Type -> "Int32Type"
  | Int64Type -> "Int64Type"
  | Float32Type -> "Float32Type"
  | Float64Type -> "Float64Type"
  | UnknownType -> "UnknownType"

let value_type_to_walue_type : Types.value_type -> walue_type = function
  | Types.I32Type -> Int32Type
  | Types.I64Type -> Int64Type
  | Types.F32Type -> Float32Type
  | Types.F64Type -> Float64Type

let value_types_to_walue_types : Types.value_type list -> walue_type list =
  fun vtys -> List.map value_type_to_walue_type vtys

let walue_type_to_value_type : walue_type -> Types.value_type -> Types.value_type =
  fun wal_ty def_ty ->
    match wal_ty with
    | Int32Type -> Types.I32Type
    | Int64Type -> Types.I64Type
    | Float32Type -> Types.F32Type
    | Float64Type -> Types.F64Type
    | UnknownType -> def_ty

let walue_types_to_value_types : walue_type list -> Types.value_type -> Types.value_type list =
  fun wal_tys def_ty ->
    List.map (fun wty -> walue_type_to_value_type wty def_ty) wal_tys

let lift_walue_types : (walue_type * walue_type) -> walue_type option = function
  | (Int32Type, Int32Type) -> Some Int32Type
  | (Int64Type, Int64Type) -> Some Int64Type
  | (Float32Type, Float32Type) -> Some Float32Type
  | (Float64Type, Float64Type) -> Some Float64Type
  | (UnknownType, UnknownType) -> Some UnknownType

  | (Int32Type, UnknownType) -> Some Int32Type
  | (Int64Type, UnknownType) -> Some Int64Type
  | (Float32Type, UnknownType) -> Some Float32Type
  | (Float64Type, UnknownType) -> Some Float64Type
  | (UnknownType, Int32Type) -> Some Int32Type
  | (UnknownType, Int64Type) -> Some Int64Type
  | (UnknownType, Float32Type) -> Some Float32Type
  | (UnknownType, Float64Type) -> Some Float64Type
  | _ -> None

let is_stopping_instr : Ast.instr -> bool =
  fun instr ->
    match instr.it with
    | Ast.Unreachable | Ast.Return
    | Ast.Br _ | Ast.BrTable _ -> true
    | _ -> false

(* Some lookups *)

let type_step
  : Ast.instr
  -> walue_type S.stack
  -> type_map_type
  -> Types.value_type
  -> walue_type S.stack =
  fun instr stack0 ty_map def_ty ->
    let def_wty = value_type_to_walue_type def_ty in
    match instr.it with
    | Ast.Nop -> stack0

    | Ast.Drop ->
      (match S.pop stack0 with
      | None -> (prerr_debug "type_step: guessing at Drop"; [])
      | Some (_, stack1) -> stack1)

    | Ast.Select ->
      (match S.pop3 stack0 with
      | None -> (prerr_debug "type_step: guessing at Select (a)"; [def_wty])
      | Some (w1, w2, _, stack1) ->
        (match lift_walue_types (w1, w2) with
        | None -> (prerr_debug "type_step: guessing at Select (b): "; [def_wty])
        | Some w -> S.push w stack1))

    | Ast.LocalGet _ -> (S.push def_wty stack0)

    | Ast.LocalSet _ ->
      (match S.pop stack0 with
      | None -> (prerr_debug "type_step: guessing at LocalSet"; [])
      | Some (_, stack1) -> stack1)

    | Ast.LocalTee _ -> stack0

    | Ast.GlobalGet _ -> (S.push def_wty stack0)

    | Ast.GlobalSet _ ->
      (match S.pop stack0 with
      | None -> (prerr_debug "type_step: guessing at GlobalSet"; [])
      | Some (_, stack1) -> stack1)

    | Ast.Load _ ->
      (match S.pop stack0 with
      | None -> (prerr_debug "type_step: guessing at Load"; [def_wty])
      | Some (_, stack1) -> (S.push def_wty stack1))
    
    | Ast.Store _ ->
      (match S.pop stack0 with
      | None -> (prerr_debug "type_step: guessing at Store (a)"; [])
      | Some (_, stack1) ->
        match S.pop stack1 with
        | None -> (prerr_debug "type_step: guessing at Store (b)"; [])
        | Some (_, stack2) -> stack2)

    | Ast.Const lit ->
      let wty = value_type_to_walue_type (Values.type_of lit.it) in
      S.push wty stack0
    
    | Ast.Test _ ->
      (match S.pop stack0 with
      | None -> (prerr_debug "type_step: guessing at Load"; [def_wty])
      | Some (_, stack1) -> S.push Int32Type stack1)
    
    | Ast.Compare _ ->
      (match S.pop2 stack0 with
      | None -> (prerr_debug "type_step: guessing at Compare"; [Int32Type])
      | Some (_, _, stack1) -> S.push Int32Type stack1)

    | Ast.Unary unop ->
      (match S.pop stack0 with
      | None -> (prerr_debug "type_step: guessing at Unary"; [def_wty])
      | Some (_, stack1) ->
        let wty = value_type_to_walue_type (Values.type_of unop) in
        S.push wty stack1)
    
    | Ast.Binary binop ->
      (match S.pop2 stack0 with
      | None -> (prerr_debug "type_step: guessing at Binary"; [def_wty])
      | Some (_, _, stack1) ->
        let wty = value_type_to_walue_type (Values.type_of binop) in
        S.push wty stack1)

    | Ast.Convert cvtop ->
      (match S.pop stack0 with
      | None -> (prerr_debug "type_step: guessing at Convert"; [UnknownType])
      | Some (_, stack1) ->
        let wty = value_type_to_walue_type (Values.type_of cvtop) in
        S.push wty stack1)
    
    | Ast.MemoryGrow -> stack0

    | Ast.MemorySize -> S.push Int32Type stack0
  
    (* Control flow instructions *)
    | Ast.Block (stack_ty, _) ->
      let wtys = value_types_to_walue_types stack_ty in
      (*
      S.from_list wtys
      *)
      S.prepend_list wtys stack0
    
    | Ast.Loop (stack_ty, _) ->
      let wtys = value_types_to_walue_types stack_ty in
      (*
      S.from_list wtys
      *)
      S.prepend_list wtys stack0

    | Ast.If (stack_ty, _, _) ->
      let wtys = value_types_to_walue_types stack_ty in
      (match S.pop stack0 with
      | None -> (prerr_debug "type_step: guessing at If"; wtys)
      | Some (_, stack1) -> S.prepend_list wtys stack1)
      (*
      S.from_list wtys
      *)

    | Ast.Br _ ->
      (*
      S.empty_stack
      *)
      stack0
    
    | Ast.BrIf _ ->
      (match S.pop stack0 with
      | None -> (prerr_debug "type_step: guessing at BrIf"; [])
      | Some (_, stack1) -> stack1)

    | Ast.BrTable _ ->
      (*
      S.empty_stack
      *)
      (match S.pop stack0 with
      | None -> (prerr_debug "type_step: guessing at BrTable"; [])
      | Some (_, stack1) -> stack1)

    | Ast.Call x ->
      let Types.FuncType (in_tys, out_tys) = ty_map x in
      let stack1 = S.delete_n (List.length in_tys) stack0 in
      let out_wtys = value_types_to_walue_types out_tys in
      S.prepend_list out_wtys stack1

    | Ast.CallIndirect x ->
      let Types.FuncType (in_tys, out_tys) = ty_map x in
      let stack1 = S.delete_n (List.length in_tys) stack0 in
      let out_wtys = value_types_to_walue_types out_tys in
      S.prepend_list out_wtys stack1

    | Ast.Return ->
      (match S.pop stack0 with
      | None -> (prerr_debug "type_step: guessing at BrTable"; [])
      | Some (wty0, stack1) -> S.from_list [wty0])

    | Ast.Unreachable -> S.from_list (List.repeat (S.size stack0) UnknownType)

let rec type_steps
  : Ast.instr list
  -> walue_type S.stack
  -> type_map_type
  -> Types.value_type
  -> walue_type S.stack =
  fun instrs stack0 ty_map def_ty ->
    match instrs with
    | [] -> stack0
    | (instr :: instrs_tl) ->
      let stack1 = type_step instr stack0 ty_map def_ty in
      if is_stopping_instr instr
        then stack1
        else type_steps instrs_tl stack1 ty_map def_ty

(* Recall that in WASM 1.0 semantics, there is at most one return type *)
let infer_stack_type
  : Ast.instr list
  -> type_map_type
  -> Types.value_type
  -> Types.stack_type =
  fun instrs ty_map def_ty ->
    let wtys = S.to_list (type_steps instrs S.empty_stack ty_map def_ty) in
    walue_types_to_value_types wtys def_ty
    (*
    match walue_types_to_value_types wtys def_ty with
    | [] -> []
    | (wty0 :: _) -> [wty0]
    *)

let trim_type : Types.stack_type -> Types.stack_type = function
  | [] -> []
  | [ty0] -> [ty0]
  | (ty0 :: _) -> []



