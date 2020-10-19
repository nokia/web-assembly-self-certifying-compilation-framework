(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


(* Test the type checker implementation *)

open Wasm

open Type_inference
open String_utils

(*
let fty : tvar list -> value_type list -> value_type list -> fun_type =
  fun bvs ins outs ->
    { empty_fun_type with
      bound_tvars = bvs;
      in_types = ins;
      out_types = outs }

let tvar : int32 -> value_type =
  fun tv -> TypeVar tv

type quick_value_types = I32 | I64 | F32 | F64

let vty : quick_value_types -> value_type = function
  | I32 -> ValueType Types.I32Type
  | I64 -> ValueType Types.I64Type
  | F32 -> ValueType Types.F32Type
  | F64 -> ValueType Types.F64Type


(* Expect: ([], [], [F64; F32]) *)
let tyseq1 : fun_type list =
  [ fty [] [] [vty I32; vty I64; vty F32];
    fty [] [vty I32; vty I64] [];
    fty [] [] [vty F64] ]

(* Expected: [0; 1] [V0; V1] [F64] *)
let tyseq2 : fun_type list =
  [ fty [0l] [tvar 0l] [vty I32; tvar 0l];
    fty [0l; 1l] [vty I32; tvar 0l; tvar 1l] [vty F64] ]

(* Expected: None *)
let tyseq3 : fun_type list =
  [ fty [0l] [] [tvar 0l];
    fty [] [vty I32] [vty F64] ]

let print_compose : fun_type list -> unit =
  fun funtys ->
    match compose_fun_types funtys empty_type_context with
    | None -> print_endline "print_compose: None"
    | Some (fty, ctx) ->
      let ctx_str =
        string_of_list_inline
          (List.of_seq (TvarMap.to_seq ctx.value_type_map))
          (fun (tv, bty) ->
            "(" ^ Int32.to_string tv
              ^ ", " ^ string_of_value_type bty ^ ")") in
      let _ =
        print_endline
          ("print_compose: " ^ string_of_fun_type fty ^ "; " ^ ctx_str) in
      ()

*)

let test_type_inference : unit -> unit =
  fun _ ->
  (*
    let _ = print_compose tyseq1 in
    let _ = print_compose tyseq2 in
    let _ = print_compose tyseq3 in
    *)

    ()



