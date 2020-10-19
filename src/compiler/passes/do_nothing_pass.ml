(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


open Func_types
open Script_types

open Pass_types

(* Inspired by Kedar, this is the identity optimization.
 * For now we have stubbed out the proofs in the pass out *)

let do_nothing_pass_fun : ufunc_ir -> pass_config -> ufunc_ir * pass_out =
  fun func_ir _ ->
    (func_ir, empty_pass_out)

let do_nothing_pass : upass =
  init_pass
    "do_nothing"
    do_nothing_pass_fun


