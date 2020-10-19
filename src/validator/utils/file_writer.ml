(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


open Wasm

(* We make this since this is supposed to be a private part of the
 * script/run.ml module within spec/interpreter, but we need it.
 * This serves to map strings into Script.scripts
 *)
module ScriptMap = Map.Make(String)

(* What's interesting about spec/interpreter is that within the
 * scripts/run.ml module there are several global references that are
 * kept around, one of them being the Run.scripts.
 * It turns out that when spec/interpreter parses things in,
 * the Run.scripts is updated, which allows subsequent passes to write
 * based on it.
 *
 * It's weird: they use an empty string "" where they should be using option?
 * Why even use a map at all if option probably serves the same purpose?
 *)
let script_to_file : Script.script -> string -> unit =
  fun script file ->
    (Run.scripts := ScriptMap.add "" script !Run.scripts;
    try
      Run.output_file file
        (fun () -> ScriptMap.find "" !Run.scripts)
        (fun () -> ScriptMap.find "" !Run.modules)
    with exn ->
      raise exn)

