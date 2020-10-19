(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


open Filename
open Wasm

let file_to_string : string -> string =
  fun file ->
    let chan = open_in file in
    let str = really_input_string chan (in_channel_length chan) in
    (close_in chan;
    str)

let is_wast_file : string -> bool =
  fun file -> ".wast" = extension (file)

let is_wasm_file : string -> bool =
  fun file -> ".wasm" = extension (file)


(* The Script.script is equivalent to a Script.command list
 * This is one of the formats that the spec/interpreter backend is able
 * give to us *)
let wast_file_to_script : string -> Script.script =
  fun file ->
    let in_chan = open_in file in
    try
      let lexbuf = Lexing.from_channel in_chan in
      Parse.parse file lexbuf Parse.Script
    with exn ->
      (close_in in_chan;
      raise exn)

