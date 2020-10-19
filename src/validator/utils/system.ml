(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


module String = String_utils

(* Runs a Unix a unix command to completion and yields stdout and stderr *)
let unix_command_stdout_stderr : string -> (string * string) =
  fun cmd ->
    let (stdout_chan, stdin_chan, stderr_chan)
      = Unix.open_process_full cmd (Array.of_list []) in
    let _ = close_out stdin_chan in
    let stdout_lines = ref [] in
    let stderr_lines = ref [] in
    try
      while true do
        let line = input_line stdout_chan in
        stdout_lines := line :: !stdout_lines
      done;
      ("", "")
    with End_of_file ->
      (try
        while true do
          let line = input_line stderr_chan in
          stderr_lines := line :: !stderr_lines
        done;
      ("", "")
      with End_of_file ->
        (let _ = Unix.close_process_full (stdout_chan, stdin_chan, stderr_chan) in
        (String.unlines (List.rev !stdout_lines),
          String.unlines (List.rev !stderr_lines))))

