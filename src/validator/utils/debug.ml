(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


let debug_level: int ref = ref 0 

let none = 0
let low = 1
let medium = 2
let high = 3

let set_debug_level: int -> unit =
  fun k ->
  if (k >= none && k <= high) then
    debug_level := k
  else
    failwith(Printf.sprintf "Debug level should be in the range [%d...%d]" none high)

let set_debug_low() = set_debug_level low
let set_debug_medium() = set_debug_level medium
let set_debug_high() = set_debug_level high
                            

let string_of_time : unit -> string =
  fun () ->
    let time = Unix.localtime (Unix.time ()) in
    let hour0 = string_of_int time.tm_hour in
    let hour1 = (if String.length hour0 < 2 then "0" else "") ^ hour0 in
    let min0 = string_of_int time.tm_min in
    let min1 = (if String.length min0 < 2 then "0" else "") ^ min0 in
    let sec0 = string_of_int time.tm_sec in
    let sec1 = (if String.length sec0 < 2 then "0" else "") ^ sec0 in
    "time: " ^ hour1 ^ ":" ^ min1 ^ ":" ^ sec1

             
let if_debug_level: int -> (unit -> unit) -> unit =
  fun k f ->
  if !debug_level >= k then
    (Printf.printf "\n[DEBUG %s]\t\n" (string_of_time()); f())
  else ()

let if_debug_none = if_debug_level none 
let if_debug_low = if_debug_level low
let if_debug_medium = if_debug_level medium
let if_debug_high = if_debug_level high
let if_debug = if_debug_medium
                                     
                            
let print_debug_level : int -> string -> unit =
  fun k msg ->
  if !debug_level >= k then
    print_endline (Printf.sprintf "\n[DEBUG %s]\t%s" (string_of_time()) msg)
  else
    ()

let print_debug_none = print_debug_level none      
let print_debug_low = print_debug_level low
let print_debug_medium = print_debug_level medium
let print_debug_high = print_debug_level high
let print_debug = print_debug_medium
                                    

let prerr_debug_level : int -> string -> unit =
  fun k msg ->
    if !debug_level >= k then
      Printf.eprintf "\n[DEBUG %s]\t%s\n" (string_of_time()) msg
    else
      ()

let prerr_debug_none = prerr_debug_level none
let prerr_debug_low = prerr_debug_level low
let prerr_debug_medium = prerr_debug_level medium
let prerr_debug_high = prerr_debug_level high
let prerr_debug = prerr_debug_low

let prerr_if_none : string -> 'a option -> 'a option =
  fun msg x ->
    match x with
    | None ->
       Printf.eprintf "\n[DEBUG %s]\tNone: %s\n" (string_of_time()) msg;
       x
    | _ -> x

let string_of_fraction : (int * int) -> string =
  fun (a, b) ->
    "(" ^ string_of_int a ^ "/" ^ string_of_int b ^ ")"




