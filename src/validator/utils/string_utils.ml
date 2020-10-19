(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


(* Utility functions for general string manipulation *)

(* Re-exports *)
let length : string -> int = String.length 

let get : string -> int -> char = String.get

let concat : string -> string list -> string = String.concat

let split_on_chat : char -> string -> string list = String.split_on_char

let sub : string -> int -> int -> string = String.sub

let lowercase_ascii : string -> string = String.lowercase_ascii

(* Repeat a list *)
let rec repeat : int -> 'a -> 'a list =
  fun n x ->
    if n <= 0 then [] else x :: repeat (n - 1) x

(* Pad a string with spaces *)
let pad : int -> string =
  fun n -> String.concat "" (repeat n " ")

(* Make each line (delineated by '\n') into an element of a list *)
let lines : string -> string list =
  fun str -> String.split_on_char '\n' str

(* Combine strings into a single joined together by "\n" *)
let unlines : string list -> string =
  fun strs -> String.concat "\n" strs

(* Wrap things in parentheses *)
let parens : string -> string =
  fun str -> "(" ^ str ^ ")"

(* A space character *)
let space : char -> bool = function
  | ' ' | '\012' | '\n' | '\r' | '\t' -> true
  | _ -> false

(* Check if one string contains another *)
let contains : string -> string -> bool =
  fun str key ->
    let re = Str.regexp key in
    try let _ = Str.search_forward re str 0 in true
    with Not_found -> false

(* Removes whitespace: https://stackoverflow.com/a/14617652/2704964 *)
let trim : string -> string =
  fun str ->
  let len = String.length str in
  let i = ref 0 in
  let _ =
    (while !i < len && space (String.get str !i) do
      incr i
    done) in
  let j = ref (len - 1) in
  let _ = (while !j >= !i && space (String.get str !j) do
    decr j
  done) in
  if !i = 0 && !j = len - 1 then
    str
  else if !j >= !i then
    String.sub str !i (!j - !i + 1)
  else
    ""
;;

(* Conct strings as a list *)
let concat_as_list : string list -> string =
  fun strs ->
    "[" ^ String.concat "; " strs ^ "]"

(* Split a string up by '\n', and then indent accordingly by the
 * specified amount *)
let indent_string : int -> string -> string =
  fun ind str ->
    unlines (List.map (fun s -> pad ind ^ s) (lines str))

(*
let indent2 : string -> string = indent_string 2

let indent4 : string -> string = indent_string 4
*)

let indent2 : string -> string = fun str -> str

let indent4 : string -> string = fun str -> str


let tab_string : string -> string =
  fun str ->
    unlines (List.map (fun s -> "\t" ^ s) (lines str))

(* Make a string out of a list;
 * need to provide the ('a -> string) function yourself, however *)
let string_of_list_inline : 'a list -> ('a -> string) -> string =
  fun xs string_of_a ->
    let strs = List.map string_of_a xs in
    "[" ^ (String.concat "; " strs) ^ "]"

(* Indent a list across multiple lines
 * To better pretty print it, we need a format like
 *
 *    [ line 1;
 *      line 2;
 *      line 3; ]
 *
 * hind / raw_hind is the horizontal indentation of each line wrt the LHS zero
 * vind / raw_vind is the vertical separation of each line *)
let string_of_list_endline
  : int -> int -> 'a list -> ('a -> string) -> string =
  fun raw_hind raw_vind xs string_of_a ->
    let hind = max 1 raw_hind in
    let vind = max 1 raw_vind in
    match xs with
    | x :: [] -> "[" ^ string_of_a x ^ "]"
    | _ ->
      let vind_str = String.concat "" (repeat vind "\n") in
      let xs_strs = List.map string_of_a xs in
      let ind_xs_strs = List.map (indent_string hind) xs_strs in
      match ind_xs_strs with
      | [] -> "[]"
      | (s :: []) -> "[" ^ s ^ "]"
      | (s :: tl_ss) ->
        let new_s = String.sub s 1 (String.length s - 1) in
        "[" ^ String.concat (";" ^ vind_str) (new_s :: tl_ss) ^ " ]"

(* Provided an option type and the function ('a -> string), print a string *)
let string_of_option : 'a option -> ('a -> string) -> string =
  fun x_opt string_of_a  ->
    match x_opt with
    | None -> "None"
    | Some x -> "Some (" ^ string_of_a x ^ ")"


