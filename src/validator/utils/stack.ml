(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


module String = String_utils

(* A stack is actually just a list :) *)
type 'a stack = 'a list

let empty_stack : 'a stack = []

let size : 'a stack -> int = List.length

(* Push consists of prepending to the beginning of the list *)
let push : 'a -> 'a stack -> 'a stack =
  fun x stack -> x :: stack

let prepend_list : 'a list -> 'a stack -> 'a stack =
  fun xs stack -> xs @ stack

(* Pop consists of removing from the beginning of the list
 * Return None if not possible
 * Return a pair with the head, and the tail of the list otherwise *)
let pop : 'a stack -> ('a * 'a stack) option = function
  | [] -> None
  | (x :: xs) -> Some (x, xs)

let pop2 : 'a stack -> ('a * 'a * 'a stack) option = function
  | (x1 :: x2 :: xs) -> Some (x1, x2, xs)
  | _ -> None

let pop3 : 'a stack -> ('a * 'a * 'a * 'a stack) option = function
  | (x1 :: x2 :: x3 :: xs) -> Some (x1, x2, x3, xs)
  | _ -> None

(* Look at the beginning of the stack without removing
 * Return None if stack is empty *)
let peek : 'a stack -> 'a option = function
  | [] -> None
  | x :: _ -> Some x

(* Convert a stack to a list, but really we don't do anything here :) *)
let to_list : 'a stack -> 'a list =
  fun stack -> stack

(* Convert a list into a stack. Again nothing happens hehe :) *)
let from_list : 'a list -> 'a stack =
  fun xs -> xs

(* Pop to the nth (0-indexed) element on top of the stack.
 * pop_to_nth 0 is equivalent to pop;
 * pop_to_nth 1 is equivalent to pop (snd (pop stack)) *)
let rec pop_to_nth : int -> 'a stack -> ('a * 'a stack) option =
  fun i stack ->
    match stack with
    | x :: xs when (i = 0) -> Some (x, xs)
    | _ :: xs when (i > 0) -> pop_to_nth (i - 1) xs
    | _  -> None

(* Remove the top n elements *)
let rec delete_n : int -> 'a stack -> 'a stack =
  fun i stack ->
    match stack with
    | x :: xs when (i > 0) -> delete_n (i - 1) xs
    | _ -> stack

(* Printing things *)

let string_of_stack : 'a stack -> ('a -> string) -> string =
  fun stack string_of_a ->
    String.string_of_list_endline 2 1 (to_list stack) string_of_a

