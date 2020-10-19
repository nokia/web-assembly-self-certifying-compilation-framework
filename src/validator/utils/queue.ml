(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


module String = String_utils

(* A queue is implemented as a list *)
type 'a queue = 'a list

let empty_queue : 'a queue = []

(* Push onto end of the queue *)
let enqueue : 'a -> 'a queue -> 'a queue =
  fun x queue -> queue @ [x]

let enqueue_list : 'a list -> 'a queue -> 'a queue =
  fun xs queue -> queue @ xs

(* Pop from the start of the queue *)
let dequeue : 'a queue -> ('a * 'a queue) option = function
  | [] -> None
  | (x :: xs) -> Some (x, xs)

let peek : 'a queue -> 'a option = function
  | [] -> None
  | x :: _ -> Some x

let to_list : 'a queue -> 'a list =
  fun queue -> queue

let from_list : 'a list -> 'a queue =
  fun xs -> xs

let mem : 'a -> 'a queue -> bool = List.mem

(* Printing functionalities *)

let string_of_queue : 'a queue -> ('a -> string) -> string =
  fun queue string_of_a ->
    String.string_of_list_endline 2 1 (to_list queue) string_of_a

