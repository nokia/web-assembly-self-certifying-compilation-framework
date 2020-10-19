(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


let hd : 'a list -> 'a = List.hd

let tl : 'a list -> 'a list = List.tl

let length : 'a list -> int = List.length

let rev : 'a list -> 'a list = List.rev

let map : ('a -> 'b) -> 'a list -> 'b list = List.map

let mapi : (int -> 'a -> 'b) -> 'a list -> 'b list = List.mapi

let iter : ('a -> unit) -> 'a list -> unit = List.iter

let iteri : (int -> 'a -> unit) -> 'a list -> unit = List.iteri

let filter : ('a -> bool) -> 'a list -> 'a list = List.filter

let fold_left : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a = List.fold_left

let fold_right : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b = List.fold_right

let concat : ('a list) list -> 'a list = List.concat

let flatten : ('a list) list -> 'a list = concat

let mem : 'a -> 'a list -> bool = List.mem

let sort : ('a -> 'a -> int) -> 'a list -> 'a list = List.sort

let to_seq : 'a list -> 'a Seq.t = List.to_seq

let of_seq : 'a Seq.t -> 'a list = List.of_seq

let assoc : 'a -> ('a * 'b) list -> 'b = List.assoc

let assoc_opt : 'a -> ('a * 'b) list -> 'b option = List.assoc_opt

let find : ('a -> bool) -> 'a list -> 'a = List.find

let rec repeat : int -> 'a -> 'a list =
  fun n x -> if n < 1 then [] else x :: repeat (n - 1) x

let rec zip : 'a list -> 'b list -> ('a * 'b) list =
  fun xs ys ->
    match (xs, ys) with
    | ([], _) -> []
    | (_, []) -> []
    | (x::xs1, y::ys1) -> (x, y) :: zip xs1 ys1

(* Contains something? *)
let all : ('a -> bool) -> 'a list -> bool =
  fun f xs ->
    List.fold_left (fun b x -> b && f x) true xs

let rec contains : 'a -> 'a list -> bool =
  fun x xs ->
    match xs with
    | [] -> false
    | h :: xs_tl -> (x = h) || (contains x xs_tl)

(* Given a list of length n returns a list of n + 1 elements,
 * where each elements is a list of the first k tails *)
let rec tails : 'a list -> ('a list) list = function
  | [] -> [[]]
  | (x :: xs) -> (x :: xs) :: tails xs
    
(* Same thing as tails, but does it for the initials instead *)
let starts : 'a list -> ('a list) list =
  fun xs -> List.map List.rev (tails (List.rev xs))

(* The nth element of a list *)
let rec nth : int -> 'a list -> 'a -> 'a =
  fun n xs defx ->
    match xs with
    | h :: _ when (n = 0) -> h
    | _ :: xs_tl when (n > 0) -> nth (n - 1) xs_tl defx
    | _ -> defx

let rec nth_int32 : int32 -> 'a list -> 'a -> 'a =
  fun n xs defx ->
    match xs with
    | h :: _ when (n = 0l) -> h
    | _ :: xs_tl when (n > 0l) -> nth_int32 (Int32.sub n 1l) xs_tl defx
    | _ -> defx

