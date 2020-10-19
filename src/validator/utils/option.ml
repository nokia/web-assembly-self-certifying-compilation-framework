(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


(* Some monad stuff *)

let opt_return : 'a -> 'a option =
  fun x -> Some x

let opt_bind : 'a option -> ('a -> 'b option) -> 'b option =
  fun x_opt f ->
    match x_opt with
    | Some x -> f x
    | None -> None

let rec fold_left_opt
  : ('a -> 'b -> 'a option) -> 'a -> 'b list -> 'a option =
  fun f acc ys ->
    match ys with
    | [] -> opt_return acc
    | y :: ys_tl ->
      match f acc y with
      | None -> None
      | Some acc1 -> fold_left_opt f acc1 ys_tl


