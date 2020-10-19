(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


(* Dragon Book (2nd ed) Figure 9.38 and 9.39 *)

open Digraph
open Instr_graph
open Dominance

let u : 'a -> ('a * unit) =
  fun x -> (x, ())

let graph_9_39_adjlist =
  [ (1, (), [u 2; u 3]);
    (2, (), [u 3]);
    (3, (), [u 4]);
    (4, (), [u 5; u 6; u 3]);
    (5, (), [u 7]);
    (6, (), [u 7]);
    (7, (), [u 8; u 4]);
    (8, (), [u 9; u 10; u 3]);
    (9, (), [u 1]);
    (10, (), [u 7]) ]

let test_graph_9_39 : unit -> unit =
  fun _ ->
    let graph_9_39 = from_adjacency_list graph_9_39_adjlist in
    let _ = print_endline (string_of_graph_simple graph_9_39) in
    let _ = print_endline "\n\n\n\n -------------------- \n\n\n\n" in
    let dt_9_39 = graph_to_dom_data graph_9_39 1 in
    let _ = print_endline (string_of_graph_simple dt_9_39.dom_tree) in
    ()


