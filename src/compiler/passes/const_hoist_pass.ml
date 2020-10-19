(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


open Wasm
open Source

open Solver_types

open Instr_graph
open Func_types
open Script_types
open State_types
open Proof_types

open Pass_types
open Debug
open Wasm_utils
open Proof_builder

module G = Digraph
module Q = Queue


(* Const hoisting algorithm
 *  (1) BFS the graph to
 *    (a) search for places where LocalGet is used (track addresses in a set)
 *    (b) search for places where Consts are used (track values + occurrences in a map)
 *
 *  (2) Based on the map of values, decide what to hoist and to what addresses
 *  (3) BFS again to replace such consts with LocalGet
 *)

type count_map = int WasmValueMap.t
type hoist_map = int32 WasmValueMap.t
type addr_set = Int32Set.t

let incr_count : WasmValue.t -> count_map -> count_map =
  fun wal ctmap ->
    match WasmValueMap.find_opt wal ctmap with
    | None -> WasmValueMap.add wal 1 ctmap
    | Some k -> WasmValueMap.add wal (k + 1) ctmap

let rec fold_instrs : Ast.instr list -> count_map -> addr_set -> (count_map * addr_set) =
  fun instrs ctmap addrset ->
    match instrs with
    | [] -> (ctmap, addrset)
    | instr :: instrs_tl ->
      match instr.it with
      | Ast.Const lit -> fold_instrs instrs_tl (incr_count lit.it ctmap) addrset
      | Ast.LocalGet x -> fold_instrs instrs_tl ctmap (Int32Set.add x.it addrset)
      | _ -> fold_instrs instrs_tl ctmap addrset

(* Search out the data *)
let rec fold_graph_bfs
  : ('a, 'b) instr_graph
  -> G.vertex Q.queue
  -> count_map
  -> addr_set
  -> G.VSet.t
  -> (count_map * addr_set) =
  fun graph queue ctmap addrset visited ->
    match Q.dequeue queue with
    | None -> (ctmap, addrset)
    | Some (this_v, queue1) ->
      match G.vertex_label this_v graph with
      | None ->
        (prerr_endline ("fold_graph_bfs: None lookup at " ^ G.string_of_vertex this_v);
          (ctmap, addrset))
      | Some (block, _) ->
        let (ctmap1, addrset1) = fold_instrs block.instrs ctmap addrset in
        let visited1 = G.VSet.add this_v visited in
        let unvisited_succs =
          List.concat (List.map
            (fun (s, _) -> if (G.VSet.mem s visited1) || (Q.mem s queue1) then [] else [s])
            (G.vertex_succs this_v graph)) in
        let queue2 = Q.enqueue_list unvisited_succs queue1 in
        fold_graph_bfs graph queue2 ctmap1 addrset1 visited1
        
(* Decide when something should be hoisted:
 * If a constant appears > 2 times and has a value >= 1e8, then we hoist.
 * This is actually mildly arbitrary since this is a custom optimization pass *)
let worth_hoisting : Values.value -> int -> bool =
  fun wal ct ->
    true
    (*
    if ct < 2 then
      false
    else
      match wal with
      | Values.I32 x -> Int32.to_int x >= 100000000
      | _ -> false
    *)

(* Next address to allocate to *)
let next_free_local : addr_set -> int32 =
  fun addrset ->
    match List.sort Int32.compare (List.of_seq (Int32Set.to_seq addrset)) with
    | [] -> 1l
    | x :: _ -> Int32.add x 1l

(* Figure out which ones are worth hoisting, then allocate accordingly *)
let mk_hoist_map : count_map -> addr_set -> hoist_map =
  fun ctmap addrset ->
    let addr0 = next_free_local addrset in
    let ctmap1 = WasmValueMap.filter (fun w k -> worth_hoisting w k) ctmap in
    let hwals = List.map fst (List.of_seq (WasmValueMap.to_seq ctmap1)) in
    let (hoistmap, _) =
      List.fold_left
        (fun (hmap, addr) w -> (WasmValueMap.add w addr hmap, Int32.add addr 1l))
        (WasmValueMap.empty, addr0) hwals in
    hoistmap

(* Rewrite graph *)
let rec rewrite_instrs : Ast.instr list -> hoist_map -> Ast.instr list =
  fun instrs hoistmap ->
    match instrs with
    | [] -> []
    | instr :: instrs_tl ->
      match instr.it with
      | Ast.Const lit ->
        (match WasmValueMap.find_opt lit.it hoistmap with
        | None -> instr :: rewrite_instrs instrs_tl hoistmap
        | Some x ->
          (noregion (Ast.LocalGet (int32_to_var x))) :: rewrite_instrs instrs_tl hoistmap)
      | _ -> instr :: rewrite_instrs instrs_tl hoistmap

let rec rewrite_graph_bfs
  : ('a, 'b) instr_graph
  -> G.vertex Q.queue
  -> hoist_map
  -> G.VSet.t
  -> ('a, 'b) instr_graph =
  fun graph queue hoistmap visited ->
    match Q.dequeue queue with
    | None -> graph
    | Some (this_v, queue1) ->
      match G.vertex_label this_v graph with
      | None ->
        (prerr_endline ("rerwite_graph_bfs: None lookup at " ^ G.string_of_vertex this_v);
          graph)
      | Some (block, a) ->
        let instrs1 = rewrite_instrs block.instrs hoistmap in
        let visited1 = G.VSet.add this_v visited in
        let block1 = { block with instrs = instrs1 } in
        let graph1 = G.add_vertex_label this_v (block1, a) graph in
        let unvisited_succs =
          List.concat (List.map
            (fun (s, _) -> if G.VSet.mem s visited1 then [] else [s])
            (G.vertex_succs this_v graph)) in
        let queue2 = Q.enqueue_list unvisited_succs queue1 in
        rewrite_graph_bfs graph1 queue2 hoistmap visited1



