(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


open Wasm
open Debug

module String = String_utils
module G = Digraph
module Q = Queue


(* The dominators tree is a data structure that is used for reasoning about
 * loops in compilers and code analysis (cf Dragon Book (2nd ed) Chapter 9.6).
 * We primarily leverage the dominators tree in order to re-construct
 * the Ast.instr list provided a instr_graph -- and other information.
 * Internally the dominators tree is just represented as a regular graph.
 *
 * A caveat we note is that the dominators tree should be connected (a tree),
 * but this is not very important for how we end up using it since we mostly
 * use it is as a reference for converting the instr_graph back to Ast.instr.
 * As long as it looks like a tree if viewed from the root, that's fine.
 *
 * Since G.vertices are internally stored as integers and should have
 * representations independent of the graph,
 * this means that the dominators tree can share the same G.vertices as the
 * graph that is is supposed to be representing, which is a convenient hack *)

(* Since we don't need special markings, we label with unit *)
type dom_tree = (unit, unit) G.graph

(* Maps each vertex to its dominator set.
 * These are the vertices that dominated it, hence "dominated by" *)
type dom_by_map = G.VSet.t G.VMap.t
type doms_map = G.VSet.t G.VMap.t

(* Dominator data
 *  dom_tree: the dominator tree
 *  root_v: root vertex of the dominator tree
 *  dom_by_map: backwards dominator relation
 *  doms_map : forward dominator relation
 *)

type dom_data =
  { dom_tree : dom_tree;
    root_vertex : G.vertex;
    dom_by_map : dom_by_map;
    doms_map : doms_map;
  }

let empty_dom_data : dom_data =
  { dom_tree = G.empty_graph;
    root_vertex = G.null_vertex;
    dom_by_map = G.VMap.empty;
    doms_map = G.VMap.empty;
  }

(* We want easier lookups to dominators *)
let vertex_dom_by_set : G.vertex -> dom_by_map -> G.VSet.t =
  fun v dby_map ->
    match G.VMap.find_opt v dby_map with
    | None -> G.VSet.singleton v
    | Some v_ds -> v_ds

let vertex_doms_set : G.vertex -> doms_map ->  G.VSet.t =
  fun v dby_map ->
    match G.VMap.find_opt v dby_map with
    | None -> G.VSet.singleton v
    | Some v_ds -> v_ds



(* Given a graph, calculate the dominators (dominated by) map.
 * Note that we have to explicitly supply the root / start vertex.
 * A dominator is given by the relationship (cf Wikipedia)
 *    https://en.wikipedia.org/wiki/Dominator_(graph_theory)#Algorithms
 *
 *  doms(r) = {r} if r is a distinguished root(s) of a tree
 *  doms(v) = {v} \cup [\cap_{p \in prevs(v)} doms(v)]
 *)

(* One-step contraction of a vertex's dominator set *)
let shrink_vertex_dom_by_map : G.vertex -> ('a, 'b) G.graph -> dom_by_map -> (dom_by_map * bool) =
  fun v graph dby_map ->
    let prevs = List.map fst (G.vertex_prevs v graph) in
    let prev_dbys = List.map (fun u -> vertex_dom_by_set u dby_map) prevs in
    let prev_dbys_inter =
      List.fold_left
        (fun accs pds -> G.VSet.inter pds accs)
        graph.vertex_set
        prev_dbys in
    let dby_val = G.VSet.union (G.VSet.singleton v) prev_dbys_inter in
    (* No adjustments were made *)
    if G.VSet.cardinal dby_val = G.VSet.cardinal (vertex_dom_by_set v dby_map) then
      (dby_map, false)
    (* An adjustment was made *)
    else
      (G.VMap.add v dby_val dby_map, true)

(* One round of contractions for all the vertices *)
let shrink_vertices_dom_by_map : G.VSet.t -> ('a, 'b) G.graph -> dom_by_map -> (dom_by_map * bool) =
  fun vertices graph dby_map ->
    G.VSet.fold
      (fun v (dbm0, bool0) ->
        let (dbm1, bool1) = shrink_vertex_dom_by_map v graph dbm0 in
        (dbm1, bool0 || bool1))
      vertices
      (dby_map, false)

let rec shrink_vertices_dom_by_map_fix : G.VSet.t -> ('a, 'b) G.graph -> dom_by_map -> dom_by_map =
  fun vertices graph dby_map0 ->
    let (dby_map1, modified) = shrink_vertices_dom_by_map vertices graph dby_map0 in
    if modified then
      shrink_vertices_dom_by_map_fix vertices graph dby_map1
    else
      dby_map1

let graph_to_dom_by_map : ('a, 'b) G.graph -> G.vertex -> dom_by_map =
  fun graph root_v ->
    let dby_map0 =
      G.VSet.fold
        (fun v dbm0 -> G.VMap.add v graph.vertex_set dbm0)
        graph.vertex_set
        G.VMap.empty in

    let dby_map1 = G.VMap.add root_v (G.VSet.singleton root_v) dby_map0 in
    let non_root_vs = G.VSet.remove root_v graph.vertex_set in
    shrink_vertices_dom_by_map_fix non_root_vs graph dby_map1
      

(* Given a dby_map, we can use this to again calculate a dominators tree.
 * However, to do this we do the following:
 *
 *  init dom_tree = empty
 *  for v in G.vertices graph:
 *    add v dom_tree
 *  for each v in G.vertices graph:
 *    let d = the smallest dominator of
 *    add edge (d, v) to dom_tree
 *
 * The functionalities are implemented in the following functions
 *)

(* Given a vertex, find the least (ie lowest on the tree) dominator that is not itself.
 * We leverage the property that the dominator relationship is transitive,
 * which means that we can search for the member of doms(v) with the second
 * largest list of dominators: the first largest will always be v itself.
 * Since this operation may fail if we are looking at a "root",
 * the return type is an option: the None case is if it's a root *)
let least_uniq_dom : ('a, 'b) G.graph -> G.vertex -> dom_by_map -> G.vertex option =
  fun graph v dby_map ->
    match List.of_seq (G.VSet.to_seq (vertex_dom_by_set v dby_map)) with
    | v_ds when (List.length v_ds < 2) -> None
    | v_ds ->
      let v_dby_lens =
        List.map
          (fun d -> (d, G.VSet.cardinal (vertex_dom_by_set d dby_map))) v_ds in
      let v_dby_asc = List.sort (fun (_, a) (_, b) -> compare a b) v_dby_lens in
      match List.rev v_dby_asc with
      (* Strange that it should be empty ... *)
      | [] -> None
      (* The singleton case is the root case *)
      | [r] -> None
      (* Second to last is the one we want *)
      | _ :: (d, _) :: _ -> Some d

(* Calculate forward dominator relation via a DFS pass.
 * Important that this is actually a tree! *)
let rec dom_tree_to_doms_map : dom_tree -> G.vertex -> doms_map -> doms_map =
  fun tree this_v ds_map ->
    match G.vertex_succs this_v tree with
    | [] -> G.VMap.add this_v (G.VSet.singleton this_v) ds_map
    | succs ->
      let svs = List.map fst succs in
      let ds_map1 = List.fold_left (fun dsm s -> dom_tree_to_doms_map tree s dsm) ds_map svs in
      let succ_ds_sets = List.map (fun s -> vertex_doms_set s ds_map1) svs in
      let this_ds_set = List.fold_left G.VSet.union (G.VSet.singleton this_v) succ_ds_sets in
      G.VMap.add this_v this_ds_set ds_map1

(* Continuation of above implementation *)
let graph_to_dom_data : ('a, 'b) G.graph -> G.vertex -> dom_data =
  fun graph root_v ->
    let vs = G.vertices graph in
    let dby_map = graph_to_dom_by_map graph root_v in
    let init_dom_tree =
      List.fold_left
        (fun acc_g v -> G.add_vertex v () acc_g) G.empty_graph vs in
    let dom_tree =
      List.fold_left
        (fun acc_dt u ->
          match least_uniq_dom graph u dby_map with
          | None -> acc_dt
          | Some d -> G.add_edge (d, (), u) acc_dt)
        init_dom_tree vs in

    let doms_map_init =
      List.fold_left
        (fun map v-> G.VMap.add v (G.VSet.singleton v) map)
        G.VMap.empty        
        vs
    in
    let doms_map = dom_tree_to_doms_map dom_tree root_v doms_map_init in
    { empty_dom_data with
      dom_tree = dom_tree;
      root_vertex = root_v;
      dom_by_map = dby_map;
      doms_map = doms_map; }

(* Having constructed a dom_tree, we can do some nice utilities on it *)

(* Does high_v dominate low_v? *)
let dominates : G.vertex -> G.vertex -> dom_data -> bool =
  fun high_v low_v dom_data ->
    G.VSet.mem low_v (vertex_doms_set high_v dom_data.doms_map)
    
(* One thing that we have to do for getting the block branch levels right
 * is to count the dominance level.
 * This is the number of edges that are traversed along the dom_tree.
 * Return None if there is no dominance relation *)
let rec domby_level : G.vertex -> G.vertex -> dom_tree -> int option =
  fun low_v high_v dom_tree ->
    if low_v = high_v then
      Some 0
    else
      match G.vertex_prevs low_v dom_tree with
      (* Oh no, we've exhausted the search *)
      | [] -> (prerr_debug "dom_level: reached root"; None)
      | [(p, _)] ->
        (match domby_level p high_v dom_tree with
        | None -> None
        | Some n -> Some (n + 1))
      (* Somehow there is more than one predecessor *)
      | _ -> (prerr_debug "dom_level: bad dom_tree"; None)

(* Detect whether a vertex in the dom tree is a loop header *)
let is_loop_header : G.vertex -> dom_data -> ('a, 'b) G.graph -> bool =
  fun this_v dom_data graph ->
    let reachs = G.reachable_set this_v dom_data.dom_tree in
    G.VSet.fold (fun u b ->
      let usuccs = List.map fst (G.vertex_succs u graph) in
      b || (List.fold_left (fun b1 s -> s = this_v) false usuccs))
      reachs false

let is_block_loop_header : G.vertex -> dom_data -> ('a, 'b) G.graph -> bool =
  fun this_v dom_data graph ->
    if (is_loop_header this_v dom_data graph) then
      let dom_succs =
        List.filter
          (fun (s, _) -> this_v <> s && dominates this_v s dom_data)
          (G.vertex_succs this_v graph) in
      List.length dom_succs > 1
    else
      false

let rec count_br_level : G.vertex -> G.vertex -> dom_data -> ('a, 'b) G.graph -> int option =
  fun low_v high_v dom_data graph ->
    if low_v = high_v then
      (* Need a + 1 to clear the block *)
      Some (if is_block_loop_header low_v dom_data graph then 1 else 0)
    else
      match G.vertex_prevs low_v dom_data.dom_tree with
      | [] -> (prerr_debug "count_br_level: hit root"; None)
      | [(p, _)] ->
        (match count_br_level p high_v dom_data graph with
        | Some n ->
          if is_block_loop_header low_v dom_data graph then Some (n + 2)
          else if is_loop_header low_v dom_data graph then Some (n + 1)
          else Some n
        | None -> None)
      | _ -> (prerr_debug "count_br_level: bad tree"; None)

    
(* Sanity checks *)
let string_of_dom_by_map : dom_by_map -> string =
  fun dby_map ->
    String.string_of_list_endline 2 2
      (G.VMap.bindings dby_map)
      (fun (k, vs) ->
        let vs_list = List.of_seq (G.VSet.to_seq vs) in
        "(" ^ G.string_of_vertex k ^ ", "
            ^ String.string_of_list_inline vs_list G.string_of_vertex ^ ")")


