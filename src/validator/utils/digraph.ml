(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


open String_utils
open Debug

module Q = Queue

(* Define a module for the vertex so that we may wrap it in a Map and Set.
 * We use integers to distinguish vertices *)
module V = struct
  type t = int
  let compare : t -> t -> int = Stdlib.compare
end

type vertex = V.t
type 'b edge = vertex * 'b * vertex
type basic_edge = vertex * vertex
type basic_path = vertex list

module VMap = Map.Make(V)
module VSet = Set.Make(V)

(* Convert vertices to integers *)
let vertex_to_int : vertex -> int =
  fun v -> v

(* The vertex that is ... null *)
let null_vertex : vertex = 0

(* Null edges *)
let null_basic_edge = (null_vertex, null_vertex)

(* For now since we store vertices as integers,
 * the next one in the sequence is simply the increment *)
let next_vertex : vertex -> vertex =
  fun v -> v + 1

(* Graphs are stored as an adjacency list
 *  'a is the vertex label type
 *  'b is the edge label type
 *  'c is the data that we may label each graph with
 *  free_vertex keeps track of the next available vertex
 *
 * We choose the graph_id to be strings and vertices to be ints arbitrarily,
 * but this does give us the ability to name graphs. *)
type graph_id = string

type ('a, 'b) graph =
  { graph_id : graph_id;
    vertex_set : VSet.t;
    label_map : 'a VMap.t;
    succs_map : ((vertex * 'b) list) VMap.t;
    free_vertex : vertex;
  }

(* The empty graph *)
let empty_graph : ('a, 'b) graph =
  { graph_id = "";
    vertex_set = VSet.empty; 
    label_map = VMap.empty;
    succs_map = VMap.empty;
    free_vertex = 1;
  }

(* Convert to adjacency list *)
let to_adjacency_list
  : ('a, 'b) graph -> (vertex * ('a option) * (vertex * 'b) list) list =
  fun graph ->
    List.map
      (fun v ->
        match VMap.find_opt v graph.succs_map with
        | None -> (v, VMap.find_opt v graph.label_map, [])
        | Some succs -> (v, VMap.find_opt v graph.label_map, succs))
      (VSet.elements graph.vertex_set)

(* Convert from an adjacency list into a graph representation *)
let from_adjacency_list
  : (vertex * 'a * (vertex * 'b) list) list -> ('a, 'b) graph =
  fun adj_list ->
    let vs = List.map (fun (v, _, _) -> v) adj_list in
    let max_v = List.fold_left max 0 (List.map vertex_to_int vs) in
    let v_label_pairs =  List.map (fun (v, a, _) -> (v, a)) adj_list in
    let v_succs_pairs = List.map (fun (v, _, s) -> (v, s)) adj_list in
    { empty_graph with
      vertex_set = VSet.of_list vs;
      label_map = VMap.of_seq (List.to_seq v_label_pairs);
      succs_map = VMap.of_seq (List.to_seq v_succs_pairs);
      free_vertex = next_vertex max_v; }

(* Get all the vertices of the graph *)
let vertices : ('a, 'b) graph -> vertex list =
  fun graph ->
    VSet.elements graph.vertex_set

let vertex_exists : vertex -> ('a, 'b) graph -> bool =
  fun v graph ->
    VSet.mem v graph.vertex_set

(* Get the edges of a graph *)
let edges : ('a, 'b) graph -> ('b edge) list =
  fun graph ->
    List.concat (List.map
      (fun v ->
        match VMap.find_opt v graph.succs_map with
        | None -> []
        | Some succs -> List.map (fun (w, b) -> (v, b, w)) succs)
      (List.map fst (VMap.bindings graph.succs_map)))

(* Lookup the label -- should it exist -- for a particular vertex. *)
let vertex_label : vertex -> ('a, 'b) graph -> 'a option =
  fun v graph ->
    VMap.find_opt v graph.label_map

(* Get the label of an edge *)
let edge_label : basic_edge -> ('a, 'b) graph -> 'b option =
  fun (src_v, dst_v) graph ->
    match VMap.find_opt src_v graph.succs_map with
    | None -> None
    | Some succs ->
      match (List.filter (fun (u, _) -> dst_v = u) succs) with
      | [] -> None
      | (_, b) :: _ -> Some b

(* Find the successors for a vertex.
 * Note that this always exists even if the VMap.find_opt returns None,
 * since it just means that it's an empty list [] *)
let vertex_succs : vertex -> ('a, 'b) graph -> (vertex * 'b) list =
  fun v graph ->
    match VMap.find_opt v graph.succs_map with
    | None -> []
    | Some succs -> succs

(* Find the predecessors for a vertex. *)
let vertex_prevs : vertex -> ('a, 'b) graph -> (vertex * 'b) list =
  fun v graph ->
    let es = edges graph in
    let prev_es = List.filter (fun (_, _, v1) -> v1 = v) es in
    List.map (fun (v0, b, _) -> (v0, b)) prev_es

(* Find the ancestors of a vertex *)
let rec ancestors_bfs : vertex -> ('a, 'b) graph -> VSet.t -> VSet.t =
  fun v graph visited ->
    let prevs = vertex_prevs v graph in
    let unvisited =
      List.concat (List.map (fun (p, _) -> if VSet.mem p visited then [] else [p]) prevs) in
    let visited1 = VSet.add v visited in
    List.fold_left (fun acc p -> ancestors_bfs p graph acc) visited1 unvisited

let ancestors : vertex -> ('a, 'b) graph -> VSet.t =
  fun v graph ->
    ancestors_bfs v graph VSet.empty
    
(* Allocate a vertex with a specific label
 * We need to update the next free_vertex available within the graph. *)
let alloc_vertex : 'a -> ('a, 'b) graph -> vertex * ('a, 'b) graph =
  fun a graph ->
    let new_v = graph.free_vertex in
    (new_v,
      { graph with
        vertex_set = VSet.add new_v graph.vertex_set;
        label_map = VMap.add new_v a graph.label_map;
        free_vertex = next_vertex new_v })

(* Insert a label to a vertex in a graph *)
let add_vertex : vertex -> 'a -> ('a, 'b) graph -> ('a, 'b) graph =
  fun v a graph ->
    { graph with
      vertex_set = VSet.add v graph.vertex_set;
      label_map = VMap.add v a graph.label_map }

let add_vertex_label : vertex -> 'a -> ('a, 'b) graph -> ('a, 'b) graph =
  fun v b graph ->
    if VSet.mem v graph.vertex_set then
      { graph with
        label_map = VMap.add v b graph.label_map }
    else
      (prerr_debug
        ("add_vertex_label: " ^ string_of_int v ^ " not found in " ^ graph.graph_id);
      graph)

(* Add an edge to the graph specifying the
 *  source vertex
 *  destination vertex
 *  edge label on the vertex *)
let add_edge : 'b edge -> ('a, 'b) graph -> ('a, 'b) graph =
  fun (src_v, b, dst_v) graph ->
    match VMap.find_opt src_v graph.succs_map with
    | None ->
      { graph with
        vertex_set = VSet.add dst_v (VSet.add src_v graph.vertex_set);
        succs_map = VMap.add src_v [(dst_v, b)] graph.succs_map }
    | Some succs ->
      { graph with
        vertex_set = VSet.add dst_v graph.vertex_set;
        succs_map = VMap.add src_v ((dst_v, b) :: succs) graph.succs_map }

(* Update the succs_map *)
let update_succs : vertex -> (vertex * 'b) list -> ('a, 'b) graph -> ('a, 'b) graph =
  fun v succs graph ->
    { graph with succs_map = VMap.add v succs graph.succs_map }

(* Does an edge exist? *)
let only_edge_exists : 'b edge -> ('a, 'b) graph -> bool =
  fun (src_v, b, dst_v) graph ->
    match List.filter (fun (s, b1) -> s = dst_v && b = b1) (vertex_succs src_v graph) with
    | [] -> false
    | _ -> true

let only_basic_edge_exists : basic_edge -> ('a, 'b) graph -> 'b option =
  fun (src_v, dst_v) graph ->
    match List.filter (fun (s, _) -> s = dst_v) (vertex_succs src_v graph) with
    | [(_, b)] -> Some b
    | _ -> None

(* Find the unique successor with a certain branch form *)
let find_only_succ : vertex -> 'b -> ('a, 'b) graph -> vertex option =
  fun src_v b graph ->
    match vertex_succs src_v graph with
    | [(sv, b1)] when (b = b1) -> Some sv
    | _ -> None

(* Doesn't need to be unique successor *)
let find_succ : vertex -> 'b -> ('a, 'b) graph -> vertex option =
  fun src_v b graph ->
    match List.filter (fun (_, b1) -> b = b1) (vertex_succs src_v graph) with
    | [(sv, _)] -> Some sv
    | _ -> None

(* Find the unique ancestor with a certain branch form *)
let find_only_prev : vertex -> 'b -> ('a, 'b) graph -> vertex option =
  fun dst_v b graph ->
    match vertex_prevs dst_v graph with
    | [(pv, b1)] when (b = b1) -> Some pv
    | _ -> None

(* Does not need to be unique, just find one *)
let find_prev : vertex -> 'b -> ('a, 'b) graph -> vertex option =
  fun dst_v b graph ->
    match List.filter (fun (_, b1) -> b = b1) (vertex_prevs dst_v graph) with
    | [(pv, _)] -> Some pv
    | _ -> None

(* Remove an edge if it exists *)
let remove_basic_edge : (vertex * vertex) -> ('a, 'b) graph -> ('a, 'b) graph =
  fun (src_v, dst_v) graph ->
    match VMap.find_opt src_v graph.succs_map with
    | None -> graph
    | Some succs ->
      let succs1 = List.filter (fun (u, _) -> u <> dst_v) succs in
      { graph with
        succs_map = VMap.add src_v succs1 graph.succs_map }

(* Delete a vertex from the graph *)
let remove_vertex : vertex -> ('a, 'b) graph -> ('a, 'b) graph =
  fun v graph ->
    let prev_es = List.map (fun (p, _) -> (p, v)) (vertex_prevs v graph) in
    let succ_es = List.map (fun (s, _) -> (v, s)) (vertex_succs v graph) in
    let delete_es = prev_es @ succ_es in
    let graph1 = List.fold_left (fun g e -> remove_basic_edge e g) graph delete_es in
    { graph1 with
      succs_map = VMap.remove v graph1.succs_map;
      vertex_set = VSet.remove v graph1.vertex_set }

(* Reachable set *)
let rec reachable_set_bfs : ('a, 'b) graph -> vertex Q.queue -> VSet.t -> VSet.t =
  fun graph queue visited ->
    match Q.dequeue queue with
    | None -> visited
    | Some (v, queue1) ->
      let visited1 = VSet.add v visited in
      let uniq_succs =
        List.concat (List.map
          (fun (s, _) -> if (VSet.mem s visited1) || (Q.mem s queue1) then [] else [s])
          (vertex_succs v graph)) in
      let queue2 = Q.enqueue_list uniq_succs queue1 in
      reachable_set_bfs graph queue2 visited1

let reachable_set : vertex -> ('a, 'b) graph -> VSet.t =
  fun v graph ->
    reachable_set_bfs graph (Q.from_list [v]) VSet.empty

(* Trim the graph down to the reachable set wrt a root *)
let trim_graph : vertex -> ('a, 'b) graph -> ('a, 'b) graph =
  fun v graph ->
    let reachs = reachable_set v graph in
    let bads = VSet.diff graph.vertex_set reachs in
    VSet.fold (fun u g -> remove_vertex u g) bads graph

(* Printing things *)

let string_of_vertex : vertex -> string =
  fun v ->
    "v" ^ string_of_int v

let string_of_vertex_label
  : vertex -> ('a -> string) -> ('a, 'b) graph -> string =
  fun v string_of_a graph ->
    let v_str = string_of_vertex v in
    match vertex_label v graph with
    | None -> "(" ^ v_str ^ ", )"
    | Some a ->
      "(" ^ v_str ^ ",\n"
          ^ indent4 (string_of_a a) ^ ")"

let string_of_edge_simple : 'b edge -> string =
  fun (src_v, _, dst_v) ->
    "(" ^ string_of_vertex src_v ^ ", " ^ string_of_vertex dst_v ^ ")"

let string_of_edge : 'b edge -> ('b -> string) -> string =
  fun (src_v, b, dst_v) string_of_b ->
    "(" ^ string_of_vertex src_v ^ ", "
        ^ string_of_b b ^ ", "
        ^ string_of_vertex dst_v ^ ")"

let string_of_basic_edge : basic_edge -> string =
  fun (src_v, dst_v) ->
    "(" ^ string_of_vertex src_v ^ ", " ^ string_of_vertex dst_v ^ ")"

let string_of_basic_path : basic_path -> string =
  fun vs ->
    string_of_list_inline vs string_of_vertex

let string_of_succ : (vertex * 'b) -> ('b -> string) -> string =
  fun (succ_v, b) string_of_b ->
    "(" ^ string_of_vertex succ_v ^ ", "
        ^ string_of_b b ^ ")"

let string_of_vertex_succs
  : vertex -> (vertex * 'b) list -> ('b -> string) -> string =
  fun v succs string_of_b ->
    let succs_str =
      string_of_list_inline succs (fun s -> string_of_succ s string_of_b) in
    let v_str = string_of_vertex v in
    "(" ^ v_str ^ ",\n"
        ^ indent4 succs_str ^ ")"

(* Adjacency list printing of a graph *)
let string_of_graph_adjs : ('a, 'b) graph -> string =
  fun graph ->
    let adjs = List.of_seq (VMap.to_seq graph.succs_map) in
    let str_fun = fun (v, succs) ->
        "(" ^ string_of_int v ^ ", "
          ^ string_of_list_inline succs (fun (s, _) -> string_of_int s) ^ ")" in
    string_of_list_endline 2 2 adjs str_fun

  

(* Only shows the vertices and edge connections
 * Does not show label information -- hence why it's called simple *)
let string_of_graph_simple : ('a, 'b) graph -> string =
  fun graph ->
    (* Strings for the vertices *)
    let vs = VSet.elements graph.vertex_set in
    let vs_str = string_of_list_inline vs string_of_vertex in

    (* String for the successors *)
    let succs_map_binds = List.map (fun v -> (v, vertex_succs v graph)) vs in
    let succs_map_str =
      string_of_list_endline 2 1
        succs_map_binds
        (fun (v, succs) ->
          "(" ^ string_of_vertex v ^ ", "
              ^ string_of_list_inline
                  succs (fun s -> string_of_vertex (fst s)) ^ ")") in

    (* Time to put them together *)
    unlines
      [ "{ graph with";
        indent2 ("id = " ^ graph.graph_id ^ ";\n"); 
        indent2 "vertices =";
          indent4 vs_str ^ ";\n";
        indent2 "succs =";
          indent4 succs_map_str ^ ";";
          "}" ]

(* Prints the vertex and connections -- in addition to information about
 * the vertex labels and edge labels *)
let string_of_graph
  : ('a, 'b) graph -> ('a -> string) -> ('b -> string) -> string =
  fun graph string_of_a string_of_b ->
    (* Strings for the vertices *)
    let vs = VSet.elements graph.vertex_set in
    let simp_vs_str = string_of_list_inline vs string_of_vertex in

    let verb_vs_str =
      string_of_list_endline 2 2
        vs (fun v -> string_of_vertex_label v string_of_a graph) in

    (* String for the successors *)
    let succs_map_binds = List.map (fun v -> (v, vertex_succs v graph)) vs in
    let simp_succs_map_str =
      string_of_list_endline 2 1
        succs_map_binds
        (fun (v, succs) ->
          "(" ^ string_of_vertex v ^ ", "
              ^ string_of_list_inline
                  succs (fun s -> string_of_vertex (fst s)) ^ ")") in

    let verb_succs_map_str =
      string_of_list_endline 2 2
        succs_map_binds
          (fun (v, succs) -> string_of_vertex_succs v succs string_of_b) in

    (* Putting these together to dump *)
    unlines
      [ "{ graph with";
        indent2 ("id = " ^ graph.graph_id ^ ";\n");
        indent2 "vertices =";
          indent4 simp_vs_str ^ ";\n";
        indent2 "succs = ";
          indent4 simp_succs_map_str ^ ";\n";
        indent2 "label_map =";
          indent4 verb_vs_str ^ ";\n";
        indent2 "succs_labels =";
          indent4 verb_succs_map_str ^ ";";
        "}" ]


