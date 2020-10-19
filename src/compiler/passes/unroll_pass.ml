(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


(* Realy simple loop unrolling
 * The goal here is to identify one (1, uno) natural loop, and unroll it once.
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

open Dominance

module G = Digraph
module Q = Queue
module List = List_utils
module String = String_utils


(* Meant to hold information about where old vertices are mapped to in new ones *)
type vertex_map = G.vertex G.VMap.t

(* Find natural loops, if available.
 * The duplication algorithm is as follows:
 *
 *  1. Identify a (head, tail pair), where
 *      - The head dominates the tail
 *      - The tail has an edge to the head
 *      - Everything in "between" the head and tail are to be copied
 *
 *  2. Gather all vertices between the (head, tail)
 *
 *  3. Populate a vertex_map with (old -> new) mappings
 *      - One can also flip the assoc list to obtain an (new -> old) mapping
 *
 *  4. Surgically stitch the two graphs together.
 *
 *)

(* A header dominates the tail, but the tail has a loop back.
 * Eveyrthing sandwhiched in-between is subject to duplication *)
let is_header_tail_pair : (G.vertex * G.vertex) -> ('a, 'b) G.graph -> dom_data -> bool =
  fun (head, tail) graph dom_data ->
    let doms_b = dominates head tail dom_data in
    let loops_b = List.mem head (List.map fst (G.vertex_succs tail graph)) in
    doms_b && loops_b
    

let find_natural_loop : ('a, 'b) G.graph -> dom_data -> (G.vertex * G.vertex) option =
  fun graph dom_data ->
    let vs = List.of_seq (G.VSet.to_seq graph.vertex_set) in
    let vpairs =
      List.concat (List.map
        (fun v -> List.map (fun u -> (v, u)) (List.filter (fun x -> x <> v) vs)) vs) in
    let htpairs = List.filter (fun p -> is_header_tail_pair p graph dom_data) vpairs in
    match htpairs with
    | [] -> None
    | (p :: _) -> Some p


(* Do a BFS search backwards from the tail vertex *)
let rec gather_loop_vertices_bfs
  : G.vertex -> G.vertex -> ('a, 'b) G.graph -> G.VSet.t -> G.VSet.t =
  fun v head graph visited ->
    if v = head then
      visited
    else
      let prevs = List.map fst (G.vertex_prevs v graph) in
      let unvisited =
        List.concat (List.map (fun p -> if G.VSet.mem p visited then [] else [p]) prevs) in
      let visited1 = G.VSet.add v visited in
      if G.VSet.subset (G.VSet.of_seq (List.to_seq unvisited)) visited1 then
        visited1
      else
        List.fold_left (fun accs p -> gather_loop_vertices_bfs p head graph accs) visited1 unvisited

let gather_loop_vertices : G.vertex -> G.vertex -> ('a, 'b) G.graph -> G.VSet.t =
  fun tail head graph ->
    gather_loop_vertices_bfs tail head graph (G.VSet.singleton head)


(* Allocate vertices, and connect the resulting graph *)
let connect_succs
  : (G.vertex * G.vertex)
    -> (G.vertex * G.vertex) list
    -> ('a, 'b) G.graph
    -> G.VSet.t
    -> G.basic_edge TargetEdgeMap.t
    -> ('a, 'b) G.graph * (G.basic_edge TargetEdgeMap.t) =
  fun (oldv, newv) apairs graph loop_vset t2s_emap ->
    List.fold_left
      (fun (g0, emap0) (olds, b) ->
        (* Case the successor has something in the loop vertices *)
        if G.VSet.mem olds loop_vset then
          let news = List.assoc olds apairs in
          let g1 = G.add_edge (newv, b, news) g0 in
          (* New back-connection from target *)
          let emap1 = TargetEdgeMap.add (newv, news) (oldv, olds) emap0 in
          (* Also the original back-connection *)
          let emap2 = TargetEdgeMap.add (oldv, olds) (oldv, olds) emap1 in
          (g1, emap2)

        (* Otherwise the successor is not newly allocated and the pairing is just original *)
        else
          let _ = prerr_debug ("connect succs: non loop_vset " ^ G.string_of_basic_edge (oldv, olds)) in
          (g0, emap0))
      (graph, t2s_emap)
      (G.vertex_succs oldv graph)

(* Returns:
 *  - Modified graph
 *  - src_v -> tgt_v mapping that tells which allocation corresponds to which vertices
 *  - tgt_e -> src_e mapping telling how the new target edges correspond back
 *)
let duplicate_subgraph
  : ('a, 'b) G.graph
    -> G.VSet.t
    -> ('a, 'b) G.graph * ((G.vertex * G.vertex) list) * (G.basic_edge TargetEdgeMap.t) =
  fun graph0 loop_vset ->
    let (graph1, apairs) =
      G.VSet.fold (fun v0 (g0, aps) ->
        match G.vertex_label v0 g0 with
        | None -> prerr_endline ("duplicate_subgraph: not found " ^ G.string_of_vertex v0); (g0, [])
        | Some lbl ->
          let (v1, g1) = G.alloc_vertex lbl g0 in
          (g1, (v0, v1) :: aps))
        loop_vset
        (graph0, []) in

    let t2s_emap1 = TargetEdgeMap.empty in

    let (graph2, t2s_emap2) =
      List.fold_left
        (fun (g0, emap0) (ov, nv) -> connect_succs (ov, nv) apairs g0 loop_vset emap0)
        (graph1, t2s_emap1)
        apairs in

    (graph2, apairs, t2s_emap2)

(*
 *    [ head0 ]
 *        |
 *    [ tail0 ]
 *        |
 *    [ head1 ]
 *        |
 *    [ tail1 ]
 *        \_______ (to head0)
 *
 *)
let stitch_loops
  : (G.vertex * G.vertex)
    -> (G.vertex * G.vertex)
    -> ('a, 'b) G.graph
    -> G.basic_edge TargetEdgeMap.t
    -> ('a, 'b) G.graph * (G.basic_edge TargetEdgeMap.t) =
  fun (head0, tail0) (head1, tail1) graph0 t2s_emap0 ->
    match G.edge_label (tail0, head0) graph0 with
    | None ->
      (prerr_endline ("stitch_loops: no edge label " ^ G.string_of_basic_edge (tail0, head0));
      graph0, t2s_emap0)

    | Some b ->
      let graph1 = G.remove_basic_edge (tail0, head0) graph0 in
      let graph2 = G.remove_basic_edge (tail1, head1) graph1 in
      let graph3 = G.add_edge (tail0, b, head1) graph2 in
      let graph4 = G.add_edge (tail1, b, head0) graph3 in
      let t2s_emap1 = TargetEdgeMap.add (tail0, head1) (tail0, head0) t2s_emap0 in
      let t2s_emap2 = TargetEdgeMap.add (tail1, head0) (tail0, head0) t2s_emap1 in
      
      (graph4, t2s_emap2)

let find_assoc_vertex : G.vertex -> (G.vertex * G.vertex) list -> G.vertex =
  fun src_v apairs ->
    match List.assoc_opt src_v apairs with
    | None -> src_v
    | Some tgt_v -> tgt_v

(* Proof generation
 *
 *      | (from T0)
 *      | (A)                   | (C)
 *    [ H0 ]                  [ H0 ]
 *      |                       |
 *      |                     [ T0 ]
 *    [ T0 ]                    | (D)
 *      | (B)                 [ H1 ]
 *      | (to H0)               |
 *                            [ T1 ]
 *                              | (E)
 *
 * The paths are:
 *    (C, D) -> (A, B)
 *    (D, E) -> (A, B)
 *    
 *)

let uf_states_equiv : state * state -> formula =
  fun (state0, state1) ->
    CommentForm ("states_equiv",
      AndForm
      [ ArrsEqForm (values state0, values state1);
        PtrsRelForm
          (stack_pointer state0,
           IntEq,
           stack_pointer state1);
        ArrsEqForm (locals state0, locals state1);
        ArrsEqForm (globals state0, globals state1);
        SymEqForm (uf_memory state0, uf_memory state1) ])

let unroll_proof
  : ufunc_ir
    -> ufunc_ir
    -> (G.vertex * G.vertex)
    -> (G.vertex * G.vertex)
    -> (G.vertex * G.vertex) list
    -> G.basic_edge TargetEdgeMap.t
    -> proof =
  fun src_ir tgt_ir (head0, tail0) (head1, tail1) apairs t2s_emap ->
    let tgt_graph = tgt_ir.body_graph in

    (* Everything gets its own checkpoint *)
    let checkpoints = List.map (fun (a, b) -> (b, a)) (TargetEdgeMap.bindings t2s_emap) in 

    (* The frontier are the one-successors *)
    let frontier_adjs : (G.basic_edge * (G.basic_edge list)) list =
      List.map
        (fun (v0, v1) ->
          let raw_v2s = List.map fst (G.vertex_succs v1 tgt_graph) in
          (* Only want those relevant to the loop *)
          let v2s = List.filter (fun v2 -> TargetEdgeMap.mem (v1, v2) t2s_emap) raw_v2s in
          ((v0, v1), List.map (fun v2 -> (v1, v2)) v2s))
        (List.map fst (TargetEdgeMap.bindings t2s_emap)) in

    (*
    let _ = prerr_endline "\n\nfrontier data dump" in
    let _ = List.iter
      (fun (t, fs) ->
        prerr_endline (G.string_of_basic_edge t ^ " -> " ^
              String.string_of_list_inline fs G.string_of_basic_edge))
      frontier_adjs in
    *)

    let frontier_map = TargetEdgeMap.of_seq (List.to_seq frontier_adjs) in

    (* To generate path matching,find all paths for both parts of the tgt,
     * and use flipped apairs to find the corresponding src path *)
    let apairs_flip = List.map (fun (a, b) -> (b, a)) apairs in

    let path_match_adjs =
      List.concat (List.map
        (fun ((tgt_v0, tgt_v1), (src_v0, src_v1)) ->
          let tgt_v2s = List.map fst (G.vertex_succs tgt_v1 tgt_graph) in
          List.map
            (fun tgt_v2 ->
              let path_lhs = ((src_v0, src_v1), [tgt_v0; tgt_v1; tgt_v2]) in
              let path_rhs = [src_v0; src_v1; find_assoc_vertex tgt_v2 apairs_flip] in
              (path_lhs, path_rhs))
            tgt_v2s)
        (TargetEdgeMap.bindings t2s_emap)) in

    let path_match_map = SourceEdge_TargetPathMap.of_seq (List.to_seq path_match_adjs) in

    (* Refinements are just equality; use the t2s_emap to generate this because only edge info needed *)
    (* Important: remember that the refinement edge pairing is (source, target)! *)
    let refinement_adjs =
      List.concat (List.map
        (fun ((tgt_v0, tgt_v1), (src_v0, src_v1)) ->
          let ref1 =
            if is_call_vertex tgt_v1 tgt_graph then
              [(((src_v0, src_v1), (tgt_v0, tgt_v1), PreCall), uf_states_equiv)]
            else
              [] in

          let ref2 =
            if is_call_vertex tgt_v0 tgt_graph then
              [(((src_v0, src_v1), (tgt_v0, tgt_v1), PostCall), uf_states_equiv)]
            else
              [] in

          let ref3 =
            [(((src_v0, src_v1), (tgt_v0, tgt_v1), Initial), uf_states_equiv);
              (((src_v0, src_v1), (tgt_v0, tgt_v1), Final), uf_states_equiv) ] in

          ref1 @ ref2 @ ref3)
        (TargetEdgeMap.bindings t2s_emap)) in

    (*
    let _ = prerr_endline ("DUMPING PATH MATCH DATA") in
    let _ = List.iter
      (fun ((src_e, tgt_path), src_path) ->
        prerr_endline ("("
          ^ G.string_of_basic_edge src_e
            ^ ", " ^ G.string_of_basic_path tgt_path ^ ") -> "
          ^ G.string_of_basic_path src_path))
      path_match_adjs in
    *)


    let refinement_map = SourceEdge_TargetEdgeMap.of_seq (List.to_seq refinement_adjs) in

    let proof =
      { empty_proof with
        transform = "Unroll";
        interpretation = INone;

        func_id = tgt_ir.func_id;
        checkpoints = checkpoints;
        refinement_map = refinement_map;
        frontier_map = frontier_map;
        path_match_map = path_match_map;
      } in
    proof


(*
    (* State pair equivalence *)

    (* The first one we can pass in an empty apairs because the mapping is identical *)
    let call_refinement_adjs_0 =
      List.concat (List.map (fun p ->
        generate_call_refinement_adjs p tgt_ir []) tgt_paths_0) in

    let call_refinement_adjs_1 =
      List.concat (List.map (fun p ->
        generate_call_refinement_adjs p tgt_ir apairs) tgt_paths_1) in

    let refinement_adjs =
      [ ((src_back_e, tgt_start_e, Initial), state_pair_equiv);
        ((src_back_e, tgt_mid_e, Final), state_pair_equiv);

        ((src_back_e, tgt_mid_e, Initial), state_pair_equiv);
        ((src_back_e, tgt_start_e, Final), state_pair_equiv) ] in

    let refinement_map =
      SourceEdge_TargetEdgeMap.of_seq (List.to_seq
        (refinement_adjs @ call_refinement_adjs_0 @ call_refinement_adjs_1)) in

    let proof =
      { empty_proof with
        transform = "Unroll";
        interpretation = INone;

        func_id = tgt_ir.func_id;
        checkpoints = checkpoints;
        refinement_map = refinement_map;
        frontier_map = frontier_map;
        path_match_map = path_match_map;
      } in
    proof
  *)

let unroll_pass_fun : ufunc_ir -> pass_config -> ufunc_ir * pass_out =
  fun src_ir pass_conf ->
    let src_graph = src_ir.body_graph in
    
    let dom_data = graph_to_dom_data src_graph src_ir.root_vertex in
    let pair_opt = find_natural_loop src_graph dom_data in
    match pair_opt with
    | None ->
      (print_debug "None natural loop found"; (src_ir, empty_pass_out))
        
    | Some (head0, tail0) ->
      let loop_vset = gather_loop_vertices tail0 head0 src_graph in

      let (graph1, apairs, t2s_emap1) = duplicate_subgraph src_graph loop_vset in
      let (head1, tail1) = (List.assoc head0 apairs, List.assoc tail0 apairs) in

      (* Remove a tail0 -> head0 back edge that no longer exists in the target graph *)
      let t2s_emap1b = TargetEdgeMap.remove (tail0, head0) t2s_emap1 in

      let (graph2, t2s_emap2) = stitch_loops (head0, tail0) (head1, tail1) graph1 t2s_emap1b in

      (*
      let _ = prerr_endline (G.string_of_graph_adjs src_graph) in
      let _ = prerr_endline ("\n\n*******************************************\n\n") in
      let _ = prerr_endline (G.string_of_graph_adjs graph2) in
      *)

      (*
      let _ =
        List.iter (fun (tgte, srce) ->
          prerr_endline (G.string_of_basic_edge tgte ^ " -> " ^ G.string_of_basic_edge srce))
          (List.of_seq (TargetEdgeMap.to_seq t2s_emap2)) in

      *)
      (*
      let _ = exit 0 in
      *)

      let tgt_ir = { src_ir with body_graph = graph2 } in
      let pass_out =
        { empty_pass_out with 
          pass_id = "unroll";
          proofs = [unroll_proof src_ir tgt_ir (head0, tail0) (head1, tail1) apairs t2s_emap2]
        } in

      (tgt_ir, pass_out)

let unroll_pass : upass =
  init_pass
    "unroll"
    unroll_pass_fun




