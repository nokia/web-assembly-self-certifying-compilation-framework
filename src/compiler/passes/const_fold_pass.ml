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

(* Does (int32) constant folding on each basic block *)


(* Convert a binop to its int32-valued function *)
let binop_int32_fun
  : Ast.IntOp.binop -> (int32 -> int32 -> int32) option = function
  | Ast.IntOp.Add -> Some Int32.add
  | Ast.IntOp.Sub -> Some Int32.sub
  | Ast.IntOp.Mul -> Some Int32.mul
  | Ast.IntOp.DivS -> Some Int32.div
  (* | Ast.IntOp.DivU -> Some Int32.unsigned_div *)
  | Ast.IntOp.RemS -> Some Int32.rem
  (* | Ast.IntOp.RemU -> Some Int32.unsigned_rem *)
  | Ast.IntOp.And -> Some Int32.logand
  | Ast.IntOp.Or -> Some Int32.logor
  | Ast.IntOp.Xor -> Some Int32.logxor
  | _ -> None


(* A one-step reduction of intructions, returning Some if possible *)
let reduce_instrs_once : Ast.instr list -> (Ast.instr list) option =
  fun instrs ->
    match instrs with
    (* Unary operations *)
    (* NOTE: Clz, Ctz, and Popcnt currently hard to support
     * due to OCaml int32 restrictions *)

    (* Binary operations *)
    | ({ it = Ast.Const { it = Values.I32 x } })
        :: ({ it = Ast.Const { it = Values.I32 y } })
        :: ({ it = Ast.Binary (Values.I32 op) })
        :: instrs_tl ->
      (match binop_int32_fun op with
      | Some f ->
        let res = int32_to_literal ((f x) y) in
        let instr0 = noregion (Ast.Const res) in
        Some (instr0 :: instrs_tl)
      | _ -> None)

    (* Nop *)
    | ({ it = Ast.Nop }) :: instrs_tl -> Some instrs_tl

    (* Dropping *)
    | hd :: ({ it = Ast.Drop }) :: instrs_tl ->
      (match hd.it with
      | Ast.Const _ | Ast.LocalGet _ | Ast.GlobalGet _
      | Ast.MemorySize -> Some instrs_tl

      | _ -> None)
    
    | _ -> None

(* Multistep reduction *)
let rec reduce_instrs : Ast.instr list -> Ast.instr list =
  fun instrs ->
    match reduce_instrs_once instrs with
    | Some instrs1 -> reduce_instrs instrs1
    | None -> 
      match instrs with
      | [] -> []
      | instrs0 :: instrs_tl -> instrs0 :: reduce_instrs instrs_tl

(* From a single vertex in a graph we can generate its proof *)
let vertex_adjacents
  : G.vertex -> ufunc_ir -> (G.vertex list) * G.vertex * (G.vertex list) =
  fun this_v func_ir ->
    let prevs = G.vertex_prevs this_v func_ir.body_graph in
    let succs = G.vertex_succs this_v func_ir.body_graph in
    (List.map fst prevs, this_v, List.map fst succs)

let adjacents_to_refinement_map
  : (G.vertex list) * G.vertex * (G.vertex list)
  -> refinement_map =
  fun (prevs, this_v, succs) ->
    let src_state0_kvs =
      List.map
        (fun pv ->
          let e0 = (pv, this_v) in
          ((e0, e0, Initial), full_state_pair_equiv))
        prevs in

    let tgt_state0_kvs =
      List.map
        (fun sv ->
          let ef = (this_v, sv) in
          ((ef, ef, Final), full_state_pair_equiv))
        succs in

    SourceEdge_TargetEdgeMap.of_seq
      (List.to_seq (src_state0_kvs @ tgt_state0_kvs))

let adjacents_to_frontier_map
  : (G.vertex list) * G.vertex * (G.vertex list)
  -> frontier_map =
  fun (prevs, this_v, succs) ->
    let tgt_front_kvs =
      List.map
        (fun pv ->
          ((pv, this_v), List.map (fun sv -> (this_v, sv)) succs))
        prevs in

    TargetEdgeMap.of_seq
      (List.to_seq (tgt_front_kvs))

let adjacents_to_path_match_map
  : (G.vertex list) * G.vertex * (G.vertex list)
  -> path_match_map =
  fun (prevs, this_v, succs) ->
    let path_match_kvs =
      List.concat
        (List.map (fun pv ->
          (List.map (fun sv ->
            let src_e0 = (pv, this_v) in
            let tgt_path = [pv; this_v; sv] in
            let src_path = [pv; this_v; sv] in
            ((src_e0, tgt_path), src_path))
          succs))
        prevs) in

    SourceEdge_TargetPathMap.of_seq (List.to_seq path_match_kvs)

let adjacents_to_checkpoints
  : (G.vertex list) * G.vertex * (G.vertex list)
  -> checkpoints =
  fun (prevs, this_v, _) ->
    List.map (fun pv -> ((pv, this_v), (pv, this_v))) prevs

let adjacents_to_proof
  : (G.vertex list) * G.vertex * (G.vertex list)
  -> ufunc_ir
  -> ufunc_ir
  -> proof =
  fun adjs src_ir tgt_ir ->
    let (_, this_v, _) = adjs in
    let refinement_map = adjacents_to_refinement_map adjs in
    let frontier_map = adjacents_to_frontier_map adjs in
    let path_match_map = adjacents_to_path_match_map adjs in
    let checkpoints = adjacents_to_checkpoints adjs in

    let src_instrs =
      (match G.vertex_label this_v src_ir.body_graph with
      | Some (block, _) -> block.instrs
      | _ -> []) in

    let tgt_instrs =
      (match G.vertex_label this_v tgt_ir.body_graph with
      | Some (block, _) -> block.instrs
      | _ -> []) in

    { empty_proof with
      func_id = tgt_ir.func_id;
      refinement_map = refinement_map;
      frontier_map = frontier_map;
      path_match_map = path_match_map;
      checkpoints = checkpoints;
      debugs =
        [ "const_fold_vertex_pass: "
            ^ tgt_ir.func_id ^ " @ " ^ G.string_of_vertex this_v;
          string_of_instrs_inline src_instrs;
          string_of_instrs_inline tgt_instrs
        ];
    }
    

(* The folding operation for a single vertex *)
let const_fold_vertex : G.vertex -> ufunc_ir -> ufunc_ir * proof =
  fun this_v func_ir0 ->
    let graph0 = func_ir0.body_graph in
    match G.vertex_label this_v graph0 with
    | None ->
      (prerr_endline
        ("const_fold_vertex: "
          ^ G.string_of_vertex this_v
          ^ " no label in "
          ^ graph0.graph_id);
        (func_ir0, empty_proof))
    | Some (block, ()) ->
      (* Constant fold *)
      let instrs1 = reduce_instrs block.instrs in
      if List.length block.instrs = List.length instrs1 then
        (func_ir0, empty_proof)
      else
        let block1 = { block with instrs = instrs1 } in
        let graph1 = G.add_vertex_label this_v (block1, ()) graph0 in
        let func_ir1 = { func_ir0 with body_graph = graph1 } in

        (* Generate proofs *)
        let adjs = vertex_adjacents this_v func_ir1 in
        let proof = adjacents_to_proof adjs func_ir0 func_ir1 in
        (func_ir1, proof)

(* Go over each vertex and do a merge *)
let const_fold_pass_fun
  : ufunc_ir -> pass_config -> ufunc_ir * pass_out =
  fun func_ir0 _ ->
    let (func_ir1, proofs) =
      List.fold_left
        (fun (ir0, pfs) v ->
          let (ir1, pf1) = const_fold_vertex v ir0 in
          (ir1, pf1 :: pfs))
        (func_ir0, [])
        (G.VSet.elements func_ir0.body_graph.vertex_set) in
    (func_ir1,
      { empty_pass_out with proofs = proofs; })

let const_fold_pass : upass =
  init_pass
    "const_fold"
    const_fold_pass_fun



