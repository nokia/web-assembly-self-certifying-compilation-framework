(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


open Wasm
open Source

open Wasm_utils
open Instr_graph
open Dominance
open Type_inference

open Debug

module S = Stack
module G = Digraph

(* A few things to help with SSA transformations *)
type phi_edge = G.vertex * int32

(* (x, e1...eN) represents a phi assignment x := e1,...,eN *)
type phi_entry = int32 * phi_edge list

(* maps each original variable x to a phi-assignment *)
type phi_vertex_map = phi_entry Int32Map.t

(* maps each CFG vertex to a phi-vertex-map *)
type phi_map = phi_vertex_map G.VMap.t

let lookup_phi_map : G.vertex -> phi_map -> phi_vertex_map =
  fun v phi_map ->
    match G.VMap.find_opt v phi_map with
    | None -> Int32Map.empty
    | Some m -> m

(* When the instruction graph is constructed from a function (func),
 * we need to track some of the information given to us from the func,
 * since we will need to be able to reconstruct the func given the graph.
 *
 * There are several invariants that we want to keep on the instr_graph
 * in order for it to be a valid IR.
 * One alternative would have been doing a lot of complicated type definitions
 * to use the OCaml's type system to help enforce these,
 * but we opt for this approach instead. *)
type func_id = string

type ('a, 'b) func_ir =
  { func_id : func_id;
    func_index : int;
    ftype : Ast.var;

    (* Data for typing information of other functions of the same module
     * The ftypes are ordered by the indices of the functions and in turn
     * index into types_table *)
    types_table : Ast.type_ list;
    ftypes : Ast.var list;

    (* This function's graph data *)
    func_locals : Types.value_type list;
    root_vertex : G.vertex;
    sink_vertex : G.vertex;
    body_graph : ('a, 'b) instr_graph;
    phi_map : phi_map;
    region : region
  }

type ufunc_ir = (unit, unit) func_ir

let empty_func_type : Ast.type_ = noregion (Types.FuncType ([], []))

let empty_ufunc_ir : ufunc_ir =
  { func_id = "";
    func_index = 0;
    ftype = noregion 0l;

    types_table = [];
    ftypes = [];

    func_locals = [];
    root_vertex = G.null_vertex;
    sink_vertex = G.null_vertex;
    body_graph = G.empty_graph;
    phi_map = G.VMap.empty;
    region = no_region
  }

(* Some of these invariants on an valid IR include:
 *  - block.instrs must be plain / "straight-line" code without control flow
 *  - every block.instr with Call or CallInd must be a singleton instruction
 *    the aim of this is to make inter-procedural analysis later easier
 *  - the trap vertex has only Unreachable as the singleton instruction.
 *)
let rec is_basic_instrs : Ast.instr list -> bool = function
  | [] -> true
  | hd_instr :: tl_instrs ->
    match hd_instr.it with
    | Ast.Block _ | Ast.Loop _
    | Ast.Br _ | Ast.BrIf _ | Ast.BrTable _
    | Ast.Call _ | Ast.CallIndirect _ -> false
    | _ -> is_basic_instrs tl_instrs

let calling_block : block -> bool =
  fun block ->
    match block.instrs with
    | hd_instr :: _ ->
      (match hd_instr.it with
      | Ast.Call _ | Ast.CallIndirect _ -> true
      | _ -> false)
    | _ -> false

(* Check to make sure that a func IR is valid.
 * This includes checking to make sure that every vertex is labeled
 * with either straightline or a calling instruction.
 * More restrictions may be applied later. *)
let func_ir_valid : ('a, 'b) func_ir -> bool =
  fun func_ir ->
    let graph_oks =
      List.map
        (fun v ->
          match G.vertex_label v func_ir.body_graph with
          | None -> false
          | Some (block, _) ->
            is_basic_instrs block.instrs || calling_block block)
        (G.vertices func_ir.body_graph) in
    let graph_ok = List.fold_left (&&) true graph_oks in
    graph_ok

(* Set up a call for the instrs_to_uinstr_graph *)
let func_to_ufunc_ir
  : Ast.func
  -> func_id
  -> int
  -> (Ast.type_ list * Ast.var list)
  -> ufunc_ir =
  fun func func_id func_ind (types_table, ftypes) ->
    let f = func.it in
    let graph = { G.empty_graph with graph_id = func_id } in

    (* Allocate root block *)
    let (root_v, graph1) = G.alloc_vertex (empty_block, ()) graph in

    (* Allocate sink block *)
    let (sink_v, graph2) = G.alloc_vertex (empty_block, ()) graph1 in

    (* Allocate trap block and connect it to the sink block.
     * We do this since we want one root and one sink vertex in the func IR,
     * and the Ast.Unreachable behavior guarantees that trapping happens *)
    let graph3 = graph2 in

    (* let graph4 = G.add_edge (trap_v, (Jump, ()), sink_v) graph3 in *)
    let graph4 = graph3 in

    (* Initial target stack *)
    let tgt_vs = S.from_list [sink_v] in

    (* Connect the root block to a new fresh basic block *)
    let (this_v, graph5) = G.alloc_vertex (empty_block, ()) graph4 in
    let graph6 = G.add_edge (root_v, (Jump, ()), this_v) graph5 in

    (* We now have enough information for the graph meta information *)
    let meta =
      { empty_build_meta with
        branch_targets = tgt_vs;
        this_vertex = this_v;
        sink_vertex = sink_v; } in
    let body_instrs = f.body in

    (* ... And to call the instrs_to_uinstr_graph *)
    let graph7 = instrs_to_uinstr_graph body_instrs graph6 meta in
    let graph8 = G.trim_graph root_v graph7 in
    let func_ir =
      { empty_ufunc_ir with
        func_id = func_id;
        func_index = func_ind;
        ftype = f.ftype;

        types_table = types_table;
        ftypes = ftypes;

        func_locals = f.locals;
        root_vertex = root_v;
        sink_vertex = sink_v;
        body_graph = graph8;
        region = func.at } in

    (* *)
    
    func_ir

(* ********** *)

(* We also need functionalities to convert uinstr_graph back to an ast/func.
 * The first step of doing this is to collapse an entire uinstr_graph back
 * into a single instruction (block).
 * We won't stop invvalid func IR's from being converted
 * since the conversion process will still be fine,
 * but what is fed in should ideally be valid func IR's. *)
let func_ir_to_func : ('a, 'b) func_ir -> Ast.func =
  fun func_ir ->
    let ty_map = lookup_func_type func_ir.types_table in
    let Types.FuncType (fty_ins, fty_outs) = ty_map func_ir.ftype in

    (* Disabled for now: code that packs CFG into WAST *)
    (*
    let body_graph = func_ir.body_graph in
    let root_v = func_ir.root_vertex in
    let def_ty =
      (match (fty_ins, fty_outs) with 
      | (_, fty_o :: _) -> fty_o
      | (fty_i :: _, _) -> fty_i
      | _ -> i32ty) in
    let body_instrs = instr_graph_to_instrs body_graph root_v ty_map def_ty in
    *)
    let body_instrs = [] in

    { Ast.ftype = func_ir.ftype;
      Ast.locals = func_ir.func_locals;
      Ast.body = body_instrs }
    @@ func_ir.region


