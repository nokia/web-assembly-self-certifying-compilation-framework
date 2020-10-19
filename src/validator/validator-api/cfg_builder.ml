(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


open Wasm
open Source
open Wasm_utils
open Instr_graph
open Func_types
open Type_inference

module G = Digraph

(* Make your own CFG for a ufunc_ir *)

(* Quick instruction constructors *)
let int_to_var : int -> Ast.var =
  fun x -> noregion (Int32.of_int x)

let unreachable : Ast.instr = noregion Ast.Unreachable

let nop : Ast.instr = noregion Ast.Nop

let drop : Ast.instr = noregion Ast.Drop

let select : Ast.instr = noregion Ast.Select

let block : Ast.instr list -> Ast.instr =
  fun instrs -> noregion (Ast.Block ([], instrs))

let loop : Ast.instr list -> Ast.instr =
  fun instrs -> noregion (Ast.Loop ([], instrs))

let if_ : Ast.instr list -> Ast.instr list -> Ast.instr =
  fun instrs_t instrs_f -> noregion (Ast.If ([], instrs_t, instrs_f))

let br : int -> Ast.instr =
  fun x -> noregion (Ast.Br (int_to_var x))

let br_if : int -> Ast.instr =
  fun x -> noregion (Ast.BrIf (int_to_var x))

let br_table : int list -> int -> Ast.instr =
  fun xs y -> noregion (Ast.BrTable (List.map int_to_var xs, int_to_var y))

let call : int -> Ast.instr =
  fun x -> noregion (Ast.Call (int_to_var x))

let call_indirect : int -> Ast.instr =
  fun x -> noregion (Ast.CallIndirect (int_to_var x))

let local_get : int -> Ast.instr =
  fun x -> noregion (Ast.LocalGet (int_to_var x))

let local_set : int -> Ast.instr =
  fun x -> noregion (Ast.LocalSet (int_to_var x))

let local_tee : int -> Ast.instr =
  fun x -> noregion (Ast.LocalTee (int_to_var x))

let global_get : int -> Ast.instr =
  fun x -> noregion (Ast.GlobalGet (int_to_var x))

let global_set : int -> Ast.instr =
  fun x -> noregion (Ast.GlobalSet (int_to_var x))

let load : int -> Ast.instr =
  fun o ->
    let op : Ast.loadop =
      { ty = Types.I32Type;
        align = 0;
        offset = Int32.of_int o;
        sz = None } in
    noregion (Ast.Load op)

let store : int -> Ast.instr =
  fun o ->
    let op : Ast.storeop =
      { ty = Types.I32Type;
        align = 0;
        offset = Int32.of_int o;
        sz = None } in
    noregion (Ast.Store op)

let memory_grow : Ast.instr = noregion Ast.MemoryGrow

let memory_size : Ast.instr = noregion Ast.MemorySize

let const : int -> Ast.instr =
  fun n -> noregion (Ast.Const (int_to_literal n))

let test : Ast.IntOp.testop -> Ast.instr =
  fun op -> noregion (Ast.Test (Values.I32 op))

let compare : Ast.IntOp.relop -> Ast.instr =
  fun op -> noregion (Ast.Compare (Values.I32 op))

let unary : Ast.IntOp.unop -> Ast.instr =
  fun op -> noregion (Ast.Unary (Values.I32 op))

let binary : Ast.IntOp.binop -> Ast.instr =
  fun op -> noregion (Ast.Binary (Values.I32 op))

let convert : Ast.IntOp.cvtop -> Ast.instr =
  fun op -> noregion (Ast.Convert (Values.I32 op))

(* Constructing a graph *)

type cfg_data =
  { cfg_id : func_id;
    root_vertex : G.vertex;
    sink_vertex : G.vertex;
    adjacency_list
      : (G.vertex * (Ast.instr list) * ((G.vertex * branch) list)) list;
    types_table : Ast.type_ list;
    ftypes : Ast.var list;
  }

let empty_cfg_data : cfg_data =
  { cfg_id = "";
    root_vertex = G.null_vertex;
    sink_vertex = G.null_vertex;
    adjacency_list = [];
    types_table = [];
    ftypes = []
  }


let cfg_data_to_ufunc_ir : cfg_data -> ufunc_ir =
  fun data ->
    let adj_list = 
      List.map
        (fun (src_v, instrs, adjs) ->
          let label = ({ empty_block with instrs = instrs }, ()) in
          let adj_vs = List.map (fun (u, br) -> (u, (br, ()))) adjs in
          (src_v, label, adj_vs))
        data.adjacency_list in
    let graph = G.from_adjacency_list adj_list in
    { empty_ufunc_ir with
      func_id = data.cfg_id;
      types_table = data.types_table;
      ftypes = data.ftypes;
      root_vertex = data.root_vertex;
      sink_vertex = data.sink_vertex;
      body_graph = graph;
    }


