(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)

open Wasm
open Wasm_utils
open Instr_graph
open Func_types
open Script_types
open Source
open Debug

module G = Digraph
module String = String_utils

(* This is the types that are used to represent states for WASM programs.
 * All ids here are typed as strings, but must also be SMTLIB-valid ids.
 * We make this a separate file from proof_types.ml because this
 * is about state-specific manipulation and data structures over the
 * func_ir that do not need formulas; which the proof_types.ml defines *)

(* A Walue :) *)
type wasm_value = Ast.literal
type smtid = string

(* We need to handle symbolic pointers, and so we go an indirect route;
 * The types need to be general enough to encode interleaving of:
 *  value stack; local variables; global variables; and linear memory *)
type pointer =
  | IntPtr of int 
  | Int32Ptr of int32
  | IdPtr of smtid (* pointer identified by an id *)
  | VarPtr of Ast.var
  | OffsetPtr of pointer * int32
  | IntOffsetPtr of pointer * int                            
  | CastedPtr of value
  | NullPtr

(* The different forms in which a value is accessed in WASM *)
and value =
  | IntVal of int 
  | Int32Val of int32
  | WasmVal of wasm_value
  | TestOpVal of Ast.testop * value
  | RelOpVal of value * Ast.relop * value
  | UnOpVal of Ast.unop * value
  | BinOpVal of value * Ast.binop * value
  | CvtOpVal of Ast.cvtop * value
  | SelectVal of array_ * pointer
  | UFVal of smtid * (value list)   (* UFVal <name> <values> represents the result of uninterpreted function <name> on a list of values. *)
  | ArrayVal of array_

(* Arrays -- as in the theory of arrays
 * This is how we will model the
 *  value stack; local variables; global variables; memory *)
and array_ =
  | IdArr of string (* Array identified by an id *)
  | StoreArr of array_ * pointer * value

(* Some value definitions *)
let zero_int32_val : value = Int32Val 0l

(* The state of a program during execution as determined by the
 * control flow graph (the instrs_graph).
 * A state occurs between edges, and we identify a state with the
 * execution immediately AFTER the branch instruction that sits on the edge.
 *  
 *      | instr m |
 *  v0  | ....... |
 *      -----------  <- vertex v0
 *           |
 *       v0v1_branch
 *           |       <- state { (v0, v1); v0v1_branch; step = Active 0 }
 *      -----------
 *  v1  | instr 1 |
 *      |         |  <- state { (v0, v1); v0v1_branch; step = 1 }
 *      | instr 2 |
 *      |         |  <- state { (v0, v1); v0v1_branch; step = 2 }
 *      | ....... | 
 *      | instr n |
 *      -----------  <- state { (v0, v1); v0v1_branch; step = n }
 *           |
 *       v1v2_branch
 *           |       <- state { (v1, v2); v1v2_branch; step = n + 1 }
 *      -----------
 *  v2  | instr 1 |
 *      | ....... |
 *)

(* Status defines whether a state is active or a final state;
 * A state is uniquely specified by the CFG edge and this status
 * (plus maybe slightly more additional information)
 * because what specifying from the CFG can tell us is limited
 * to little more than pure graph data *)
type step_status =
  | Active of int
  | Stopped

type state =
  { this_edge : G.basic_edge;
    step_status : step_status;
    tag : string;
  }

let empty_state : state =
  { this_edge = (G.null_vertex, G.null_vertex);
    step_status = Active 0;
    tag = "TAG";
  }

let source_tag : string = "SRC"
let target_tag : string = "TGT"

(* Initialize the state given vertices and stuff *)
let init_state0 : G.basic_edge -> string -> state =
  fun this_e tag ->
    { empty_state with
      this_edge = this_e;
      step_status = Active 0;
      tag = tag;
    }

let init_statef : G.basic_edge -> string -> state =
  fun this_e tag ->
    { empty_state with
      this_edge = this_e;
      step_status = Stopped;
      tag = tag
    }

(* Tag a state with a particular string - ie update the tag *)
let tag_state : state -> string -> state =
  fun state tag ->
    { state with tag = tag }

(* Action labels *)
type action =
  | BasicAct of Ast.instr
  | JumpAct of branch * G.vertex (* vertex we are branching to *)
  | PhiAct of G.vertex * G.vertex (* (old_v, new_v) *)
  | CallAct of Ast.var
  | CallIndirectAct of Ast.var
  | StopAct

(* Calculates the next state based on the action *)
let next_state : state -> action -> state =
  fun state0 act ->
    match (state0.step_status, act) with
    | (Active n, BasicAct _) ->
      { state0 with
        step_status = Active (n + 1)
      }

    | (Active n, JumpAct (_, next_v)) ->
      let (base_v, this_v) = state0.this_edge in
      { state0 with
        this_edge = (this_v, next_v);
        step_status = Active (n + 1)
      }

    | (Active n, PhiAct _) ->
      { state0 with
        step_status = Active (n + 1)
      }

    | (Active n, CallAct x) ->
      { state0 with
        step_status = Active (n + 1)
      }

    | (Active n, CallIndirectAct _) ->
      { state0 with
        step_status = Active (n + 1)
      }

    | (Active _, StopAct) ->
      { state0 with step_status = Stopped }

    | (Stopped, _) ->
      (prerr_debug ("next_state: cannot advance final state"); empty_state)

(* Some stuff for generating strings (smtids) that are acceptable
 * as identifiers in SMTLIB format *)

(* From the constituents of a state we can extract a lot of string id's *)
let vertex_smtid : G.vertex -> smtid =
  fun v -> "v" ^ string_of_int v

let branch_smtid : branch -> smtid = function
  | Jump-> "br"
  | JumpIf true -> "if_true"
  | JumpIf false -> "if_false"
  | JumpBrIf true -> "brif_true"
  | JumpBrIf false -> "brif_false"
  | JumpIndex ind -> "branchindex_" ^ Int32.to_string ind
  | JumpDefault size -> "branchdefault_" ^ Int32.to_string size

(* A pair of edges on a graph along with the status (Active / Stopped)
 * uniquely determines a state (to the SMT solver)
 * The rational behind this design is to make it easier for annotating
 * the CFG, where little more than raw graph information can be given. *)
let step_status_smtid : step_status -> smtid = function
  | Active n -> "active_" ^ string_of_int n
  | Stopped -> "final"

let state_smtid : state -> smtid =
  fun state ->
    state.tag
      ^ "_" ^ (vertex_smtid (fst state.this_edge))
      ^ "" ^ (vertex_smtid (snd state.this_edge))
      ^ "_s" ^ step_status_smtid (state.step_status)

let values_smtid : state -> smtid =
  fun state ->
    "values_" ^ state_smtid state

let stack_pointer_smtid : state -> smtid =
  fun state ->
    "pointer_" ^ state_smtid state
 
let locals_smtid : state -> smtid =
  fun state ->
    "locals_" ^ state_smtid state

let globals_smtid : state -> smtid =
  fun state ->
    "globals_" ^ state_smtid state

let memory_smtid : state -> smtid =
  fun state ->
    "memory_" ^ state_smtid state
    
(* Easy way to actually access the array_ types *)
let values : state -> array_ =
  fun state ->
  IdArr (values_smtid state)


let stack_pointer : state -> pointer =
  fun state ->
    IdPtr (stack_pointer_smtid state)

let locals : state -> array_ =
  fun state ->
    IdArr (locals_smtid state)

let globals : state -> array_ =
  fun state ->
    IdArr (globals_smtid state)


let full_memory : state -> array_ =
  fun state ->
    IdArr (memory_smtid state)


let uf_memory : state -> value =
  fun state ->
  UFVal (memory_smtid state, [])

(* Pointer arithmetics *)
let rec offset_pointer : pointer -> int32 -> pointer =
  fun ptr n -> 
    match ptr with
    | OffsetPtr (p, x) -> OffsetPtr (p, I32.add x n)
    | _ -> OffsetPtr (ptr, n)
  
let succ_pointer : pointer -> pointer =
  fun ptr ->
    offset_pointer ptr 1l

let prev_pointer : pointer -> pointer =
  fun ptr ->
    offset_pointer ptr (Int32.neg 1l)

(* The first edge of a path *)
let path_start_edge : G.basic_path -> G.basic_edge =
  fun path ->
    match path with
    | (v0 :: v1 :: _) -> (v0, v1)
    | _ -> (prerr_debug ("path_start_edge: bad"); G.null_basic_edge)

(* The final edge of a path *)
let path_final_edge : G.basic_path -> G.basic_edge =
  fun path ->
    match List.rev path with
    | (vn :: vm :: _) -> (vm, vn) (* note the flip *)
    | _ -> (prerr_debug ("path_final_edge: bad"); G.null_basic_edge)

(* The initial state *)
let path_start_state : G.basic_path -> string -> state =
  fun path tag ->
    init_state0 (path_start_edge path) tag

let path_final_state : G.basic_path -> string -> state =
  fun path tag ->
    init_statef (path_final_edge path) tag

(* Actions of a vertex *)
let vertex_actions : G.vertex -> ufunc_ir -> action list =
  fun v func_ir ->
    match G.vertex_label v func_ir.body_graph with
    (* The case where label does not exist *)
    | None -> (prerr_debug "vertex_actions: None"; [])

    (* The case where we have a single call instruction *)
    | Some ({ instrs = [{ it = Ast.Call x }] }, _) ->
      (match G.vertex_succs v func_ir.body_graph with
      | (sv, (Jump, ())) :: [] -> [CallAct x]
      | _ ->
        (prerr_debug
          ("vertex_actions: Call at "
            ^ G.string_of_vertex v
            ^ " not followed by single successor");
          []))

    (* The case where every instruction is basic *)
    | Some (block, _) ->
      List.map
        (fun i -> match i.it with
          | Ast.Call x -> CallAct x
          | Ast.CallIndirect x -> CallIndirectAct x
          | _ when (is_basic_instr i) -> BasicAct i
          | _ ->
            (prerr_debug ("vertex_action: non-basic " ^ string_of_instr_inline i);
            BasicAct i))
        block.instrs

(* Actions of an edge, does *not* include the phi vertex *)
let edge_actions : G.basic_edge -> ufunc_ir -> action list =
  fun (src_v, dst_v) func_ir ->
    match G.edge_label (src_v, dst_v) func_ir.body_graph with
    | None ->
      (prerr_debug
        ("edge_actions: None @ " ^ G.string_of_basic_edge (src_v, dst_v));
      [])
    | Some (br, _) -> [JumpAct (br, dst_v)]

(* Unlike path_actions, gets the action of every thing in this path.
 * When we say paths here, we mean paths in the sense of what is used
 * for a proof: for these the first and last edges are special markers *)
let rec path_actions_raw : G.basic_path -> ufunc_ir -> action list =
  fun path func_ir ->
    match path with
    | [] -> []
    | v :: [] -> vertex_actions v func_ir
    | v0 :: (v1 :: path_tl) ->
      (vertex_actions v0 func_ir)
        @ (edge_actions (v0, v1) func_ir)
        @ [PhiAct (v0, v1)]
        @ path_actions_raw (v1 :: path_tl) func_ir

(* The type of path actions that we want to suit how we specify proofs.
 *
 *    [v0] --> [*v1] --> ... -> [vm] --> [*vn]
 *              ^                         ^
 * Starred ( * ) points are where actions begin and end:
 *   (v0, v1, ind_0) is the first state and action begins here
 *   (vm, vn, ind_0) is the penultimate state; we act over the (vm, vn) edge
 *
 * The last action along a path is the StopAct,
 * which serves to mark the penultimate state's final flag to true.
 * The reason for this indirection is to make it easier to declare
 * the final state along a path -- which is useful when encoding proofs.
 *)
let rec path_actions : G.basic_path -> ufunc_ir -> action list =
  fun path func_ir ->
    match path with
    (* Completely empty path *)
    | [] -> []
    | [_] -> []
    | (v0 :: v1 :: path_tl) ->
      let main_vs = v1 :: path_tl in
      match List.rev main_vs with
      | (vn :: vm :: mid_rev) ->
        let act_vs = List.rev (vm :: mid_rev) in
        (PhiAct (v0, v1))
          :: (path_actions_raw act_vs func_ir)
          @ (edge_actions (vm, vn) func_ir)
          @ [StopAct]
      | _ -> []

(* All states along a path, as a function of the path_actions *)
let path_states : G.basic_path -> ufunc_ir -> string -> state list =
  fun path func_ir tag ->
    let state0 = path_start_state path tag in
    let acts = path_actions path func_ir in
    let (_, states_rev) =
      List.fold_left
        (fun (s0, accs) act ->
          let s1 = next_state s0 act in (s1, s1 :: accs))
        (state0, [state0]) acts in
    List.rev states_rev

(* Generate a phi state for each entry of the phi map *)
let phi_state : string -> (G.vertex * int32) -> (G.vertex * int32) -> state =
  fun tag (old_v, old_x) (new_v, new_x) ->
  (* Printf.printf "\n Debug tag = %s" tag;*)
    let state_tag = tag ^ "_Phi_" ^ Int32.to_string old_x ^ "_" ^ Int32.to_string new_x in
    init_state0 (old_v, new_v) state_tag

let phi_states : ('a, 'b) func_ir -> string -> state list =
  fun func_ir tag ->
    G.VMap.fold
      (fun this_v this_map acc_states ->
        let this_states =
          Int32Map.fold
            (fun _ (new_x, phi_entry_for_x) accs ->
              let xstates =
                List.map
                  (fun (prev_v, old_x) -> phi_state tag (prev_v, old_x) (this_v, new_x))
                  phi_entry_for_x in
              xstates @ accs)
            this_map
            [] in
        this_states @ acc_states)
      func_ir.phi_map
      []

(* Printing things *)
let string_of_wasm_value : wasm_value -> string =
  fun wal -> Values.string_of_value wal.it

let rec string_of_pointer : pointer -> string = function
  | IntPtr i -> Printf.sprintf "IntPtr %d" i
  | Int32Ptr i -> "Int32Ptr " ^ Int32.to_string i
  | IdPtr pid -> "IdPtr (" ^ pid ^ ")"
  | VarPtr x -> "VarPtr (" ^ string_of_var x ^ ")"
  | OffsetPtr (ptr, x) ->
    "OffsetPtr (" ^ string_of_pointer ptr ^ ", " ^ Int32.to_string x ^ ")"
  | IntOffsetPtr (ptr, x) ->
    "IntOffsetPtr (" ^ string_of_pointer ptr ^ ", " ^ (Printf.sprintf "%d" x) ^ ")"                                                                          
  | CastedPtr wal -> "CastedPtr (" ^ string_of_value wal ^ ")"
  | NullPtr -> "NullPtr"

and string_of_value : value -> string = function
  | IntVal i -> Printf.sprintf "%d" i
  | Int32Val i -> Int32.to_string i
  | WasmVal wal -> string_of_wasm_value wal

  | TestOpVal (testop, wal) ->
    "TestOpVal ("
      ^ string_of_testop testop ^ ", "
      ^ string_of_value wal ^ ")"

  | RelOpVal (wal0, relop, wal1) ->
    "RelOpVal ("
      ^ string_of_value wal0 ^ ", "
      ^ string_of_relop relop ^ ", "
      ^ string_of_value wal1 ^ ")"

  | UnOpVal (unop, wal) ->
    "UnOpVal ("
      ^ string_of_unop unop ^ ", "
      ^ string_of_value wal ^ ")"

  | BinOpVal (wal0, binop, wal1) ->
    "BinOpVal ("
      ^ string_of_value wal0 ^ ", "
      ^ string_of_binop binop ^ ", "
      ^ string_of_value wal1 ^ ")"

  | CvtOpVal (cvtop, wal) ->
    "CvtOpVal ("
      ^ string_of_cvtop cvtop ^ ", "
      ^ string_of_value wal ^ ")"

  | SelectVal (arr, ptr) ->
    "SelectVal ("
      ^ string_of_array arr ^ ", "
      ^ string_of_pointer ptr ^ ")"

  | UFVal (funcid, args) ->
     "UFVal ("
     ^ funcid 
     ^ (List.fold_left
          (fun r a -> r ^ "," ^ string_of_value a)
          ""
          args)
     ^ ")"

  | ArrayVal (arr) ->
    "ArrayVal ("
      ^ string_of_array arr ^ ") "         

and string_of_array : array_ -> string = function
  | IdArr aid -> "IdArr (" ^ aid ^ ")"

  | StoreArr (arr, ptr, wal) ->
    "StoreArr ("
      ^ string_of_array arr ^ ", "
      ^ string_of_pointer ptr ^ ", "
      ^ string_of_value wal ^ ")"

let string_of_step_status : step_status -> string = function
  | Active n -> "Active " ^ string_of_int n
  | Stopped -> "Stopped"

let string_of_state : state -> string =
  fun state ->
    "{ state with "
      ^ "this_edge = " ^ (G.string_of_basic_edge state.this_edge) ^ "; "
      ^ "step_status = " ^ string_of_step_status state.step_status ^ "; "
      ^ "tag = " ^ state.tag ^ " }"

let string_of_action : action -> string = function
  | BasicAct instr -> "BasicAct (" ^ string_of_instr_inline instr ^ ")"
  | JumpAct (br, v) ->
    "JumpAct ("
      ^ string_of_branch br ^ ", " ^ G.string_of_vertex v ^ ")"
  | PhiAct (prev_v, this_v) ->
    "PhiAct (" ^ G.string_of_vertex prev_v ^ "," ^ G.string_of_vertex this_v ^ ")"
  | CallAct x -> "CallAct " ^ string_of_var x
  | CallIndirectAct x -> "CallIndirectAct " ^ string_of_var x
  | StopAct -> "StopAct"


let string_of_actions : action list -> string =
  fun acts ->
     String.string_of_list_inline acts string_of_action

let rec convert_to_int_pointer: pointer -> pointer =
  (* used for the uninterpreted sym eval *)
  fun p -> 
  match p with
  | Int32Ptr k -> IntPtr(Int32.to_int k)
  | OffsetPtr(q,k) -> IntOffsetPtr(convert_to_int_pointer q, Int32.to_int k)
  | IntOffsetPtr(q,k) -> IntOffsetPtr(convert_to_int_pointer q, k)
  | _ -> p


