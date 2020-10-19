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
open State_types
open Debug

module G = Digraph
module String = String_utils

(* The formulas that we can encode.
 * This is just propositional logic with theory of arrays lacking quantifiers.
 * We need to be assert equality on (first-order) values
 * as well as arrays of values (first-order? debateable) *)

type relop =
  | AstRelOp of Ast.relop      (* fixed bitwidth relational operator *)
  | IntEq | IntNeq | IntLeq    (* mathematical integer relations *)
                       
type formula =
  (* Does the LHS equal the RHS? As an assertion to solvers *)
  | PtrsRelForm of pointer * relop * pointer
  | ValsRelForm of value * relop * value
  | ArrsEqForm of array_ * array_
  | ArrZeroAfterForm of array_ * pointer * value (* Array has value zero after a certain pointer *)
  (*
  | ArrsRangeEqForm of array_ * array_ * pointer * pointer
  *)
  | UFBoolForm of smtid * (value list)    (* uninterpreted boolean function *)
  | SymEqForm of value * value

  (* Typical logical conjunctions *)
  | BoolForm of bool
  | AndForm of formula list
  | OrForm of formula list
  | ImplForm of formula * formula
  | NotForm of formula

  (* Add comments to our formula; can only wrap an existing formula *)
  | CommentForm of string * formula

(* A simpler representation than the one in digraphs *)
type source_edge = G.basic_edge
type target_edge = G.basic_edge

type source_path = G.basic_path
type target_path = G.basic_path

(* Define the OCaml modules needed for some data structures to work *)
module BasicEdge = struct
  type t = G.basic_edge
  let compare : t -> t -> int = Stdlib.compare
end

(* We assume function calls in the CFG to have form
 *                  (cv)
 *    --> [pv] --> [Call x] --> [sv] -->
 *
 * A path specifying a function call is likewise just [pv; cv; sv].
 *
 * That is, paths that verify calls are isolated in a single block, then:
 *
 *  state0 = init_state0 (pv,cv) tag // state immediately before call
 *  state1 = next_state state0 (CallAct x) // state immediately after call
 *  state2 = next_state (JumpAct (Jump, sv)) // penultimate state
 *  statef = next_state (FinalAct state2) = init_statef (cv,sv) tag // final
 *
 *)
type state_status_flag =
  | Initial
  | PreCall
  | PostCall
  | Final

module SourceEdge_TargetEdge = struct
  type t = source_edge * target_edge * state_status_flag
  let compare : t -> t -> int = Stdlib.compare
end

module SourceEdge_TargetPath = struct
  type t = source_edge * target_path
  let compare : t -> t -> int = Stdlib.compare
end

module TargetEdgeMap = Map.Make(BasicEdge)
module SourceEdge_TargetEdgeMap = Map.Make(SourceEdge_TargetEdge)
module SourceEdge_TargetPathMap = Map.Make(SourceEdge_TargetPath)

(* Some types
 *  checkpoints:
 *    the edge pairs that we need to check.
 *    The current algorithm requires us to explicitly specify these
 *    to add to the worklist. 
 *
 *  state_pair_formula:
 *    the proof requires that the user provide us a function of how to
 *    generate formulas given a pair of source / target states
 *
 *  refinement_map:
 *    maps each edge pair to a state_pair_formula.
 *
 *  frontier_map:
 *    explicitly marks where each edge in the target has its next frontier.
 *    Although this is redundant information (like the checkpoints) since
 *    it can be reverse engineed from the path_match_map,
 *    it's still a quality-of-life thing to have around.
 *
 *  path_match_map:
 *    tells us how each source-edge target-path pair maps to a souce path.
 *)

type checkpoints = (source_edge * target_edge) list
type state_pair_formula = (state * state) -> formula
type refinement_map = state_pair_formula SourceEdge_TargetEdgeMap.t
type frontier_map = (target_edge list) TargetEdgeMap.t
type path_match_map = source_path SourceEdge_TargetPathMap.t

(* Mode for which form of proofs to generate:
 * using uninterpreted functions, or fully interpreted bitvector operations? *)
type interpretation = 
  (* fully interpreted operators *)
  | IFull
  (* fully uninterpreted operators *)
  | INone

                                  
type proof =
  {
    (* transformation name *)
    transform : string;
    interpretation : interpretation; 
    
    func_id : func_id;
    checkpoints : checkpoints;
    refinement_map : refinement_map;
    frontier_map : frontier_map;
    path_match_map : path_match_map;
    debugs : string list
  }

let empty_proof =
  {
    transform = "empty";
    interpretation = INone;
    func_id = "";
    checkpoints = [];
    refinement_map = SourceEdge_TargetEdgeMap.empty;
    frontier_map = TargetEdgeMap.empty;
    path_match_map = SourceEdge_TargetPathMap.empty;
    debugs = []
  }

let string_of_state_status_flag : state_status_flag -> string = function
  | Initial -> "Initial"
  | PreCall -> "PreCall"
  | PostCall -> "PostCall"
  | Final -> "Final"

(* Some default comparison formulas *)

(* Basic lookup functions with error messages *)
let lookup_refinement
  : (source_edge * target_edge * state_status_flag) -> proof
  -> state_pair_formula =
  fun key proof ->
    match SourceEdge_TargetEdgeMap.find_opt key proof.refinement_map with
    | Some st_form -> st_form
    | None ->
      let (src_e, tgt_e, stat) = key in
      if proof.interpretation = IFull && (stat = PreCall || stat = PostCall) then
        let _ = prerr_debug
          ("lookup_refinement: inferring state_pair_equiv at "
            ^ "(" ^ G.string_of_basic_edge src_e ^ ","
                  ^ G.string_of_basic_edge tgt_e ^ ","
                  ^ string_of_state_status_flag stat ^ ")") in
        (fun (state0, state1) ->
          CommentForm ("states_equiv",
            AndForm
              [ ArrsEqForm (values state0, values state1);
                PtrsRelForm
                  (stack_pointer state0,
                   AstRelOp (Values.I32 Ast.IntOp.Eq),
                   stack_pointer state1);
                ArrsEqForm (locals state0, locals state1);
                ArrsEqForm (globals state0, globals state1);
                ArrsEqForm (full_memory state0, full_memory state1) ]))

      else if proof.interpretation = INone && (stat = PreCall || stat = PostCall) then
        let _ = prerr_debug
          ("lookup_refinement: inferring state_pair_equiv at "
            ^ "(" ^ G.string_of_basic_edge src_e ^ ","
                  ^ G.string_of_basic_edge tgt_e ^ ","
                  ^ string_of_state_status_flag stat ^ ")") in
        (fun (state0, state1) ->
          CommentForm ("states_equiv",
            AndForm
              [ ArrsEqForm (values state0, values state1);
                PtrsRelForm
                  (stack_pointer state0,
                   IntEq,
                   stack_pointer state1);
                ArrsEqForm (locals state0, locals state1);
                ArrsEqForm (globals state0, globals state1);
                SymEqForm (uf_memory state0, uf_memory state1) ]))

      else
        (prerr_debug
          ("lookup_refinement: proof "
            ^ proof.func_id 
            ^ " / missing key "
            ^ "(" ^ G.string_of_basic_edge src_e ^ ","
                  ^ G.string_of_basic_edge tgt_e ^ ","
                  ^ string_of_state_status_flag stat ^ ")");
            fun _ -> BoolForm false)

let lookup_frontier : target_edge -> proof -> target_edge list =
  fun key proof ->
    match TargetEdgeMap.find_opt key proof.frontier_map with
    | Some fronts -> fronts
    | None ->
      (prerr_debug
        ("lookup_frontier: proof "
          ^ proof.func_id
          ^ " / missing key "
          ^ G.string_of_basic_edge key);
      [])

let lookup_path_match
  : (source_edge * target_path) -> proof -> source_path =
  fun key proof ->
    match SourceEdge_TargetPathMap.find_opt key proof.path_match_map with
    | Some src_p -> src_p
    | None ->
      let (src_e, tgt_p) = key in
      (prerr_debug
        ("lookup_path_match: proof"
          ^ proof.func_id
          ^ " / missing key "
          ^ "(" ^ G.string_of_basic_edge src_e ^ ","
                ^ G.string_of_basic_path tgt_p ^ ")");
        [])

(* Some helpful functions *)
let even_int32_value : value -> formula =
  fun wal ->
    ValsRelForm
      (BinOpVal (wal, Values.I32 Ast.IntOp.RemS, Int32Val 2l),
       AstRelOp (Values.I32 Ast.IntOp.Eq),
      zero_int32_val)

(* ******************************** *)

let string_of_interpretation : interpretation -> string = function
  | IFull -> "IFull"
  | INone -> "INone"


let string_of_relop: relop -> string =
  fun relop -> 
  match relop with
  | IntEq -> "IntEq"
  | IntNeq -> "IntNeq"
  | IntLeq -> "IntLeq"
  | AstRelOp rop ->
     Wasm_utils.string_of_relop rop
                               
let rec string_of_formula : formula -> string = function
  | PtrsRelForm (ptr0, relop, ptr1) ->
    "PtrsRelForm ("
      ^ string_of_pointer ptr0 ^ ", "
      ^ string_of_relop relop ^ ", "
      ^ string_of_pointer ptr1 ^ ")"

  | ValsRelForm (wal0, relop, wal1) ->
    "ValsRelForm ("
      ^ string_of_value wal0 ^ ", "
      ^ string_of_relop relop ^ ", "
      ^ string_of_value wal1 ^ ")"

  | ArrsEqForm (arr0, arr1) ->
    "ArrsEqForm ("
      ^ string_of_array arr0 ^ ", "
      ^ string_of_array arr1 ^ ")"

  | ArrZeroAfterForm (arr, ptr, wal0) ->
    "(ArrZeroAfterForm ("
      ^ string_of_array arr ^ ", "
      ^ string_of_pointer ptr ^ ", "
      ^ string_of_value wal0 ^ ")"

  | UFBoolForm(fnid,args) ->
     "UFBoolForm "
     ^ String.string_of_list_inline args string_of_value

  | SymEqForm(v0,v1) ->
     "SymEqForm ("
     ^ string_of_value v0 ^ ","
     ^ string_of_value v1 ^ ")"
                       

  | BoolForm b -> "BoolForm (" ^ string_of_bool b ^ ")"

  | AndForm forms ->
    "AndForm "
      ^ String.string_of_list_inline forms string_of_formula

  | OrForm forms ->
    "OrForm "
      ^ String.string_of_list_inline forms string_of_formula

  | ImplForm (form0, form1) ->
    "ImplForm ("
      ^ string_of_formula form0 ^ ", "
      ^ string_of_formula form1 ^ ")"

  | NotForm form -> "NotForm (" ^ string_of_formula form ^ ")"

  | CommentForm (msg, form) ->
    "CommentForm (" ^ msg ^ ", " ^ string_of_formula form ^ ")"

let string_of_refinement_map
  : formula SourceEdge_TargetEdgeMap.t -> string =
  fun ee_map ->
    String.string_of_list_endline 2 2
      (List.of_seq (SourceEdge_TargetEdgeMap.to_seq ee_map))
      (fun ((src_e, tgt_e, stat), form) ->
        "((" ^ G.string_of_basic_edge src_e ^ ", "
            ^ G.string_of_basic_edge tgt_e ^ ", "
            ^ string_of_state_status_flag stat ^ ")")

let string_of_frontier_map
: target_edge list TargetEdgeMap.t -> string =
  fun ie_map ->
    String.string_of_list_endline 2 2
      (List.of_seq (TargetEdgeMap.to_seq ie_map))
      (fun (tgt_e, front_es) ->
        "(" ^ G.string_of_basic_edge tgt_e ^ ", "
          ^ (String.string_of_list_inline
              front_es G.string_of_basic_edge) ^ ")")

let string_of_path_match_map
  : source_path SourceEdge_TargetPathMap.t -> string =
  fun ep_map ->
    String.string_of_list_endline 2 2
      (List.of_seq (SourceEdge_TargetPathMap.to_seq ep_map))
      (fun ((src_e, tgt_p), src_p) ->
        "((" ^ G.string_of_basic_edge src_e ^ ", "
             ^ G.string_of_basic_path tgt_p ^ ")" ^ ", "
          ^ G.string_of_basic_path src_p ^ ")")


