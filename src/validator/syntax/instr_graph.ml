(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)

open Wasm_utils
open Wasm
open Source
open Dominance
open Type_inference
open Option

module S = Stack
module G = Digraph
module String = String_utils
module List = List_utils
open Debug

(* Blocks are the vertex labels of the graph,
 * and represent a sequence of instructions to execute.
 * We can hack together some WASM thing later to infer the
 * stack type of a sequence of instructions in case this is
 * needed to use the spec/interpreter backend.
 *
 * There are several invariants we aim to keep that are
 * explained further in the func_ir.ml.
 * The code here is menat to work over any instr_graph,
 * but "valid" IR's need a few invariants.
 *)
type block =
  { instrs : Ast.instr list;
    region : region;
  }

let empty_block : block =
  { instrs = [];
    region = no_region;
  }

(* The edge labels that show how blocks are connected.
 * Although the llvm::BasicBlock holds much more information,
 * much of this can be inferred given the functionalities we have,
 * especially for the phi nodes *)
type branch =
  | Jump
  | JumpIf of bool
  | JumpBrIf of bool
  | JumpIndex of int32 (* track table index *)
  | JumpDefault of int32 (* table size *)

(* A graph of the instructions where the vertices are labeled by a block
 * and the edges are labeled by a (type of) branch *)
type ('a, 'b) instr_graph = ((block * 'a), (branch * 'b)) G.graph

(* The result of initial initial processing is parametrized (unit, unit).
 * Subsequent analyses can be applied to make these into more useful types *)
type uinstr_edge = (branch * unit) G.edge
type uinstr_graph = (unit, unit) instr_graph

(* Printing functionalities *)
let string_of_block_simple : block -> string =
  fun block ->
    "{ block with "
      ^ "instrs[" ^ string_of_int (List.length block.instrs) ^ "] }"

let string_of_block : block -> string =
  fun block ->
    "{ block with "
      ^ "instrs = [\n"
      ^ String.unlines
          (List.map (string_of_instr_indent 2) block.instrs) ^ "] }"

let string_of_branch : branch -> string = function
  | Jump -> "Jump"
  | JumpIf b -> "JumpIf " ^ string_of_bool b
  | JumpBrIf b -> "JumpBrIf " ^ string_of_bool b
  | JumpIndex ti ->"JumpIndex (" ^ Int32.to_string ti ^ ")"
  | JumpDefault ts -> "JumpDefault (" ^ Int32.to_string ts ^ ")"


let string_of_instr_graph : ('a, 'b) instr_graph -> string =
  fun graph ->
  G.string_of_graph graph (fun (a, _) -> string_of_block a) (fun (b, _) -> string_of_branch b) 

(* Meta information when constructing the CFG -- too many arguments otherwise:
 *  branch_targets stack is the branch (branch) targets
 *  this_vertex is the current vertex under modification
 *  sink_vertex is the vertex to direct edges to if instrs is empty
 *)
type build_meta =
  { branch_targets : G.vertex S.stack;
    this_vertex : G.vertex;
    sink_vertex : G.vertex;
  }

let empty_build_meta : build_meta =
  { branch_targets = S.empty_stack;
    this_vertex = G.null_vertex;
    sink_vertex = G.null_vertex;
  }

(* Append instructions to a block *)
let init_block : Ast.instr list -> block =
  fun instrs ->
    { empty_block with instrs = instrs }

let append_instrs : block -> Ast.instr list -> block =
  fun block instrs ->
    { block with instrs = block.instrs @ instrs }

(* Find the appropriate level of breaking, and return the null vertex otherwise *)
let branch_target_vertex : Ast.var -> build_meta -> G.vertex =
  fun x meta ->
    match S.pop_to_nth (Int32.to_int x.it) meta.branch_targets with
    | None ->
      (prerr_debug ("branch_target_vertex: bad target level "
        ^ Int32.to_string x.it); meta.sink_vertex)
    | Some (tgt_v, _) -> tgt_v

(* Is this instruction a basic instruction? *)
let is_basic_instr : Ast.instr -> bool =
  fun instr ->
    match instr.it with
    | Ast.Block _ | Ast.Loop _
    | Ast.If _ | Ast.Br _ | Ast.BrIf _ | Ast.BrTable _
    | Ast.Call _ | Ast.CallIndirect _ -> false
    (* Should we classify unreachable as control flow? *)
    | Ast.Return -> true
    | Ast.Unreachable -> true
    (* Everything else is considered to be basic *)
    | _ -> true

(* Is the instruction a control flow? Complement of basic instruction ...
 * Probably shouldn't even have this predicate around *)
let is_instr_control_flow : Ast.instr -> bool =
  fun ins ->
    match ins.it with
    | Ast.Block _ | Ast.Loop _
    | Ast.If _ | Ast.Br _ | Ast.BrIf _ | Ast.BrTable _
    | Ast.Return | Ast.Call _ | Ast.CallIndirect _ -> true
    (* Should we classify unreachable as control flow? *)
    | Ast.Unreachable -> true
    | _ -> false

let is_call_vertex : G.vertex -> uinstr_graph -> bool =
  fun v graph ->
    match G.vertex_label v graph with
    | Some ({ instrs = [{ it = Ast.Call _ }] }, _) -> true
    | Some ({ instrs = [{ it = Ast.CallIndirect _ }] }, _) -> true
    | _ -> false

(* Recursively consume a instr list to make a graph.
 * We use the build_meta to help guide us in the construction.
 * This meta would be initialized by an appropriate caller,
 * such as perhaps the func ir *)
let rec instrs_to_uinstr_graph
  : Ast.instr list -> uinstr_graph -> build_meta -> uinstr_graph =
  fun instrs graph meta ->
    let { branch_targets = tgt_vs;
          this_vertex = this_v;
          sink_vertex = sink_v; } = meta in

    match instrs with
    (* Nothing left to do; connect this_v with sink_v *)
    | [] -> G.add_edge (this_v, (Jump, ()), sink_v) graph

    (* Process the next instruction *)
    | hd_instr :: tl_instrs ->
      match hd_instr.it with
      (* Encountering a block consists of making a new block
       * containing only the instructions of that block:
       *
       *       -------------
       *       | old_stuff |
       *       -------------
       *             |
       *      ---------------
       *      | basic block |  <- Note that block may be many blocks
       *      ---------------
       *             |
       *        -----------
       *        | post_v  |    <- This one pushed onto the branch target stack.
       *        -----------        Also becomes the new sink of basic block
       * *)
      | Ast.Block (stack_type, block_instrs) ->
        (* Allocate and connect block_v *)
        let (block_v, graph1) = G.alloc_vertex (empty_block, ()) graph in
        let graph2 = G.add_edge (this_v, (Jump, ()), block_v) graph1 in

        (* Allocate the post_v *)
        let (post_v, graph3) = G.alloc_vertex (empty_block, ()) graph2 in

        (* Construct the meta for the recursive call to the block_instrs *)
        let block_meta =
          { meta with
            branch_targets = S.push post_v tgt_vs;
            this_vertex = block_v;
            sink_vertex = post_v; } in
        let graph4 = instrs_to_uinstr_graph block_instrs graph3 block_meta in

        (* Now we are ready to continue with the rest of the instructions
         * What used to be the sink is now the this
         * Note: be careful about touching block_meta (or don't touch it)
         * Many things get reset when we actually do recursion
         * on tl_instrs *)
        let meta1 =
          { meta with
            branch_targets = tgt_vs;
            this_vertex = post_v;
            sink_vertex = sink_v; } in
        instrs_to_uinstr_graph tl_instrs graph4 meta1

      (* Encountering a loop is similar to block, except the loop_v is
       * what gets pushed onto the branch targets instead of the post_v
       * 
       *      -------------
       *      | old_stuff |
       *      -------------
       *            |
       *      --------------
       *      | loop block |  <- This is pushed onto branch_targets
       *      --------------
       *            |
       *        ----------
       *        | post_v |    <- This is the sink
       *        ----------
       * *)
      | Ast.Loop (stack_type, loop_instrs) ->
        (* Allocate and connect loop_v *)
        let (loop_v, graph1) = G.alloc_vertex (empty_block, ()) graph in
        let graph2 = G.add_edge (this_v, (Jump, ()), loop_v) graph1 in

        (* Allocate the post_v *)
        let (post_v, graph3) = G.alloc_vertex (empty_block, ()) graph2 in

        (* Up until now everything is like the block stuff,
         * Except the loop_meta is slightly different *)
        let loop_meta =
          { meta with
            branch_targets = S.push loop_v tgt_vs;
            this_vertex = loop_v;
            sink_vertex = post_v; } in

        let graph4 = instrs_to_uinstr_graph loop_instrs graph3 loop_meta in

        (* Similar rationale for the Block stuff: a bunch of resets *)
        let meta1 =
          { meta with
            branch_targets = tgt_vs;
            this_vertex = post_v;
            sink_vertex = sink_v; } in
        instrs_to_uinstr_graph tl_instrs graph4 meta1

      (* For if statements we need to make a little diamond structure:
       *
       *             ------------
       *             |  this_v  |
       *             ------------
       *             /          \
       *    ------------       ------------
       *    |  true_v  |       | false_v  |
       *    ------------       ------------
       *              \          /
       *              ------------
       *              |  post_v  |   <- This is the sink AND branch target
       *              ------------      for both true_v and false_v
       *)
      | Ast.If (stack_type, true_instrs, false_instrs) ->
        (* Make true_v and connect *)
        let (true_v, graph1) = G.alloc_vertex (empty_block, ()) graph in
        let graph2 = G.add_edge (this_v, (JumpIf true, ()), true_v) graph1 in

        (* Make false_v and connect *)
        let (false_v, graph3) = G.alloc_vertex (empty_block, ()) graph2 in
        let graph4 = G.add_edge (this_v, (JumpIf false, ()), false_v) graph3 in

        (* Make post_v and don't touch it yet *)
        let (post_v, graph5) = G.alloc_vertex (empty_block, ()) graph4 in

        (* Allocating things in this order doesn't matter as long as we
         * use the right graph variable for each call *)

        (* Do recurisve calls for true *)
        let true_meta =
          { meta with
            branch_targets = tgt_vs;
            (*
            branch_targets = S.push post_v tgt_vs;
            *)
            this_vertex = true_v;
            sink_vertex = post_v; } in
        let graph6 = instrs_to_uinstr_graph true_instrs graph5 true_meta in

        (* Now for false *)
        let false_meta =
          { meta with
            branch_targets = tgt_vs;
            (*
            branch_targets = S.push post_v tgt_vs;
            *)
            this_vertex = false_v;
            sink_vertex = post_v; } in
        let graph7 = instrs_to_uinstr_graph false_instrs graph6 false_meta in

        (* Finally set up the call for recursion on post_v *)
        let meta1 =
          { meta with
            branch_targets = tgt_vs;
            this_vertex = post_v;
            sink_vertex = sink_v; } in
        instrs_to_uinstr_graph tl_instrs graph7 meta1

      (* Find out the right thing to branch to to add the edge.
       * We need to figure out how many layers to pop back up
       *
       *      ------------
       *      | vertex A |     <- Bottom of the branch stack
       *      ------------
       *          ...                     ...
       *           |
       *      ------------
       *      | vertex Z |     <- Top of the branch stack
       *      ------------
       *          ...
       *           |           ^  need to branch to the nth from top
       *      -----------      |  eg "br 0" is the top of the stack
       *      | this_v |  _____/  eg (br (length branch_targets - 1)) is bottom
       *      -----------
       *
       * Note that if an unconditional branch happens, we can ignore
       * the remaining instructions -- since they'll be unreachable anyways.
       * Also, the x is an Ast.var, which is an int32
       *)
      | Ast.Br x ->
        
        G.add_edge (this_v, (Jump, ()), branch_target_vertex x meta) graph

      (* Conditional branching depending on if the top of the stack is true.
       * This also consumes the top of the value stack
       *
       *                 ----------
       *                 | this_v |
       *                 ----------
       *     BrIf false  /        \  BrIf true
       *    --------------        -------------
       *    | tl_instrs  |        |   tgt_v   |
       *    --------------        -------------
       *          ^
       *           \______ this becomes the new "this" for the
       *                   rest of the instructions
       *)
      | Ast.BrIf x ->
        (* Make the true_v *)
        let true_v = branch_target_vertex x meta in
        let graph1 = G.add_edge (this_v, (JumpBrIf true, ()), true_v) graph in

        (* For the false_v we need to allocate it *)
        let (false_v, graph2) = G.alloc_vertex (empty_block, ()) graph1 in
        let graph3 = G.add_edge (this_v, (JumpBrIf false, ()), false_v) graph2 in

        (* Set up the meta1 on top of the false_v
         * Since we already have the true_v populated from previous
         * work we don't have to go there, but we do have to work
         * on the remaining instructions that would be in the false_v.
         *)
        let meta1 =
          { meta with
            branch_targets = tgt_vs;
            this_vertex = false_v;
            sink_vertex = sink_v; } in
        instrs_to_uinstr_graph tl_instrs graph3 meta1
 
      (* For BrTable this is similar to the BrIf, except we need to make
       * a whole bunch of connections -- one for each of the targets levels,
       * and a special one for the default level.
       * *)
      | Ast.BrTable (xs, def_x) ->
        (* (index, level, target) list *)
        let trips = List.mapi (fun i x -> (i, x, branch_target_vertex x meta)) xs in

        (* We now need to add all of these edges in graph via folding *)
        let graph1 =
          List.fold_left
            (fun acc_g (i, x, tgt_v) ->
              G.add_edge (this_v, (JumpIndex (Int32.of_int i), ()), tgt_v) acc_g)
            graph
            trips in

        (* Finally need to add in the default *)
        let def_v = branch_target_vertex def_x meta in
        let tbl_size = Int32.of_int (List.length xs) in
        G.add_edge (this_v, (JumpDefault tbl_size, ()), def_v) graph1

      (* For both Call and CallIndirect we set up a graph like:
       *
       *    -----------
       *    | this_v  |
       *    -----------
       *         |
       *    -----------
       *    | call_v  |
       *    -----------
       *         |
       *    -----------
       *    | post_v  |    <- populate this with instruction tail
       *    -----------
       *
       * An invariant we keep is that blocks where a call is performed
       * have said call / indirect call as their singleton instruction.
       *)
      | Ast.Call x ->
        let call_block = init_block [hd_instr] in
        let (call_v, graph1) = G.alloc_vertex (call_block, ()) graph in
        let graph2 = G.add_edge (this_v, (Jump, ()), call_v) graph1 in

        let (post_v, graph3) = G.alloc_vertex (empty_block, ()) graph2 in
        let graph4 = G.add_edge (call_v, (Jump, ()), post_v) graph3 in

        let meta1 =
          { meta with
            branch_targets = tgt_vs;
            this_vertex = post_v;
            sink_vertex = sink_v; } in
        instrs_to_uinstr_graph tl_instrs graph4 meta1

      | Ast.CallIndirect x ->
        let calli_block = init_block [hd_instr] in
        let (calli_v, graph1) = G.alloc_vertex (calli_block, ()) graph in
        let graph2 = G.add_edge (this_v, (Jump, ()), calli_v) graph1 in

        let (post_v, graph3) = G.alloc_vertex (empty_block, ()) graph2 in
        let graph4 = G.add_edge (calli_v, (Jump, ()), post_v) graph3 in

        let meta1 =
          { meta with
            branch_targets = tgt_vs;
            this_vertex = post_v;
            sink_vertex = sink_v; } in
        instrs_to_uinstr_graph tl_instrs graph4 meta1

      (* If we are to return, just connect this with the sink;
       * we can ignore the remaining instructions since we force exit *)
       (*
      | Ast.Return -> G.add_edge (this_v, (Jump, ()), sink_v) graph
      | Ast.Unreachable -> G.add_edge (this_v, (Jump, ()), trap_v) graph
      *)
      | Ast.Return | Ast.Unreachable ->
        (match G.vertex_label this_v graph with
        | Some (block, ()) ->
          let graph1 = G.add_vertex this_v (append_instrs block [hd_instr], ()) graph in
          graph1
        | _ ->
          (* Oh no, something has gone terribly wrong *)
          (prerr_debug ("instrs_to_uinstr_graph: no vertex label (b)");
          graph))

      (* For regular instructions we just append this to whatever's in the
       * block of this_vertex ... if it is a basic vertex *)
      | _ ->
        (* First we do some sanity checks *)
        (match G.vertex_label this_v graph with
        | Some (block, ()) -> 
          let graph1 = G.add_vertex this_v (append_instrs block [hd_instr], ()) graph in

          (* Continue the recursion with this new graph *)
          instrs_to_uinstr_graph tl_instrs graph1 meta

        | _ ->
          (* Oh no, something has gone terribly wrong *)
          (prerr_debug ("instrs_to_uinstr_graph: no vertex label (b)");
          graph))


(* ************************** *)
let vertex_instrs : G.vertex -> ('a, 'b) instr_graph -> Ast.instr list =
  fun v graph ->
    match G.vertex_label v graph with
    | None -> []
    | Some (block, _) -> block.instrs

let vertex_block : G.vertex -> ('a, 'b) instr_graph -> block =
  fun v graph ->
    match G.vertex_label v graph with
    | None -> empty_block
    | Some (block, _) -> block

let all_instrs : ('a, 'b) instr_graph -> Ast.instr list =
  fun graph ->
    G.VSet.fold (fun v instrs -> instrs @ vertex_instrs v graph) graph.vertex_set []

let eqz_instr : Ast.instr = noregion (Ast.Test (Values.I32 Ast.IntOp.Eqz))


(* T1 T2 Algorithms as described in
 * "Flow Graph Reducibility" by Hecht and Ullman
 *
 * Currently for ease of implementation we are ignoring BrTable and BrDefault
 *)

(* T1: self loops at one vertex
 *
 *    \ | /
 *  @ [ a ]   (where the self loop is BrIf bool)
 *      |
 *      |     (... and the break is BrIf (not bool))
 *    [ b ]
 *
 * Case (a -> a) is BrIf true (ie a -> b is false)
 *
 *    \ | /
 *    [ a ]
 *      |   (now regular Jump to b)
 *    [ b ]
 *            new_instrs(a) = loop { instrs(a) @ [brif 0] }
 *
 *  Case (a -> a) is Brif false (ie a -> b is true)
 *    (1) add eqz as the final statement of instrs(a)
 *    (2) flip the order of BrIf true and BrIf false
 *    (3) recursion
 *)
let rec t1_self_A : G.vertex -> uinstr_graph -> type_map_type -> uinstr_graph option =
  fun a_v graph ty_map ->
    match (G.find_succ a_v (JumpBrIf true, ()) graph,
      G.find_succ a_v (JumpBrIf false, ()) graph) with
    (* Case 1 *)
    | (Some a1_v, Some b_v) when ((a1_v = a_v) && (a_v <> b_v)) ->
      let a_block = vertex_block a_v graph in
      let a_instrs = a_block.instrs in
      let brif_instr = noregion (Ast.BrIf (int_to_var 0)) in
      let body_instrs = a_instrs @ [brif_instr] in
      let body_type = infer_stack_type body_instrs ty_map i32ty in
      let loop_instr = noregion (Ast.Loop (body_type, body_instrs)) in
      let a_block1 = { a_block with instrs = [loop_instr] } in

      (* Update graph *)
      let graph1 = G.add_vertex_label a_v (a_block1, ()) graph in
      let graph2 = G.remove_basic_edge (a_v, a_v) graph1 in
      let graph3 = G.remove_basic_edge (a_v, b_v) graph2 in
      let graph4 = G.add_edge (a_v, (Jump, ()), b_v) graph3 in
      Some graph4

    (* Case 2: do recursion *)
    | (Some b_v, Some a1_v) when ((a1_v = a_v) && (a_v <> b_v)) ->
      let a_block = vertex_block a_v graph in
      let a_instrs1 = a_block.instrs @ [eqz_instr] in
      let a_block1 = { a_block with instrs = a_instrs1 } in

      (* Update the graph and recurse *)
      let graph1 = G.add_vertex_label a_v (a_block1, ()) graph in
      let graph2 = G.remove_basic_edge (a_v, a_v) graph1 in
      let graph3 = G.remove_basic_edge (a_v, b_v) graph2 in
      let graph4 = G.add_edge (a_v, (JumpBrIf true, ()), a_v) graph3 in
      let graph5 = G.add_edge (a_v, (JumpBrIf false, ()), b_v) graph4 in

      t1_self_A a_v graph5 ty_map

    | _ ->
      (* Degenerate case where it's just a self-loop on a_v all the time *)
      match G.find_succ a_v (Jump, ()) graph with
      | Some a1_v when (a_v = a1_v) ->
        let a_block = vertex_block a_v graph in
        let br_instr = noregion (Ast.Br (int_to_var 0)) in
        let body_instrs = a_block.instrs @ [br_instr] in
        let body_type = infer_stack_type body_instrs ty_map i32ty in
        let loop_instr = noregion (Ast.Loop (body_type, body_instrs)) in
        let a_block1 = { a_block with instrs = [loop_instr] } in

        (* Update graph *)
        let graph1 = G.add_vertex_label a_v (a_block1, ()) graph in
        let graph2 = G.remove_basic_edge (a_v, a_v) graph1 in
        Some graph2

      | _ -> None


(* T1: looping involving 2 vertices
 *
 *    \ | /
 *    [ a ] ----> [ c ] (where a dominates c)
 *     ^ |
 *     | v
 *    [ b ] (where a BrIf bool to b and b Br to a)
 *
 *
 *    Note that this doesn't generalize well to the case when b points
 *    to some sb where sb dominates a. The reaosn is because then we
 *    will have a harder time deciding when to wrap sb in a loop header.
 *
 * Case (a -> b) is BrIf false (ie a -> c is true)
 *    
 *    \ | /
 *    [ a ]
 *      |   (now a regular Jump)
 *    [ c ]
 *          where instrs(a) = block { loop { instrs(a) @ [brif 1] @ instrs(b) @ [br 0] } }
 *
 * Case (a -> b) is BrIf true (ie a -> c is false)
 *  (1) add eqz to the final statmeent of instrs(a)
 *  (2) flip the order of BrIf true and BrIf false edges
 *  (3) recursion
 *   
 *)
let rec t1_self_B : G.vertex -> uinstr_graph -> dom_data -> type_map_type -> uinstr_graph option =
  fun a_v graph dom_data ty_map ->
    match (G.find_succ a_v (JumpBrIf true, ()) graph,
        G.find_succ a_v (JumpBrIf false, ()) graph) with

    (* Case 1 *)
    | (Some c_v, Some b_v)
      when ((a_v <> b_v) && (a_v <> c_v) && (b_v <> c_v)
        && (G.only_edge_exists (b_v, (Jump, ()), a_v) graph)
        && (dominates a_v c_v dom_data)) ->
      let a_block = vertex_block a_v graph in
      let a_instrs = a_block.instrs in
      let brif_instr = noregion (Ast.BrIf (int_to_var 1)) in
      let b_instrs = vertex_instrs b_v graph in
      let br_instr = noregion (Ast.Br (int_to_var 0)) in
      let body_instrs = a_instrs @ [brif_instr] @ b_instrs @ [br_instr] in
      let body_type = infer_stack_type body_instrs ty_map i32ty in
      let block_instr =
        noregion (Ast.Block (body_type,
          [noregion (Ast.Loop (body_type, body_instrs))])) in
      let a_block1 = { a_block with instrs = [block_instr] } in

      (* Update graph *)
      let graph1 = G.add_vertex_label a_v (a_block1, ()) graph in
      let graph2 = G.remove_vertex b_v graph1 in
      let graph3 = G.remove_basic_edge (a_v, c_v) graph2 in
      let graph4 = G.add_edge (a_v, (Jump, ()), c_v) graph3 in
      Some graph4

    (* Case 2 *)
    | (Some b_v, Some c_v)
      when ((a_v <> b_v) && (a_v <> c_v) && (b_v <> c_v)
        && (G.only_edge_exists (b_v, (Jump, ()), a_v) graph)
        && (dominates a_v c_v dom_data)) ->
      let a_block = vertex_block a_v graph in
      let a_block1 = { a_block with instrs = a_block.instrs @ [eqz_instr] } in

      (* Update the graph and recurse *)
      let graph1 = G.add_vertex_label a_v (a_block1, ()) graph in
      let graph2 = G.remove_basic_edge (a_v, b_v) graph1 in
      let graph3 = G.remove_basic_edge (a_v, c_v) graph2 in
      let graph4 = G.add_edge (a_v, (JumpBrIf false, ()), b_v) graph3 in
      let graph5 = G.add_edge (a_v, (JumpBrIf true, ()), c_v) graph4 in

      t1_self_B a_v graph5 dom_data ty_map

    | _ -> None

(* T1: mutual looping on two vertices
 *
 *    \ | /
 *    [ a ]
 *     ^ |    where both of these are Jump (unconditional br)
 *     | v
 *    [ b ]
 *
 * Then this becomes
 *    \ | /
 *    [ a ]
 * where we now have instrs(a) = loop { instrs(a) @ instrs(b) @ [br0] }
 *)
let rec t1_self_C : G.vertex -> uinstr_graph -> type_map_type -> uinstr_graph option =
  fun a_v graph ty_map ->
    match (G.find_only_succ a_v (Jump, ()) graph) with
    | Some b_v when ((a_v <> b_v) && (G.only_edge_exists (b_v, (Jump, ()), a_v) graph)) ->
      let a_block = vertex_block a_v graph in
      let a_instrs = a_block.instrs in
      let b_instrs = vertex_instrs b_v graph in
      let br_instr = noregion (Ast.Br (int_to_var 0)) in
      let body_instrs = a_instrs @ b_instrs @ [br_instr] in
      let body_type = infer_stack_type body_instrs ty_map i32ty in
      let loop_instr = noregion (Ast.Loop (body_type, body_instrs)) in
      let a_block1 = { a_block with instrs = [loop_instr] } in

      (* Update the graph *)
      let graph1 = G.add_vertex_label a_v (a_block1, ()) graph in
      let graph2 = G.remove_vertex b_v graph1 in
      Some graph2

    | _ -> None
      

(* T1: remove the inner most nested loop
 *
 *   \ | /
 *   [ b ] ---> [ a ] (where a dominates b)
 *    ^ |
 *    | v
 *   [ c ]
 *
 *  where (b -> c) is a brif, and so is (b -> a), such that
 *    (1) b-c forms a loop
 *    (2) a dominates b (thereby making b-c a nested loop)
 *          
 *  Case brif b -> c is false (ie b -> a is true)
 *
 *    \ | /
 *    [ b ] ---> [ a ] where the connection is unconditional Jump (was brif)
 *
 *  where instrs(b) = loop { instrs(b) @ [br #a] @ instrs(c) @ [br 0] }
 *
 *  Note that we leave a "vestigial" (b -> a) connection, which becomes dead code,
 *  but still allows (a) to be correctly detected as a loop header when necessary.
 *
 *  Case brif b -> c is true (ie b -> a is false)
 *    (1) Add eqz instr to end of instrs(b)
 *    (2) Flip brif edges
 *    (3) Recursion
 *)
let rec t1_nested_A : G.vertex -> uinstr_graph -> dom_data -> type_map_type -> uinstr_graph option =
  fun b_v graph dom_data ty_map ->
    match (G.find_only_succ b_v (JumpBrIf true, ()) graph,
        G.find_only_succ b_v (JumpBrIf false, ()) graph) with

    (* Case 1 *)
    | (Some a_v, Some c_v)
        when ((b_v <> a_v) && (b_v <> c_v) && (a_v <> c_v)
          && (G.only_edge_exists (c_v, (Jump, ()), b_v) graph)
          && (dominates a_v b_v dom_data)) ->
      (match count_br_level b_v a_v dom_data graph with
      | Some a_lvl ->
        let b_block = vertex_block b_v graph in
        let b_instrs = b_block.instrs in
        let brif_instr = noregion (Ast.BrIf (int_to_var a_lvl)) in
        let c_instrs = vertex_instrs c_v graph in
        let br_instr = noregion (Ast.Br (int_to_var 0)) in
        let body_instrs = b_instrs @ [brif_instr] @ c_instrs @ [br_instr] in
        let body_type = infer_stack_type body_instrs ty_map i32ty in
        let loop_instr = noregion (Ast.Loop (body_type, body_instrs)) in
        let b_block1 = { b_block with instrs = [loop_instr] } in

        (* Update the graph *)
        let graph1 = G.add_vertex_label b_v (b_block1, ()) graph in
        let graph2 = G.remove_vertex c_v graph1 in
        let graph3 = G.remove_basic_edge (b_v, a_v) graph2 in
        let graph4 = G.add_edge (b_v, (Jump, ()), a_v) graph3 in
        Some graph4

      | _ -> None)

    (* Case 2 *)
    | (Some c_v, Some a_v)
        when ((b_v <> a_v) && (b_v <> c_v) && (a_v <> c_v)
          && (G.only_edge_exists (c_v, (Jump, ()), b_v) graph)
          && (dominates a_v b_v dom_data)) ->
      let b_block = vertex_block b_v graph in
      let b_instrs1 = b_block.instrs @ [eqz_instr] in
      let b_block1 = { b_block with instrs = b_instrs1 } in

      (* Update the graph and recurse *)
      let graph1 = G.add_vertex_label b_v (b_block1, ()) graph in
      let graph2 = G.remove_basic_edge (b_v, c_v) graph1 in
      let graph3 = G.remove_basic_edge (b_v, a_v) graph2 in
      let graph4 = G.add_edge (b_v, (JumpBrIf true, ()), a_v) graph3 in
      let graph5 = G.add_edge (b_v, (JumpBrIf false, ()), c_v) graph4 in

      t1_nested_A b_v graph5 dom_data ty_map

    | _ -> None


(* T1: nested looping branches to something it does not dominate
 *
 *  [ a ] (dominates b)
 *       \
 *        [ d ] (a is the direct ancestor of d; d does NOT dominate b)
 *       ^      
 *      / brif to d
 *  [ b ] 
 *    | brif to c
 *  [ c ]
 *
 *
 *  Case b -> c is brif false (ie b -> d is brif true)
 *  
 *    [ a ] -> [ d ]
 *     ...
 *    [ b ]
 *      | (now a regular Jump)
 *    [ c ]
 *
 *    where instrs(b) = instrs(b) @ [brif #a]
 *    and there is no longer a b->d edge
 *
 *  Case b -> c is brif true (ie b -> d is brif false)
 *    (1) Add a eqz to the end of instrs(b)
 *    (2) Flip the brif edges
 *    (3) Recurse
 **)
let rec t1_nested_B : G.vertex -> uinstr_graph -> dom_data -> type_map_type -> uinstr_graph option =
  fun b_v graph dom_data ty_map ->
  match (G.find_succ b_v (JumpBrIf true, ()) graph,
      G.find_succ b_v (JumpBrIf false, ()) graph) with
  | (Some d_v, Some c_v)
      when ((b_v <> c_v) && (b_v <> d_v) && (c_v <> d_v)
        && (not (dominates d_v b_v dom_data))) ->
    let ok_pvs =
      List.filter
        (fun (a1_v, _) -> (a1_v <> b_v) && (dominates a1_v b_v dom_data))
        (G.vertex_prevs d_v graph) in
    (match ok_pvs with
    | [(a_v, _)] ->
      (match count_br_level b_v a_v dom_data graph with
      | Some a_lvl ->
        let b_block = vertex_block b_v graph in
        let b_instrs = b_block.instrs in
        (* Need to break up at a slightly higher level *)
        let brif_instr = noregion (Ast.BrIf (int_to_var (a_lvl))) in
        let b_block1 = { b_block with instrs = b_instrs @ [brif_instr] } in

        (* Update the graph *)
        let graph1 = G.add_vertex_label b_v (b_block1, ()) graph in
        let graph2 = G.remove_basic_edge (b_v, d_v) graph1 in
        let graph3 = G.remove_basic_edge (b_v, c_v) graph2 in
        let graph4 = G.add_edge (b_v, (Jump, ()), c_v) graph3 in
        Some graph4

      | _ -> None)
    | _ -> None)

  | (Some c_v, Some d_v)
      when ((b_v <> c_v) && (b_v <> d_v) && (c_v <> d_v)
        && (not (dominates d_v b_v dom_data))) ->
    let b_block = vertex_block b_v graph in
    let b_instrs1 = b_block.instrs @ [eqz_instr] in
    let b_block1 = { b_block with instrs = b_instrs1 } in

    (* Update the graph and recurse *)
    let graph1 = G.add_vertex_label b_v (b_block1, ()) graph in
    let graph2 = G.remove_basic_edge (b_v, c_v) graph1 in
    let graph3 = G.remove_basic_edge (b_v, d_v) graph2 in
    let graph4 = G.add_edge (b_v, (JumpBrIf true, ()), d_v) graph3 in
    let graph5 = G.add_edge (b_v, (JumpBrIf false, ()), c_v) graph4 in
    
    t1_nested_B b_v graph5 dom_data ty_map
  | _ -> None


(* Do contraction on everything in this graph *)
let t1_seq : uinstr_graph -> G.vertex -> type_map_type -> uinstr_graph option =
  fun graph root_v ty_map ->
    (* Fold the self loops *)
    let (graph_sA, dom_data_sA, count_sA) = G.VSet.fold
      (fun u (g, d, c) ->
        match t1_self_A u g ty_map with
        | None -> (g, d, c)
        | Some g1 ->
          let _ = print_debug_medium ("t1_self_A: " ^ string_of_int u) in
          (g1, graph_to_dom_data g1 root_v, c + 1))
      graph.vertex_set (graph, graph_to_dom_data graph root_v, 0) in

    (* Fold the indirect jump of 1-level *)
    let (graph_sB, dom_data_sB, count_sB) = G.VSet.fold
      (fun u (g, d, c) ->
        match t1_self_B u g d ty_map with
        | None -> (g, d, c)
        | Some g1 ->
          let _ = print_debug_medium ("t1_self_B: " ^ string_of_int u) in
          (g1, graph_to_dom_data g1 root_v, c + 1))
      graph_sA.vertex_set (graph_sA, dom_data_sA, count_sA) in

    let (graph_sC, dom_data_sC, count_sC) = G.VSet.fold
      (fun u (g, d, c) ->
        match t1_self_C u g ty_map with
        | None -> (g, d, c)
        | Some g1 ->
          let _ = print_debug ("t1_self_C: " ^ string_of_int u) in
          (g1, graph_to_dom_data g1 root_v, c + 1))
      graph_sB.vertex_set (graph_sB, dom_data_sB, count_sB) in


    let (graph_nA, dom_data_nA, count_nA) = G.VSet.fold
      (fun u (g, d, c) ->
        match t1_nested_A u g d ty_map with
        | None -> (g, d, c)
        | Some g1 ->
          let _ = print_debug ("t1_nested_A: " ^ string_of_int u) in
          (g1, graph_to_dom_data g1 root_v, c + 1))
        graph_sC.vertex_set (graph_sC, dom_data_sC, count_sC) in


    let (graph_nB, dom_data_nB, count_nB) = G.VSet.fold
      (fun u (g, d, c) ->
        match t1_nested_B u g d ty_map with
        | None -> (g, d, c)
        | Some g1 ->
          (g1, graph_to_dom_data g1 root_v, c + 1))
        graph_nA.vertex_set (graph_nA, dom_data_nA, count_nA) in

    match count_nB with
    | 0 -> None
    | _ -> Some graph_nB

(* T2 algorithm
 * Perform edge contraction when this_v matches one of the following specific structures
 * .....
 *  \ | /
 *  [ a ]
 *    |  where br is Jump
 *  [ b ]
 *  / | \
 * .....
 *
 *  This becomes
 * .....
 *  \|/
 *  [instrs(a) @ instrs(b)]
 *  /|\
 * .....
 *)
let t2_branch : G.vertex -> uinstr_graph -> uinstr_graph option =
  fun b_v graph ->
    match G.find_only_prev b_v (Jump, ()) graph with
    | Some a_v when  (a_v <> b_v) ->
      (* Update a_v label *)
      let a_block = vertex_block a_v graph in
      let a_instrs1 = a_block.instrs @ (vertex_instrs b_v graph) in
      let a_block1 = { a_block with instrs = a_instrs1 } in
      let graph1 = G.add_vertex_label a_v (a_block1, ()) graph in

      (* Delete b_v from the graph *)
      let b_succs = G.vertex_succs b_v graph1 in
      let graph2 = G.remove_vertex b_v graph1 in
      let graph3 = List.fold_left (fun g (s, b) -> G.add_edge (a_v, b, s) g) graph2 b_succs in
      Some graph3
    | _ -> None

(* T2 algorithm cont'd
 * Another case is geting the if statement to collapse correctly:
 *             \ | /
 *             [ a ]
 *    if true  /   \ if false
 *         [ b ]   [ c ]
 *             \   /
 *             [ d ]
 *             / | \
 *
 * This is tranformed into
 *          \ | /
 *          [ a @ if (b, c) ]
 *            |
 *          [ d ]
 *          / | \
 *)
let t2_ifA : G.vertex -> uinstr_graph -> type_map_type -> uinstr_graph option =
  fun this_v graph ty_map ->
    match (G.find_succ this_v (JumpIf true, ()) graph,
        G.find_succ this_v (JumpIf false, ()) graph) with
    | (Some vt, Some vf) ->
      (* See if vt and vf share the same unique successor *)
      (match (G.vertex_succs vt graph, G.vertex_succs vf graph) with
      | ([(t1, (Jump, _))], [(t2, (Jump, _))]) when (t1 = t2) ->
        (* Update this_v with the new block *)
        let block = vertex_block this_v graph in
        let true_instrs = vertex_instrs vt graph in
        let false_instrs = vertex_instrs vf graph in
        let if_type = infer_stack_type true_instrs ty_map i32ty in
        let if_instr = noregion (Ast.If (if_type, true_instrs, false_instrs)) in
        let block1 = { block with instrs = block.instrs @ [if_instr] } in
        let graph1 = G.add_vertex_label this_v (block1, ()) graph in

        (* Remove vt, vf, and make a new connection from this_v to t *)
        let graph2 = G.remove_vertex vt graph1 in
        let graph3 = G.remove_vertex vf graph2 in
        let graph4 = G.update_succs this_v [(t1, (Jump, ()))] graph3 in
        Some graph4

      | _ -> None)
    | _ -> None

(* T2 algorithm cont'd
 * Another case is geting the if statement to collapse correctly:
 *             \ | /
 *             [ a ]
 *    if true  /   \ if false
 *         [ b ]   [ c ]
 * where b and c are leaves
 *
 * This is tranformed into
 *          \ | /
 *          [ a @ if (b, c) ]
 *)
let t2_ifB : G.vertex -> uinstr_graph -> type_map_type -> uinstr_graph option =
  fun a_v graph ty_map ->
    match (G.find_succ a_v (JumpIf true, ()) graph,
        G.find_succ a_v (JumpIf false, ()) graph) with
    | (Some b_v, Some c_v)
        when ((b_v <> c_v)
            && (G.vertex_succs b_v graph = [])
            && (G.vertex_succs c_v graph = [])) ->
      let a_block = vertex_block a_v graph in
      let a_instrs = a_block.instrs in
      let b_instrs = vertex_instrs b_v graph in
      let c_instrs = vertex_instrs c_v graph in
      let b_type = infer_stack_type b_instrs ty_map i32ty in
      let if_instr = noregion (Ast.If (b_type, b_instrs, c_instrs)) in
      let a_block1 = { a_block with instrs = a_instrs @ [if_instr] } in

      let graph1 = G.add_vertex_label a_v (a_block1, ()) graph in
      let graph2 = G.remove_vertex b_v graph1 in
      let graph3 = G.remove_vertex c_v graph2 in
      Some graph3

    | _ -> None

(* T2 algorithm cont'd
 * BrIf statements being all that
 *         \ | /
 *         [ a ]
 * (brif b)  |  \ (brif b)
 *         [ b ] |
 *           |  /
 *         [ c ]
 *         / | \
 *
 * Case (a -> b) is BrIf false (ie a -> c is true)
 * Would be transformed into
 *    \ | /
 *    [ a ]
 *      |
 *    [ c ]
 *    / | \
 *  where instrs(a) = block { instrs(a) @ [brif 0] @ instrs(b) }
 *
 * Case (a -> b) is BrIf true (ie a -> c is false)
 *  (1) add eqz to the final statement of instrs(a)
 *  (2) flip the order of BrIf true and BrIf false edges
 *  (3) recursion
 *)
let rec t2_brif_A : G.vertex -> uinstr_graph -> dom_data -> type_map_type -> uinstr_graph option =
  fun a_v graph dom_data ty_map ->
    match (G.find_succ a_v (JumpBrIf true, ()) graph,
        G.find_succ a_v (JumpBrIf false, ()) graph) with

    (* Case 1 *)
    | (Some c_v, Some b_v)
      when ((a_v <> b_v) && (a_v <> c_v) && (b_v <> c_v)
        && (G.only_edge_exists (b_v, (Jump, ()), c_v) graph)
        && (dominates a_v c_v dom_data)) ->
      let a_block = vertex_block a_v graph in
      let a_instrs = a_block.instrs in
      let brif_instr = noregion (Ast.BrIf (int_to_var 0)) in
      let b_instrs = vertex_instrs b_v graph in
      let body_type = infer_stack_type (a_instrs @ [brif_instr] @ b_instrs) ty_map i32ty in
      let block_instr =
        noregion (Ast.Block (body_type,
          a_instrs @ [brif_instr] @ b_instrs)) in
      let a_block1 = { a_block with instrs = [block_instr] } in

      (* Update grpah *)
      let graph1 = G.add_vertex_label a_v (a_block1, ()) graph in
      let graph2 = G.remove_vertex b_v graph1 in
      let graph3 = G.remove_basic_edge (a_v, c_v) graph2 in
      let graph4 = G.add_edge (a_v, (Jump, ()), c_v) graph3 in
      Some graph4

    (* Case 2 *)
    | (Some b_v, Some c_v)
      when ((a_v <> b_v) && (a_v <> c_v) && (b_v <> c_v)
        && (G.only_edge_exists (b_v, (Jump, ()), c_v) graph)
        && (dominates a_v c_v dom_data)) ->
      let a_block = vertex_block a_v graph in
      let a_block1 = { a_block with instrs = a_block.instrs @ [eqz_instr] } in

      (* Update the graph and recurse *)
      let graph1 = G.add_vertex_label a_v (a_block1, ()) graph in
      let graph2 = G.remove_basic_edge (a_v, b_v) graph1 in
      let graph3 = G.remove_basic_edge (a_v, c_v) graph2 in
      let graph4 = G.add_edge (a_v, (JumpBrIf false, ()), b_v) graph3 in
      let graph5 = G.add_edge (a_v, (JumpBrIf true, ()), c_v) graph4 in

      t2_brif_A a_v graph5 dom_data ty_map

    | _ -> None


(* T2 algorithm cont'd
 * BrIf statements being all that
 *         \ | /
 *         [ a ]
 * (brif b)  |  \ (brif b)
 *         [ b ] [ c ]
 *               / | \
 *
 * where b is a leaf vertex: guaranteed have Return
 *
 * Case (a -> b) is BrIf false (ie a -> c is true)
 * Would be transformed into
 *    \ | /
 *    [ a ]
 *      |
 *    [ c ]
 *    / | \
 *  where instrs(a) = block { block { instrs(a) @ [brif 0] @ instrs(b) }
 *
 * Case (a -> b) is BrIf true (ie a -> c is false)
 *  (1) add eqz to the final statement of instrs(a)
 *  (2) flip the order of BrIf true and BrIf false edges
 *  (3) recursion
 *)
let rec t2_brif_B : G.vertex -> uinstr_graph -> dom_data -> type_map_type -> uinstr_graph option =
  fun a_v graph dom_data ty_map ->
    match (G.find_succ a_v (JumpBrIf true, ()) graph,
        G.find_succ a_v (JumpBrIf false, ()) graph) with

    (* Case 1 *)
    | (Some c_v, Some b_v)
      when ((a_v <> b_v) && (a_v <> c_v) && (b_v <> c_v)
        && (G.vertex_succs b_v graph = [])
        && (exists_instr is_instr_return (vertex_instrs b_v graph))
        && (dominates a_v c_v dom_data)) ->

      let a_block = vertex_block a_v graph in
      let a_instrs = a_block.instrs in
      let brif_instr = noregion (Ast.BrIf (int_to_var 0)) in
      let b_instrs = vertex_instrs b_v graph in
      let body_instrs = a_instrs @ [brif_instr] @ b_instrs in
      let body_type =
        if vertex_instrs c_v graph = []
          then infer_stack_type body_instrs ty_map i32ty
          (*
          else infer_stack_type body_instrs ty_map i32ty in
          *)
          else [] in

      let block_instr = noregion (Ast.Block (body_type, body_instrs)) in
      let a_block1 = { a_block with instrs = [block_instr] } in

      let graph1 = G.add_vertex_label a_v (a_block1, ()) graph in
      let graph2 = G.remove_vertex b_v graph1 in
      let graph3 = G.remove_basic_edge (a_v, c_v) graph2 in
      let graph4 = G.add_edge (a_v, (Jump, ()), c_v) graph3 in
      Some graph4

    (* Case 2 *)
    | (Some b_v, Some c_v)
      when ((a_v <> b_v) && (a_v <> c_v) && (b_v <> c_v)
        && (G.vertex_succs b_v graph = [])
        && (exists_instr is_instr_return (vertex_instrs b_v graph))
        && (dominates a_v c_v dom_data)) ->
      let a_block = vertex_block a_v graph in
      let a_block1 = { a_block with instrs = a_block.instrs @ [eqz_instr] } in

      (* Update the graph and recurse *)
      let graph1 = G.add_vertex_label a_v (a_block1, ()) graph in
      let graph2 = G.remove_basic_edge (a_v, b_v) graph1 in
      let graph3 = G.remove_basic_edge (a_v, c_v) graph2 in
      let graph4 = G.add_edge (a_v, (JumpBrIf false, ()), b_v) graph3 in
      let graph5 = G.add_edge (a_v, (JumpBrIf true, ()), c_v) graph4 in

      t2_brif_B a_v graph5 dom_data ty_map

    | _ -> None


(* T2 algorithm cont'd
 * BrIf statements being all that
 *         \ | /
 *         [ a ]
 * (brif b) | |  (brif not b)
 *         [ b ]
 *         / | \
 *
 *  when both brif true and brif false go to the same branch
 *
 * Would be transformed into
 *    \ | /
 *    [ a ]
 *      | (regular jump)
 *    [ b ]
 *    / | \
 *  where instrs(a) = instrs(a) @ [Drop]
 *
 *)
let rec t2_brif_C : G.vertex -> uinstr_graph -> dom_data -> type_map_type -> uinstr_graph option =
  fun a_v graph dom_data ty_map ->
    match (G.find_succ a_v (JumpBrIf true, ()) graph,
        G.find_succ a_v (JumpBrIf false, ()) graph) with

    (* Case 1 *)
    | (Some b_v, Some b_v1)
      when (b_v = b_v1) ->

      let a_block = vertex_block a_v graph in
      let a_instrs = a_block.instrs in
      let drop_instr = noregion (Ast.Drop) in
      let a_block1 = { a_block with instrs = a_instrs @ [drop_instr] } in

      let graph1 = G.add_vertex_label a_v (a_block1, ()) graph in
      let graph2 = G.remove_basic_edge (a_v, b_v) graph1 in (* Removes both *)
      let graph3 = G.remove_basic_edge (a_v, b_v) graph2 in (* Just to be sure *)
      let graph4 = G.add_edge (a_v, (Jump, ()), b_v) graph3 in

      Some graph4

    | _ -> None


(* Run t2 in seq *)
let t2_seq : uinstr_graph -> G.vertex -> type_map_type -> uinstr_graph option =
  fun graph root_v ty_map ->
    (* Fold the self loops *)
    let (graph1, count1) = G.VSet.fold
      (fun u (g, c) ->
        match t2_branch u g with
        | None -> (g, c)
        | Some g1 ->
          let _ = print_debug ("t2_branch: " ^ string_of_int u) in
          (g1, c + 1))
      graph.vertex_set (graph, 0) in

    (* Fold the indirect jump of 1-level *)
    let (graph2, count2) = G.VSet.fold
      (fun u (g, c) ->
        match t2_ifA u g ty_map with
        | None -> (g, c)
        | Some g1 ->
          let _ = print_debug ("t2_ifA: " ^ string_of_int u) in
          (g1, c + 1))
      graph1.vertex_set (graph1, count1) in

    let dom2 = graph_to_dom_data graph2 root_v in
    let (graph3, dom3, count3) = G.VSet.fold
      (fun u (g, d, c) ->
        match t2_brif_A u g d ty_map with
        | None -> (g, d, c)
        | Some g1 ->
          let _ = print_debug_medium ("t2_brif_A: " ^ string_of_int u) in
          (g1, graph_to_dom_data g1 root_v, c + 1))
      graph2.vertex_set (graph2, dom2, count2) in

    let (graph4, dom4, count4) = G.VSet.fold
      (fun u (g, d, c) ->
        match t2_brif_B u g d ty_map with
        | None -> (g, d, c)
        | Some g1 ->
          let _ = print_debug_medium ("t2_brif_B: " ^ string_of_int u) in
          (g1, graph_to_dom_data g1 root_v, c + 1))
      graph3.vertex_set (graph3, dom3, count3) in

    let (graph5, dom5, count5) = G.VSet.fold
      (fun u (g, d, c) ->
        match t2_brif_C u g d ty_map with
        | None -> (g, d, c)
        | Some g1 ->
          let _ = print_debug_medium ("t2_brif_C: " ^ string_of_int u) in
          (g1, graph_to_dom_data g1 root_v, c + 1))
      graph4.vertex_set (graph4, dom4, count4) in

    let (graph6, dom6, count6) = G.VSet.fold
      (fun u (g, d, c) ->
        match t2_ifB u g ty_map with
        | None -> (g, d, c)
        | Some g1 ->
          let _ = print_debug_medium ("t2_if_B: " ^ string_of_int u) in
          (g1, graph_to_dom_data g1 root_v, c + 1))
      graph5.vertex_set (graph5, dom5, count5) in

    match count6 with
    | 0 -> None
    | _ -> Some graph6

(* Run both t1 and t2 until both converge *)
let rec contract_flow : uinstr_graph -> G.vertex -> type_map_type -> uinstr_graph =
  fun graph root_v ty_map ->
    let _ = print_debug ("contract fow called!") in
    match t2_seq graph root_v ty_map with
    | None ->
      (match t1_seq graph root_v ty_map with
      | None -> graph
      | Some graph1 -> contract_flow graph1 root_v ty_map)
    | Some graph1 -> contract_flow graph1 root_v ty_map

(* Putting all the above together.
 * Initialize the calls to dom_data_to_block then extract *)
let instr_graph_to_instrs
  : ('a, 'b) instr_graph
  -> G.vertex
  -> type_map_type
  -> Types.value_type
  -> Ast.instr list =
  fun graph root_v ty_map def_ty ->

    let graph0 = G.trim_graph root_v graph in
    let graph1 = contract_flow graph0 root_v ty_map in

    let _ = print_debug_high ("pre-contracting graph") in
    let _ = print_debug_high (string_of_instr_graph graph0) in
    
    let _ = print_debug_high ("post-contracting graph") in
    let _ = print_debug_high (string_of_instr_graph graph1) in

    match G.vertices graph1 with
    | [root1_v] when (root_v = root1_v) ->

      let instrs = vertex_instrs root_v graph1 in
      let block_instrs = instrs in
      block_instrs

    | _ ->
      let _ = print_debug "instr_graph_to_instrs: non-singleton graph after contract" in
      let _ = print_debug (string_of_instr_graph graph1) in
      []


let instr_graphs_differ : uinstr_graph -> uinstr_graph -> bool =
  fun graph0 graph1 ->
    true


