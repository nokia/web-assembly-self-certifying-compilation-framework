(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


open Wasm
open Ast
open Operators
       
open Wasm_utils
open Instr_graph
open State_types
open Proof_types
open Func_types
open Debug

open Smt_ir 
open Sym_eval_interface

module Eval: EvalT =
  struct

    let memory = uf_memory

    (* redefinitions *)
    let prev_pointer p = convert_to_int_pointer (State_types.prev_pointer p)
    let succ_pointer p = convert_to_int_pointer (State_types.succ_pointer p)                                                
                   
    (* States being equivalent *)
    let states_equiv : state -> state -> formula =
      fun state0 state1 ->
      CommentForm ("states_equiv",
                   AndForm
                     [ ArrsEqForm (values state0, values state1);
                       PtrsRelForm
                         (stack_pointer state0,
                          IntEq,
                          stack_pointer state1);
                       ArrsEqForm (locals state0, locals state1);
                       ArrsEqForm (globals state0, globals state1);
                       SymEqForm (memory state0, memory state1) ])

    module ConstMap =
      (* maps constant values to uninterpreted symbols *)
      struct 
        type const_map = {
            map: (wasm_value,string) Hashtbl.t;
            mutable nxt: int;
          }

        let new_map: unit -> const_map =
          fun () ->
          {
            map = Hashtbl.create 10;
            nxt = 0;
          }

        let cmap = new_map()  (* fixed map vs. creating a new one per evaluation *)
                          
        let lookup: wasm_value -> string =
          fun c -> 
          try Hashtbl.find cmap.map c
          with Not_found ->
            let k = cmap.nxt in
            let cstr = Printf.sprintf "C%d" k in 
            cmap.nxt <- k+1;
            Hashtbl.add cmap.map c cstr;
            cstr

        let zero = UFVal(lookup (Wasm_utils.int32_to_literal 0l), [])
                        
        let const_decls: unit -> smt_decl list =
          fun () ->
          Hashtbl.fold 
            (fun _ csmt res ->
              let decl = SmtDecls [Printf.sprintf "(declare-const %s Val)" csmt] in
              decl::res
            )
            cmap.map
            []
            
      end



        
    (* Evaluation semantics *)
    let eval_state_instr : state -> Ast.instr -> state -> sym_config -> formula =
      fun state0 instr0 state1 sym_conf ->
      (* Variables for state0 *)
      let k0 = values state0 in
      let p0 = stack_pointer state0 in
      let l0 = locals state0 in
      let g0 = globals state0 in
      let m0 = memory state0 in

      (* Variables for state1 *)
      let k1 = values state1 in
      let p1 = stack_pointer state1 in
      let l1 = locals state1 in
      let g1 = globals state1 in
      let m1 = memory state1 in

      (* Some common pointer / values manipulations on state0 *)
      let p0_p = prev_pointer p0 in
      let p0_pp = prev_pointer p0_p in
      let p0_s = succ_pointer p0 in

      (* The top k values from the value stack *)
      let k0_v0 = SelectVal (k0, p0) in
      let k0_v1 = SelectVal (k0, p0_p) in
      let k0_v2 = SelectVal (k0, p0_pp) in

      (* Top k-values of k0 become set to zero *)
      let k0_z = StoreArr (k0, p0, ConstMap.zero) in
      let k0_zz = StoreArr (k0_z, p0_p, ConstMap.zero) in

      (* Numeric operations *)

      match instr0.it with

      | Ast.Unreachable ->
         CommentForm ("eval: unreachable", BoolForm false)

      (* k1 = k0[p0 + 1 <- c]
       * p1 = p0 + 1 *)
      | Ast.Const c ->
         let vals_rhs = StoreArr (k0, p0_s, UFVal(ConstMap.lookup c, [])) in
         CommentForm ("eval: const " ^ string_of_literal c,
                      AndForm
                        [ ArrsEqForm (k1, vals_rhs);
                          PtrsRelForm (p1, IntEq, p0_s);
                          ArrsEqForm (l1, l0);
                          ArrsEqForm (g1, g0);
                          SymEqForm (m1, m0); ])

      (* k1 = k0[p0 <- unary(unop, k0[p0])] *)
      | Ast.Unary unop ->
         let vals_rhs = StoreArr (k0, p0, UFVal(string_of_unop unop, [k0_v0])) in
         CommentForm ("eval: unary " ^ string_of_unop unop,
                      AndForm
                        [ ArrsEqForm (k1, vals_rhs);
                          PtrsRelForm (p1, IntEq, p0);
                          ArrsEqForm (l1, l0);
                          ArrsEqForm (g1, g0);
                          SymEqForm (m1, m0); ])

      (* k1 = k0[p0 <- 0; p0 - 1 <- binary(binop, k0[p0], k0[p0 - 1])]
       * p1 = p0 - 1 *)
      | Ast.Binary binop ->
         let bin_val = UFVal(string_of_binop binop, [k0_v0; k0_v1]) in
         let vals_rhs = StoreArr (k0_z, p0_p, bin_val) in
         CommentForm ("eval: binary " ^ string_of_binop binop,
                      AndForm
                        [ ArrsEqForm (k1, vals_rhs);
                          PtrsRelForm (p1, IntEq, p0_p);
                          ArrsEqForm (l1, l0);
                          ArrsEqForm (g1, g0);
                          SymEqForm (m1, m0); ])

      (* k1 = k0[p0 <- test(testop, k0[p0]] *)
      | Ast.Test testop ->
         let vals_rhs = StoreArr (k0, p0, UFVal(string_of_testop testop, [k0_v0])) in
         CommentForm ("eval: testop " ^ string_of_testop testop,
                      AndForm
                        [ ArrsEqForm (k1, vals_rhs);
                          PtrsRelForm (p1, IntEq, p0);
                          ArrsEqForm (l1, l0);
                          ArrsEqForm (g1, g0);
                          SymEqForm (m1, m0); ])

      (* k1 = k0[p0 <- 0; p0 - 1 <- compare(relop, k0[p0], k0[p0 - 1]]
       * p1 = p0 - 1 *)
      | Ast.Compare relop ->
         let comp_val = UFVal(Wasm_utils.string_of_relop relop, [k0_v0;k0_v1]) in
         let vals_rhs = StoreArr (k0_z, p0_p, comp_val) in
         CommentForm ("eval: compare " ^ Wasm_utils.string_of_relop relop,
                      AndForm
                        [ ArrsEqForm (k1, vals_rhs);
                          PtrsRelForm (p1, IntEq, p0_p);
                          ArrsEqForm (l1, l0);
                          ArrsEqForm (g1, g0);
                          SymEqForm (m1, m0); ])

      (* k1 = k0[p0 <- convert(cvtop, k0[p0]] *)
      | Ast.Convert cvtop ->
         let cvt_val = UFVal(string_of_cvtop cvtop, [k0_v0]) in
         let vals_rhs = StoreArr (k0, p0, cvt_val) in
         CommentForm ("eval: convert " ^ string_of_cvtop cvtop,
                      AndForm
                        [ ArrsEqForm (k1, vals_rhs);
                          PtrsRelForm (p1, IntEq, p0);
                          ArrsEqForm (l1, l0);
                          ArrsEqForm (g1, g0);
                          SymEqForm (m1, m0); ])

      (* Nothing happens here *)
      | Ast.Nop ->
         CommentForm ("eval: nop",
                      AndForm
                        [ ArrsEqForm (k1, k0);
                          PtrsRelForm (p1, IntEq, p0);
                          ArrsEqForm (l1, l0);
                          ArrsEqForm (g1, g0);
                          SymEqForm (m1, m0); ])

      (* k1 = k0[p0 <- 0]
       * p1 = p0 - 1 *)
      | Ast.Drop ->
         CommentForm ("eval: drop",
                      AndForm
                        [ ArrsEqForm (k1, k0_z);
                          PtrsRelForm (p1, IntEq, p0_p);
                          ArrsEqForm (l1, l0);
                          ArrsEqForm (g1, g0);
                          SymEqForm (m1, m0) ])

      (* if isZero k0[p0] then
       *    k1 = k0[p0 - 2 <- k0[p0 - 1]]
       * else
       *    k1 = k0[p0 - 2 <- k0[p0 - 2]]
       * endif
       * p1 = p0 - 2 *)
      | Ast.Select ->
         let is_zero = UFVal("is_zero", [k0_v0]) in
         (* let not_zero = UFBoolForm("is_nonzero", [k0_v0]) in *)
         let vals_rhs_zero = StoreArr (k0_zz, p0_pp, k0_v1) in
         let vals_rhs_not = StoreArr (k0_zz, p0_pp, k0_v2) in
         CommentForm ("eval: select",
                      AndForm
                        [
                          SymEqForm(ArrayVal k1, UFVal("ite", [is_zero; ArrayVal vals_rhs_zero; ArrayVal vals_rhs_not])); 

                          (* ImplForm (is_zero, ArrsEqForm (k1, vals_rhs_zero));
                          ImplForm (not_zero, ArrsEqForm (k1, vals_rhs_not)); *)
                          
                          PtrsRelForm (p1, IntEq, p0_pp);
                          ArrsEqForm (l1, l0);
                          ArrsEqForm (g1, g0);
                          SymEqForm (m1, m0) ])

      (* k1 = k0[p0 + 1 <- l0[x]]
       * p1 = p0 + 1 *)
      | Ast.LocalGet x ->
         let x_ptr = VarPtr x in
         let loc_val = SelectVal (l0, x_ptr) in
         let vals_rhs = StoreArr (k0, p0_s, loc_val) in
         CommentForm ("eval: local_get " ^ string_of_var x,
                      AndForm
                        [ ArrsEqForm (k1, vals_rhs);
                          PtrsRelForm (p1, IntEq, p0_s);
                          ArrsEqForm (l1, l0);
                          ArrsEqForm (g1, g0);
                          SymEqForm (m1, m0); ])

      (* k1 = k0[p0 <- 0]
       * l1 = l0[x <- k0[p0]]
       * p1 = p0 - 1 *) 
      | Ast.LocalSet x ->
         let x_ptr = VarPtr x in
         let locs_rhs = StoreArr (l0, x_ptr, k0_v0) in
         CommentForm ("eval: local_set " ^ string_of_var x,
                      AndForm
                        [ ArrsEqForm (k1, k0_z);
                          PtrsRelForm (p1, IntEq, p0_p);
                          ArrsEqForm (l1, locs_rhs);
                          ArrsEqForm (g1, g0);
                          SymEqForm (m1, m0); ])
                     
      (* l1 = l0[x <- k0[p0]] *)
      | Ast.LocalTee x ->
         let x_ptr = VarPtr x in
         let locs_rhs = StoreArr (l0, x_ptr, k0_v0) in
         CommentForm ("eval: local_tee " ^ string_of_var x,
                      AndForm
                        [ ArrsEqForm (k1, k0);
                          PtrsRelForm (p1, IntEq, p0);
                          ArrsEqForm (l1, locs_rhs);
                          ArrsEqForm (g1, g0);
                          SymEqForm (m1, m0); ])

      (* k1 = k0[p0 + 1 <- g0[x]]
       * p1 = p0 + 1 *)
      | Ast.GlobalGet x ->
         let x_ptr = VarPtr x in
         let globs_val = SelectVal (g0, x_ptr) in
         let vals_rhs = StoreArr (k0, p0_s, globs_val) in
         CommentForm ("eval: global_get " ^ string_of_var x,
                      AndForm
                        [ ArrsEqForm (k1, vals_rhs);
                          PtrsRelForm (p1, IntEq, p0_s);
                          ArrsEqForm (l1, l0);
                          ArrsEqForm (g1, g0);
                          SymEqForm (m1, m0) ])


      (* k1 = k0[p0 <- 0]
       * g1 = g0[x <- k0[p0]]
       * p1 = p0 - 1 *)
      | Ast.GlobalSet x ->
         let x_ptr = VarPtr x in
         let glbs_rhs = StoreArr (g0, x_ptr, k0_v0) in
         CommentForm ("eval: global_set " ^ string_of_var x,
                      AndForm
                        [ ArrsEqForm (k1, k0_z);
                          PtrsRelForm (p1, IntEq, p0_p);
                          ArrsEqForm (l1, l0);
                          ArrsEqForm (g1, glbs_rhs);
                          SymEqForm (m1, m0) ])

      (* k1 = k0[p0 <- m0[k0[p0] + offset]] *)
      | Ast.Load op ->
         let mem_val = UFVal(string_of_loadop op, [m0; k0_v0]) in 
         let vals_rhs = StoreArr (k0, p0, mem_val) in
         CommentForm ("eval: load " ^ Int32.to_string op.offset,
                      AndForm
                        [ ArrsEqForm (k1, vals_rhs);
                          PtrsRelForm (p1, IntEq, p0);
                          ArrsEqForm (l1, l0);
                          ArrsEqForm (g1, g0);
                          SymEqForm (m1, m0); ])

      (* m1 = m0[k0[p0 - 1] + offset <- k0[p0]]
       * p1 = p0 - 2 *)
      | Ast.Store op ->
         (* let addr = OffsetPtr (CastedPtr k0_v1, op.offset) in *)
         let mems_rhs = UFVal(string_of_storeop op, [m0; k0_v0; k0_v1]) in
         CommentForm ("eval: store " ^ Int32.to_string op.offset,
                      AndForm
                        [ ArrsEqForm (k1, k0_zz);
                          PtrsRelForm (p1, IntEq, p0_pp);
                          ArrsEqForm (l1, l0);
                          ArrsEqForm (g1, g0);
                          SymEqForm (m1, mems_rhs); ])

      | Ast.MemorySize ->
         let mem_size = UFVal(ConstMap.lookup (Wasm_utils.int32_to_literal sym_conf.memory_max),[]) in
         let vals_rhs = StoreArr (k0, p0_s, mem_size) in
         CommentForm ("eval: memory_size",
                      AndForm
                        [ ArrsEqForm (k1, vals_rhs);
                          PtrsRelForm (p1, IntEq, p0_s);
                          ArrsEqForm (l1, l0);
                          ArrsEqForm (g1, g0);
                          SymEqForm (m1, m0); ])

      | Ast.MemoryGrow ->
         let mem_size = UFVal(ConstMap.lookup (Wasm_utils.int32_to_literal sym_conf.memory_max),[]) in
         let vals_rhs = StoreArr (k0, p0_s, mem_size) in
         CommentForm ("eval: memory_grow",
                      AndForm
                        [ ArrsEqForm (k1, vals_rhs);
                          PtrsRelForm (p1, IntEq, p0_s);
                          ArrsEqForm (l1, l0);
                          ArrsEqForm (g1, g0);
                          SymEqForm (m1, m0); ])

      (* Block, Loop, If, Br, BrIf, Br,
       * Return, Call, CallIndirect, Unreachable *)
      | Ast.Block _ | Ast.Loop _
        | Ast.If _ | Ast.Br _ | Ast.BrIf _ | Ast.BrTable _
        | Ast.Return | Ast.Call _ | Ast.CallIndirect _ ->
         CommentForm ("eval: control_flow",
                      (prerr_debug "eval_state_action: non-basic instruction"; BoolForm false))

    (* Evaluating branch conditions *)
    let eval_state_branch : state -> branch -> state -> sym_config -> formula =
      fun state0 br state1 sym_conf ->
      (* Variables for state0 *)
      let k0 = values state0 in
      let p0 = stack_pointer state0 in
      let l0 = locals state0 in
      let g0 = globals state0 in
      let m0 = memory state0 in

      (* Variables for state1 *)
      let k1 = values state1 in
      let p1 = stack_pointer state1 in
      let l1 = locals state1 in
      let g1 = globals state1 in
      let m1 = memory state1 in

      (* Some helpful definitions *)
      let p0_p = prev_pointer p0 in
      let k0_z = StoreArr (k0, p0, ConstMap.zero) in


      match br with
      (* Unconditional *)
      | Jump ->
         CommentForm ("eval: br",
                      AndForm
                        [ ArrsEqForm (k1, k0);
                          PtrsRelForm (p1, IntEq, p0);
                          ArrsEqForm (l1, l0);
                          ArrsEqForm (g1, g0);
                          SymEqForm (m1, m0); ])

      (* Due to If *)
      | JumpIf b ->
         CommentForm ("eval: if " ^ string_of_bool b,
                      AndForm
                        [ ArrsEqForm (k1, k0_z);
                          PtrsRelForm (p1, IntEq, p0_p);
                          ArrsEqForm (l1, l0);
                          ArrsEqForm (g1, g0);
                          SymEqForm (m1, m0); ])

      | JumpBrIf b ->
         CommentForm ("eval: brif " ^ string_of_bool b,
                      AndForm
                        [ ArrsEqForm (k1, k0_z);
                          PtrsRelForm (p1, IntEq, p0_p);
                          ArrsEqForm (l1, l0);
                          ArrsEqForm (g1, g0);
                          SymEqForm (m1, m0); ])

      | JumpIndex ind ->
         CommentForm ("eval: brindex " ^ Int32.to_string ind,
                      AndForm
                        [ ArrsEqForm (k1, k0_z);
                          PtrsRelForm (p1, IntEq, p0_p);
                          ArrsEqForm (l1, l0);
                          ArrsEqForm (g1, g0);
                          SymEqForm (m1, m0); ])

      | JumpDefault size ->
         CommentForm ("eval: brdefault " ^ Int32.to_string size,
                      AndForm
                        [ ArrsEqForm (k1, k0_z);
                          PtrsRelForm (p1, IntEq, p0_p);
                          ArrsEqForm (l1, l0);
                          ArrsEqForm (g1, g0);
                          SymEqForm (m1, m0); ])

    (* Phi function evaluation *)
    let eval_state_phi_map
        : G.vertex -> G.vertex -> state -> phi_vertex_map -> state -> sym_config -> string -> formula =
      fun prev_vertex this_vertex state0 phimap_at_vertex state1 sym_conf tag ->
      (* builds a formula that relates the symbolic state state0 and the
       * successor state state1 that results from evaluating the phi assignments
       * at this_vertex following the edge originating at prev_vertex. *)

      (* Numeric operations *)

      (* Work over a bunch of phi ghost states along the way *)
      let (phi_forms, phi_state1) =
        Int32Map.fold
          (fun _ xentry (phi_forms, phi_state0) ->
            let (new_x, phi_entry_for_x) = xentry in
            try
              let old_x = List.assoc prev_vertex phi_entry_for_x in
              let phi_state1 = phi_state tag (prev_vertex, old_x) (this_vertex, new_x) in

              let phi_k0 = values phi_state0 in
              let phi_p0 = stack_pointer phi_state0 in
              let phi_l0 = locals phi_state0 in
              let phi_g0 = globals phi_state0 in
              let phi_m0 = memory phi_state0 in

              (* Variables for state1 *)
              let phi_k1 = values phi_state1 in
              let phi_p1 = stack_pointer phi_state1 in
              let phi_l1 = locals phi_state1 in
              let phi_g1 = globals phi_state1 in
              let phi_m1 = memory phi_state1 in

              (* Build phi_state1 = phi_state0[new x <- phi_state0[old_x]] *)
              let old_x_ptr = VarPtr (noregion old_x) in
              let new_x_ptr = VarPtr (noregion new_x) in
              let old_x_val = SelectVal (phi_l0, old_x_ptr) in
              let phi_l_rhs = StoreArr (phi_l0, new_x_ptr, old_x_val) in
              let phi_form =
                AndForm
                  [ ArrsEqForm (phi_k1, phi_k0);
                    PtrsRelForm (phi_p1, IntEq, phi_p0);
                    ArrsEqForm (phi_l1, phi_l_rhs);
                    ArrsEqForm (phi_g1, phi_g0);
                    SymEqForm (phi_m1, phi_m0);] in
              (phi_form :: phi_forms, phi_state1)
            with
            | Not_found -> failwith("eval_state_phimap: missing entry in phimap"))
          phimap_at_vertex
          ([], state0) in

      CommentForm ("eval: phis ",
                   AndForm
                     ([ ArrsEqForm (values state1, values phi_state1);
                        PtrsRelForm (stack_pointer state1, IntEq, stack_pointer phi_state1);
                        ArrsEqForm (locals state1, locals phi_state1);
                        ArrsEqForm (globals state1, globals phi_state1);
                        SymEqForm (memory state1, memory phi_state1);]
                      @ phi_forms))


    (* Formulaic representation of evaluation for local basic and branches *)
    let eval_state_action : state -> action -> state -> phi_map -> sym_config -> string -> formula =
      fun state0 act0 state1 phi_map sym_conf tag ->
      match act0 with
      | BasicAct instr when (is_basic_instr instr) ->
         eval_state_instr state0 instr state1 sym_conf

      | JumpAct (br, next_v) ->
         eval_state_branch state0 br state1 sym_conf

      | PhiAct (prev_v, this_v) ->
         let phiv_map = lookup_phi_map this_v phi_map in
         eval_state_phi_map prev_v this_v state0 phiv_map state1 sym_conf tag

      (* Allow Calls to silently happen and check their validity in
       * the synchronization thing *)
      | CallAct x ->
         CommentForm ("eval: call " ^ string_of_var x,
                      BoolForm true)

      | CallIndirectAct x ->
         CommentForm ("eval: call_indirect " ^ string_of_var x,
                      BoolForm true)

      | StopAct ->
         CommentForm ("eval: stop",
                      states_equiv state0 state1)

      | _ ->
         CommentForm ("eval: default",
                      (prerr_debug ("eval_state_action: fallthrough case"); BoolForm false))

    (* Formulaic representation of exectuion *)
    let rec exec_state_actions : state -> action list -> phi_map -> sym_config -> string -> formula =
      fun state0 acts phi_map sym_conf tag ->
      match acts with
      | [] -> AndForm [BoolForm true]
      | (act0 :: acts_tl) ->
         let state1 = next_state state0 act0 in
         let evald = eval_state_action state0 act0 state1 phi_map sym_conf tag in
         match exec_state_actions state1 acts_tl phi_map sym_conf tag with
         | AndForm forms -> AndForm (evald :: forms)
         | execd -> AndForm [evald; execd]

    (* The "guard" predicate.
     * This differs from the "defined" predicate:
     * guard makes sure that the boolean conditions for branching are satisfied,
     * while defined makes sure that the state-action is well-defined *)
    let guarded_state_action : state -> action -> sym_config -> formula =
      fun state act sym_conf ->
      let k = values state in
      let p = stack_pointer state in
      let k_v0 = SelectVal (k, p) in

      match act with
      | JumpAct (br, _) ->
         (match br with
          | JumpIf b ->
             CommentForm ("guarded: if " ^ string_of_bool b,
                          ValsRelForm
                            (k_v0, (if b = false then IntEq else IntNeq), ConstMap.zero))

          | JumpBrIf b ->
             CommentForm ("guarded: brif " ^ string_of_bool b,
                          ValsRelForm
                            (k_v0, (if b = false then IntEq else IntNeq), ConstMap.zero))

          | JumpIndex ind ->
             CommentForm ("guarded: brindex " ^ Int32.to_string ind,
                          ValsRelForm (k_v0, IntEq, UFVal(ConstMap.lookup (Wasm_utils.int32_to_literal ind),[])))

          | JumpDefault size ->
             CommentForm ("guarded: brdefault " ^ Int32.to_string size,
                          UFBoolForm("leq", [UFVal(ConstMap.lookup (Wasm_utils.int32_to_literal size),[]); k_v0]))

          | _ ->
             CommentForm ("guarded: default",
                          BoolForm true))

      | BasicAct instr when (is_basic_instr instr) ->
         CommentForm ("guarded: instr",
                      BoolForm true)

      | PhiAct (prev_v, this_v) ->
         CommentForm ("guarded: phi " ^ G.string_of_vertex prev_v ^ "->" ^ G.string_of_vertex this_v,
                      BoolForm true)

      | CallAct x ->
         CommentForm ("guarded: call " ^ string_of_var x,
                      BoolForm true)

      | CallIndirectAct x ->
         CommentForm ("guarded: call_indirect " ^ string_of_var x,
                      BoolForm true)

      | StopAct ->
         CommentForm ("guarded: final",
                      BoolForm true)

      | _ ->
         CommentForm ("guarded: default",
                      (prerr_debug "guarded: fall through case"; BoolForm false))

    (* Stack pointer range.
     * sym_config.values_min is the value during an empty stack.
     *)
    let valid_stack_pointer : pointer -> sym_config -> formula =
      fun ptr sym_conf ->
      let vals_min = IntPtr (Int32.to_int sym_conf.values_min) in
      let vals_max = IntPtr (Int32.to_int sym_conf.values_max) in
      CommentForm ("valid: stack_pointer " ^ string_of_pointer ptr,
                   AndForm
                     [ PtrsRelForm (vals_min, IntLeq, ptr);
                       PtrsRelForm (ptr, IntLeq, vals_max) ])

    let valid_local_var : Ast.var -> sym_config -> formula =
      fun var sym_conf ->
      let locs_min = IntVal (Int32.to_int sym_conf.locals_min) in
      let locs_max = IntVal (Int32.to_int sym_conf.locals_max) in
      CommentForm ("valid: local_var " ^ string_of_var var,
                   AndForm
                     [ ValsRelForm (locs_min, IntLeq , IntVal (Int32.to_int var.it));
                       ValsRelForm (IntVal (Int32.to_int var.it), IntLeq, locs_max) ])

    let valid_global_var : Ast.var -> sym_config -> formula =
      fun var sym_conf ->
      let globs_min = IntVal (Int32.to_int sym_conf.globals_min) in
      let globs_max = IntVal (Int32.to_int sym_conf.globals_max) in
      CommentForm ("valid: global_var " ^ string_of_var var,
                   AndForm
                     [ ValsRelForm (globs_min, IntLeq, IntVal (Int32.to_int var.it));
                       ValsRelForm (IntVal (Int32.to_int var.it), IntLeq, globs_max) ])

    let valid_memory_address : pointer -> sym_config -> formula =
      fun ptr sym_conf ->
      let mems_min = IntPtr (Int32.to_int sym_conf.memory_min) in
      let mems_max = IntPtr (Int32.to_int sym_conf.memory_max) in
      CommentForm ("valid: memory_address " ^ string_of_pointer ptr,
                   AndForm
                     [ PtrsRelForm (mems_min, IntLeq, ptr);
                       PtrsRelForm (ptr, IntLeq, mems_max) ])

    (* The "defd" predicate *)
    let defined_state_action : state -> action -> sym_config -> formula =
      fun state act sym_conf ->
      let k = values state in
      let m = memory state in 
      let p = stack_pointer state in
      let p_p = prev_pointer p in
      let p_pp = prev_pointer p_p in
      let p_s = succ_pointer p in
      let k_v0 = SelectVal (k, p) in
      let k_v1 = SelectVal (k, p_p) in

      match act with
      | BasicAct instr when (is_basic_instr instr) ->
         AndForm
           [ valid_stack_pointer p sym_conf;
             (match instr.it with
              | Ast.Unreachable ->
                 CommentForm ("defined: unreachable",
                              BoolForm true)

              | Ast.Binary op ->
                 CommentForm ("defined: binary " ^ string_of_binop op,
                              valid_stack_pointer p_p sym_conf)

              | Ast.Compare op ->
                 CommentForm ("defined: compare " ^ Wasm_utils.string_of_relop op,
                              valid_stack_pointer p_p sym_conf)

              | Ast.Drop ->
                 CommentForm ("defined: drop",
                              valid_stack_pointer p_p sym_conf)

              | Ast.Select ->
                 CommentForm ("defined: select",
                              valid_stack_pointer p_pp sym_conf)

              | Ast.LocalGet x ->
                 CommentForm ("defined: local_get " ^ string_of_var x,
                              AndForm
                                [valid_stack_pointer p_s sym_conf; valid_local_var x sym_conf])

              | Ast.LocalSet x ->
                 CommentForm ("defined: local_get" ^ string_of_var x,
                              AndForm
                                [valid_stack_pointer p_p sym_conf; valid_local_var x sym_conf])

              | Ast.LocalTee x ->
                 CommentForm ("defined: local_tee " ^ string_of_var x,
                              valid_local_var x sym_conf)

              | Ast.GlobalGet x ->
                 CommentForm ("defined: global_get " ^ string_of_var x,
                              AndForm
                                [valid_stack_pointer p_s sym_conf; valid_global_var x sym_conf])

              | Ast.GlobalSet x ->
                 CommentForm ("defined: global_set " ^ string_of_var x,
                              AndForm
                                [valid_stack_pointer p_p sym_conf; valid_global_var x sym_conf])

              | Ast.Load op ->
                 CommentForm (
                     "defined: load " ^ Int32.to_string op.offset,
                     UFBoolForm("isdefined_" ^ string_of_loadop op, [m; k_v0])) 

              (* valid_memory_address
              (OffsetPtr (CastedPtr k_v0, op.offset)) sym_conf) *)

              | Ast.Store op ->
                 CommentForm (
                     "defined: store " ^ Int32.to_string op.offset,
                     AndForm
                       [ valid_stack_pointer p_pp sym_conf;
                         UFBoolForm("isdefined_" ^ string_of_storeop op, [m; k_v0; k_v1])
                       ]
                   )

              | _ ->
                 CommentForm ("defined: instr default",
                              BoolForm true)) ]

      | JumpAct (br, _) ->
         AndForm
           [ valid_stack_pointer p sym_conf;
             (match br with
              | JumpIf b ->
                 CommentForm ("defined: if " ^ string_of_bool b,
                              valid_stack_pointer p_p sym_conf)

              | JumpBrIf b ->
                 CommentForm ("defined: brif " ^ string_of_bool b,
                              valid_stack_pointer p_p sym_conf)

              | JumpIndex ind ->
                 CommentForm ("defined: brindex " ^ Int32.to_string ind,
                              valid_stack_pointer p_p sym_conf)

              | JumpDefault size ->
                 CommentForm ("defined: brdefault " ^ Int32.to_string size,
                              valid_stack_pointer p_p sym_conf)

              | _ ->
                 CommentForm ("defined: branch default",
                              BoolForm true))]

      | PhiAct (prev_v, this_v) ->
         CommentForm ("defined: phi " ^ G.string_of_vertex prev_v ^ "->" ^ G.string_of_vertex this_v,
                      BoolForm true)

      | CallAct x ->
         CommentForm ("defined: call " ^ string_of_var x,
                      BoolForm true)

      | CallIndirectAct x ->
         CommentForm ("defined: call_indirect" ^ string_of_var x,
                      BoolForm true)

      | StopAct ->
         CommentForm ("defined: final",
                      BoolForm true)

      | _ ->
         let _ = prerr_debug ("failing at action: " ^ string_of_action act) in
         CommentForm ("defined: default",
                      (prerr_debug "defined_state_action: fallthrough case"; BoolForm false))

    (* The enabled_upto predicate.
     * Checks that everything except for the last label is defined and guarded.
     * The tuple includes the trajectory formula and penultimate state. *)
    let rec enabled_upto_state_actions
            : state -> action list -> sym_config -> (state * formula) =
      fun state0 acts sym_conf ->
      match acts with
      | [] -> (state0, AndForm [BoolForm true])
      | (_ :: []) -> (state0, AndForm [BoolForm true])
      | (act0 :: acts_tl) ->
         let state1 = next_state state0 act0 in
         let defined = defined_state_action state0 act0 sym_conf in
         let guarded = guarded_state_action state0 act0 sym_conf in
         match enabled_upto_state_actions state1 acts_tl sym_conf with
         | (statef, AndForm forms) ->
            (statef, AndForm (defined :: guarded :: forms))
         | (statef, enabled) ->
            (statef, AndForm [defined; guarded; enabled])

    (* Enabled up to the last command and then blocked *)
    let blocked_at_state_actions
        : state -> action list -> sym_config -> formula =
      fun state0 acts sym_conf ->
      match List.rev acts with
      | [] -> BoolForm false
      | (actf :: _) ->
         let (statef, enabled) =
           enabled_upto_state_actions state0 acts sym_conf in
         let definedf = defined_state_action statef actf sym_conf in
         let guardedf = guarded_state_action statef actf sym_conf in
         CommentForm ("blocked_at: " ^ string_of_int (List.length acts),
                      AndForm [enabled; definedf; NotForm guardedf])

    (* Trapping? *)
    let rec trapped_at_state_actions
            : state -> action list -> sym_config -> formula =
      fun state0 acts sym_conf ->
      match List.rev acts with
      | [] -> BoolForm false
      | (actf :: _) ->
         let (statef, enabled) =
           enabled_upto_state_actions state0 acts sym_conf in
         let definedf = defined_state_action statef actf sym_conf in
         CommentForm ("trapped_at: " ^ string_of_int (List.length acts),
                      AndForm [enabled; NotForm definedf])

    (* Synchronize the function calls.
     * Makes all the function calls in the path actions line up.
     *
     * This returns a list of form (assumps, consequents)
     * where we AND the assumps and assert the negation of (AND conseqts).
     * Since we check validity these are in negation form: UNSAT iff valid
     *
     *  For all pairs of triples along a path of form
     *                  (sv1)     (br)
     *    --> [sv0] --> [Call sx] ---> [svf] -->     // Source call triplet
     *
     *                  (tv1)     (br)
     *    --> [tv0] --> [Call tx] ---> [tvf] -->     // Target call triplet
     *
     * We want to generate the following formulas
     *  src_state0 = init_state0 (sv0, sv1)
     *  tgt_state0 = init_state0 (tv0, tv1)
     *
     *  src_state1 = next_state src_state0 (CallAct sx)
     *  tgt_state1 = next_state tgt_state0 (CallAct tx)  // if sx.it = tx.it
     *
     *  src_statef = init_statef (sv1,svf)
     *  tgt_statef = init_statef (tv1,tv1)
     *
     * Note the missing JumpAct and StopAct between state1s and statefs.
     *
     * Check the folloing for validity (by encoding negative conditions):
     *
     *  (1) Pre-call condition holds:
     *
     *    refined((sv0,sv1), (tv0,tv1), Active, 0))
     *      IMPLIES (states_equiv src_state0 src_state1)
     *
     *  (2) Post-call condition holds (on the one immediately after the call)
     *
     *    (refined((sv0,sv1), (tv0,tv1), Active, 0)
     *      AND (states_equiv src_state1 tgt_state1)
     *      AND (state0s_state1s_rel))
     *        IMPLIES (refined ((sv0,sv1), (tv0,tv1), Active, 1)  // Note the 1
     *
     *  (3) Call sync final condition holds
     *
     *    refined((sv0,sv1), (tv0,tv1), Active, 0)
     *      IMPLIES refined((sv1,svf), (tv1,tvf), Final, 0)
     *
     * We rely on the eval_action to generate counter examples via SAT
     *)

    let is_call: action -> bool =
      fun a ->
      match a with
      | CallAct _ -> true
      | CallIndirectAct _ -> true 
      | _ -> false

    let identical_calls: action -> action -> bool =
      fun a b ->
      match a,b with
      | CallAct sx, CallAct tx when sx.it = tx.it -> true
      | CallIndirectAct sx, CallIndirectAct tx when sx.it = tx.it -> true
      | _ -> false

    let call_id: action -> Ast.var =
      fun a -> 
      match a with
      | CallAct x -> x
      | CallIndirectAct x -> x
      | _ ->
         failwith("uf_sym_eval: call_id invoked for non-call")

    let string_of_action_list: action list -> string =
      fun al ->
      List.fold_left
        (fun r a -> r ^ " " ^(string_of_action a))
        ""
        al


    let rec source_target_calls_synced
            : (state * action list * ufunc_ir)
              -> (state * action list * ufunc_ir)
              -> proof
              -> sym_config
              -> (formula * formula) list =
      fun (src_state0, src_acts, src_ir)
          (tgt_state0, tgt_acts, tgt_ir)
          proof
          sym_conf ->
      (* print_debug_high (Printf.sprintf "\n calls_syncd invoked with src=[%s] tgt=[%s]" 
                         (string_of_action_list src_acts) 
                         (string_of_action_list tgt_acts)); *)
        
      match src_acts, tgt_acts with
      (* matching calls: issue a check *)
      | (a :: (JumpAct (Jump, svf) as ja) :: src_acts_tl),
        (b :: (JumpAct (Jump, tvf) as jb) :: tgt_acts_tl)
           when (identical_calls a b) ->
         (* print_debug_high (Printf.sprintf "\n\t Matching calls found"); *)
         (* State 0 calculations *)
         let (sv0,sv1) = src_state0.this_edge in
         let (tv0,tv1) = tgt_state0.this_edge in

         (* The states immediately after a function call and before branch *)
         let src_state1 = next_state src_state0 a in
         let tgt_state1 = next_state tgt_state0 b in

         (* The states immediately after a branch instruction *)
         let src_state2 = next_state src_state1 ja in 
         let tgt_state2 = next_state tgt_state1 jb in

         (* PreCall is different from Initial as the call may be embedded in a longer path *)

         let r0_fun = lookup_refinement ((sv0,sv1),(tv0,tv1),PreCall) proof in    
         let refined0 = r0_fun (src_state0, tgt_state0) in

         (* check 1: The PreCall refinement relation implies that both calls execute in identical contexts. 
          * context = stack arguments + globals + memory. 
          * We simplify and equate full stacks vs. only the top portions *)
         let alpha_pre =
           CommentForm (
               "call pre-check: assume pre-call relation",
               refined0)
                       
         and beta_pre = (* identical contexts in src_state0 and tgt_state0 *)
           CommentForm (
               "call pre-check: require identical contexts before call", 
               AndForm
                 [ ArrsEqForm   (values src_state0, values tgt_state0);
                   PtrsRelForm  (stack_pointer src_state0,  IntEq, stack_pointer tgt_state0);
                   ArrsEqForm   (globals src_state0, globals tgt_state0);
                   SymEqForm    (memory src_state0, memory tgt_state0); ]
             )
         in
         (* check 2: 
          * assume that 
          *      src_state1 and src_state2 are identical, 
          *      tgt_state1 and tgt_state2 are identical,
          *      src_state1 and tgt_state1 have identical memory, stack, and globals
          *      src_state1 inherits locals from src_state0
          *      tgt_state1 inherits locals from tgt_state0
          * require that 
          *      post-call condition holds for src_state2, tgt_state2.
          *)
         let alpha_post =
           CommentForm(
               "call post-check: assume related state0 and state1 and identical state1 and state2", 
               AndForm
                 [
                   (* identical states 1 and 2 *)
                   states_equiv src_state1 src_state2;
                   states_equiv tgt_state1 tgt_state2;
                   
                   (* src_state1 and tgt_state1 have identical memory, stack, and globals *)
                   ArrsEqForm  (values src_state1, values tgt_state1);
                   PtrsRelForm (stack_pointer src_state1, IntEq, stack_pointer tgt_state1);
                   ArrsEqForm  (globals src_state1, globals tgt_state1);
                   SymEqForm   (memory src_state1, memory tgt_state1);
                   
                   (* state1 inherits locals from state0 *)
                   ArrsEqForm (locals src_state0, locals src_state1);
                   ArrsEqForm (locals tgt_state0, locals tgt_state1)
                 ]
             )
         in
         let r2_fun = lookup_refinement ((sv1,svf),(tv1,tvf),PostCall) proof in
         let refined2 = r2_fun (src_state2, tgt_state2) in 
         let beta_post = (* post-call condition holds *)
           CommentForm (
               "call post-check: require post-call condition to hold for src_state2 tgt_state2",
               refined2
             )
         in 
         (* Aggregate everything and do recursion *)
         (alpha_pre, beta_pre)
         :: (alpha_post, beta_post)
         :: (source_target_calls_synced
               (src_state2, src_acts_tl, src_ir)
               (tgt_state2, tgt_acts_tl, tgt_ir)
               proof
               sym_conf)


      (* first action on either side is a call, but calls are mismatched: error *)
      | (a::_), (b::_) when (is_call a) && (is_call b) ->
         print_debug_none (Printf.sprintf "\n\t Mismatched calls: mistake");         
         []

      (* at end *)
      | [], [] ->
         (* print_debug_high (Printf.sprintf "\n\t at end"); *)
         []

      (* at least one side does not have a call action, move ahead on that side *)
      | (a::src_acts_tl), _ when (not (is_call a)) ->
         (* print_debug_high (Printf.sprintf "\n\t skip on src"); *)
         let src_state1 = next_state src_state0 a in
         source_target_calls_synced
           (src_state1, src_acts_tl, src_ir)
           (tgt_state0, tgt_acts, tgt_ir)
           proof
           sym_conf

      | _, (b::tgt_acts_tl) when (not (is_call b)) ->
         (* print_debug_high (Printf.sprintf "\n\t skip on tgt");          *)
         let tgt_state1 = next_state tgt_state0 b in
         source_target_calls_synced
           (src_state0, src_acts, src_ir)
           (tgt_state1, tgt_acts_tl, tgt_ir)
           proof
           sym_conf

      | _ ->
         print_debug_none (Printf.sprintf "\n\t fallthrough: mistake");
         [] (* This catches a case where a,b are matched calls but not followed by jump instruction.
                 * That should not occur by CFG construction invariant. *)

           



               

             
      (* OLD CODE: 
       * Mismatch at the functions they call means we discard it 
      | (CallAct sx :: src_acts_tl, CallAct tx :: tgt_acts_tl)
           when (sx.it <> tx.it) -> []

      | (CallIndirectAct sx :: src_acts_tl, CallIndirectAct tx :: tgt_acts_tl)
           when (sx.it <> tx.it) -> []                                      

      | (CallAct _ :: _, CallIndirectAct _ :: _)
        | (CallIndirectAct _ :: _, CallAct _ :: _)
        -> []
             
      | (CallAct _ :: _, []) -> []
      | (CallIndirectAct _ :: _, []) -> []                                   

      | ([], CallAct _ :: _) -> []
      | ([], CallIndirectAct _ :: _) -> []

                                   
      (* The two calls match *)
      | (CallAct sx :: JumpAct (Jump, svf) :: src_acts_tl,
         CallAct tx :: JumpAct (Jump, tvf) :: tgt_acts_tl)
           when (sx.it = tx.it) -> 

         (* State 0 calculations *)
         let (sv0,sv1) = src_state0.this_edge in
         let (tv0,tv1) = tgt_state0.this_edge in
         let Types.FuncType (fty_ins, fty_outs) = lookup_func_type src_ir.types_table sx in
         (*
      let f_ins = Int32.of_int (List.length fty_ins) in
      let f_outs = Int32.of_int (List.length fty_outs) in
          *)
         (* let state0s_equiv = states_equiv src_state0 tgt_state0 in *)

         (* The states immediately after a function call and before branch *)
         let src_state1 = next_state src_state0 (CallAct sx) in
         let tgt_state1 = next_state tgt_state0 (CallAct tx) in
         (* let state1s_equiv = states_equiv src_state1 tgt_state1 in *)

         (* The states immediately after a branch instruction *)
         (*  *)
         let src_state2 = next_state src_state1 (JumpAct (Jump, svf)) in
         let tgt_state2 = next_state tgt_state1 (JumpAct (Jump, tvf)) in
         (* let state2s_equiv = states_equiv src_state2 tgt_state2 in *)
         (*  *)

         (* PreCall is different from Initial as the call may be embedded in a longer path *)

         let r0_fun = lookup_refinement ((sv0,sv1),(tv0,tv1),PreCall) proof in    
         let refined0 = r0_fun (src_state0, tgt_state0) in

         (* check 1: The PreCall refinement relation implies that both calls execute in identical contexts. 
          * context = stack arguments + globals + memory. 
          *
          * We simplify and equate full stacks vs. only the top portions
          *)
         let alpha_pre =
           CommentForm (
               "call pre-check: assume pre-call relation",
               refined0)
                       
         and beta_pre = (* identical contexts in src_state0 and tgt_state0 *)
           CommentForm (
               "call pre-check: require identical contexts before call", 
               AndForm
                 [ ArrsEqForm (values src_state0, values tgt_state0);
                   PtrsRelForm
                     (stack_pointer src_state0,  IntEq, stack_pointer tgt_state0);
                   ArrsEqForm (globals src_state0, globals tgt_state0);
                   SymEqForm (memory src_state0, memory tgt_state0); ]
             )
         in


         (* check 2: 
          * assume that 
          *      src_state1 and src_state2 are identical, 
          *      tgt_state1 and tgt_state2 are identical,
          *      src_state1 and tgt_state1 have identical memory, stack, and globals
          *      src_state1 inherits locals from src_state0
          *      tgt_state1 inherits locals from tgt_state0
          * require that 
          *      post-call condition holds for src_state2, tgt_state2.
          *)
         let alpha_post =
           CommentForm(
               "call post-check: assume related state0 and state1 and identical state1 and state2", 
               AndForm
                 [
                   (* identical states 1 and 2 *)
                   states_equiv src_state1 src_state2;
                   states_equiv tgt_state1 tgt_state2;
                   
                   (* src_state1 and tgt_state1 have identical memory, stack, and globals *)
                   ArrsEqForm(values src_state1, values tgt_state1);
                   PtrsRelForm(stack_pointer src_state1, IntEq, stack_pointer tgt_state1);
                   ArrsEqForm (globals src_state1, globals tgt_state1);
                   SymEqForm (memory src_state1, memory tgt_state1);
                   
                   (* state1 inherits locals from state0 *)
                   ArrsEqForm (locals src_state0, locals src_state1);
                   ArrsEqForm (locals tgt_state0, locals tgt_state1)
                 ]
             )
         in
         let r2_fun = lookup_refinement ((sv1,svf),(tv1,tvf),PostCall) proof in
         let refined2 = r2_fun (src_state2, tgt_state2) in 
         let beta_post = (* post-call condition holds *)
           CommentForm (
               "call post-check: require post-call condition to hold for src_state2 tgt_state2",
               refined2
             )
         in 

         (* Aggregate everything and do recursion *)
         (alpha_pre, beta_pre)
         :: (alpha_post, beta_post)
         :: (source_target_calls_synced
               (next_state src_state0 (CallAct sx), src_acts_tl, src_ir)
               (next_state tgt_state0 (CallAct tx), tgt_acts_tl, tgt_ir)
               proof
               sym_conf)

      (* When one is a call but the other isn't, step the other *)
      | (CallAct _ :: _, tgt_act0 :: tgt_acts_tl) ->
         let tgt_state1 = next_state tgt_state0 tgt_act0 in
         source_target_calls_synced
           (src_state0, src_acts, src_ir)
           (tgt_state1, tgt_acts_tl, tgt_ir)
           proof
           sym_conf

      | (src_act0 :: src_acts_tl, CallAct _ :: _) ->
         let src_state1 = next_state src_state0 src_act0 in
         source_target_calls_synced
           (src_state1, src_acts_tl, src_ir)
           (tgt_state0, tgt_acts, tgt_ir)
           proof
           sym_conf

      (* When neither are calls, step both if possible 
      | (src_act0 :: src_acts_tl, []) ->
         let src_state1 = next_state src_state0 src_act0 in
         source_target_calls_synced
           (src_state1, src_acts_tl, src_ir)
           (tgt_state0, [], tgt_ir)
           proof
           sym_conf

      | ([], tgt_act0 :: tgt_acts_tl) ->
         let tgt_state1 = next_state tgt_state0 tgt_act0 in
         source_target_calls_synced
           (src_state0, src_acts, src_ir)
           (tgt_state1, tgt_acts_tl, tgt_ir)
           proof
           sym_conf


      | (src_act0 :: src_acts_tl, tgt_act0 :: tgt_acts_tl) ->
         let src_state1 = next_state src_state0 src_act0 in
         let tgt_state1 = next_state tgt_state0 tgt_act0 in
         source_target_calls_synced
           (src_state1, src_acts_tl, src_ir)
           (tgt_state1, tgt_acts_tl, tgt_ir)
           proof
           sym_conf

      | ([], []) -> []
       *)
       *)
               
    (* ---------------- operator declarations ---------------- *)
    let opdecl: instr' -> string list =
      fun it ->
      match it with 
      | Unary unop ->
         let unop_str = string_of_unop unop in 
         ["(declare-fun " ^ unop_str ^ "(Val) Val)";
          "(declare-fun isdefined_" ^ unop_str ^ "(Val) Val)";
         ]
           
      | Binary binop ->
         let binop_str = string_of_binop binop in 
         ["(declare-fun " ^ binop_str ^ "(Val Val) Val)";
          "(declare-fun isdefined_" ^ binop_str ^ "(Val Val) Bool)";
         ]
           
      | Compare relop ->
         let relop_str = Wasm_utils.string_of_relop relop in 
         ["(declare-fun " ^ relop_str ^ "(Val Val) Val)";
          "(declare-fun isdefined_" ^ relop_str ^ "(Val Val) Bool)";
         ]
           
      | Test testop ->
         let testop_str = string_of_testop testop in 
         ["(declare-fun " ^ testop_str ^ "(Val) Val)";
          "(declare-fun isdefined_" ^ testop_str ^ "(Val) Bool)"]
           
      | Convert cvtop ->
         let cvtop_str = string_of_cvtop cvtop in 
         ["(declare-fun " ^ cvtop_str ^ "(Val) Val)";
          "(declare-fun isdefined_" ^ cvtop_str ^ "(Val) Bool)"]

      | Load loadop ->
         let loadop_str = string_of_loadop loadop in
         ["(declare-fun " ^ loadop_str ^ "(Mem Val) Val)"  ;
          "(declare-fun " ^ "isdefined_"^loadop_str ^ "(Mem Val) Bool)";
         ]
      | Store storeop ->
         let storeop_str = string_of_storeop storeop in
         ["(declare-fun " ^ storeop_str ^ "(Mem Val Val) Mem)";
          "(declare-fun " ^ "isdefined_"^storeop_str ^ "(Mem Val Val) Bool)";
         ]
           
      | _ -> (* other instructions do not require uninterpreted operators *)
         [] 
           
    (* list taken from operators.ml *)
           
    let fixed_operators =
      [
        i32_clz; 
        i32_ctz; 
        i32_popcnt; 
        i64_clz; 
        i64_ctz; 
        i64_popcnt; 
        f32_neg; 
        f32_abs; 
        f32_sqrt;
        f32_ceil;
        f32_floor; 
        f32_trunc; 
        f32_nearest; 
        f64_neg; 
        f64_abs; 
        f64_sqrt; 
        f64_ceil; 
        f64_floor;
        f64_trunc;
        f64_nearest;

        i32_add; 
        i32_sub; 
        i32_mul; 
        i32_div_s; 
        i32_div_u; 
        i32_rem_s; 
        i32_rem_u; 
        i32_and; 
        i32_or; 
        i32_xor; 
        i32_shl; 
        i32_shr_s;
        i32_shr_u;
        i32_rotl; 
        i32_rotr; 
        i64_add; 
        i64_sub; 
        i64_mul; 
        i64_div_s; 
        i64_div_u; 
        i64_rem_s; 
        i64_rem_u; 
        i64_and; 
        i64_or; 
        i64_xor;
        i64_shl;
        i64_shr_s;
        i64_shr_u;
        i64_rotl; 
        i64_rotr; 
        f32_add;
        f32_sub;
        f32_mul;
        f32_div;
        f32_min;
        f32_max;
        f32_copysign; 
        f64_add; 
        f64_sub; 
        f64_mul; 
        f64_div; 
        f64_min; 
        f64_max; 
        f64_copysign;

        i32_eqz; 
        i64_eqz; 

        i32_eq; 
        i32_ne; 
        i32_lt_s; 
        i32_lt_u; 
        i32_le_s; 
        i32_le_u; 
        i32_gt_s; 
        i32_gt_u; 
        i32_ge_s; 
        i32_ge_u; 
        i64_eq; 
        i64_ne; 
        i64_lt_s;
        i64_lt_u;
        i64_le_s;
        i64_le_u;
        i64_gt_s;
        i64_gt_u;
        i64_ge_s;
        i64_ge_u;
        f32_eq; 
        f32_ne; 
        f32_lt; 
        f32_le; 
        f32_gt; 
        f32_ge; 
        f64_eq; 
        f64_ne; 
        f64_lt; 
        f64_le; 
        f64_gt; 
        f64_ge; 

        i32_wrap_i64;
        i32_trunc_f32_s;
        i32_trunc_f32_u;
        i32_trunc_f64_s;
        i32_trunc_f64_u;
        i64_extend_i32_s;
        i64_extend_i32_u; 
        i64_trunc_f32_s; 
        i64_trunc_f32_u; 
        i64_trunc_f64_s; 
        i64_trunc_f64_u; 
        f32_convert_i32_s; 
        f32_convert_i32_u; 
        f32_convert_i64_s; 
        f32_convert_i64_u; 
        f32_demote_f64; 
        f64_convert_i32_s; 
        f64_convert_i32_u; 
        f64_convert_i64_s; 
        f64_convert_i64_u; 
        f64_promote_f32; 
        i32_reinterpret_f32; 
        i64_reinterpret_f64; 
        f32_reinterpret_i32; 
        f64_reinterpret_i64;
      ]


    let uf_operator_decls: action list -> smt_decl list =
      fun acts ->
      let instr_op_set = (* form a set to remove duplicates *)
        InstrOpSet.of_list
          (List.flatten
             (List.map (fun a -> match a with BasicAct i -> [i.Source.it] | _ -> []) acts))
      in
      List.map (fun i -> SmtDecls (opdecl i)) (InstrOpSet.elements instr_op_set)
               

    let fixed_sort_decls =
      [SmtDecls ["(declare-sort Mem 0)"; "(declare-sort Val 0)"]]

    let fixed_fun_decls =
      [SmtDecls ["(declare-fun is_zero (Val) Bool)";
                 "(declare-fun leq (Val Val) Bool)"]]

    let fixed_decls = fixed_sort_decls @ fixed_fun_decls (* order is important *)
        
    let smt_operator_decls: action list -> smt_decl list =
      fun actions ->
      let operator_decls = uf_operator_decls actions in
      operator_decls

    let smt_const_decls: unit -> smt_decl list =
      fun () ->
      fixed_decls@(ConstMap.const_decls())

    let smt_int_value: int32 -> value =
      fun k ->
      if k = 0l then
        ConstMap.zero
      else 
        UFVal(ConstMap.lookup (Wasm_utils.int32_to_literal k), [])
  end

