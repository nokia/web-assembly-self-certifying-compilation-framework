(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


open Wasm
open Instr_graph
open Func_types
open State_types
open Proof_types

open Solver_types
open Smt_ir
open Smt_interface
open Debug
open Wasm_utils

module List = List_utils
module Q = Queue
module G = Digraph
open Option

open Sym_eval_interface


(* Symbolic evaluator actions,
 * avoids having to set up a functor over Sym_eval_interface.EvalT *)

module Full = Full_sym_eval.Eval
module UF = Uf_sym_eval.Eval

let exec_state_actions ip =
  match ip with
  | IFull -> Full.exec_state_actions 
  | INone -> UF.exec_state_actions 
  
let enabled_upto_state_actions ip =
  match ip with
  | IFull -> Full.enabled_upto_state_actions 
  | INone -> UF.enabled_upto_state_actions 

let blocked_at_state_actions ip =
  match ip with
  | IFull -> Full.blocked_at_state_actions 
  | INone -> UF.blocked_at_state_actions 
                                              
let trapped_at_state_actions ip =
  match ip with
  | IFull -> Full.trapped_at_state_actions
  | INone -> UF.trapped_at_state_actions


let source_target_calls_synced ip = 
  match ip with
  | IFull -> Full.source_target_calls_synced
  | INone -> UF.source_target_calls_synced

let smt_operator_decls ip = 
  match ip with
  | IFull -> Full.smt_operator_decls
  | INone -> UF.smt_operator_decls

let smt_const_decls ip = 
  match ip with
  | IFull -> Full.smt_const_decls
  | INone -> UF.smt_const_decls

let smt_int_value ip = 
  match ip with
  | IFull -> Full.smt_int_value
  | INone -> UF.smt_int_value                              
       
       
(* Configurations for when checking things *)
type checker_config =
  {
    (* is checking enabled? *)
    enabled: bool;

    (* Maximum size of generated formula, counting nodes *)
    max_states : int;
    
    (* Pointer ranges *)
    values_min : int32;
    values_max : int32;

    locals_min : int32;
    locals_max : int32;

    globals_min : int32;
    globals_max : int32;

    memory_min : int32;
    memory_max : int32;

    stack_pointer_start : int32;

    (* Appended and prepended to the smt formula *)
    smt_headers : smt_stmt list;
    smt_footers : smt_meta list;
    solver_mode : solver_mode;

    (* Are printed right before a call to the solver_mode *)
    smt_debugs : string list;
  }

let default_checker_config : checker_config =
  { enabled = true;

    max_states = default_sym_config.max_states;

    values_min = default_sym_config.values_min;
    values_max = default_sym_config.values_max;

    locals_min = default_sym_config.locals_min;
    locals_max = default_sym_config.locals_max;

    globals_min = default_sym_config.globals_min;
    globals_max = default_sym_config.globals_max;

    memory_min = default_sym_config.memory_min;
    memory_max = default_sym_config.memory_max;

    stack_pointer_start = default_sym_config.values_min;

    smt_headers = default_smt_query.smt_headers;
    smt_footers = default_smt_query.smt_footers;
    solver_mode = default_solver_config.solver_mode;
    smt_debugs = [];
  }

(* Generate other configurations based on the checking config *)
let checker_to_solver_config : checker_config -> solver_config =
  fun check_conf ->
    { solver_mode = check_conf.solver_mode;
      debugs = check_conf.smt_debugs;
    }

let checker_to_sym_config : checker_config -> sym_config =
  fun check_conf ->
    { max_states = check_conf.max_states;
      values_min = check_conf.values_min;
      values_max = check_conf.values_max;

      locals_min = check_conf.locals_min;
      locals_max = check_conf.locals_max;

      globals_min = check_conf.globals_min;
      globals_max = check_conf.globals_max;

      memory_min = check_conf.memory_min;
      memory_max = check_conf.memory_max;
    }

let checker_to_smt_query : checker_config -> smt_query =
  fun check_conf ->
    { default_smt_query with
      smt_headers = check_conf.smt_headers;
      smt_footers = check_conf.smt_footers;
    }

(* =============== New cycle-free paths calculation ================*)

let rec loop_free_paths_search
  : ('a,'b) instr_graph
    -> G.basic_path  (* non-empty candidate path p *)
    -> G.vertex      (* vertex u that ends p *)
    -> G.vertex      (* goal vertex v *)
    -> (G.basic_path list) =
  fun graph p u v ->
  (* Done with path *)
  if (u = v) then [p]
  else match G.vertex_succs u graph with
    | [] -> []  (* drop candidate path p as it does not reach v *)
    | u_succs ->
        List.concat (List.map
          (fun (u',_) ->
            (* u->u' loops back into p, ignore. u' cannot be v. *)
            if (List.mem u' p) || (u' = u) then []
            else loop_free_paths_search graph (p@[u']) u' v)
          u_succs)

         
let loop_free_paths
  : ('a,'b) instr_graph
    -> G.vertex      (* start vertex u *)
    -> G.vertex      (* goal vertex v *)
    -> (G.basic_path list) =
  fun graph u v -> loop_free_paths_search graph [u] u v 
           
    
let frontier_paths
  : ('a,'b) instr_graph
    -> G.basic_edge   (* start edge e *)
    -> G.basic_edge   (* frontier edge f *)
    -> (G.basic_path list) =
  fun graph e f -> 
    let (u,u') = e and (v,v') = f in
    let paths = loop_free_paths graph u' v in
    List.map (fun p -> [u]@p@[v']) paths
          

let no_cycle_paths : G.basic_edge -> G.basic_edge list -> ufunc_ir -> G.basic_path list =
  fun e fs func_ir ->
    let graph = func_ir.body_graph in
    let paths =
      List.concat (List.map
         (fun f ->
           let paths_e_to_f = frontier_paths graph e f in
           let _ = 
             if paths_e_to_f = [] then
               Printf.eprintf
                 "\n WARNING: no paths from edge %s to frontier edge %s "
                 (G.string_of_basic_edge e)
                 (G.string_of_basic_edge f)
             else ()
           in
           paths_e_to_f)
         fs) 
    in
    Debug.if_debug_high
      (fun () ->
        Printf.eprintf "\n No-cycle paths for edge e = %s" (G.string_of_basic_edge e);
        Printf.eprintf "\n\t Frontier edges: ";
        List.iter (fun f -> Printf.eprintf "%s " (G.string_of_basic_edge f)) fs;
        Printf.eprintf "\n\t Paths: ";
        List.iter (fun p -> Printf.eprintf "\n\t\t %s " (G.string_of_basic_path p)) paths;
        Printf.eprintf "\n";);
    paths

(* =============== END NEW cycle-free paths calculation ================*)
                      
(* The algorithms for checking things *)

let path_smt_decls_headers
  : (source_path * target_path)
  -> ufunc_ir
  -> ufunc_ir
  -> proof
  -> sym_config
  -> (smt_decl list * smt_stmt list) option =
  fun (src_path, tgt_path) src_ir tgt_ir proof sym_conf ->
    (* We firs compute a the formulas and gauge the size to see if it's worth trying *)
    let src_states = path_states src_path src_ir source_tag in
    let tgt_states = path_states tgt_path tgt_ir target_tag in

    (* Source semantics *)
    let src_state0 = List.hd src_states in
    let src_acts = path_actions src_path src_ir in
    let src_execd =
      CommentForm ("source execution semantics: " ^ src_ir.func_id,
        (exec_state_actions proof.interpretation)
          src_state0 src_acts src_ir.phi_map sym_conf source_tag) in

    (* Target semantics *)
    let tgt_state0 = List.hd tgt_states in
    let tgt_acts = path_actions tgt_path tgt_ir in
    let tgt_execd =
      CommentForm ("target execution semantics: " ^ tgt_ir.func_id,
        (exec_state_actions proof.interpretation)
          tgt_state0 tgt_acts tgt_ir.phi_map sym_conf target_tag) in

    (* Refinement on state0 *)
    let src_e0 = path_start_edge src_path in
    let tgt_e0 = path_start_edge tgt_path in
    let r0_fun = lookup_refinement (src_e0, tgt_e0, Initial) proof in
    let refined0_pre = r0_fun (src_state0, tgt_state0) in
    let refined0 =
      CommentForm ("refinement on state0s: ("
          ^ src_ir.func_id ^ ", " ^ tgt_ir.func_id ^ ")",
          refined0_pre) in

    (* Do a size check *)

    (* Declare states now *)
    let tgt_phi_states = phi_states tgt_ir target_tag 
    and src_phi_states = phi_states src_ir source_tag in

    let num_states =
      List.length src_states
        + List.length src_phi_states
        + List.length tgt_states
        + List.length tgt_phi_states in
    if num_states > sym_conf.max_states then
      let _ =
      print_debug
        ("too many states: "
          ^ string_of_int num_states ^ " > " ^ string_of_int (sym_conf.max_states)) in
        None
    else

    let state_decls = declare_states (src_states @ src_phi_states @ tgt_states @ tgt_phi_states) in

    (* If the size check passes we add a few things *)
    let exec_stmts = assert_formulas [src_execd; tgt_execd] in

    let refined0_stmts = assert_formulas [refined0] in

    (* Make sure that the initial values are all zeroed out past the stack pointer *)
    let id_src_val0 = IdArr (values_smtid src_state0) in
    let id_src_ptr0 = IdPtr (stack_pointer_smtid src_state0) in
    let id_tgt_val0 = IdArr (values_smtid tgt_state0) in
    let id_tgt_ptr0 = IdPtr (stack_pointer_smtid tgt_state0) in
    let src_values0 = ArrZeroAfterForm (id_src_val0, id_src_ptr0,
                                        (smt_int_value proof.interpretation) 0l) in
    let tgt_values0 = ArrZeroAfterForm (id_tgt_val0, id_tgt_ptr0,
                                        (smt_int_value proof.interpretation) 0l) in
    let values0_after = assert_formulas [src_values0; tgt_values0] in

    (* Make sure that the initial locals are all zeroed out *)

    (* Make sure that the initial stack pointers are the lowest possible *)
    (* let ptr0 = Int32Ptr sym_conf.values_min in *)
    let ptr0 = IntPtr (Int32.to_int sym_conf.values_min) in 
    let src_ptr0 = IdPtr (stack_pointer_smtid src_state0) in
    let tgt_ptr0 = IdPtr (stack_pointer_smtid tgt_state0) in
    let src_ptr0_min = PtrsRelForm (src_ptr0, IntEq, ptr0) in
    let tgt_ptr0_min = PtrsRelForm (tgt_ptr0, IntEq, ptr0) in

    (* let ptrs0_min_smts = assert_smts [src_ptr0_min; tgt_ptr0_min] in *)
    let ptrs0_min_stmts = assert_formulas [src_ptr0_min; tgt_ptr0_min] in

    (* Make sure that the function calls are all synced.
     * This is already in negation form (UNSAT iff valid),
     * and is included in the headers because calls also constitute as
     * execution semantics *)
    let calls_synced_aggregate =
      (source_target_calls_synced proof.interpretation)
        (src_state0, src_acts, src_ir)
        (tgt_state0, tgt_acts, tgt_ir)
        proof
        sym_conf in
    let call_synced_assumps = AndForm (List.map fst calls_synced_aggregate) in
    let call_synced_conseqs = AndForm (List.map snd calls_synced_aggregate) in

    let calls_synced_neg_stmts =
      if List.length calls_synced_aggregate > 0 then
        assert_formulas [ call_synced_assumps; NotForm call_synced_conseqs ]
      else
        [] in

    (* Determine any added declarations, e.g., for uninterpreted operators or constants *)
    let operator_decls = (smt_operator_decls proof.interpretation) (src_acts@tgt_acts) in

    Some
      (operator_decls @ state_decls, (* order is important *)
        exec_stmts
          @ refined0_stmts
          @ ptrs0_min_stmts
          @ values0_after
          @ calls_synced_neg_stmts)

(* Target enabled implies source enabled.
 * Assumes that a header has already been generated before doing this
 * Valid iff this is UNSAT. *)
let path_pair_enabled
  : (source_path * target_path)
  -> ufunc_ir
  -> ufunc_ir
  -> proof
  -> checker_config
  -> formula =
  fun (src_path, tgt_path) src_ir tgt_ir proof check_conf ->
    let src_state0 = path_start_state src_path source_tag in
    let tgt_state0 = path_start_state tgt_path target_tag in
    let src_acts = path_actions src_path src_ir in
    let tgt_acts = path_actions tgt_path tgt_ir in
    let sym_conf = checker_to_sym_config check_conf in

    let (_, src_enabled) =
      (enabled_upto_state_actions proof.interpretation) src_state0 src_acts sym_conf in
    let (_, tgt_enabled) =
      (enabled_upto_state_actions proof.interpretation) tgt_state0 tgt_acts sym_conf in

    AndForm
      [ CommentForm ("target path enabled: " ^ tgt_ir.func_id, tgt_enabled);
        CommentForm
          ("source path disabled: " ^ src_ir.func_id,
          NotForm (src_enabled)) ]

(* Target blocked implies source blocked.
 * Assumes that a header has already been generated before doing this
 * Valid iff this is UNSAT. *)
let path_pair_blocked
  : (source_path * target_path)
  -> ufunc_ir
  -> ufunc_ir
  -> proof
  -> checker_config
  -> formula =
  fun (src_path, tgt_path) src_ir tgt_ir proof check_conf ->
    let src_state0 = path_start_state src_path source_tag in
    let tgt_state0 = path_start_state tgt_path target_tag in
    let src_acts = path_actions src_path src_ir in
    let tgt_acts = path_actions tgt_path tgt_ir in
    let sym_conf = checker_to_sym_config check_conf in

    let tgt_blocked =
        OrForm
          (List.map (fun act0s ->
            (blocked_at_state_actions proof.interpretation) tgt_state0 act0s sym_conf)
          (List.starts tgt_acts)) in

    let src_blocked =
        OrForm
          (List.map (fun act0s ->
            (blocked_at_state_actions proof.interpretation) src_state0 act0s sym_conf)
          (List.starts src_acts)) in

    AndForm
      [ CommentForm ("target path blocked: " ^ tgt_ir.func_id, tgt_blocked);
        CommentForm
          ("source path not blocked: " ^ src_ir.func_id,
          NotForm src_blocked) ]

(* Target trapped implies source trapped
 * Assumes that a header has already been generated before doing this
 * Valid iff this is UNSAT. *)
let path_pair_trapped
  : (source_path * target_path)
  -> ufunc_ir
  -> ufunc_ir
  -> proof
  -> checker_config
  -> formula =
  fun (src_path, tgt_path) src_ir tgt_ir proof check_conf ->
    let src_state0 = path_start_state src_path source_tag in
    let tgt_state0 = path_start_state tgt_path target_tag in
    let src_acts = path_actions src_path src_ir in
    let tgt_acts = path_actions tgt_path tgt_ir in
    let sym_conf = checker_to_sym_config check_conf in

    let tgt_trapped =
      OrForm
        (List.map (fun act0s ->
          (trapped_at_state_actions proof.interpretation) tgt_state0 act0s sym_conf)
        (List.starts tgt_acts)) in

    let src_trapped =
      OrForm
        (List.map (fun act0s ->
          (trapped_at_state_actions proof.interpretation) src_state0 act0s sym_conf)
        (List.starts src_acts)) in

    AndForm
      [ CommentForm ("target path trapped: " ^ tgt_ir.func_id, tgt_trapped);
        CommentForm
          ("source path not trapped: " ^ src_ir.func_id,
          NotForm src_trapped) ]

(* Target satisfies refinement implies source satisfies refinement
 * Assumes that a header has already been generated before doing this
 * Valid iff this is UNSAT *)
let path_pair_inductive
  : (source_path * target_path)
  -> ufunc_ir
  -> ufunc_ir
  -> proof
  -> checker_config
  -> formula =
  fun (src_path, tgt_path) src_ir tgt_ir proof check_conf ->
    let src_ef = path_final_edge src_path in
    let tgt_ef = path_final_edge tgt_path in
    let src_statef = init_statef src_ef source_tag in
    let tgt_statef = init_statef tgt_ef target_tag in

    let rf_fun = lookup_refinement (src_ef, tgt_ef, Final) proof in
    let refinedf = rf_fun (src_statef, tgt_statef) in
    CommentForm
      ("path pair not inductive: ("
          ^ src_ir.func_id ^ ", " ^ tgt_ir.func_id ^ ")" ,
        NotForm refinedf)

      
let check_if_unsat: string -> solver_result -> source_edge -> target_edge -> solver_status =
  fun msg r se te ->
    let check_str = string_of_solver_status r.solver_status in
    let edges =
      Printf.sprintf "[source %s, target %s]"
        (G.string_of_basic_edge se) (G.string_of_basic_edge te) in
    match r.solver_status with
    | Unsat -> (print_debug_low (Printf.sprintf "%s: [%s] %s" msg check_str edges); Unsat)
    | status ->
      let _ = print_debug_none (Printf.sprintf "%s: [%s] %s" msg check_str edges) in
      let _ = List.iter (fun s -> print_debug_low (String.tab_string s)) r.debug_strings in
      status

(* Loop depth 3 body *)
let check_target_path
  : (source_edge * (target_edge * target_edge list * target_path))
  -> ufunc_ir
  -> ufunc_ir
  -> proof
  -> checker_config
  -> solver_result list =
  fun (src_e, (tgt_e, front_es, tgt_path)) src_ir tgt_ir proof check_conf ->
    let src_path = lookup_path_match (src_e, tgt_path) proof in
    let sym_conf0 = checker_to_sym_config check_conf in
    let solv_conf0 = checker_to_solver_config check_conf in
    let query0 = checker_to_smt_query check_conf in

    let (enabled_res, blocked_res, trapped_res, inductive_res) =
      (match path_smt_decls_headers (src_path, tgt_path) src_ir tgt_ir proof sym_conf0 with
      | None ->
        ({ empty_solver_result with solver_status = NotCalled; debug_strings = ["too many states"]},
          { empty_solver_result with solver_status = NotCalled; debug_strings = ["too many states"]},
          { empty_solver_result with solver_status = NotCalled; debug_strings = ["too many states"]},
          { empty_solver_result with solver_status = NotCalled; debug_strings = ["too many states"]})

      | Some (smt_decls, smt_headers) ->

        let query1 = append_decls query0 smt_decls in
        let query2 = append_headers query1 smt_headers in
        let meta_str = tgt_ir.func_id ^ "_" ^ G.string_of_basic_path tgt_path in

        let query3 = query2 in
        let solv_conf1 = { solv_conf0 with debugs = [ meta_str ] } in

        (* Valid iff UNSAT *)
        let enabled = path_pair_enabled (src_path, tgt_path) src_ir tgt_ir proof check_conf in
        let enabled_stmts = assert_formulas [enabled] in
        let enabled_query = append_stmts query3 enabled_stmts in

        let blocked = path_pair_blocked (src_path, tgt_path) src_ir tgt_ir proof check_conf in
        let blocked_stmts = assert_formulas [blocked] in
        let blocked_query = append_stmts query3 blocked_stmts in

        let trapped = path_pair_trapped (src_path, tgt_path) src_ir tgt_ir proof check_conf in
        let trapped_stmts = assert_formulas [trapped] in
        let trapped_query = append_stmts query3 trapped_stmts in

        let inductive = path_pair_inductive (src_path, tgt_path) src_ir tgt_ir proof check_conf in
        let inductive_stmts = assert_formulas [inductive] in
        let inductive_query = append_stmts query3 inductive_stmts in

        (* Fill in any uninterpreted constants *)
        let const_decls = (smt_const_decls proof.interpretation)() in
        
        let enabled_query1 = prepend_decls const_decls enabled_query
        and blocked_query1 = prepend_decls const_decls blocked_query
        and trapped_query1 = prepend_decls const_decls trapped_query
        and inductive_query1 = prepend_decls const_decls inductive_query in 

        (* Make the queries *)
        (run_smt_query  proof.interpretation enabled_query1 solv_conf1,
          run_smt_query proof.interpretation blocked_query1 solv_conf1,
          run_smt_query proof.interpretation trapped_query1 solv_conf1,
          run_smt_query proof.interpretation inductive_query1 solv_conf1)) in

    let _ = if check_if_unsat "E" enabled_res src_e tgt_e = Unknown
      then ()
      else () in

    let _ = if check_if_unsat "B" blocked_res src_e tgt_e = Unknown
      then ()
      else () in

    let _ = if check_if_unsat "T" trapped_res src_e tgt_e = Unknown
      then ()
      else () in

    let _ = if check_if_unsat "W" inductive_res src_e tgt_e = Unknown
      then ()
      else () in

    (* Aggregate the smt results *)
    [enabled_res; blocked_res; trapped_res; inductive_res]

      
(* Loop depth 2 body *)
let check_frontier
  : (source_edge * (target_edge * target_edge list))
  -> ufunc_ir
  -> ufunc_ir
  -> proof
  -> checker_config
  -> solver_result list =
  fun (src_e, (tgt_e, front_es)) src_ir tgt_ir proof check_conf ->
    let okpaths =  (no_cycle_paths tgt_e front_es tgt_ir) in
    List.concat (List.map (fun tgt_path ->
        check_target_path
          (src_e, (tgt_e, front_es, tgt_path)) src_ir tgt_ir proof check_conf)
        okpaths)

(* Loop depth 1 body *)
let check_edge_pair
  : (source_edge * target_edge)
  -> ufunc_ir
  -> ufunc_ir
  -> proof
  -> checker_config
  -> solver_result list =
  fun (src_e, tgt_e) src_ir tgt_ir proof check_conf ->
    let front_es = lookup_frontier tgt_e proof in
    check_frontier (src_e, (tgt_e, front_es)) src_ir tgt_ir proof check_conf

(* Loop depth 0 body *)
let rec refinement_check_worklist
  : ufunc_ir
  -> ufunc_ir
  -> proof
  -> ((source_edge * target_edge) * (unit -> unit)) Q.queue (* Debugging *)
  -> checker_config
  -> solver_result list
  -> solver_result list =
  fun src_ir tgt_ir proof queue check_conf solv_ress ->
    match Q.dequeue queue with
    | None -> solv_ress
    | Some ((this_pair, msg_fun), queue1) ->
      (* Special handling for messages for now *)
      let _ = msg_fun () in
      (* End of special handling *)
      let solv_ress1 =
        check_edge_pair this_pair src_ir tgt_ir proof check_conf in
      refinement_check_worklist
        src_ir tgt_ir proof queue1 check_conf (solv_ress @ solv_ress1)

(* Refinement checking interface algorithm that calls the worklist *)
let refinement_check
  : ufunc_ir
  -> ufunc_ir
  -> proof
  -> checker_config
  -> solver_result list =
  fun src_ir tgt_ir proof check_conf ->
    let todos = List.map (fun c -> (c, (fun () -> ()))) proof.checkpoints in
    let queue = Q.from_list todos in
    refinement_check_worklist
      src_ir tgt_ir proof queue check_conf []

(* Refinement checking hack that lets us inject the custom checkpoint list *)
let refinement_check_inject
  : ufunc_ir
  -> ufunc_ir
  -> proof
  -> ((source_edge * target_edge) * (unit -> unit)) list
  -> checker_config
  -> solver_result list =
  fun src_ir tgt_ir proof checkpts check_conf ->
    let queue = Q.from_list checkpts in
    refinement_check_worklist src_ir tgt_ir proof queue check_conf []


