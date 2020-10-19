(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


open Wasm
open Source

open Func_types
open Type_inference
open Debug
open System

open Wasm_utils

(* We may want to annotate the modules that are parsed out of the
 * spec/interpreter's parser -- perhaps with control flow graphs.
 * However, at the same time, we may wish to re-use much of the original
 * functionality, which means that we have to be able to readily convert
 * between whatever internal representation we use and the spec/interpreter's
 * syntax/ast.ml and script/script.ml.
 *
 * The compromise we have is that we opt to create a mimic of the
 * data structures present within spec/interpreter,
 * and then write conversion functions between the two.
 * As a consequence, critical code should never "open Wasm.Ast" or equivalent
 * in order to avoid namespace collision.
 *
 * The type annotations are:
 *  'modty: for each module in textual, encoded, or quoted format
 *  'actty: for each action
 *  'asrty: for each assertion
 *
 * Whether all of these end up getting used is another question,
 * but the framework exists should they be relevant.
 *)

type var = string Source.phrase

type 'modty module_ = Ast.module_ * 'modty
type 'modty encoded = (string * string) * 'modty
type 'modty quoted = (string * string) * 'modty
type 'modty definition = ('modty definition') Source.phrase
and 'modty definition' =
  | Textual of 'modty module_
  | Encoded of 'modty encoded
  | Quoted of 'modty quoted

type 'actty action = 'actty action' Source.phrase
and 'actty action' =
  | Invoke of var option * Ast.name * Ast.literal list * 'actty
  | Get of var option * Ast.name * 'actty

type ('modty, 'actty, 'asrty) assertion =
  (('modty, 'actty, 'asrty) assertion') Source.phrase
and ('modty, 'actty, 'asrty) assertion' =
  | AssertMalformed of 'modty definition * string * 'asrty
  | AssertInvalid of 'modty definition * string * 'asrty
  | AssertUnlinkable of 'modty definition * string * 'asrty
  | AssertUninstantiable of 'modty definition * string * 'asrty
  | AssertReturn of 'actty action * Ast.literal list * 'asrty
  | AssertReturnCanonicalNaN of 'actty action * 'asrty
  | AssertReturnArithmeticNaN of 'actty action * 'asrty
  | AssertTrap of 'actty action * string * 'asrty
  | AssertExhaustion of 'actty action * string * 'asrty

type ('modty, 'actty, 'asrty) command =
  ('modty, 'actty, 'asrty) command' Source.phrase
and ('modty, 'actty, 'asrty) command' =
  | Module of var option * 'modty definition
  | Register of Ast.name * var option
  | Action of 'actty action
  | Assertion of ('modty, 'actty, 'asrty) assertion
  | Meta of ('modty, 'actty, 'asrty) meta

and ('modty, 'actty, 'asrty) meta =
  (('modty, 'actty, 'asrty) meta') Source.phrase
and ('modty, 'actty, 'asrty) meta' =
  | Input of var option * string
  | Output of var option * string option
  | Script of var option * ('modty, 'actty, 'asrty) script

and ('modty, 'actty, 'asrty) script = (('modty, 'actty, 'asrty) command) list

exception Syntax of Source.region * string

(* These are the data structures that we keep around for a particular
 * internal representation where the function graphs (CFGs)
 * of modules are needed.
 * Note that we parametrize over the kinds of graphs accepted,
 * with the goal that this adds flexibility for various optimization passes.
 * Here we do not care as much about the action annotations nor the
 * assertion annotations. *)

(* Effectively, we tag each function with a graph,
 * where functions' id's are identified by their index within a module.
 * An alternative approach would have been going down one step further
 * and redefining what was in Ast.module_,
 * but leaving at this abstraction level allows a bit more generality,
 * and we can implicitly (via indices) calculate the function id's anyways
 *
 * We take the module id to be the file + line + column info.
 *)
type ('a, 'b) modty =
  { module_id : string; func_irs : ('a, 'b) func_ir list }

let empty_umodty : (unit, unit) modty =
  { module_id = ""; func_irs = [] }

type actty = unit
type asrty = unit

type ('a, 'b) module_ir = (('a, 'b) modty) module_
type ('a, 'b) definition_ir = (('a, 'b) modty) definition
type action_ir = actty action
type ('a, 'b) assertion_ir = (('a, 'b) modty, actty, asrty) assertion
type ('a, 'b) command_ir = (('a, 'b) modty, actty, asrty) command
type ('a, 'b) meta_ir = (('a, 'b) modty, actty, asrty) meta
type ('a, 'b) script_ir = (('a, 'b) modty, actty, asrty) script

(* Mostly we first work with the unit versions *)

type umodule_ir = (unit, unit) module_ir
type udefinition_ir = (unit, unit) definition_ir
type uaction_ir = action_ir
type uassertion_ir = (unit, unit) assertion_ir
type ucommand_ir = (unit, unit) command_ir
type umeta_ir = (unit, unit) meta_ir
type uscript_ir = (unit, unit) script_ir

(* **************************** *)

(* Conversions from the ir back into script format *)

let definition_ir_to_definition : 'a definition -> Script.definition =
  fun def_ir ->
    (match def_ir.it with
    | Textual (md, _) -> Script.Textual md
    | Encoded ((name, buf), _) -> Script.Encoded (name, buf)
    | Quoted ((name, str), _) -> Script.Quoted (name, str))
    @@ def_ir.at

let action_ir_to_action : 'c action -> Script.action =
  fun act_ir ->
    (match act_ir.it with
    | Invoke (x_opt, name, vs, _) -> Script.Invoke (x_opt, name, vs)
    | Get (x_opt, name, _) -> Script.Get (x_opt, name))
    @@ act_ir.at

let assertion_ir_to_assertion : ('a, 'b, 'c) assertion -> Script.assertion =
  fun asr_ir ->
    (match asr_ir.it with
    | AssertMalformed (def_ir, why, _) ->
      Script.AssertMalformed (definition_ir_to_definition def_ir, why)
    | AssertInvalid (def_ir, why, _) ->
      Script.AssertInvalid (definition_ir_to_definition def_ir, why)
    | AssertUnlinkable (def_ir, why, _) ->
      Script.AssertUnlinkable (definition_ir_to_definition def_ir, why)
    | AssertUninstantiable (def_ir, why, _) ->
      Script.AssertUninstantiable (definition_ir_to_definition def_ir, why)
    | AssertReturn (act_ir, vs, _) ->
      Script.AssertReturn (action_ir_to_action act_ir, vs)
    | AssertReturnCanonicalNaN (act_ir, _) ->
      Script.AssertReturnCanonicalNaN (action_ir_to_action act_ir)
    | AssertReturnArithmeticNaN (act_ir, _) ->
      Script.AssertReturnArithmeticNaN (action_ir_to_action act_ir)
    | AssertTrap (act_ir, why, _) ->
      Script.AssertTrap (action_ir_to_action act_ir, why)
    | AssertExhaustion (act_ir, why, _) ->
      Script.AssertExhaustion (action_ir_to_action act_ir, why))
    @@ asr_ir.at

let rec command_ir_to_command : ('a, 'b, 'c) command -> Script.command =
  fun cmd_ir ->
    (match cmd_ir.it with
    | Module (x_opt, def_ir) ->
      Script.Module (x_opt, (definition_ir_to_definition def_ir))
    | Register (name, x_opt) -> Script.Register (name, x_opt)
    | Action act_ir -> Script.Action (action_ir_to_action act_ir)
    | Assertion asr_ir -> Script.Assertion (assertion_ir_to_assertion asr_ir)
    | Meta meta_ir -> Script.Meta (meta_ir_to_meta meta_ir))
    @@ cmd_ir.at

and meta_ir_to_meta : ('a, 'b, 'c) meta -> Script.meta =
  fun meta_ir ->
    (match meta_ir.it with
    | Input (x_opt, file) -> Script.Input (x_opt, file)
    | Output (x_opt, file_opt) -> Script.Output (x_opt, file_opt)
    | Script (x_opt, script_ir) ->
      Script.Script (x_opt, script_ir_to_script script_ir))
    @@ meta_ir.at

and script_ir_to_script : ('a, 'b, 'c) script -> Script.script =
  fun script_ir -> List.map command_ir_to_command script_ir

(* ******************** *)

(* Conversion functions from the regular script into the IR.
 * Everything is fairly boring except for a part that interacts with
 * the Ast.func and func ir within the module. *)

(* This is maybe the most "interesting" part of the IR conversion:
 * it's when we call the func_to_ufunc_ir to generate the func ir *)
let region_to_module_id : region -> string =
  fun reg ->
    "M" ^ reg.left.file
        ^ "_L" ^ string_of_int (reg.left.line)
        ^ "_C" ^ string_of_int (reg.left.column)

let module_to_func_type_data : Ast.module_ -> (Ast.type_ list * Ast.var list) =
  fun mod_ ->
    let types_ = mod_.it.types in
    let funcs = mod_.it.funcs in
    (* let fun_types = List.map (fun t -> from_func_type t.it) types in *)
    let ftypes = List.map (fun (f : Ast.func) -> f.it.ftype) funcs in
    (types_, ftypes)

let module_to_umodule_ir : Ast.module_ -> umodule_ir =
  fun mod_ ->
    let type_data = module_to_func_type_data mod_ in
    let func_count = List.length mod_.it.funcs in
    let func_irs =
      List.mapi
        (fun ind f ->
          let _ = print_debug_none ("\t converting function "
                    ^ (string_of_fraction (ind + 1, func_count))) in
          let fid = (region_to_module_id mod_.at ^ "_F" ^ string_of_int ind) in
          func_to_ufunc_ir f fid ind type_data)
        mod_.it.funcs in
    (mod_,
      { empty_umodty with
        module_id = region_to_module_id mod_.at;
        func_irs = func_irs })

let definition_to_udefinition_ir : Script.definition -> udefinition_ir =
  fun def ->
    (match def.it with
    | Script.Textual mod_ -> Textual (module_to_umodule_ir mod_)
    | Script.Encoded (name, buf) ->
      Encoded ((name, buf),
        { empty_umodty with module_id = region_to_module_id def.at })
    | Script.Quoted (name, str) ->
      Quoted ((name, str),
        { empty_umodty with module_id = region_to_module_id def.at }))
    @@ def.at

let action_to_uaction_ir : Script.action -> uaction_ir =
  fun act ->
    (match act.it with
    | Script.Invoke (x_opt, name, vs) -> Invoke (x_opt, name, vs, ())
    | Script.Get (x_opt, name) -> Get (x_opt, name, ()))
    @@ act.at

let assertion_to_uassertion_ir : Script.assertion -> uassertion_ir =
  fun asr_ ->
    (match asr_.it with
    | Script.AssertMalformed (def, why) ->
      AssertMalformed (definition_to_udefinition_ir def, why, ())
    | Script.AssertInvalid (def, why) ->
      AssertInvalid (definition_to_udefinition_ir def, why, ())
    | Script.AssertUnlinkable (def, why) ->
      AssertUnlinkable (definition_to_udefinition_ir def, why, ())
    | Script.AssertUninstantiable (def, why) ->
      AssertUninstantiable (definition_to_udefinition_ir def, why, ())
    | Script.AssertReturn (act, why) ->
      AssertReturn (action_to_uaction_ir act, why, ())
    | Script.AssertReturnCanonicalNaN act ->
      AssertReturnCanonicalNaN (action_to_uaction_ir act, ())
    | Script.AssertReturnArithmeticNaN act ->
      AssertReturnArithmeticNaN (action_to_uaction_ir act, ())
    | Script.AssertTrap (act, why) ->
      AssertTrap (action_to_uaction_ir act, why, ())
    | Script.AssertExhaustion (act, why) ->
      AssertExhaustion (action_to_uaction_ir act, why, ()))
    @@ asr_.at

let rec command_to_ucommand_ir : Script.command -> ucommand_ir =
  fun cmd ->
    (match cmd.it with
    | Script.Module (x_opt, def) ->
      Module (x_opt, definition_to_udefinition_ir def)
    | Script.Register (name, x_opt) -> Register (name, x_opt)
    | Script.Action act -> Action (action_to_uaction_ir act)
    | Script.Assertion asr_ -> Assertion (assertion_to_uassertion_ir asr_)
    | Script.Meta meta -> Meta (meta_to_umeta_ir meta))
    @@ cmd.at

and meta_to_umeta_ir : Script.meta -> umeta_ir =
  fun meta ->
    (match meta.it with
    | Script.Input (x_opt, file) -> Input (x_opt, file)
    | Script.Output (x_opt, file_opt) -> Output (x_opt, file_opt)
    | Script.Script (x_opt, script) ->
      Script (x_opt, script_to_uscript_ir script))
    @@ meta.at

and script_to_uscript_ir : Script.script -> uscript_ir =
  fun script -> List.map (command_to_ucommand_ir) script


