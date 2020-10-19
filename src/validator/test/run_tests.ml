(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


open Wasm

(* API *)
open Cfg_builder
open Proof_builder

(* Debug settings *)
open Debug

(* Test cases *)
open Test_proof_A
open Test_proof_B

open Test_proof_C
open Test_dce
open Test_const_prop
open Test_const_fold
open Test_const_hoist
open Test_loop_unroll
open Test_call

(* Other internal stuff *)
open Test_type_inference
open Pass_master
open Basic_basic_merge_pass
open Const_fold_pass

open Ssa_pass

open Worklist


let test_manual_proofs () =
  (*
  let _ = prerr_endline ("<<< test_proof_A >>>") in
  let _ = test_proof_A () in
  let _ = prerr_endline "\n%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n" in

  let _ = prerr_endline ("<<< test_proof_B >>>") in
  let _ = test_proof_B () in
  let _ = prerr_endline "\n%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n" in

  let _ = prerr_endline ("<<< test_proof_C >>>") in
  let _ = test_proof_C () in
  let _ = prerr_endline "\n%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n" in
  *)


  let _ = prerr_endline ("<<< test_dce >>>") in
  let _ = test_dce () in
  let _ = prerr_endline "\n%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n" in

  let _ = prerr_endline ("<<< test_const_prop >>>") in
  let _ = test_const_prop () in
  let _ = prerr_endline "\n%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n" in


  let _ = prerr_endline ("<<< test_const_fold >>>") in
  let _ = test_const_fold () in
  let _ = prerr_endline "\n%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n" in

  let _ = prerr_endline ("<<< test_const_hoist >>>") in
  let _ = test_const_hoist () in
  let _ = prerr_endline "\n%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n" in

  let _ = prerr_endline ("<<< test_loop_unroll >>>") in
  let _ = test_loop_unroll () in
  let _ = prerr_endline "\n%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n" in

  let _ = prerr_endline ("<<< test_call >>>") in
  let _ = test_call () in
  let _ = prerr_endline "\n%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n" in

  (*
  let _ = test_type_inference () in
  *)

  ()


(* ************************* *)

let main () =
  (let _ = print_endline "compiles!" in

  let _ = Printexc.record_backtrace true in

  let _ = set_debug_low () in

  let _ = test_manual_proofs () in

  (*
  let _ = run_passes_tmp
    [
      basic_basic_merge_pass;
      const_fold_pass
    ] in
  *)
  (*
  let _ = run_passes_tmp [] in
  *)

  print_endline "done!");;

main ()



