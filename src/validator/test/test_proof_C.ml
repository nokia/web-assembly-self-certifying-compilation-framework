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
open State_types
open Proof_types
open Solver_types
open Worklist

open Digraph

open Cfg_builder
open Proof_builder

module List = List_utils

(* The goal of this is to test the enabling checks *)

(* Here we attempt to test whether enable / disables are correctly checked.
 * Source graph:
 *  If tests: {v100, v101 (true), v102 (false), v103}
 *  BrIf tests: {v200, v201 (true), v202 (false), v203}
 *  BrTable tests: {v300, v301 (index 0), v302 (index 2), v303 (default)}
 *
 *                    [000]
 *                      |
 *          __________[001]____________
 *         /            |              \
 *      [100]         [200]           [300]
 *      /  \          /  \           /  |  \
 *  [101]  [102]  [201]  [202]  [301] [302] [303]
 *      \  /          \  /           \  |  /
 *      [103]         [203]           [304]
 *         \__________  |  ____________/
 *                    [002]
 *                      |
 *                    [003]
 *
 * Target graph:
 *
 *                           [000]
 *                             |
 *             ______________[001]_______________
 *            /                |                 \
 *        [100]              [200]               [300]_______
 *       /  |               /  |  \             /  |  \      \
 *  [101] [102]        [201] [202] [204]  [301] [302] [303] [305]
 *       \  |               \  |  /             \  |  /______/
 *        [103]              [203]               [304]
 *             \_____________  |  _______________/
 *                           [002]
 *                             |
 *                           [003]
 *
 * The main changes here are that we add v204 and v305, where:
 *  v204 has the same content as v201
 *  v305 has the same content as v303
 *
 * However the branch conditions into v204, and v305 are all disabled,
 * and this lets us "diff" it against an enabled path
 * passing through v101, v201, and v301 respectively.
 *)

let src_adjs
  : (G.vertex * (Ast.instr list) * ((G.vertex * branch) list)) list =
  [ (* Source and sink *)
    (0, [], [(1, Jump)]);
    (1, [const 12345],
      [ (100, JumpIndex 0l);
        (200, JumpIndex 1l);
        (300, JumpDefault 2l); ]);
    (2, [], [(3, Jump)]);
    (3, [], []);

    (* If *)
    (100, [const 100],
      [ (101, JumpIf true);
        (102, JumpIf false); ]);
    (101, [const 101], [(103, Jump)]);
    (102, [const 102], [(103, Jump)]);
    (103, [const 103], [(2, Jump)]);

    (* BrIf *)
    (200, [const 200],
      [ (201, JumpBrIf true);
        (202, JumpBrIf false); ]);
    (201, [const 201], [(203, Jump)]);
    (202, [const 202], [(203, Jump)]);
    (203, [const 203], [(2, Jump)]);

    (* BrTable *)
    (300, [const 0],
      [ (301, JumpIndex 0l);
        (302, JumpIndex 1l);
        (303, JumpDefault 2l) ]);
    (301, [const 301], [(304, Jump)]);
    (302, [const 302], [(304, Jump)]);
    (303, [const 303], [(304, Jump)]);
    (304, [const 304], [(2, Jump)]);
  ]

let src_cfg_data : cfg_data =
  { empty_cfg_data with
    cfg_id = "test_proof_C_src";
    root_vertex = 1;
    sink_vertex = 2;
    adjacency_list = src_adjs;
  }

let tgt_adjs
  : (G.vertex * (Ast.instr list) * ((G.vertex * branch) list)) list =
  [ (* Source and sink *)
    (0, [], [(1, Jump)]);
    (1, [const 12345],
      [ (100, JumpIndex 0l);
        (200, JumpIndex 1l);
        (300, JumpDefault 2l); ]);
    (2, [], [(3, Jump)]);
    (3, [], []);

    (* If *)
    (100, [const 100],
      [ (101, JumpIf true);
        (102, JumpIf false); ]);
        (* (104, JumpIf false); ]); *) (* MODIFIED ; year 2019 commits *)
    (101, [const 101], [(103, Jump)]);
    (102, [const 102], [(103, Jump)]);
    (103, [const 103], [(2, Jump)]);
    (* (104, [const 101], [(103, Jump)]); *) (* MODIFIED ; year 2019 commits *) 

    (* BrIf *)
    (200, [const 200],
      [ (201, JumpBrIf true);
        (202, JumpBrIf false);
        (204, JumpBrIf false); ]);  (* MODIFIED *)
    (201, [const 201], [(203, Jump)]);
    (202, [const 202], [(203, Jump)]);
    (203, [const 203], [(2, Jump)]);
    (204, [const 201], [(203, Jump)]);  (* MODIFIED *)

    (* BrTable *)
    (300, [const 0],
      [ (301, JumpIndex 0l);
        (302, JumpIndex 1l);
        (303, JumpDefault 2l);
        (305, JumpDefault 2l); ]);  (* MODIFIED *)
    (301, [const 301], [(304, Jump)]);
    (302, [const 302], [(304, Jump)]);
    (303, [const 303], [(304, Jump)]);
    (304, [const 304], [(2, Jump)]);
    (305, [const 303], [(304, Jump)]);  (* MODIFIED *)
  ]

let tgt_cfg_data : cfg_data =
  { empty_cfg_data with
    cfg_id = "test_proof_C_tgt";
    root_vertex = 1;
    sink_vertex = 2;
    adjacency_list = tgt_adjs;
  }

(* Make the proof *)

let refinement_adjs
  : ((source_edge * target_edge * state_status_flag) * state_pair_formula) list =

  [ (((0,1),(0,1),Initial), full_state_pair_equiv);
    
    (* Lefts *)
    (((100,101),(100,101),Final), full_state_pair_equiv);
    (((100,102),(100,102),Final), full_state_pair_equiv);

    (((100,101),(100,101),Initial), full_state_pair_equiv);
    (((100,102),(100,102),Initial), full_state_pair_equiv);

    (* Middles *)
    (((200,201),(200,201),Final), full_state_pair_equiv);
    (((200,202),(200,202),Final), full_state_pair_equiv);
    (((200,201),(200,204),Final), full_state_pair_equiv);

    (((200,201),(200,201),Initial), full_state_pair_equiv);
    (((200,202),(200,202),Initial), full_state_pair_equiv);
    (((200,201),(200,204),Initial), full_state_pair_equiv);

    (* Rights *)
    (((300,301),(300,301),Final), full_state_pair_equiv);
    (((300,302),(300,302),Final), full_state_pair_equiv);
    (((300,303),(300,303),Final), full_state_pair_equiv);
    (((300,303),(300,305),Final), full_state_pair_equiv);

    (((300,301),(300,301),Initial), full_state_pair_equiv);
    (((300,302),(300,302),Initial), full_state_pair_equiv);
    (((300,303),(300,303),Initial), full_state_pair_equiv);
    (((300,303),(300,305),Initial), full_state_pair_equiv);


    (((2,3), (2,3), Final), full_state_pair_equiv); ]


(* Frontiers for the target.
 * There is only one for (null, 1) to (11, null) *)
let frontier_adjs : (target_edge * (target_edge list)) list =
  [ ((0, 1),
      [ (100,101); (100,102);
        (200,201); (200,202); (200,204);
        (300,301); (300,302); (300,303); (300,305) ]);

    ((100,101), [(2,3)]);
    ((100,102), [(2,3)]);

    ((200,201), [(2,3)]);
    ((200,202), [(2,3)]);
    ((200,204), [(2,3)]);

    ((300,301), [(2,3)]);
    ((300,302), [(2,3)]);
    ((300,303), [(2,3)]);
    ((300,305), [(2,3)]); ]

(* Match paths, where we map the following:
 *  tgt_001_100_101_103_002  \mapsto src_001_100_101_103_102 (should SAT)
 *  tgt_101_100_102'_103_002 \mapsto src_001_100_101_103_102 (should UNSAT)
 *)
let match_path_adjs : ((source_edge * target_path) * source_path) list =
  [ (* The very starts *)
    (((0,1), [0;1;100;101]), [0;1;100;101]);
    (((0,1), [0;1;100;102]), [0;1;100;102]);

    (((0,1), [0;1;200;201]), [0;1;200;201]);
    (((0,1), [0;1;200;202]), [0;1;200;202]);
    (((0,1), [0;1;200;204]), [0;1;200;201]);

    (((0,1), [0;1;300;301]), [0;1;300;301]);
    (((0,1), [0;1;300;302]), [0;1;300;302]);
    (((0,1), [0;1;300;303]), [0;1;300;303]);
    (((0,1), [0;1;300;305]), [0;1;300;303]);

    (* Lefts *)
    (((100,101), [100;101;103;2;3]), [100;101;103;2;3]);
    (((100,102), [100;102;103;2;3]), [100;102;103;2;3]);

    (* Middles *)
    (((200,201), [200;201;203;2;3]), [200;201;203;2;3]);
    (((200,202), [200;202;203;2;3]), [200;202;203;2;3]);
    (((200,201), [200;204;203;2;3]), [200;201;203;2;3]);

    (* Rights *)
    (((300,301), [300;301;304;2;3]), [300;301;304;2;3]);
    (((300,302), [300;302;304;2;3]), [300;302;304;2;3]);
    (((300,303), [300;303;304;2;3]), [300;303;304;2;3]);
    (((300,303), [300;305;304;2;3]), [300;303;304;2;3]);
  ]

(* Construct the proof object *)
let proof_C : proof =
  { empty_proof with
    func_id = "test_proof_C";
    refinement_map =
      SourceEdge_TargetEdgeMap.of_seq (List.to_seq refinement_adjs);
    frontier_map =
      TargetEdgeMap.of_seq (List.to_seq frontier_adjs);
    path_match_map =
      SourceEdge_TargetPathMap.of_seq (List.to_seq match_path_adjs);
    checkpoints =
      [ ((0,1), (0,1));

        ((100,101), (100,101));
        ((100,102), (100,102));

        ((200,201), (200,201));
        ((200,202), (200,202));
        ((200,201), (200,204));

        ((300,301), (300,301));
        ((300,302), (300,302));
        ((300,303), (300,303));
        ((300,303), (300,305));
      ]
  }

let test_proof_C : unit -> unit =
  fun _ ->
    let _ =
      refinement_check_inject
        (cfg_data_to_ufunc_ir src_cfg_data)
        (cfg_data_to_ufunc_ir tgt_cfg_data)
        proof_C
        [ (((0,1), (0,1)),
            (fun _ -> prerr_endline "should be valid"));

          (((100,101), (100,101)),
            (fun _ -> prerr_endline "should be valid"));

          (((100,102), (100,102)),
            (fun _ -> prerr_endline "should be valid"));

          (((200,201), (200,201)),
            (fun _ -> prerr_endline "should be valid"));

          (((200,202), (200,202)),
            (fun _ -> prerr_endline "should be valid"));

          (((200,201), (200,204)),
            (fun _ -> prerr_endline "should be valid?"));

          (((300,301), (300,301)),
            (fun _ -> prerr_endline "should be valid?"));

          (((300,302), (300,302)),
            (fun _ -> prerr_endline "should be valid?"));

          (((300,303), (300,303)),
            (fun _ -> prerr_endline "should be valid?"));

          (((300,303), (300,305)),
            (fun _ -> prerr_endline "should be valid?"));
        ]
        default_checker_config in
    ()


