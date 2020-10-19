(**
   Copyright 2020 Nokia
   Licensed under the BSD 3-Clause License.
   SPDX-License-Identifier: BSD-3-Clause
*)


type ('a, 'b) either =
  | Left of 'a
  | Right of 'b

