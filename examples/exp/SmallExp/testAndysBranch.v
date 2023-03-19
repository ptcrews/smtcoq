(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Binary Integers : results about order predicates *)
(** Initial author : Pierre Crégut (CNET, Lannion, France) *)

(** THIS FILE IS DEPRECATED.
    It is now almost entirely made of compatibility formulations
    for results already present in BinInt.Z. *)

Require Import BinPos BinInt Decidable Zcompare.
Require Import Arith_base. (* Useless now, for compatibility only *)
Require Import SMTCoq.SMTCoq.

Local Open Scope Z_scope.

Lemma Zle_gt_succ n m : n <= m -> Z.succ m > n.
Proof. Show. Fail (abduce 1). Admitted.
