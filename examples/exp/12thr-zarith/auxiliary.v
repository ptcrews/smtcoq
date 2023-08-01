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

(** Binary Integers (Pierre Crégut, CNET, Lannion, France) *)

Require Export Arith_base.
Require Import BinInt.
Require Import Zorder.
Require Import Decidable.
Require Import Peano_dec.
Require Export Compare_dec.
Add Rec LoadPath "/home/arjun/Desktop/smtcoq/abduction-arjunvish-smtcoq/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Local Open Scope Z_scope.

(***************************************************************)
(** * Moving terms from one side to the other of an inequality *)

Theorem Zne_left n m : Zne n m -> Zne (n + - m) 0.
Proof. Show. Fail (abduce 3). Admitted.

Theorem Zegal_left n m : n = m -> n + - m = 0.
Proof. Show. Fail (abduce 3). Admitted.

Theorem Zle_left n m : n <= m -> 0 <= m + - n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem Zle_left_rev n m : 0 <= m + - n -> n <= m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem Zlt_left_rev n m : 0 < m + - n -> n < m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem Zlt_left_lt n m : n < m -> 0 < m + - n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem Zlt_left n m : n < m -> 0 <= m + -1 + - n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem Zge_left n m : n >= m -> 0 <= n + - m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem Zgt_left n m : n > m -> 0 <= n + -1 + - m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem Zgt_left_gt n m : n > m -> n + - m > 0.
Proof. Show. Fail (abduce 3). Admitted.

Theorem Zgt_left_rev n m : n + - m > 0 -> n > m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem Zle_mult_approx n m p :
  n > 0 -> p > 0 -> 0 <= m -> 0 <= m * n + p.
Proof. Show. Fail (abduce 3). Admitted.

Theorem Zmult_le_approx n m p :
  n > 0 -> n > p -> 0 <= m * n + p -> 0 <= m.
Proof. Show. Fail (abduce 3). Admitted.

Register Zegal_left as plugins.omega.Zegal_left.
Register Zne_left as plugins.omega.Zne_left.
Register Zlt_left as plugins.omega.Zlt_left.
Register Zgt_left as plugins.omega.Zgt_left.
Register Zle_left as plugins.omega.Zle_left.
Register Zge_left as plugins.omega.Zge_left.
Register Zmult_le_approx as plugins.omega.Zmult_le_approx.
