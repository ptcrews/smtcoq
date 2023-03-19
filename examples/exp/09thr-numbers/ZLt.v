(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Export ZMul.
Require Import SMTCoq.SMTCoq.
Module ZOrderProp (Import Z : ZAxiomsMiniSig').
Include ZMulProp Z.

(** Instances of earlier theorems for m == 0 *)

Theorem neg_pos_cases : forall n, n ~= 0 <-> n < 0 \/ n > 0.
Proof. Show. Fail (abduce 3). Admitted.

Theorem nonpos_pos_cases : forall n, n <= 0 \/ n > 0.
Proof. Show. Fail (abduce 3). Admitted.

Theorem neg_nonneg_cases : forall n, n < 0 \/ n >= 0.
Proof. Show. Fail (abduce 3). Admitted.

Theorem nonpos_nonneg_cases : forall n, n <= 0 \/ n >= 0.
Proof. Show. Fail (abduce 3). Admitted.

Ltac zinduct n := induction_maker n ltac:(apply order_induction_0).

(** Theorems that are either not valid on N or have different proofs
    on N and Z *)

Theorem lt_pred_l : forall n, P n < n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem le_pred_l : forall n, P n <= n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem lt_le_pred : forall n m, n < m <-> n <= P m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem nle_pred_r : forall n, ~ n <= P n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem lt_pred_le : forall n m, P n < m <-> n <= m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem lt_lt_pred : forall n m, n < m -> P n < m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem le_le_pred : forall n m, n <= m -> P n <= m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem lt_pred_lt : forall n m, n < P m -> n < m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem le_pred_lt : forall n m, n <= P m -> n <= m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem pred_lt_mono : forall n m, n < m <-> P n < P m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem pred_le_mono : forall n m, n <= m <-> P n <= P m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem lt_succ_lt_pred : forall n m, S n < m <-> n < P m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem le_succ_le_pred : forall n m, S n <= m <-> n <= P m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem lt_pred_lt_succ : forall n m, P n < m <-> n < S m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem le_pred_lt_succ : forall n m, P n <= m <-> n <= S m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem neq_pred_l : forall n, P n ~= n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem lt_m1_r : forall n m, n < m -> m < 0 -> n < -1.
Proof. Show. Fail (abduce 3). Admitted.

End ZOrderProp.

