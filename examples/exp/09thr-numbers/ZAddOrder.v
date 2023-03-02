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

Require Export ZLt.
Require Import SMTCoq.SMTCoq.
Module ZAddOrderProp (Import Z : ZAxiomsMiniSig').
Include ZOrderProp Z.

(** Theorems that are either not valid on N or have different proofs
    on N and Z *)

Theorem add_neg_neg : forall n m, n < 0 -> m < 0 -> n + m < 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem add_neg_nonpos : forall n m, n < 0 -> m <= 0 -> n + m < 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem add_nonpos_neg : forall n m, n <= 0 -> m < 0 -> n + m < 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem add_nonpos_nonpos : forall n m, n <= 0 -> m <= 0 -> n + m <= 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Sub and order *)

Theorem lt_0_sub : forall n m, 0 < m - n <-> n < m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Notation sub_pos := lt_0_sub (only parsing).

Theorem le_0_sub : forall n m, 0 <= m - n <-> n <= m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Notation sub_nonneg := le_0_sub (only parsing).

Theorem lt_sub_0 : forall n m, n - m < 0 <-> n < m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Notation sub_neg := lt_sub_0 (only parsing).

Theorem le_sub_0 : forall n m, n - m <= 0 <-> n <= m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Notation sub_nonpos := le_sub_0 (only parsing).

Theorem opp_lt_mono : forall n m, n < m <-> - m < - n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem opp_le_mono : forall n m, n <= m <-> - m <= - n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem opp_pos_neg : forall n, 0 < - n <-> n < 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem opp_neg_pos : forall n, - n < 0 <-> 0 < n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem opp_nonneg_nonpos : forall n, 0 <= - n <-> n <= 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem opp_nonpos_nonneg : forall n, - n <= 0 <-> 0 <= n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem lt_m1_0 : -1 < 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem sub_lt_mono_l : forall n m p, n < m <-> p - m < p - n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem sub_lt_mono_r : forall n m p, n < m <-> n - p < m - p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem sub_lt_mono : forall n m p q, n < m -> q < p -> n - p < m - q.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem sub_le_mono_l : forall n m p, n <= m <-> p - m <= p - n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem sub_le_mono_r : forall n m p, n <= m <-> n - p <= m - p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem sub_le_mono : forall n m p q, n <= m -> q <= p -> n - p <= m - q.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem sub_lt_le_mono : forall n m p q, n < m -> q <= p -> n - p < m - q.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem sub_le_lt_mono : forall n m p q, n <= m -> q < p -> n - p < m - q.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem le_lt_sub_lt : forall n m p q, n <= m -> p - n < q - m -> p < q.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem lt_le_sub_lt : forall n m p q, n < m -> p - n <= q - m -> p < q.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem le_le_sub_lt : forall n m p q, n <= m -> p - n <= q - m -> p <= q.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem lt_add_lt_sub_r : forall n m p, n + p < m <-> n < m - p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem le_add_le_sub_r : forall n m p, n + p <= m <-> n <= m - p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem lt_add_lt_sub_l : forall n m p, n + p < m <-> p < m - n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem le_add_le_sub_l : forall n m p, n + p <= m <-> p <= m - n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem lt_sub_lt_add_r : forall n m p, n - p < m <-> n < m + p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem le_sub_le_add_r : forall n m p, n - p <= m <-> n <= m + p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem lt_sub_lt_add_l : forall n m p, n - m < p <-> n < m + p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem le_sub_le_add_l : forall n m p, n - m <= p <-> n <= m + p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem lt_sub_lt_add : forall n m p q, n - m < p - q <-> n + q < m + p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem le_sub_le_add : forall n m p q, n - m <= p - q <-> n + q <= m + p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem lt_sub_pos : forall n m, 0 < m <-> n - m < n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem le_sub_nonneg : forall n m, 0 <= m <-> n - m <= n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem sub_lt_cases : forall n m p q, n - m < p - q -> n < m \/ q < p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem sub_le_cases : forall n m p q, n - m <= p - q -> n <= m \/ q <= p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem sub_neg_cases : forall n m, n - m < 0 -> n < 0 \/ 0 < m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem sub_pos_cases : forall n m, 0 < n - m -> 0 < n \/ m < 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem sub_nonpos_cases : forall n m, n - m <= 0 -> n <= 0 \/ 0 <= m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem sub_nonneg_cases : forall n m, 0 <= n - m -> 0 <= n \/ m <= 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Section PosNeg.

Variable P : Z.t -> Prop.
Hypothesis P_wd : Proper (eq ==> iff) P.

Theorem zero_pos_neg :
  P 0 -> (forall n, 0 < n -> P n /\ P (- n)) -> forall n, P n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End PosNeg.

Ltac zero_pos_neg n := induction_maker n ltac:(apply zero_pos_neg).

End ZAddOrderProp.


