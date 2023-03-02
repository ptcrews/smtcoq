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

Require Export ZAddOrder.
Require Import SMTCoq.SMTCoq.
Module Type ZMulOrderProp (Import Z : ZAxiomsMiniSig').
Include ZAddOrderProp Z.

Theorem mul_lt_mono_nonpos :
  forall n m p q, m <= 0 -> n < m -> q <= 0 -> p < q ->  m * q < n * p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem mul_le_mono_nonpos :
  forall n m p q, m <= 0 -> n <= m -> q <= 0 -> p <= q ->  m * q <= n * p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem mul_nonpos_nonpos : forall n m, n <= 0 -> m <= 0 -> 0 <= n * m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem mul_nonneg_nonpos : forall n m, 0 <= n -> m <= 0 -> n * m <= 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem mul_nonpos_nonneg : forall n m, n <= 0 -> 0 <= m -> n * m <= 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Notation mul_pos := lt_0_mul (only parsing).

Theorem lt_mul_0 :
  forall n m, n * m < 0 <-> n < 0 /\ m > 0 \/ n > 0 /\ m < 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Notation mul_neg := lt_mul_0 (only parsing).

Theorem le_0_mul :
  forall n m, 0 <= n * m -> 0 <= n /\ 0 <= m \/ n <= 0 /\ m <= 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Notation mul_nonneg := le_0_mul (only parsing).

Theorem le_mul_0 :
  forall n m, n * m <= 0 -> 0 <= n /\ m <= 0 \/ n <= 0 /\ 0 <= m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Notation mul_nonpos := le_mul_0 (only parsing).

Notation le_0_square := square_nonneg (only parsing).

Theorem nlt_square_0 : forall n, ~ n * n < 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem square_lt_mono_nonpos : forall n m, n <= 0 -> m < n -> n * n < m * m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem square_le_mono_nonpos : forall n m, n <= 0 -> m <= n -> n * n <= m * m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem square_lt_simpl_nonpos : forall n m, m <= 0 -> n * n < m * m -> m < n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem square_le_simpl_nonpos : forall n m, m <= 0 -> n * n <= m * m -> m <= n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem lt_1_mul_neg : forall n m, n < -1 -> m < 0 -> 1 < n * m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem lt_mul_m1_neg : forall n m, 1 < n -> m < 0 -> n * m < -1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem lt_mul_m1_pos : forall n m, n < -1 -> 0 < m -> n * m < -1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem lt_1_mul_l : forall n m, 1 < n ->
 n * m < -1 \/ n * m == 0 \/ 1 < n * m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem lt_m1_mul_r : forall n m, n < -1 ->
 n * m < -1 \/ n * m == 0 \/ 1 < n * m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem eq_mul_1 : forall n m, n * m == 1 -> n == 1 \/ n == -1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem lt_mul_diag_l : forall n m, n < 0 -> (1 < m <-> n * m < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem lt_mul_diag_r : forall n m, 0 < n -> (1 < m <-> n < n * m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem le_mul_diag_l : forall n m, n < 0 -> (1 <= m <-> n * m <= n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem le_mul_diag_r : forall n m, 0 < n -> (1 <= m <-> n <= n * m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem lt_mul_r : forall n m p, 0 < n -> 1 < p -> n < m -> n < m * p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Alternative name : *)

Definition mul_eq_1 := eq_mul_1.

End ZMulOrderProp.

