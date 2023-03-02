(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import ZAxioms ZMulOrder GenericMinMax.
Require Import SMTCoq.SMTCoq.
(** * Properties of minimum and maximum specific to integer numbers *)

Module Type ZMaxMinProp (Import Z : ZAxiomsMiniSig').
Include ZMulOrderProp Z.

(** The following results are concrete instances of [max_monotone]
    and similar lemmas. *)

(** Succ *)

Lemma succ_max_distr n m : S (max n m) == max (S n) (S m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma succ_min_distr n m : S (min n m) == min (S n) (S m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Pred *)

Lemma pred_max_distr n m : P (max n m) == max (P n) (P m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pred_min_distr n m : P (min n m) == min (P n) (P m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Add *)

Lemma add_max_distr_l n m p : max (p + n) (p + m) == p + max n m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma add_max_distr_r n m p : max (n + p) (m + p) == max n m + p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma add_min_distr_l n m p : min (p + n) (p + m) == p + min n m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma add_min_distr_r n m p : min (n + p) (m + p) == min n m + p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Opp *)

Lemma opp_max_distr n m : -(max n m) == min (-n) (-m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma opp_min_distr n m : -(min n m) == max (-n) (-m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Sub *)

Lemma sub_max_distr_l n m p : max (p - n) (p - m) == p - min n m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sub_max_distr_r n m p : max (n - p) (m - p) == max n m - p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sub_min_distr_l n m p : min (p - n) (p - m) == p - max n m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sub_min_distr_r n m p : min (n - p) (m - p) == min n m - p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Mul *)

Lemma mul_max_distr_nonneg_l n m p : 0 <= p ->
 max (p * n) (p * m) == p * max n m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mul_max_distr_nonneg_r n m p : 0 <= p ->
 max (n * p) (m * p) == max n m * p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mul_min_distr_nonneg_l n m p : 0 <= p ->
 min (p * n) (p * m) == p * min n m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mul_min_distr_nonneg_r n m p : 0 <= p ->
 min (n * p) (m * p) == min n m * p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mul_max_distr_nonpos_l n m p : p <= 0 ->
 max (p * n) (p * m) == p * min n m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mul_max_distr_nonpos_r n m p : p <= 0 ->
 max (n * p) (m * p) == min n m * p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mul_min_distr_nonpos_l n m p : p <= 0 ->
 min (p * n) (p * m) == p * max n m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mul_min_distr_nonpos_r n m p : p <= 0 ->
 min (n * p) (m * p) == max n m * p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End ZMaxMinProp.
