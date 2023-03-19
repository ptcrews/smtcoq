(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Properties of the greatest common divisor *)

Require Import ZAxioms ZMulOrder ZSgnAbs NZGcd.
Require Import SMTCoq.SMTCoq.
Module Type ZGcdProp
 (Import A : ZAxiomsSig')
 (Import B : ZMulOrderProp A)
 (Import C : ZSgnAbsProp A B).

 Include NZGcdProp A A B.

(** Results concerning divisibility*)

Lemma divide_opp_l : forall n m, (-n | m) <-> (n | m).
Proof. Show. Fail (abduce 3). Admitted.

Lemma divide_opp_r : forall n m, (n | -m) <-> (n | m).
Proof. Show. Fail (abduce 3). Admitted.

Lemma divide_abs_l : forall n m, (abs n | m) <-> (n | m).
Proof. Show. Fail (abduce 3). Admitted.

Lemma divide_abs_r : forall n m, (n | abs m) <-> (n | m).
Proof. Show. Fail (abduce 3). Admitted.

Lemma divide_1_r_abs : forall n, (n | 1) -> abs n == 1.
Proof. Show. Fail (abduce 3). Admitted.

Lemma divide_1_r : forall n, (n | 1) -> n==1 \/ n==-1.
Proof. Show. Fail (abduce 3). Admitted.

Lemma divide_antisym_abs : forall n m,
 (n | m) -> (m | n) -> abs n == abs m.
Proof. Show. Fail (abduce 3). Admitted.

Lemma divide_antisym : forall n m,
 (n | m) -> (m | n) -> n == m \/ n == -m.
Proof. Show. Fail (abduce 3). Admitted.

Lemma divide_sub_r : forall n m p, (n | m) -> (n | p) -> (n | m - p).
Proof. Show. Fail (abduce 3). Admitted.

Lemma divide_add_cancel_r : forall n m p, (n | m) -> (n | m + p) -> (n | p).
Proof. Show. Fail (abduce 3). Admitted.

(** Properties of gcd *)

Lemma gcd_opp_l : forall n m, gcd (-n) m == gcd n m.
Proof. Show. Fail (abduce 3). Admitted.

Lemma gcd_opp_r : forall n m, gcd n (-m) == gcd n m.
Proof. Show. Fail (abduce 3). Admitted.

Lemma gcd_abs_l : forall n m, gcd (abs n) m == gcd n m.
Proof. Show. Fail (abduce 3). Admitted.

Lemma gcd_abs_r : forall n m, gcd n (abs m) == gcd n m.
Proof. Show. Fail (abduce 3). Admitted.

Lemma gcd_0_l : forall n, gcd 0 n == abs n.
Proof. Show. Fail (abduce 3). Admitted.

Lemma gcd_0_r : forall n, gcd n 0 == abs n.
Proof. Show. Fail (abduce 3). Admitted.

Lemma gcd_diag : forall n, gcd n n == abs n.
Proof. Show. Fail (abduce 3). Admitted.

Lemma gcd_add_mult_diag_r : forall n m p, gcd n (m+p*n) == gcd n m.
Proof. Show. Fail (abduce 3). Admitted.

Lemma gcd_add_diag_r : forall n m, gcd n (m+n) == gcd n m.
Proof. Show. Fail (abduce 3). Admitted.

Lemma gcd_sub_diag_r : forall n m, gcd n (m-n) == gcd n m.
Proof. Show. Fail (abduce 3). Admitted.

Definition Bezout n m p := exists a b, a*n + b*m == p.

Instance Bezout_wd : Proper (eq==>eq==>eq==>iff) Bezout.
Proof. Show. Fail (abduce 3). Admitted.

Lemma bezout_1_gcd : forall n m, Bezout n m 1 -> gcd n m == 1.
Proof. Show. Fail (abduce 3). Admitted.

Lemma gcd_bezout : forall n m p, gcd n m == p -> Bezout n m p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma gcd_mul_mono_l :
  forall n m p, gcd (p * n) (p * m) == abs p * gcd n m.
Proof. Show. Fail (abduce 3). Admitted.

Lemma gcd_mul_mono_l_nonneg :
 forall n m p, 0<=p -> gcd (p*n) (p*m) == p * gcd n m.
Proof. Show. Fail (abduce 3). Admitted.

Lemma gcd_mul_mono_r :
 forall n m p, gcd (n * p) (m * p) == gcd n m * abs p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma gcd_mul_mono_r_nonneg :
 forall n m p, 0<=p -> gcd (n*p) (m*p) == gcd n m * p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma gauss : forall n m p, (n | m * p) -> gcd n m == 1 -> (n | p).
Proof. Show. Fail (abduce 3). Admitted.

Lemma divide_mul_split : forall n m p, n ~= 0 -> (n | m * p) ->
 exists q r, n == q*r /\ (q | m) /\ (r | p).
Proof. Show. Fail (abduce 3). Admitted.

(** TODO : more about rel_prime (i.e. gcd == 1), about prime ... *)

End ZGcdProp.
