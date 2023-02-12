(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Greatest Common Divisor *)

Require Import NZAxioms NZMulOrder.
Add Rec LoadPath "/home/arjun/Desktop/smtcoq/abduction-arjunvish-smtcoq/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
(** Interface of a gcd function, then its specification on naturals *)

Module Type Gcd (Import A : Typ).
 Parameter Inline gcd : t -> t -> t.
End Gcd.

Module Type NZGcdSpec (A : NZOrdAxiomsSig')(B : Gcd A).
 Import A B.
 Definition divide n m := exists p, m == p*n.
 Local Notation "( n | m )" := (divide n m) (at level 0).
 Axiom gcd_divide_l : forall n m, (gcd n m | n).
 Axiom gcd_divide_r : forall n m, (gcd n m | m).
 Axiom gcd_greatest : forall n m p, (p | n) -> (p | m) -> (p | gcd n m).
 Axiom gcd_nonneg : forall n m, 0 <= gcd n m.
End NZGcdSpec.

Module Type DivideNotation (A:NZOrdAxiomsSig')(B:Gcd A)(C:NZGcdSpec A B).
 Import A B C.
 Notation "( n | m )" := (divide n m) (at level 0).
End DivideNotation.

Module Type NZGcd (A : NZOrdAxiomsSig) := Gcd A <+ NZGcdSpec A.
Module Type NZGcd' (A : NZOrdAxiomsSig) :=
 Gcd A <+ NZGcdSpec A <+ DivideNotation A.

(** Derived properties of gcd *)

Module NZGcdProp
 (Import A : NZOrdAxiomsSig')
 (Import B : NZGcd' A)
 (Import C : NZMulOrderProp A).

(** Results concerning divisibility*)

Instance divide_wd : Proper (eq==>eq==>iff) divide.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma divide_1_l : forall n, (1 | n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma divide_0_r : forall n, (n | 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma divide_0_l : forall n, (0 | n) -> n==0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma eq_mul_1_nonneg : forall n m,
 0<=n -> n*m == 1 -> n==1 /\ m==1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma eq_mul_1_nonneg' : forall n m,
 0<=m -> n*m == 1 -> n==1 /\ m==1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma divide_1_r_nonneg : forall n, 0<=n -> (n | 1) -> n==1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma divide_refl : forall n, (n | n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma divide_trans : forall n m p, (n | m) -> (m | p) -> (n | p).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Instance divide_reflexive : Reflexive divide | 5 := divide_refl.
Instance divide_transitive : Transitive divide | 5 := divide_trans.

(** Due to sign, no general antisymmetry result *)

Lemma divide_antisym_nonneg : forall n m,
 0<=n -> 0<=m -> (n | m) -> (m | n) -> n == m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mul_divide_mono_l : forall n m p, (n | m) -> (p * n | p * m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mul_divide_mono_r : forall n m p, (n | m) -> (n * p | m * p).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mul_divide_cancel_l : forall n m p, p ~= 0 ->
 ((p * n | p * m) <-> (n | m)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mul_divide_cancel_r : forall n m p, p ~= 0 ->
 ((n * p | m * p) <-> (n | m)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma divide_add_r : forall n m p, (n | m) -> (n | p) -> (n | m + p).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma divide_mul_l : forall n m p, (n | m) -> (n | m * p).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma divide_mul_r : forall n m p, (n | p) -> (n | m * p).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma divide_factor_l : forall n m, (n | n * m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma divide_factor_r : forall n m, (n | m * n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma divide_pos_le : forall n m, 0 < m -> (n | m) -> n <= m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Basic properties of gcd *)

Lemma gcd_unique : forall n m p,
 0<=p -> (p|n) -> (p|m) ->
 (forall q, (q|n) -> (q|m) -> (q|p)) ->
 gcd n m == p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Instance gcd_wd : Proper (eq==>eq==>eq) gcd.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gcd_divide_iff : forall n m p,
  (p | gcd n m) <-> (p | n) /\ (p | m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gcd_unique_alt : forall n m p, 0<=p ->
 (forall q, (q|p) <-> (q|n) /\ (q|m)) ->
 gcd n m == p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gcd_comm : forall n m, gcd n m == gcd m n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gcd_assoc : forall n m p, gcd n (gcd m p) == gcd (gcd n m) p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gcd_0_l_nonneg : forall n, 0<=n -> gcd 0 n == n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gcd_0_r_nonneg : forall n, 0<=n -> gcd n 0 == n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gcd_1_l : forall n, gcd 1 n == 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gcd_1_r : forall n, gcd n 1 == 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gcd_diag_nonneg : forall n, 0<=n -> gcd n n == n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gcd_eq_0_l : forall n m, gcd n m == 0 -> n == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gcd_eq_0_r : forall n m, gcd n m == 0 -> m == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gcd_eq_0 : forall n m, gcd n m == 0 <-> n == 0 /\ m == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gcd_mul_diag_l : forall n m, 0<=n -> gcd n (n*m) == n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma divide_gcd_iff : forall n m, 0<=n -> ((n|m) <-> gcd n m == n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End NZGcdProp.
