(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import BinPos BinNat PeanoNat Pnat.

(** * Conversions from [N] to [nat] *)
Add Rec LoadPath "/home/arjun/Desktop/smtcoq/abduction-arjunvish-smtcoq/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Module N2Nat.

(** [N.to_nat] is a bijection between [N] and [nat],
    with [Pos.of_nat] as reciprocal.
    See [Nat2N.id] below for the dual equation. *)

Lemma id a : N.of_nat (N.to_nat a) = a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** [N.to_nat] is hence injective *)

Lemma inj a a' : N.to_nat a = N.to_nat a' -> a = a'.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_iff a a' : N.to_nat a = N.to_nat a' <-> a = a'.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Interaction of this translation and usual operations. *)

Lemma inj_double a : N.to_nat (N.double a) = 2*(N.to_nat a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_succ_double a : N.to_nat (N.succ_double a) = S (2*(N.to_nat a)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_succ a : N.to_nat (N.succ a) = S (N.to_nat a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_add a a' :
  N.to_nat (a + a') = N.to_nat a + N.to_nat a'.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_mul a a' :
  N.to_nat (a * a') = N.to_nat a * N.to_nat a'.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_sub a a' :
  N.to_nat (a - a') = N.to_nat a - N.to_nat a'.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_pred a : N.to_nat (N.pred a) = Nat.pred (N.to_nat a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_div2 a : N.to_nat (N.div2 a) = Nat.div2 (N.to_nat a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_compare a a' :
 (a ?= a')%N = (N.to_nat a ?= N.to_nat a').
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_max a a' :
  N.to_nat (N.max a a') = Nat.max (N.to_nat a) (N.to_nat a').
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_min a a' :
  N.to_nat (N.min a a') = Nat.min (N.to_nat a) (N.to_nat a').
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_iter a {A} (f:A->A) (x:A) :
  N.iter a f x = Nat.iter (N.to_nat a) f x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End N2Nat.

Hint Rewrite N2Nat.inj_double N2Nat.inj_succ_double
 N2Nat.inj_succ N2Nat.inj_add N2Nat.inj_mul N2Nat.inj_sub
 N2Nat.inj_pred N2Nat.inj_div2 N2Nat.inj_max N2Nat.inj_min
 N2Nat.id
 : Nnat.


(** * Conversions from [nat] to [N] *)

Module Nat2N.

(** [N.of_nat] is an bijection between [nat] and [N],
    with [Pos.to_nat] as reciprocal.
    See [N2Nat.id] above for the dual equation. *)

Lemma id n : N.to_nat (N.of_nat n) = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Hint Rewrite id : Nnat.
Ltac nat2N := apply N2Nat.inj; now autorewrite with Nnat.

(** [N.of_nat] is hence injective *)

Lemma inj n n' : N.of_nat n = N.of_nat n' -> n = n'.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_iff n n' : N.of_nat n = N.of_nat n' <-> n = n'.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Interaction of this translation and usual operations. *)

Lemma inj_double n : N.of_nat (2*n) = N.double (N.of_nat n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_succ_double n : N.of_nat (S (2*n)) = N.succ_double (N.of_nat n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_succ n : N.of_nat (S n) = N.succ (N.of_nat n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_pred n : N.of_nat (Nat.pred n) = N.pred (N.of_nat n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_add n n' : N.of_nat (n+n') = (N.of_nat n + N.of_nat n')%N.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_sub n n' : N.of_nat (n-n') = (N.of_nat n - N.of_nat n')%N.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_mul n n' : N.of_nat (n*n') = (N.of_nat n * N.of_nat n')%N.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_div2 n : N.of_nat (Nat.div2 n) = N.div2 (N.of_nat n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_compare n n' :
  (n ?= n') = (N.of_nat n ?= N.of_nat n')%N.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_min n n' :
  N.of_nat (Nat.min n n') = N.min (N.of_nat n) (N.of_nat n').
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_max n n' :
  N.of_nat (Nat.max n n') = N.max (N.of_nat n) (N.of_nat n').
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_iter n {A} (f:A->A) (x:A) :
  Nat.iter n f x = N.iter (N.of_nat n) f x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End Nat2N.

Hint Rewrite Nat2N.id : Nnat.

(** Compatibility notations *)

Notation nat_of_N_inj := N2Nat.inj (only parsing).
Notation N_of_nat_of_N := N2Nat.id (only parsing).
Notation nat_of_Ndouble := N2Nat.inj_double (only parsing).
Notation nat_of_Ndouble_plus_one := N2Nat.inj_succ_double (only parsing).
Notation nat_of_Nsucc := N2Nat.inj_succ (only parsing).
Notation nat_of_Nplus := N2Nat.inj_add (only parsing).
Notation nat_of_Nmult := N2Nat.inj_mul (only parsing).
Notation nat_of_Nminus := N2Nat.inj_sub (only parsing).
Notation nat_of_Npred := N2Nat.inj_pred (only parsing).
Notation nat_of_Ndiv2 := N2Nat.inj_div2 (only parsing).
Notation nat_of_Ncompare := N2Nat.inj_compare (only parsing).
Notation nat_of_Nmax := N2Nat.inj_max (only parsing).
Notation nat_of_Nmin := N2Nat.inj_min (only parsing).

Notation nat_of_N_of_nat := Nat2N.id (only parsing).
Notation N_of_nat_inj := Nat2N.inj (only parsing).
Notation N_of_double := Nat2N.inj_double (only parsing).
Notation N_of_double_plus_one := Nat2N.inj_succ_double (only parsing).
Notation N_of_S := Nat2N.inj_succ (only parsing).
Notation N_of_pred := Nat2N.inj_pred (only parsing).
Notation N_of_plus := Nat2N.inj_add (only parsing).
Notation N_of_minus := Nat2N.inj_sub (only parsing).
Notation N_of_mult := Nat2N.inj_mul (only parsing).
Notation N_of_div2 := Nat2N.inj_div2 (only parsing).
Notation N_of_nat_compare := Nat2N.inj_compare (only parsing).
Notation N_of_min := Nat2N.inj_min (only parsing).
Notation N_of_max := Nat2N.inj_max (only parsing).
