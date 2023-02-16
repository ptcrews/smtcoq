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

Require Import BinPos PeanoNat.
Add Rec LoadPath "/home/arjun/Desktop/smtcoq/abduction-arjunvish-smtcoq/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
(** Properties of the injection from binary positive numbers
    to Peano natural numbers *)

(** Original development by Pierre Crégut, CNET, Lannion, France *)

Local Open Scope positive_scope.
Local Open Scope nat_scope.

Module Pos2Nat.
 Import Pos.

(** [Pos.to_nat] is a morphism for successor, addition, multiplication *)

Lemma inj_succ p : to_nat (succ p) = S (to_nat p).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem inj_add p q : to_nat (p + q) = to_nat p + to_nat q.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem inj_mul p q : to_nat (p * q) = to_nat p * to_nat q.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Mapping of xH, xO and xI through [Pos.to_nat] *)

Lemma inj_1 : to_nat 1 = 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_xO p : to_nat (xO p) = 2 * to_nat p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_xI p : to_nat (xI p) = S (2 * to_nat p).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** [Pos.to_nat] maps to the strictly positive subset of [nat] *)

Lemma is_succ p : exists n, to_nat p = S n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** [Pos.to_nat] is strictly positive *)

Lemma is_pos p : 0 < to_nat p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** [Pos.to_nat] is a bijection between [positive] and
    non-zero [nat], with [Pos.of_nat] as reciprocal.
    See [Nat2Pos.id] below for the dual equation. *)

Theorem id p : of_nat (to_nat p) = p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** [Pos.to_nat] is hence injective *)

Lemma inj p q : to_nat p = to_nat q -> p = q.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_iff p q : to_nat p = to_nat q <-> p = q.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** [Pos.to_nat] is a morphism for comparison *)

Lemma inj_compare p q : (p ?= q)%positive = (to_nat p ?= to_nat q).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** [Pos.to_nat] is a morphism for [lt], [le], etc *)

Lemma inj_lt p q : (p < q)%positive <-> to_nat p < to_nat q.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_le p q : (p <= q)%positive <-> to_nat p <= to_nat q.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_gt p q : (p > q)%positive <-> to_nat p > to_nat q.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_ge p q : (p >= q)%positive <-> to_nat p >= to_nat q.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** [Pos.to_nat] is a morphism for subtraction *)

Theorem inj_sub p q : (q < p)%positive ->
 to_nat (p - q) = to_nat p - to_nat q.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem inj_sub_max p q :
 to_nat (p - q) = Nat.max 1 (to_nat p - to_nat q).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem inj_pred p : (1 < p)%positive ->
 to_nat (pred p) = Nat.pred (to_nat p).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem inj_pred_max p :
 to_nat (pred p) = Nat.max 1 (Peano.pred (to_nat p)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** [Pos.to_nat] and other operations *)

Lemma inj_min p q :
 to_nat (min p q) = Nat.min (to_nat p) (to_nat q).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_max p q :
 to_nat (max p q) = Nat.max (to_nat p) (to_nat q).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem inj_iter p {A} (f:A->A) (x:A) :
    Pos.iter f x p = nat_rect _ x (fun _ => f) (to_nat p).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End Pos2Nat.

Module Nat2Pos.

(** [Pos.of_nat] is a bijection between non-zero [nat] and
    [positive], with [Pos.to_nat] as reciprocal.
    See [Pos2Nat.id] above for the dual equation. *)

Theorem id (n:nat) : n<>0 -> Pos.to_nat (Pos.of_nat n) = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem id_max (n:nat) : Pos.to_nat (Pos.of_nat n) = max 1 n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** [Pos.of_nat] is hence injective for non-zero numbers *)

Lemma inj (n m : nat) : n<>0 -> m<>0 -> Pos.of_nat n = Pos.of_nat m -> n = m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_iff (n m : nat) : n<>0 -> m<>0 ->
 (Pos.of_nat n = Pos.of_nat m <-> n = m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Usual operations are morphisms with respect to [Pos.of_nat]
    for non-zero numbers. *)

Lemma inj_succ (n:nat) : n<>0 -> Pos.of_nat (S n) = Pos.succ (Pos.of_nat n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_pred (n:nat) : Pos.of_nat (pred n) = Pos.pred (Pos.of_nat n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_add (n m : nat) : n<>0 -> m<>0 ->
 Pos.of_nat (n+m) = (Pos.of_nat n + Pos.of_nat m)%positive.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_mul (n m : nat) : n<>0 -> m<>0 ->
 Pos.of_nat (n*m) = (Pos.of_nat n * Pos.of_nat m)%positive.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_compare (n m : nat) : n<>0 -> m<>0 ->
 (n ?= m) = (Pos.of_nat n ?= Pos.of_nat m)%positive.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_sub (n m : nat) : m<>0 ->
 Pos.of_nat (n-m) = (Pos.of_nat n - Pos.of_nat m)%positive.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_min (n m : nat) :
 Pos.of_nat (min n m) = Pos.min (Pos.of_nat n) (Pos.of_nat m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_max (n m : nat) :
 Pos.of_nat (max n m) = Pos.max (Pos.of_nat n) (Pos.of_nat m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End Nat2Pos.

(**********************************************************************)
(** Properties of the shifted injection from Peano natural numbers
    to binary positive numbers *)

Module Pos2SuccNat.

(** Composition of [Pos.to_nat] and [Pos.of_succ_nat] is successor
    on [positive] *)

Theorem id_succ p : Pos.of_succ_nat (Pos.to_nat p) = Pos.succ p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Composition of [Pos.to_nat], [Pos.of_succ_nat] and [Pos.pred]
    is identity on [positive] *)

Theorem pred_id p : Pos.pred (Pos.of_succ_nat (Pos.to_nat p)) = p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End Pos2SuccNat.

Module SuccNat2Pos.

(** Composition of [Pos.of_succ_nat] and [Pos.to_nat] is successor on [nat] *)

Theorem id_succ (n:nat) : Pos.to_nat (Pos.of_succ_nat n) = S n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem pred_id (n:nat) : pred (Pos.to_nat (Pos.of_succ_nat n)) = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** [Pos.of_succ_nat] is hence injective *)

Lemma inj (n m : nat) : Pos.of_succ_nat n = Pos.of_succ_nat m -> n = m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_iff (n m : nat) : Pos.of_succ_nat n = Pos.of_succ_nat m <-> n = m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Another formulation *)

Theorem inv n p : Pos.to_nat p = S n -> Pos.of_succ_nat n = p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Successor and comparison are morphisms with respect to
    [Pos.of_succ_nat] *)

Lemma inj_succ n : Pos.of_succ_nat (S n) = Pos.succ (Pos.of_succ_nat n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_compare n m :
 (n ?= m) = (Pos.of_succ_nat n ?= Pos.of_succ_nat m)%positive.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Other operations, for instance [Pos.add] and [plus] aren't
    directly related this way (we would need to compensate for
    the successor hidden in [Pos.of_succ_nat] *)

End SuccNat2Pos.

(** For compatibility, old names and old-style lemmas *)

Notation Psucc_S := Pos2Nat.inj_succ (only parsing).
Notation Pplus_plus := Pos2Nat.inj_add (only parsing).
Notation Pmult_mult := Pos2Nat.inj_mul (only parsing).
Notation Pcompare_nat_compare := Pos2Nat.inj_compare (only parsing).
Notation nat_of_P_xH := Pos2Nat.inj_1 (only parsing).
Notation nat_of_P_xO := Pos2Nat.inj_xO (only parsing).
Notation nat_of_P_xI := Pos2Nat.inj_xI (only parsing).
Notation nat_of_P_is_S := Pos2Nat.is_succ (only parsing).
Notation nat_of_P_pos := Pos2Nat.is_pos (only parsing).
Notation nat_of_P_inj_iff := Pos2Nat.inj_iff (only parsing).
Notation nat_of_P_inj := Pos2Nat.inj (only parsing).
Notation Plt_lt := Pos2Nat.inj_lt (only parsing).
Notation Pgt_gt := Pos2Nat.inj_gt (only parsing).
Notation Ple_le := Pos2Nat.inj_le (only parsing).
Notation Pge_ge := Pos2Nat.inj_ge (only parsing).
Notation Pminus_minus := Pos2Nat.inj_sub (only parsing).
Notation iter_nat_of_P := @Pos2Nat.inj_iter (only parsing).

Notation nat_of_P_of_succ_nat := SuccNat2Pos.id_succ (only parsing).
Notation P_of_succ_nat_of_P := Pos2SuccNat.id_succ (only parsing).

Notation nat_of_P_succ_morphism := Pos2Nat.inj_succ (only parsing).
Notation nat_of_P_plus_morphism := Pos2Nat.inj_add (only parsing).
Notation nat_of_P_mult_morphism := Pos2Nat.inj_mul (only parsing).
Notation nat_of_P_compare_morphism := Pos2Nat.inj_compare (only parsing).
Notation lt_O_nat_of_P := Pos2Nat.is_pos (only parsing).
Notation ZL4 := Pos2Nat.is_succ (only parsing).
Notation nat_of_P_o_P_of_succ_nat_eq_succ := SuccNat2Pos.id_succ (only parsing).
Notation P_of_succ_nat_o_nat_of_P_eq_succ := Pos2SuccNat.id_succ (only parsing).
Notation pred_o_P_of_succ_nat_o_nat_of_P_eq_id := Pos2SuccNat.pred_id (only parsing).

Lemma nat_of_P_minus_morphism p q :
 Pos.compare_cont Eq p q = Gt ->
  Pos.to_nat (p - q) = Pos.to_nat p - Pos.to_nat q.
Proof (fun H => Pos2Nat.inj_sub p q (Pos.gt_lt _ _ H)).

Lemma nat_of_P_lt_Lt_compare_morphism p q :
 Pos.compare_cont Eq p q = Lt -> Pos.to_nat p < Pos.to_nat q.
Proof (proj1 (Pos2Nat.inj_lt p q)).

Lemma nat_of_P_gt_Gt_compare_morphism p q :
 Pos.compare_cont Eq p q = Gt -> Pos.to_nat p > Pos.to_nat q.
Proof (proj1 (Pos2Nat.inj_gt p q)).

Lemma nat_of_P_lt_Lt_compare_complement_morphism p q :
 Pos.to_nat p < Pos.to_nat q -> Pos.compare_cont Eq p q = Lt.
Proof (proj2 (Pos2Nat.inj_lt p q)).

Definition nat_of_P_gt_Gt_compare_complement_morphism p q :
 Pos.to_nat p > Pos.to_nat q -> Pos.compare_cont Eq p q = Gt.
Proof (proj2 (Pos2Nat.inj_gt p q)).

(** Old intermediate results about [Pmult_nat] *)

Section ObsoletePmultNat.

Lemma Pmult_nat_mult : forall p n,
 Pmult_nat p n = Pos.to_nat p * n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Pmult_nat_succ_morphism :
 forall p n, Pmult_nat (Pos.succ p) n = n + Pmult_nat p n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Pmult_nat_l_plus_morphism :
 forall p q n, Pmult_nat (p + q) n = Pmult_nat p n + Pmult_nat q n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Pmult_nat_plus_carry_morphism :
 forall p q n, Pmult_nat (Pos.add_carry p q) n = n + Pmult_nat (p + q) n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Pmult_nat_r_plus_morphism :
 forall p n, Pmult_nat p (n + n) = Pmult_nat p n + Pmult_nat p n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ZL6 : forall p, Pmult_nat p 2 = Pos.to_nat p + Pos.to_nat p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma le_Pmult_nat : forall p n, n <= Pmult_nat p n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End ObsoletePmultNat.
