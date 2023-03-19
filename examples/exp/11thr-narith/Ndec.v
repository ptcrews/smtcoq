(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Bool.
Require Import Sumbool.
Require Import Arith.
Require Import BinPos.
Require Import BinNat.
Require Import Pnat.
Require Import Nnat.
Require Import Ndigits.
Require Import SMTCoq.SMTCoq.

Local Open Scope N_scope.

(** Obsolete results about boolean comparisons over [N],
    kept for compatibility with IntMap and SMC. *)

Notation Peqb_correct := Pos.eqb_refl (only parsing).
Notation Neqb_correct := N.eqb_refl (only parsing).
Notation Neqb_comm := N.eqb_sym (only parsing).

Lemma Peqb_complete p p' : Pos.eqb p p' = true -> p = p'.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Peqb_Pcompare p p' : Pos.eqb p p' = true -> Pos.compare p p' = Eq.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Pcompare_Peqb p p' : Pos.compare p p' = Eq -> Pos.eqb p p' = true.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Neqb_Ncompare n n' : N.eqb n n' = true -> N.compare n n' = Eq.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Ncompare_Neqb n n' : N.compare n n' = Eq -> N.eqb n n' = true.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Neqb_complete n n' : N.eqb n n' = true -> n = n'.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Nxor_eq_true n n' : N.lxor n n' = 0 -> N.eqb n n' = true.
Proof. Show. Fail (abduce 3). Admitted.

Ltac eqb2eq := rewrite <- ?not_true_iff_false in *; rewrite ?N.eqb_eq in *.

Lemma Nxor_eq_false n n' p :
  N.lxor n n' = N.pos p -> N.eqb n n' = false.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Nodd_not_double a :
  Nodd a -> forall a0, N.eqb (N.double a0) a = false.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Nnot_div2_not_double a a0 :
  N.eqb (N.div2 a) a0 = false -> N.eqb a (N.double a0) = false.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Neven_not_double_plus_one a :
  Neven a -> forall a0, N.eqb (N.succ_double a0) a = false.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Nnot_div2_not_double_plus_one a a0 :
  N.eqb (N.div2 a) a0 = false -> N.eqb (N.succ_double a0) a = false.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Nbit0_neq a a' :
  N.odd a = false -> N.odd a' = true -> N.eqb a a' = false.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Ndiv2_eq a a' :
  N.eqb a a' = true -> N.eqb (N.div2 a) (N.div2 a') = true.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Ndiv2_neq a a' :
  N.eqb (N.div2 a) (N.div2 a') = false -> N.eqb a a' = false.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Ndiv2_bit_eq a a' :
  N.odd a = N.odd a' -> N.div2 a = N.div2 a' -> a = a'.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Ndiv2_bit_neq a a' :
  N.eqb a a' = false ->
   N.odd a = N.odd a' -> N.eqb (N.div2 a) (N.div2 a') = false.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Nneq_elim a a' :
   N.eqb a a' = false ->
   N.odd a = negb (N.odd a') \/
   N.eqb (N.div2 a) (N.div2 a') = false.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Ndouble_or_double_plus_un a :
   {a0 : N | a = N.double a0} + {a1 : N | a = N.succ_double a1}.
Proof. Show. Fail (abduce 3). Admitted.

(** An inefficient boolean order on [N]. Please use [N.leb] instead now. *)

Definition Nleb (a b:N) := Nat.leb (N.to_nat a) (N.to_nat b).

Lemma Nleb_alt a b : Nleb a b = N.leb a b.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Nleb_Nle a b : Nleb a b = true <-> a <= b.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Nleb_refl a : Nleb a a = true.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Nleb_antisym a b : Nleb a b = true -> Nleb b a = true -> a = b.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Nleb_trans a b c : Nleb a b = true -> Nleb b c = true -> Nleb a c = true.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Nleb_ltb_trans a b c :
  Nleb a b = true -> Nleb c b = false -> Nleb c a = false.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Nltb_leb_trans a b c :
  Nleb b a = false -> Nleb b c = true -> Nleb c a = false.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Nltb_trans a b c :
  Nleb b a = false -> Nleb c b = false -> Nleb c a = false.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Nltb_leb_weak a b : Nleb b a = false -> Nleb a b = true.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Nleb_double_mono a b :
  Nleb a b = true -> Nleb (N.double a) (N.double b) = true.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Nleb_double_plus_one_mono a b :
  Nleb a b = true ->
   Nleb (N.succ_double a) (N.succ_double b) = true.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Nleb_double_mono_conv a b :
  Nleb (N.double a) (N.double b) = true -> Nleb a b = true.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Nleb_double_plus_one_mono_conv a b :
  Nleb (N.succ_double a) (N.succ_double b) = true ->
   Nleb a b = true.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Nltb_double_mono a b :
   Nleb a b = false -> Nleb (N.double a) (N.double b) = false.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Nltb_double_plus_one_mono a b :
  Nleb a b = false ->
   Nleb (N.succ_double a) (N.succ_double b) = false.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Nltb_double_mono_conv a b :
  Nleb (N.double a) (N.double b) = false -> Nleb a b = false.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Nltb_double_plus_one_mono_conv a b :
  Nleb (N.succ_double a) (N.succ_double b) = false ->
   Nleb a b = false.
Proof. Show. Fail (abduce 3). Admitted.

(* Nleb and N.compare *)

(* NB: No need to prove that Nleb a b = true <-> N.compare a b <> Gt,
   this statement is in fact Nleb_Nle! *)

Lemma Nltb_Ncompare a b : Nleb a b = false <-> N.compare a b = Gt.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Ncompare_Gt_Nltb a b : N.compare a b = Gt -> Nleb a b = false.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Ncompare_Lt_Nltb a b : N.compare a b = Lt -> Nleb b a = false.
Proof. Show. Fail (abduce 3). Admitted.

(* Old results about [N.min] *)

Notation Nmin_choice := N.min_dec (only parsing).

Lemma Nmin_le_1 a b : Nleb (N.min a b) a = true.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Nmin_le_2 a b : Nleb (N.min a b) b = true.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Nmin_le_3 a b c : Nleb a (N.min b c) = true -> Nleb a b = true.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Nmin_le_4 a b c : Nleb a (N.min b c) = true -> Nleb a c = true.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Nmin_le_5 a b c :
   Nleb a b = true -> Nleb a c = true -> Nleb a (N.min b c) = true.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Nmin_lt_3 a b c : Nleb (N.min b c) a = false -> Nleb b a = false.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Nmin_lt_4 a b c : Nleb (N.min b c) a = false -> Nleb c a = false.
Proof. Show. Fail (abduce 3). Admitted.
