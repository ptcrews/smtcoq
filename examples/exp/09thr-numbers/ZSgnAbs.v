(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Properties of [abs] and [sgn] *)

Require Import ZMulOrder.
Add Rec LoadPath "/home/arjun/Desktop/smtcoq/abduction-arjunvish-smtcoq/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
(** Since we already have [max], we could have defined [abs]. *)

Module GenericAbs (Import Z : ZAxiomsMiniSig')
                  (Import ZP : ZMulOrderProp Z) <: HasAbs Z.
 Definition abs n := max n (-n).
 Lemma abs_eq : forall n, 0<=n -> abs n == n.
 Proof. Show. Fail (cvc5_abduct 3). Admitted.
 Lemma abs_neq : forall n, n<=0 -> abs n == -n.
 Proof. Show. Fail (cvc5_abduct 3). Admitted.
End GenericAbs.

(** We can deduce a [sgn] function from a [compare] function *)

Module Type ZDecAxiomsSig := ZAxiomsMiniSig <+ HasCompare.
Module Type ZDecAxiomsSig' := ZAxiomsMiniSig' <+ HasCompare.

Module Type GenericSgn (Import Z : ZDecAxiomsSig')
                       (Import ZP : ZMulOrderProp Z) <: HasSgn Z.
 Definition sgn n :=
  match compare 0 n with Eq => 0 | Lt => 1 | Gt => -1 end.
 Lemma sgn_null n : n==0 -> sgn n == 0.
 Proof. Show. Fail (cvc5_abduct 3). Admitted.
 Lemma sgn_pos n : 0<n -> sgn n == 1.
 Proof. Show. Fail (cvc5_abduct 3). Admitted.
 Lemma sgn_neg n : n<0 -> sgn n == -1.
 Proof. Show. Fail (cvc5_abduct 3). Admitted.
End GenericSgn.


(** Derived properties of [abs] and [sgn] *)

Module Type ZSgnAbsProp (Import Z : ZAxiomsSig')
                        (Import ZP : ZMulOrderProp Z).

Ltac destruct_max n :=
 destruct (le_ge_cases 0 n);
  [rewrite (abs_eq n) by auto | rewrite (abs_neq n) by auto].

Instance abs_wd : Proper (eq==>eq) abs.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma abs_max : forall n, abs n == max n (-n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma abs_neq' : forall n, 0<=-n -> abs n == -n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma abs_nonneg : forall n, 0 <= abs n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma abs_eq_iff : forall n, abs n == n <-> 0<=n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma abs_neq_iff : forall n, abs n == -n <-> n<=0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma abs_opp : forall n, abs (-n) == abs n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma abs_0 : abs 0 == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma abs_0_iff : forall n, abs n == 0 <-> n==0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma abs_pos : forall n, 0 < abs n <-> n~=0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma abs_eq_or_opp : forall n, abs n == n \/ abs n == -n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma abs_or_opp_abs : forall n, n == abs n \/ n == - abs n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma abs_involutive : forall n, abs (abs n) == abs n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma abs_spec : forall n,
  (0 <= n /\ abs n == n) \/ (n < 0 /\ abs n == -n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma abs_case_strong :
  forall (P:t->Prop) n, Proper (eq==>iff) P ->
    (0<=n -> P n) -> (n<=0 -> P (-n)) -> P (abs n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma abs_case : forall (P:t->Prop) n, Proper (eq==>iff) P ->
 P n -> P (-n) -> P (abs n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma abs_eq_cases : forall n m, abs n == abs m -> n == m \/ n == - m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma abs_lt : forall a b, abs a < b <-> -b < a < b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma abs_le : forall a b, abs a <= b <-> -b <= a <= b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Triangular inequality *)

Lemma abs_triangle : forall n m, abs (n + m) <= abs n + abs m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma abs_sub_triangle : forall n m, abs n - abs m <= abs (n-m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Absolute value and multiplication *)

Lemma abs_mul : forall n m, abs (n * m) == abs n * abs m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma abs_square : forall n, abs n * abs n == n * n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Some results about the sign function. *)

Ltac destruct_sgn n :=
 let LT := fresh "LT" in
 let EQ := fresh "EQ" in
 let GT := fresh "GT" in
 destruct (lt_trichotomy 0 n) as [LT|[EQ|GT]];
 [rewrite (sgn_pos n) by auto|
  rewrite (sgn_null n) by auto with relations|
  rewrite (sgn_neg n) by auto].

Instance sgn_wd : Proper (eq==>eq) sgn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgn_spec : forall n,
  0 < n /\ sgn n == 1 \/
  0 == n /\ sgn n == 0 \/
  0 > n /\ sgn n == -1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgn_0 : sgn 0 == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgn_pos_iff : forall n, sgn n == 1 <-> 0<n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgn_null_iff : forall n, sgn n == 0 <-> n==0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgn_neg_iff : forall n, sgn n == -1 <-> n<0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgn_opp : forall n, sgn (-n) == - sgn n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgn_nonneg : forall n, 0 <= sgn n <-> 0 <= n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgn_nonpos : forall n, sgn n <= 0 <-> n <= 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgn_mul : forall n m, sgn (n*m) == sgn n * sgn m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgn_abs : forall n, n * sgn n == abs n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma abs_sgn : forall n, abs n * sgn n == n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgn_sgn : forall x, sgn (sgn x) == sgn x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End ZSgnAbsProp.


