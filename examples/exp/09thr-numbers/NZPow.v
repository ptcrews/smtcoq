(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Power Function *)

Require Import NZAxioms NZMulOrder.
Require Import SMTCoq.SMTCoq.
(** Interface of a power function, then its specification on naturals *)

Module Type Pow (Import A : Typ).
 Parameters Inline pow : t -> t -> t.
End Pow.

Module Type PowNotation (A : Typ)(Import B : Pow A).
 Infix "^" := pow.
End PowNotation.

Module Type Pow' (A : Typ) := Pow A <+ PowNotation A.

Module Type NZPowSpec (Import A : NZOrdAxiomsSig')(Import B : Pow' A).
 Declare Instance pow_wd : Proper (eq==>eq==>eq) pow.
 Axiom pow_0_r : forall a, a^0 == 1.
 Axiom pow_succ_r : forall a b, 0<=b -> a^(succ b) == a * a^b.
 Axiom pow_neg_r : forall a b, b<0 -> a^b == 0.
End NZPowSpec.

(** The above [pow_neg_r] specification is useless (and trivially
   provable) for N. Having it here already allows deriving
   some slightly more general statements. *)

Module Type NZPow (A : NZOrdAxiomsSig) := Pow A <+ NZPowSpec A.
Module Type NZPow' (A : NZOrdAxiomsSig) := Pow' A <+ NZPowSpec A.

(** Derived properties of power *)

Module Type NZPowProp
 (Import A : NZOrdAxiomsSig')
 (Import B : NZPow' A)
 (Import C : NZMulOrderProp A).

Hint Rewrite pow_0_r pow_succ_r : nz.

(** Power and basic constants *)

Lemma pow_0_l : forall a, 0<a -> 0^a == 0.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pow_0_l' : forall a, a~=0 -> 0^a == 0.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pow_1_r : forall a, a^1 == a.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pow_1_l : forall a, 0<=a -> 1^a == 1.
Proof. Show. Fail (abduce 3). Admitted.

Hint Rewrite pow_1_r pow_1_l : nz.

Lemma pow_2_r : forall a, a^2 == a*a.
Proof. Show. Fail (abduce 3). Admitted.

Hint Rewrite pow_2_r : nz.

(** Power and nullity *)

Lemma pow_eq_0 : forall a b, 0<=b -> a^b == 0 -> a == 0.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pow_nonzero : forall a b, a~=0 -> 0<=b -> a^b ~= 0.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pow_eq_0_iff : forall a b, a^b == 0 <-> b<0 \/ (0<b /\ a==0).
Proof. Show. Fail (abduce 3). Admitted.

(** Power and addition, multiplication *)

Lemma pow_add_r : forall a b c, 0<=b -> 0<=c ->
  a^(b + c) == a^b * a^c.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pow_mul_l : forall a b c,
  (a*b)^c == a^c * b^c.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pow_mul_r : forall a b c, 0<=b -> 0<=c ->
  a^(b*c) == (a^b)^c.
Proof. Show. Fail (abduce 3). Admitted.

(** Positivity *)

Lemma pow_nonneg : forall a b, 0<=a -> 0<=a^b.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pow_pos_nonneg : forall a b, 0<a -> 0<=b -> 0<a^b.
Proof. Show. Fail (abduce 3). Admitted.

(** Monotonicity *)

Lemma pow_lt_mono_l : forall a b c, 0<c -> 0<=a<b -> a^c < b^c.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pow_le_mono_l : forall a b c, 0<=a<=b -> a^c <= b^c.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pow_gt_1 : forall a b, 1<a -> (0<b <-> 1<a^b).
Proof. Show. Fail (abduce 3). Admitted.

Lemma pow_lt_mono_r : forall a b c, 1<a -> 0<=c -> b<c -> a^b < a^c.
Proof. Show. Fail (abduce 3). Admitted.

(** NB: since 0^0 > 0^1, the following result isn't valid with a=0 *)

Lemma pow_le_mono_r : forall a b c, 0<a -> b<=c -> a^b <= a^c.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pow_le_mono : forall a b c d, 0<a<=c -> b<=d ->
 a^b <= c^d.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pow_lt_mono : forall a b c d, 0<a<c -> 0<b<d ->
 a^b < c^d.
Proof. Show. Fail (abduce 3). Admitted.

(** Injectivity *)

Lemma pow_inj_l : forall a b c, 0<=a -> 0<=b -> 0<c ->
 a^c == b^c -> a == b.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pow_inj_r : forall a b c, 1<a -> 0<=b -> 0<=c ->
 a^b == a^c -> b == c.
Proof. Show. Fail (abduce 3). Admitted.

(** Monotonicity results, both ways *)

Lemma pow_lt_mono_l_iff : forall a b c, 0<=a -> 0<=b -> 0<c ->
  (a<b <-> a^c < b^c).
Proof. Show. Fail (abduce 3). Admitted.

Lemma pow_le_mono_l_iff : forall a b c, 0<=a -> 0<=b -> 0<c ->
  (a<=b <-> a^c <= b^c).
Proof. Show. Fail (abduce 3). Admitted.

Lemma pow_lt_mono_r_iff : forall a b c, 1<a -> 0<=c ->
  (b<c <-> a^b < a^c).
Proof. Show. Fail (abduce 3). Admitted.

Lemma pow_le_mono_r_iff : forall a b c, 1<a -> 0<=c ->
  (b<=c <-> a^b <= a^c).
Proof. Show. Fail (abduce 3). Admitted.

(** For any a>1, the a^x function is above the identity function *)

Lemma pow_gt_lin_r : forall a b, 1<a -> 0<=b -> b < a^b.
Proof. Show. Fail (abduce 3). Admitted.

(** Someday, we should say something about the full Newton formula.
    In the meantime, we can at least provide some inequalities about
    (a+b)^c.
*)

Lemma pow_add_lower : forall a b c, 0<=a -> 0<=b -> 0<c ->
  a^c + b^c <= (a+b)^c.
Proof. Show. Fail (abduce 3). Admitted.

(** This upper bound can also be seen as a convexity proof for x^c :
    image of (a+b)/2 is below the middle of the images of a and b
*)

Lemma pow_add_upper : forall a b c, 0<=a -> 0<=b -> 0<c ->
  (a+b)^c <= 2^(pred c) * (a^c + b^c).
Proof. Show. Fail (abduce 3). Admitted.

End NZPowProp.
