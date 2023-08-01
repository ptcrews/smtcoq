(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Properties of the power function *)

Require Import Bool ZAxioms ZMulOrder ZParity ZSgnAbs NZPow.
Add Rec LoadPath "/home/arjun/Desktop/smtcoq/abduction-arjunvish-smtcoq/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Module Type ZPowProp
 (Import A : ZAxiomsSig')
 (Import B : ZMulOrderProp A)
 (Import C : ZParityProp A B)
 (Import D : ZSgnAbsProp A B).

 Include NZPowProp A A B.

(** A particular case of [pow_add_r], with no precondition *)

Lemma pow_twice_r a b : a^(2*b) == a^b * a^b.
Proof. Show. Fail (abduce 3). Admitted.

(** Parity of power *)

Lemma even_pow : forall a b, 0<b -> even (a^b) = even a.
Proof. Show. Fail (abduce 3). Admitted.

Lemma odd_pow : forall a b, 0<b -> odd (a^b) = odd a.
Proof. Show. Fail (abduce 3). Admitted.

(** Properties of power of negative numbers *)

Lemma pow_opp_even : forall a b, Even b -> (-a)^b == a^b.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pow_opp_odd : forall a b, Odd b -> (-a)^b == -(a^b).
Proof. Show. Fail (abduce 3). Admitted.

Lemma pow_even_abs : forall a b, Even b -> a^b == (abs a)^b.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pow_even_nonneg : forall a b, Even b -> 0 <= a^b.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pow_odd_abs_sgn : forall a b, Odd b -> a^b == sgn a * (abs a)^b.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pow_odd_sgn : forall a b, 0<=b -> Odd b -> sgn (a^b) == sgn a.
Proof. Show. Fail (abduce 3). Admitted.

Lemma abs_pow : forall a b, abs (a^b) == (abs a)^b.
Proof. Show. Fail (abduce 3). Admitted.

End ZPowProp.
