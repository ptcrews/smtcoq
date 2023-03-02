(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Bool ZMulOrder NZParity.
Require Import SMTCoq.SMTCoq.
(** Some more properties of [even] and [odd]. *)

Module Type ZParityProp (Import Z : ZAxiomsSig')
                        (Import ZP : ZMulOrderProp Z).

Include NZParityProp Z Z ZP.

Lemma odd_pred : forall n, odd (P n) = even n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma even_pred : forall n, even (P n) = odd n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma even_opp : forall n, even (-n) = even n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma odd_opp : forall n, odd (-n) = odd n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma even_sub : forall n m, even (n-m) = Bool.eqb (even n) (even m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma odd_sub : forall n m, odd (n-m) = xorb (odd n) (odd m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End ZParityProp.
