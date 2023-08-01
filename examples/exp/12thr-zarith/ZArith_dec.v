(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Sumbool.

Require Import BinInt.
Require Import Zorder.
Require Import Zcompare.
Local Open Scope Z_scope.
Add Rec LoadPath "/home/arjun/Desktop/smtcoq/abduction-arjunvish-smtcoq/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
(* begin hide *)
(* Trivial, to deprecate? *)
Lemma Dcompare_inf : forall r:comparison, {r = Eq} + {r = Lt} + {r = Gt}.
Proof. Show. Fail (abduce 3). Admitted.
(* end hide *)

Lemma Zcompare_rect (P:Type) (n m:Z) :
  ((n ?= m) = Eq -> P) -> ((n ?= m) = Lt -> P) -> ((n ?= m) = Gt -> P) -> P.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zcompare_rec (P:Set) (n m:Z) :
  ((n ?= m) = Eq -> P) -> ((n ?= m) = Lt -> P) -> ((n ?= m) = Gt -> P) -> P.
Proof. Show. Fail (abduce 3). Admitted.

Section decidability.

  Variables x y : Z.

  (** * Decidability of order on binary integers *)

  Definition Z_lt_dec : {x < y} + {~ x < y}.
  Proof. Show. Fail (abduce 3). Admitted.

  Definition Z_le_dec : {x <= y} + {~ x <= y}.
  Proof. Show. Fail (abduce 3). Admitted.

  Definition Z_gt_dec : {x > y} + {~ x > y}.
  Proof. Show. Fail (abduce 3). Admitted.

  Definition Z_ge_dec : {x >= y} + {~ x >= y}.
  Proof. Show. Fail (abduce 3). Admitted.

  Definition Z_lt_ge_dec : {x < y} + {x >= y}.
  Proof. Show. Fail (abduce 3). Admitted.

  Lemma Z_lt_le_dec : {x < y} + {y <= x}.
  Proof. Show. Fail (abduce 3). Admitted.

  Definition Z_le_gt_dec : {x <= y} + {x > y}.
  Proof. Show. Fail (abduce 3). Admitted.

  Definition Z_gt_le_dec : {x > y} + {x <= y}.
  Proof. Show. Fail (abduce 3). Admitted.

  Definition Z_ge_lt_dec : {x >= y} + {x < y}.
  Proof. Show. Fail (abduce 3). Admitted.

  Definition Z_le_lt_eq_dec : x <= y -> {x < y} + {x = y}.
  Proof. Show. Fail (abduce 3). Admitted.

End decidability.

(** * Cotransitivity of order on binary integers *)

Lemma Zlt_cotrans : forall n m:Z, n < m -> forall p:Z, {n < p} + {p < m}.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zlt_cotrans_pos : forall n m:Z, 0 < n + m -> {0 < n} + {0 < m}.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zlt_cotrans_neg : forall n m:Z, n + m < 0 -> {n < 0} + {m < 0}.
Proof. Show. Fail (abduce 3). Admitted.

Lemma not_Zeq_inf : forall n m:Z, n <> m -> {n < m} + {m < n}.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Z_dec : forall n m:Z, {n < m} + {n > m} + {n = m}.
Proof. Show. Fail (abduce 3). Admitted.


Lemma Z_dec' : forall n m:Z, {n < m} + {m < n} + {n = m}.
Proof. Show. Fail (abduce 3). Admitted.

(* begin hide *)
(* To deprecate ? *)
Corollary Z_zerop : forall x:Z, {x = 0} + {x <> 0}.
Proof. Show. Fail (abduce 3). Admitted.

Corollary Z_notzerop : forall (x:Z), {x <> 0} + {x = 0}.
Proof (fun x => sumbool_not _ _ (Z_zerop x)).

Corollary Z_noteq_dec : forall (x y:Z), {x <> y} + {x = y}.
Proof (fun x y => sumbool_not _ _ (Z.eq_dec x y)).
(* end hide *)
