(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * DecimalZ

    Proofs that conversions between decimal numbers and [Z]
    are bijections. *)

Require Import Decimal DecimalFacts DecimalPos DecimalN ZArith.
Require Import SMTCoq.SMTCoq.
Lemma of_to (z:Z) : Z.of_int (Z.to_int z) = z.
Proof. Show. Fail (abduce 3). Admitted.

Lemma to_of (d:int) : Z.to_int (Z.of_int d) = norm d.
Proof. Show. Fail (abduce 3). Admitted.

(** Some consequences *)

Lemma to_int_inj n n' : Z.to_int n = Z.to_int n' -> n = n'.
Proof. Show. Fail (abduce 3). Admitted.

Lemma to_int_surj d : exists n, Z.to_int n = norm d.
Proof. Show. Fail (abduce 3). Admitted.

Lemma of_int_norm d : Z.of_int (norm d) = Z.of_int d.
Proof. Show. Fail (abduce 3). Admitted.

Lemma of_inj d d' :
  Z.of_int d = Z.of_int d' -> norm d = norm d'.
Proof. Show. Fail (abduce 3). Admitted.

Lemma of_iff d d' : Z.of_int d = Z.of_int d' <-> norm d = norm d'.
Proof. Show. Fail (abduce 3). Admitted.

(** Various lemmas *)

Lemma of_uint_iter_D0 d n :
  Z.of_uint (app d (Nat.iter n D0 Nil)) = Nat.iter n (Z.mul 10) (Z.of_uint d).
Proof. Show. Fail (abduce 3). Admitted.

Lemma of_int_iter_D0 d n :
  Z.of_int (app_int d (Nat.iter n D0 Nil)) = Nat.iter n (Z.mul 10) (Z.of_int d).
Proof. Show. Fail (abduce 3). Admitted.

Lemma nztail_to_uint_pow10 n :
  Decimal.nztail (Pos.to_uint (Nat.iter n (Pos.mul 10) 1%positive))
  = (D1 Nil, n).
Proof. Show. Fail (abduce 3). Admitted.
