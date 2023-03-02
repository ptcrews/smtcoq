(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * DecimalNat

    Proofs that conversions between decimal numbers and [nat]
    are bijections. *)

Require Import Decimal DecimalFacts Arith.
Require Import SMTCoq.SMTCoq.
Module Unsigned.

(** A few helper functions used during proofs *)

Definition hd d :=
  match d with
  | Nil => 0
  | D0 _ => 0
  | D1 _ => 1
  | D2 _ => 2
  | D3 _ => 3
  | D4 _ => 4
  | D5 _ => 5
  | D6 _ => 6
  | D7 _ => 7
  | D8 _ => 8
  | D9 _ => 9
 end.

Definition tl d :=
  match d with
  | Nil => d
  | D0 d | D1 d | D2 d | D3 d | D4 d | D5 d | D6 d | D7 d | D8 d | D9 d => d
  end.

Fixpoint usize (d:uint) : nat :=
  match d with
  | Nil => 0
  | D0 d => S (usize d)
  | D1 d => S (usize d)
  | D2 d => S (usize d)
  | D3 d => S (usize d)
  | D4 d => S (usize d)
  | D5 d => S (usize d)
  | D6 d => S (usize d)
  | D7 d => S (usize d)
  | D8 d => S (usize d)
  | D9 d => S (usize d)
  end.

(** A direct version of [to_little_uint], not tail-recursive *)
Fixpoint to_lu n :=
  match n with
  | 0 => Decimal.zero
  | S n => Little.succ (to_lu n)
  end.

(** A direct version of [of_little_uint] *)
Fixpoint of_lu (d:uint) : nat :=
  match d with
  | Nil => 0
  | D0 d => 10 * of_lu d
  | D1 d => 1 + 10 * of_lu d
  | D2 d => 2 + 10 * of_lu d
  | D3 d => 3 + 10 * of_lu d
  | D4 d => 4 + 10 * of_lu d
  | D5 d => 5 + 10 * of_lu d
  | D6 d => 6 + 10 * of_lu d
  | D7 d => 7 + 10 * of_lu d
  | D8 d => 8 + 10 * of_lu d
  | D9 d => 9 + 10 * of_lu d
  end.

(** Properties of [to_lu] *)

Lemma to_lu_succ n : to_lu (S n) = Little.succ (to_lu n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma to_little_uint_succ n d :
  Nat.to_little_uint n (Little.succ d) =
    Little.succ (Nat.to_little_uint n d).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma to_lu_equiv n :
  to_lu n = Nat.to_little_uint n zero.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma to_uint_alt n :
  Nat.to_uint n = rev (to_lu n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Properties of [of_lu] *)

Lemma of_lu_eqn d :
  of_lu d = hd d + 10 * of_lu (tl d).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Ltac simpl_of_lu :=
  match goal with
  | |- context [ of_lu (?f ?x) ] =>
    rewrite (of_lu_eqn (f x)); simpl hd; simpl tl
  end.

Lemma of_lu_succ d :
  of_lu (Little.succ d) = S (of_lu d).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma of_to_lu n :
  of_lu (to_lu n) = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma of_lu_revapp d d' :
  of_lu (revapp d d') =
    of_lu (rev d) + of_lu d' * 10^usize d.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma of_uint_acc_spec n d :
  Nat.of_uint_acc d n = of_lu (rev d) + n * 10^usize d.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma of_uint_alt d : Nat.of_uint d = of_lu (rev d).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** First main bijection result *)

Lemma of_to (n:nat) : Nat.of_uint (Nat.to_uint n) = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** The other direction *)

Lemma to_lu_tenfold n : n<>0 ->
  to_lu (10 * n) = D0 (to_lu n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma of_lu_0 d : of_lu d = 0 <-> nztail d = Nil.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma to_of_lu_tenfold d :
  to_lu (of_lu d) = lnorm d ->
  to_lu (10 * of_lu d) = lnorm (D0 d).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma to_of_lu d : to_lu (of_lu d) = lnorm d.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Second bijection result *)

Lemma to_of (d:uint) : Nat.to_uint (Nat.of_uint d) = unorm d.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Some consequences *)

Lemma to_uint_inj n n' : Nat.to_uint n = Nat.to_uint n' -> n = n'.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma to_uint_surj d : exists n, Nat.to_uint n = unorm d.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma of_uint_norm d : Nat.of_uint (unorm d) = Nat.of_uint d.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma of_inj d d' :
  Nat.of_uint d = Nat.of_uint d' -> unorm d = unorm d'.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma of_iff d d' : Nat.of_uint d = Nat.of_uint d' <-> unorm d = unorm d'.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End Unsigned.

(** Conversion from/to signed decimal numbers *)

Module Signed.

Lemma of_to (n:nat) : Nat.of_int (Nat.to_int n) = Some n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma to_of (d:int)(n:nat) : Nat.of_int d = Some n -> Nat.to_int n = norm d.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma to_int_inj n n' : Nat.to_int n = Nat.to_int n' -> n = n'.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma to_int_pos_surj d : exists n, Nat.to_int n = norm (Pos d).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma of_int_norm d : Nat.of_int (norm d) = Nat.of_int d.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma of_inj_pos d d' :
  Nat.of_int (Pos d) = Nat.of_int (Pos d') -> unorm d = unorm d'.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End Signed.
