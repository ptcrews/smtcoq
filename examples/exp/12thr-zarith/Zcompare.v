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

(** Binary Integers : results about Z.compare *)
(** Initial author: Pierre Crégut (CNET, Lannion, France *)

(** THIS FILE IS DEPRECATED.
    It is now almost entirely made of compatibility formulations
    for results already present in BinInt.Z. *)

Require Export BinPos BinInt.
Require Import Lt Gt Plus Mult. (* Useless now, for compatibility only *)
Add Rec LoadPath "/home/arjun/Desktop/smtcoq/abduction-arjunvish-smtcoq/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Local Open Scope Z_scope.

(***************************)
(** * Comparison on integers *)

Lemma Zcompare_Gt_Lt_antisym : forall n m:Z, (n ?= m) = Gt <-> (m ?= n) = Lt.
Proof Z.gt_lt_iff.

Lemma Zcompare_antisym n m : CompOpp (n ?= m) = (m ?= n).
Proof eq_sym (Z.compare_antisym n m).

(** * Transitivity of comparison *)

Lemma Zcompare_Lt_trans :
  forall n m p:Z, (n ?= m) = Lt -> (m ?= p) = Lt -> (n ?= p) = Lt.
Proof Z.lt_trans.

Lemma Zcompare_Gt_trans :
  forall n m p:Z, (n ?= m) = Gt -> (m ?= p) = Gt -> (n ?= p) = Gt.
Proof. Show. Fail (abduce 3). Admitted.

(** * Comparison and opposite *)

Lemma Zcompare_opp n m : (n ?= m) = (- m ?= - n).
Proof. Show. Fail (abduce 3). Admitted.

(** * Comparison first-order specification *)

Lemma Zcompare_Gt_spec n m : (n ?= m) = Gt ->  exists h, n + - m = Zpos h.
Proof. Show. Fail (abduce 3). Admitted.

(** * Comparison and addition *)

Lemma Zcompare_plus_compat n m p : (p + n ?= p + m) = (n ?= m).
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zplus_compare_compat (r:comparison) (n m p q:Z) :
  (n ?= m) = r -> (p ?= q) = r -> (n + p ?= m + q) = r.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zcompare_succ_Gt n : (Z.succ n ?= n) = Gt.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zcompare_Gt_not_Lt n m : (n ?= m) = Gt <-> (n ?= m+1) <> Lt.
Proof. Show. Fail (abduce 3). Admitted.

(** * Successor and comparison *)

Lemma Zcompare_succ_compat n m : (Z.succ n ?= Z.succ m) = (n ?= m).
Proof. Show. Fail (abduce 3). Admitted.

(** * Multiplication and comparison *)

Lemma Zcompare_mult_compat :
  forall (p:positive) (n m:Z), (Zpos p * n ?= Zpos p * m) = (n ?= m).
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zmult_compare_compat_l n m p:
  p > 0 -> (n ?= m) = (p * n ?= p * m).
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zmult_compare_compat_r n m p :
  p > 0 -> (n ?= m) = (n * p ?= m * p).
Proof. Show. Fail (abduce 3). Admitted.

(** * Relating [x ?= y] to [=], [<=], [<], [>=] or [>] *)

Lemma Zcompare_elim :
  forall (c1 c2 c3:Prop) (n m:Z),
    (n = m -> c1) ->
    (n < m -> c2) ->
    (n > m -> c3) -> match n ?= m with
                       | Eq => c1
                       | Lt => c2
                       | Gt => c3
                     end.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zcompare_eq_case :
  forall (c1 c2 c3:Prop) (n m:Z),
    c1 -> n = m -> match n ?= m with
                     | Eq => c1
                     | Lt => c2
                     | Gt => c3
                   end.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zle_compare :
  forall n m:Z,
    n <= m -> match n ?= m with
		| Eq => True
		| Lt => True
		| Gt => False
              end.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zlt_compare :
  forall n m:Z,
   n < m -> match n ?= m with
              | Eq => False
              | Lt => True
              | Gt => False
            end.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zge_compare :
  forall n m:Z,
    n >= m -> match n ?= m with
		| Eq => True
		| Lt => False
		| Gt => True
              end.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zgt_compare :
  forall n m:Z,
    n > m -> match n ?= m with
               | Eq => False
               | Lt => False
               | Gt => True
             end.
Proof. Show. Fail (abduce 3). Admitted.

(** Compatibility notations *)

Notation Zcompare_Eq_eq := Z.compare_eq (only parsing).
Notation Zcompare_Eq_iff_eq := Z.compare_eq_iff (only parsing).
Notation Zabs_non_eq := Z.abs_neq (only parsing).
Notation Zsgn_0 := Z.sgn_null (only parsing).
Notation Zsgn_1 := Z.sgn_pos (only parsing).
Notation Zsgn_m1 := Z.sgn_neg (only parsing).

(** Not kept: Zcompare_egal_dec *)
