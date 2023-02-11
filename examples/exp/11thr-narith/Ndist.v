(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
Require Import Arith.
Require Import Min.
Require Import BinPos.
Require Import BinNat.
Require Import Ndigits.
Add Rec LoadPath "/home/arjun/Desktop/smtcoq/abduction-arjunvish-smtcoq/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
(** An ultrametric distance over [N] numbers *)

Inductive natinf : Set :=
  | infty : natinf
  | ni : nat -> natinf.

Fixpoint Pplength (p:positive) : nat :=
  match p with
  | xH => 0
  | xI _ => 0
  | xO p' => S (Pplength p')
  end.

Definition Nplength (a:N) :=
  match a with
  | N0 => infty
  | Npos p => ni (Pplength p)
  end.

Lemma Nplength_infty : forall a:N, Nplength a = infty -> a = N0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nplength_zeros :
 forall (a:N) (n:nat),
   Nplength a = ni n -> forall k:nat, k < n -> N.testbit_nat a k = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nplength_one :
 forall (a:N) (n:nat), Nplength a = ni n -> N.testbit_nat a n = true.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nplength_first_one :
 forall (a:N) (n:nat),
   (forall k:nat, k < n -> N.testbit_nat a k = false) ->
   N.testbit_nat a n = true -> Nplength a = ni n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition ni_min (d d':natinf) :=
  match d with
  | infty => d'
  | ni n => match d' with
            | infty => d
            | ni n' => ni (min n n')
            end
  end.

Lemma ni_min_idemp : forall d:natinf, ni_min d d = d.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ni_min_comm : forall d d':natinf, ni_min d d' = ni_min d' d.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ni_min_assoc :
 forall d d' d'':natinf, ni_min (ni_min d d') d'' = ni_min d (ni_min d' d'').
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ni_min_O_l : forall d:natinf, ni_min (ni 0) d = ni 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ni_min_O_r : forall d:natinf, ni_min d (ni 0) = ni 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ni_min_inf_l : forall d:natinf, ni_min infty d = d.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ni_min_inf_r : forall d:natinf, ni_min d infty = d.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition ni_le (d d':natinf) := ni_min d d' = d.

Lemma ni_le_refl : forall d:natinf, ni_le d d.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ni_le_antisym : forall d d':natinf, ni_le d d' -> ni_le d' d -> d = d'.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ni_le_trans :
 forall d d' d'':natinf, ni_le d d' -> ni_le d' d'' -> ni_le d d''.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ni_le_min_1 : forall d d':natinf, ni_le (ni_min d d') d.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ni_le_min_2 : forall d d':natinf, ni_le (ni_min d d') d'.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ni_min_case : forall d d':natinf, ni_min d d' = d \/ ni_min d d' = d'.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ni_le_total : forall d d':natinf, ni_le d d' \/ ni_le d' d.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ni_le_min_induc :
 forall d d' dm:natinf,
   ni_le dm d ->
   ni_le dm d' ->
   (forall d'':natinf, ni_le d'' d -> ni_le d'' d' -> ni_le d'' dm) ->
   ni_min d d' = dm.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma le_ni_le : forall m n:nat, m <= n -> ni_le (ni m) (ni n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ni_le_le : forall m n:nat, ni_le (ni m) (ni n) -> m <= n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nplength_lb :
 forall (a:N) (n:nat),
   (forall k:nat, k < n -> N.testbit_nat a k = false) -> ni_le (ni n) (Nplength a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nplength_ub :
 forall (a:N) (n:nat), N.testbit_nat a n = true -> ni_le (Nplength a) (ni n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.


(** We define an ultrametric distance between [N] numbers:
    $d(a,a')=1/2^pd(a,a')$,
    where $pd(a,a')$ is the number of identical bits at the beginning
    of $a$ and $a'$ (infinity if $a=a'$).
    Instead of working with $d$, we work with $pd$, namely
    [Npdist]: *)

Definition Npdist (a a':N) := Nplength (N.lxor a a').

(** d is a distance, so $d(a,a')=0$ iff $a=a'$; this means that
    $pd(a,a')=infty$ iff $a=a'$: *)

Lemma Npdist_eq_1 : forall a:N, Npdist a a = infty.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Npdist_eq_2 : forall a a':N, Npdist a a' = infty -> a = a'.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** $d$ is a distance, so $d(a,a')=d(a',a)$: *)

Lemma Npdist_comm : forall a a':N, Npdist a a' = Npdist a' a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** $d$ is an ultrametric distance, that is, not only $d(a,a')\leq
    d(a,a'')+d(a'',a')$,
  but in fact $d(a,a')\leq max(d(a,a''),d(a'',a'))$.
  This means that $min(pd(a,a''),pd(a'',a'))<=pd(a,a')$ (lemma [Npdist_ultra] below).
  This follows from the fact that $a ~Ra~|a| = 1/2^{\texttt{Nplength}}(a))$
  is an ultrametric norm, i.e. that $|a-a'| \leq max (|a-a''|, |a''-a'|)$,
  or equivalently that $|a+b|<=max(|a|,|b|)$, i.e. that
  min $(\texttt{Nplength}(a), \texttt{Nplength}(b)) \leq
  \texttt{Nplength} (a~\texttt{xor}~ b)$
  (lemma [Nplength_ultra]).
*)

Lemma Nplength_ultra_1 :
 forall a a':N,
   ni_le (Nplength a) (Nplength a') ->
   ni_le (Nplength a) (Nplength (N.lxor a a')).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nplength_ultra :
 forall a a':N,
   ni_le (ni_min (Nplength a) (Nplength a')) (Nplength (N.lxor a a')).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Npdist_ultra :
 forall a a' a'':N,
   ni_le (ni_min (Npdist a a'') (Npdist a'' a')) (Npdist a a').
Proof. Show. Fail (cvc5_abduct 3). Admitted.
