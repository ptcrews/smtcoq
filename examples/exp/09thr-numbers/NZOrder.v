(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Import NZAxioms NZBase Decidable OrdersTac.
Require Import SMTCoq.SMTCoq.
Module Type NZOrderProp
 (Import NZ : NZOrdSig')(Import NZBase : NZBaseProp NZ).

Instance le_wd : Proper (eq==>eq==>iff) le.
Proof. Show. Fail (abduce 3). Admitted.

Ltac le_elim H := rewrite lt_eq_cases in H; destruct H as [H | H].

Theorem lt_le_incl : forall n m, n < m -> n <= m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem le_refl : forall n, n <= n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem lt_succ_diag_r : forall n, n < S n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem le_succ_diag_r : forall n, n <= S n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem neq_succ_diag_l : forall n, S n ~= n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem neq_succ_diag_r : forall n, n ~= S n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem nlt_succ_diag_l : forall n, ~ S n < n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem nle_succ_diag_l : forall n, ~ S n <= n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem le_succ_l : forall n m, S n <= m <-> n < m.
Proof. Show. Fail (abduce 3). Admitted.

(** Trichotomy *)

Theorem le_gt_cases : forall n m, n <= m \/ n > m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem lt_trichotomy : forall n m,  n < m \/ n == m \/ m < n.
Proof. Show. Fail (abduce 3). Admitted.

Notation lt_eq_gt_cases := lt_trichotomy (only parsing).

(** Asymmetry and transitivity. *)

Theorem lt_asymm : forall n m, n < m -> ~ m < n.
Proof. Show. Fail (abduce 3). Admitted.

Notation lt_ngt := lt_asymm (only parsing).

Theorem lt_trans : forall n m p, n < m -> m < p -> n < p.
Proof. Show. Fail (abduce 3). Admitted.

Theorem le_trans : forall n m p, n <= m -> m <= p -> n <= p.
Proof. Show. Fail (abduce 3). Admitted.

(** Some type classes about order *)

Instance lt_strorder : StrictOrder lt.
Proof. Show. Fail (abduce 3). Admitted.

Instance le_preorder : PreOrder le.
Proof. Show. Fail (abduce 3). Admitted.

Instance le_partialorder : PartialOrder _ le.
Proof. Show. Fail (abduce 3). Admitted.

(** We know enough now to benefit from the generic [order] tactic. *)

Definition lt_compat := lt_wd.
Definition lt_total := lt_trichotomy.
Definition le_lteq := lt_eq_cases.

Module Private_OrderTac.
Module IsTotal.
 Definition eq_equiv := eq_equiv.
 Definition lt_strorder := lt_strorder.
 Definition lt_compat := lt_compat.
 Definition lt_total := lt_total.
 Definition le_lteq := le_lteq.
End IsTotal.
Module Tac := !MakeOrderTac NZ IsTotal.
End Private_OrderTac.
Ltac order := Private_OrderTac.Tac.order.

(** Some direct consequences of [order]. *)

Theorem lt_neq : forall n m, n < m -> n ~= m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem le_neq : forall n m, n < m <-> n <= m /\ n ~= m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem eq_le_incl : forall n m, n == m -> n <= m.
Proof. Show. Fail (abduce 3). Admitted.

Lemma lt_stepl : forall x y z, x < y -> x == z -> z < y.
Proof. Show. Fail (abduce 3). Admitted.

Lemma lt_stepr : forall x y z, x < y -> y == z -> x < z.
Proof. Show. Fail (abduce 3). Admitted.

Lemma le_stepl : forall x y z, x <= y -> x == z -> z <= y.
Proof. Show. Fail (abduce 3). Admitted.

Lemma le_stepr : forall x y z, x <= y -> y == z -> x <= z.
Proof. Show. Fail (abduce 3). Admitted.

Declare Left  Step lt_stepl.
Declare Right Step lt_stepr.
Declare Left  Step le_stepl.
Declare Right Step le_stepr.

Theorem le_lt_trans : forall n m p, n <= m -> m < p -> n < p.
Proof. Show. Fail (abduce 3). Admitted.

Theorem lt_le_trans : forall n m p, n < m -> m <= p -> n < p.
Proof. Show. Fail (abduce 3). Admitted.

Theorem le_antisymm : forall n m, n <= m -> m <= n -> n == m.
Proof. Show. Fail (abduce 3). Admitted.

(** More properties of [<] and [<=] with respect to [S] and [0]. *)

Theorem le_succ_r : forall n m, n <= S m <-> n <= m \/ n == S m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem lt_succ_l : forall n m, S n < m -> n < m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem le_le_succ_r : forall n m, n <= m -> n <= S m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem lt_lt_succ_r : forall n m, n < m -> n < S m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem succ_lt_mono : forall n m, n < m <-> S n < S m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem succ_le_mono : forall n m, n <= m <-> S n <= S m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem lt_0_1 : 0 < 1.
Proof. Show. Fail (abduce 3). Admitted.

Theorem le_0_1 : 0 <= 1.
Proof. Show. Fail (abduce 3). Admitted.

Theorem lt_1_2 : 1 < 2.
Proof. Show. Fail (abduce 3). Admitted.

Theorem lt_0_2 : 0 < 2.
Proof. Show. Fail (abduce 3). Admitted.

Theorem le_0_2 : 0 <= 2.
Proof. Show. Fail (abduce 3). Admitted.

(** The order tactic enriched with some knowledge of 0,1,2 *)

Ltac order' := generalize lt_0_1 lt_1_2; order.

Theorem lt_1_l : forall n m, 0 < n -> n < m -> 1 < m.
Proof. Show. Fail (abduce 3). Admitted.

(** More Trichotomy, decidability and double negation elimination. *)

(** The following theorem is cleary redundant, but helps not to
remember whether one has to say le_gt_cases or lt_ge_cases *)

Theorem lt_ge_cases : forall n m, n < m \/ n >= m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem le_ge_cases : forall n m, n <= m \/ n >= m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem lt_gt_cases : forall n m, n ~= m <-> n < m \/ n > m.
Proof. Show. Fail (abduce 3). Admitted.

(** Decidability of equality, even though true in each finite ring, does not
have a uniform proof. Otherwise, the proof for two fixed numbers would
reduce to a normal form that will say if the numbers are equal or not,
which cannot be true in all finite rings. Therefore, we prove decidability
in the presence of order. *)

Theorem eq_decidable : forall n m, decidable (n == m).
Proof. Show. Fail (abduce 3). Admitted.

(** DNE stands for double-negation elimination *)

Theorem eq_dne : forall n m, ~ ~ n == m <-> n == m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem le_ngt : forall n m, n <= m <-> ~ n > m.
Proof. Show. Fail (abduce 3). Admitted.

(** Redundant but useful *)

Theorem nlt_ge : forall n m, ~ n < m <-> n >= m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem lt_decidable : forall n m, decidable (n < m).
Proof. Show. Fail (abduce 3). Admitted.

Theorem lt_dne : forall n m, ~ ~ n < m <-> n < m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem nle_gt : forall n m, ~ n <= m <-> n > m.
Proof. Show. Fail (abduce 3). Admitted.

(** Redundant but useful *)

Theorem lt_nge : forall n m, n < m <-> ~ n >= m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem le_decidable : forall n m, decidable (n <= m).
Proof. Show. Fail (abduce 3). Admitted.

Theorem le_dne : forall n m, ~ ~ n <= m <-> n <= m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem nlt_succ_r : forall n m, ~ m < S n <-> n < m.
Proof. Show. Fail (abduce 3). Admitted.

(** The difference between integers and natural numbers is that for
every integer there is a predecessor, which is not true for natural
numbers. However, for both classes, every number that is bigger than
some other number has a predecessor. The proof of this fact by regular
induction does not go through, so we need to use strong
(course-of-value) induction. *)

Lemma lt_exists_pred_strong :
  forall z n m, z < m -> m <= n -> exists k, m == S k /\ z <= k.
Proof. Show. Fail (abduce 3). Admitted.

Theorem lt_exists_pred :
  forall z n, z < n -> exists k, n == S k /\ z <= k.
Proof. Show. Fail (abduce 3). Admitted.

Lemma lt_succ_pred : forall z n, z < n -> S (P n) == n.
Proof. Show. Fail (abduce 3). Admitted.

(** Stronger variant of induction with assumptions n >= 0 (n < 0)
in the induction step *)

Section Induction.

Variable A : t -> Prop.
Hypothesis A_wd : Proper (eq==>iff) A.

Section Center.

Variable z : t. (* A z is the basis of induction *)

Section RightInduction.

Let A' (n : t) := forall m, z <= m -> m < n -> A m.
Let right_step :=   forall n, z <= n -> A n -> A (S n).
Let right_step' :=  forall n, z <= n -> A' n -> A n.
Let right_step'' := forall n, A' n <-> A' (S n).

Lemma rs_rs' :  A z -> right_step -> right_step'.
Proof. Show. Fail (abduce 3). Admitted.

Lemma rs'_rs'' : right_step' -> right_step''.
Proof. Show. Fail (abduce 3). Admitted.

Lemma rbase : A' z.
Proof. Show. Fail (abduce 3). Admitted.

Lemma A'A_right : (forall n, A' n) -> forall n, z <= n -> A n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem strong_right_induction: right_step' -> forall n, z <= n -> A n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem right_induction : A z -> right_step -> forall n, z <= n -> A n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem right_induction' :
  (forall n, n <= z -> A n) -> right_step -> forall n, A n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem strong_right_induction' :
  (forall n, n <= z -> A n) -> right_step' -> forall n, A n.
Proof. Show. Fail (abduce 3). Admitted.

End RightInduction.

Section LeftInduction.

Let A' (n : t) := forall m, m <= z -> n <= m -> A m.
Let left_step :=   forall n, n < z -> A (S n) -> A n.
Let left_step' :=  forall n, n <= z -> A' (S n) -> A n.
Let left_step'' := forall n, A' n <-> A' (S n).

Lemma ls_ls' :  A z -> left_step -> left_step'.
Proof. Show. Fail (abduce 3). Admitted.

Lemma ls'_ls'' : left_step' -> left_step''.
Proof. Show. Fail (abduce 3). Admitted.

Lemma lbase : A' (S z).
Proof. Show. Fail (abduce 3). Admitted.

Lemma A'A_left : (forall n, A' n) -> forall n, n <= z -> A n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem strong_left_induction: left_step' -> forall n, n <= z -> A n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem left_induction : A z -> left_step -> forall n, n <= z -> A n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem left_induction' :
  (forall n, z <= n -> A n) -> left_step -> forall n, A n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem strong_left_induction' :
  (forall n, z <= n -> A n) -> left_step' -> forall n, A n.
Proof. Show. Fail (abduce 3). Admitted.

End LeftInduction.

Theorem order_induction :
  A z ->
  (forall n, z <= n -> A n -> A (S n)) ->
  (forall n, n < z  -> A (S n) -> A n) ->
    forall n, A n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem order_induction' :
  A z ->
  (forall n, z <= n -> A n -> A (S n)) ->
  (forall n, n <= z -> A n -> A (P n)) ->
    forall n, A n.
Proof. Show. Fail (abduce 3). Admitted.

End Center.

Theorem order_induction_0 :
  A 0 ->
  (forall n, 0 <= n -> A n -> A (S n)) ->
  (forall n, n < 0  -> A (S n) -> A n) ->
    forall n, A n.
Proof (order_induction 0).

Theorem order_induction'_0 :
  A 0 ->
  (forall n, 0 <= n -> A n -> A (S n)) ->
  (forall n, n <= 0 -> A n -> A (P n)) ->
    forall n, A n.
Proof (order_induction' 0).

(** Elimintation principle for < *)

Theorem lt_ind : forall (n : t),
  A (S n) ->
  (forall m, n < m -> A m -> A (S m)) ->
   forall m, n < m -> A m.
Proof. Show. Fail (abduce 3). Admitted.

(** Elimination principle for <= *)

Theorem le_ind : forall (n : t),
  A n ->
  (forall m, n <= m -> A m -> A (S m)) ->
   forall m, n <= m -> A m.
Proof. Show. Fail (abduce 3). Admitted.

End Induction.

Tactic Notation "nzord_induct" ident(n) :=
  induction_maker n ltac:(apply order_induction_0).

Tactic Notation "nzord_induct" ident(n) constr(z) :=
  induction_maker n ltac:(apply order_induction with z).

Section WF.

Variable z : t.

Let Rlt (n m : t) := z <= n < m.
Let Rgt (n m : t) := m < n <= z.

Instance Rlt_wd : Proper (eq ==> eq ==> iff) Rlt.
Proof. Show. Fail (abduce 3). Admitted.

Instance Rgt_wd : Proper (eq ==> eq ==> iff) Rgt.
Proof. Show. Fail (abduce 3). Admitted.

Theorem lt_wf : well_founded Rlt.
Proof. Show. Fail (abduce 3). Admitted.

Theorem gt_wf : well_founded Rgt.
Proof. Show. Fail (abduce 3). Admitted.

End WF.

End NZOrderProp.

(** If we have moreover a [compare] function, we can build
    an [OrderedType] structure. *)

(* Temporary workaround for bug #2949: remove this problematic + unused functor
Module NZOrderedType (NZ : NZDecOrdSig')
 <: DecidableTypeFull <: OrderedTypeFull
 := NZ <+ NZBaseProp <+ NZOrderProp <+ Compare2EqBool <+ HasEqBool2Dec.
*)
