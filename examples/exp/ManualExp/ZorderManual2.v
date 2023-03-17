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

(** Binary Integers : results about order predicates *)
(** Initial author : Pierre Crégut (CNET, Lannion, France) *)

(** THIS FILE IS DEPRECATED.
    It is now almost entirely made of compatibility formulations
    for results already present in BinInt.Z. *)

(* 
94 Goals
33 Solved by smt
28 non-linear goals
4 non-bool
We solve 13/29 of the remaining goals.
*)
(* Coq-8.16
   cvc5 grammar without ITE *)
Require Import BinPos BinInt Decidable Zcompare.
Require Import Arith_base. (* Useless now, for compatibility only *)
Require Import SMTCoq.SMTCoq.
Require Import String.
Local Open Scope Z_scope.

(*********************************************************)
(** Properties of the order relations on binary integers *)

(** * Trichotomy *)

(* Fail *)
Theorem Ztrichotomy_inf n m : {n < m} + {n = m} + {n > m}.
Proof.
  unfold ">", "<". generalize (Z.compare_eq n m).
  destruct (n ?= m); [ left; right | left; left | right]; auto.
Defined.

(* Pass *)
Lemma Zle_gt_succ n m : n <= m -> Z.succ m > n.
Proof. (* Timeout 20 (time cvc5_abduct 1).  
Finished failing transaction in 1.885 secs (0.004u,0.008s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
(Z.succ m) = 1 + m
(Z.succ m) = n + 1
n + 1 <= (Z.succ m)
*)
assert ((Z.succ m) = 1 + m). { unfold Z.succ. smt. }
smt.
Qed.

Theorem Ztrichotomy n m : n < m \/ n = m \/ n > m.
Proof. smt. Qed.

(**********************************************************************)
(** * Decidability of equality and order on Z *)

Notation dec_eq := Z.eq_decidable (only parsing).
Notation dec_Zle := Z.le_decidable (only parsing).
Notation dec_Zlt := Z.lt_decidable (only parsing).

(* Fail *)
Theorem dec_Zne n m : decidable (Zne n m).
Proof. (* Timeout 20 (time cvc5_abduct 1). 
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
*)
Admitted.

(* Fail *)
Theorem dec_Zgt n m : decidable (n > m).
Proof. (* Timeout 20 (time cvc5_abduct 1). 
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
*)
Admitted.

(* Fail *)
Theorem dec_Zge n m : decidable (n >= m).
Proof. (* Timeout 20 (time cvc5_abduct 1). 
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
*)
Admitted.

Theorem not_Zeq n m : n <> m -> n < m \/ m < n.
Proof. smt. Qed.

Register dec_Zne as plugins.omega.dec_Zne.
Register dec_Zgt as plugins.omega.dec_Zgt.
Register dec_Zge as plugins.omega.dec_Zge.
Register not_Zeq as plugins.omega.not_Zeq.

(** * Relating strict and large orders *)

Notation Zgt_iff_lt := Z.gt_lt_iff (only parsing).
Notation Zge_iff_le := Z.ge_le_iff (only parsing).

Lemma Zle_not_lt n m : n <= m -> ~ m < n.
Proof. smt. Qed.

Lemma Zlt_not_le n m : n < m -> ~ m <= n.
Proof. smt. Qed.

Lemma Zle_not_gt n m : n <= m -> ~ n > m.
Proof. smt. Qed.

Lemma Zgt_not_le n m : n > m -> ~ n <= m.
Proof. smt. Qed.

Lemma Znot_ge_lt n m : ~ n >= m -> n < m.
Proof. smt. Qed.

Lemma Znot_lt_ge n m : ~ n < m -> n >= m.
Proof. smt. Qed.

Lemma Znot_gt_le n m: ~ n > m -> n <= m.
Proof. smt. Qed.

Lemma Znot_le_gt n m : ~ n <= m -> n > m.
Proof. smt. Qed.

(* Fail *)
Lemma not_Zne n m : ~ Zne n m -> n = m.
Proof.
  intros H.
  destruct (Z.eq_decidable n m); [assumption|now elim H].
Qed.

Register Znot_le_gt as plugins.omega.Znot_le_gt.
Register Znot_lt_ge as plugins.omega.Znot_lt_ge.
Register Znot_ge_lt as plugins.omega.Znot_ge_lt.
Register Znot_gt_le as plugins.omega.Znot_gt_le.
Register not_Zne as plugins.omega.not_Zne.

(** * Equivalence and order properties *)

(** Reflexivity *)

Notation Zeq_le := Z.eq_le_incl (only parsing).

#[global]
Hint Resolve Z.le_refl: zarith.

(** Antisymmetry *)

Notation Zle_antisym := Z.le_antisymm (only parsing).

(** Asymmetry *)

Notation Zlt_asym := Z.lt_asymm (only parsing).

Lemma Zgt_asym n m : n > m -> ~ m > n.
Proof. smt. Qed.

(** Irreflexivity *)

Notation Zlt_not_eq := Z.lt_neq (only parsing).

Lemma Zgt_irrefl n : ~ n > n.
Proof. smt. Qed.

(** Large = strict or equal *)

Notation Zlt_le_weak := Z.lt_le_incl (only parsing).
Notation Zle_lt_or_eq_iff := Z.lt_eq_cases (only parsing).

Lemma Zle_lt_or_eq n m : n <= m -> n < m \/ n = m.
Proof. smt. Qed.

(** Dichotomy *)

Notation Zle_or_lt := Z.le_gt_cases (only parsing).

(** Transitivity of strict orders *)

Lemma Zgt_trans n m p : n > m -> m > p -> n > p.
Proof. smt. Qed.

(** Mixed transitivity *)

Lemma Zle_gt_trans n m p : m <= n -> m > p -> n > p.
Proof. smt. Qed.

Lemma Zgt_le_trans n m p : n > m -> p <= m -> n > p.
Proof. smt. Qed.

(** Transitivity of large orders *)

Lemma Zge_trans n m p : n >= m -> m >= p -> n >= p.
Proof. smt. Qed.

#[global]
Hint Resolve Z.le_trans: zarith.

(** * Compatibility of order and operations on Z *)

(** ** Successor *)

(** Compatibility of successor wrt to order *)

(* Fail *)
Lemma Zsucc_le_compat n m : m <= n -> Z.succ m <= Z.succ n.
Proof. (* Timeout 20 (time cvc5_abduct 2). 
Finished failing transaction in 3.469 secs (0.007u,0.019s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
n <= m
(Z.succ n) = (Z.succ m) *)
Admitted.

(* Fail *)
Lemma Zsucc_lt_compat n m : n < m -> Z.succ n < Z.succ m.
Proof. (* Timeout 20 (time cvc5_abduct 1). *)
Admitted.

(* Fail *)
Lemma Zsucc_gt_compat n m : m > n -> Z.succ m > Z.succ n.
Proof. (* Timeout 20 (time cvc5_abduct 1). *)
Admitted.

#[global]
Hint Resolve Zsucc_le_compat: zarith.

(** Simplification of successor wrt to order *)

(* Fail *)
Lemma Zsucc_gt_reg n m : Z.succ m > Z.succ n -> m > n.
Proof. (* Timeout 20 (time cvc5_abduct 1).
Tactic call ran for 0.329 secs (0.007u,0.012s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
n <= m *)
Admitted.

(* Fail *)
Lemma Zsucc_le_reg n m : Z.succ m <= Z.succ n -> m <= n.
Proof. (* Timeout 20 (time cvc5_abduct 1).
Tactic call ran for 0.283 secs (0.01u,0.008s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
m <= n *)
Admitted.

(* Fail *)
Lemma Zsucc_lt_reg n m : Z.succ n < Z.succ m -> n < m.
Proof. (* Timeout 20 (time cvc5_abduct 2). 
Tactic call ran for 0.263 secs (0.008u,0.012s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
n <= m *)
Admitted.

(** Special base instances of order *)

Notation Zlt_succ := Z.lt_succ_diag_r (only parsing).
Notation Zlt_pred := Z.lt_pred_l (only parsing).

(* Pass *)
Lemma Zgt_succ n : Z.succ n > n.
Proof. (* Timeout 20 (time cvc5_abduct 1). 
Tactic call ran for 1.029 secs (0.u,0.016s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
1 + n <= (Z.succ n) *)
assert (1 + n <= (Z.succ n)). { unfold Z.succ. smt. } smt.
Qed.

(* Pass *)
Lemma Znot_le_succ n : ~ Z.succ n <= n.
Proof. (* Timeout 20 (time cvc5_abduct 1).
Tactic call ran for 1.072 secs (0.007u,0.012s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
1 + n <= (Z.succ n)
*)
assert (1 + n <= (Z.succ n)). { unfold Z.succ. smt. }
smt.
Qed.

(** Relating strict and large order using successor or predecessor *)

(* Pass *)
Lemma Zgt_le_succ n m : m > n -> Z.succ n <= m.
Proof. (* Timeout 20 (time cvc5_abduct 4).
Tactic call ran for 1.505 secs (0.002u,0.019s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
(Z.succ n) <= n
(Z.succ n) = m
(Z.succ n) <= m
(Z.succ n) <= n + 1 *)
assert ((Z.succ n) <= n + 1). { unfold Z.succ. smt. }
smt.
Qed.

(* Pass *)
Lemma Zle_lt_succ n m : n <= m -> n < Z.succ m.
Proof. (* Timeout 20 (time cvc5_abduct 1).
Tactic call ran for 0.997 secs (0.003u,0.012s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
(Z.succ m) = 1 + m *)
assert ((Z.succ m) = 1 + m). { unfold Z.succ. smt. }
smt.
Qed.

(* Pass *)
Lemma Zlt_le_succ n m : n < m -> Z.succ n <= m.
Proof. (* Timeout 20 (time cvc5_abduct 3).
Tactic call ran for 7.262 secs (0.004u,0.016s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
(Z.succ n) <= n
(Z.succ n) <= m
n + 1 = (Z.succ n) *)
assert (n + 1 = (Z.succ n)). { unfold Z.succ. smt. }
smt.
Qed.

(* Pass *)
Lemma Zgt_succ_le n m : Z.succ m > n -> n <= m.
Proof. (* Timeout 20 (time cvc5_abduct 3).
Tactic call ran for 5.341 secs (0.004u,0.016s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
n <= m
(Z.succ m) <= m
m + 1 = (Z.succ m) *)
assert (m + 1 = (Z.succ m)). { unfold Z.succ. smt. }
smt.
Qed.

(* Pass *)
Lemma Zlt_succ_le n m : n < Z.succ m -> n <= m.
Proof. (* Timeout 20 (time cvc5_abduct 4).
Tactic call ran for 1.724 secs (0.007u,0.012s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
n <= m
(Z.succ m) = m
(Z.succ m) <= m
(Z.succ m) <= m + 1 *)
assert ((Z.succ m) <= m + 1). { unfold Z.succ. smt. }
smt.
Qed.

(* Pass *)
Lemma Zle_succ_gt n m : Z.succ n <= m -> m > n.
Proof. (* Timeout 20 (time cvc5_abduct 2).
Tactic call ran for 1.365 secs (0.004u,0.016s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
n + 1 <= m
n + 1 = (Z.succ n) *)
assert (n + 1 = (Z.succ n)). {unfold Z.succ. smt. }
smt.
Qed.
(** Weakening order *)

Notation Zle_succ := Z.le_succ_diag_r (only parsing).
Notation Zle_pred := Z.le_pred_l (only parsing).
Notation Zlt_lt_succ := Z.lt_lt_succ_r (only parsing).
Notation Zle_le_succ := Z.le_le_succ_r (only parsing).

(* Pass *)
Lemma Zle_succ_le n m : Z.succ n <= m -> n <= m.
Proof. (* Timeout 20 (time cvc5_abduct 2).
Tactic call ran for 0.739 secs (0.001u,0.018s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
n <= m
n <= (Z.succ n) *)
assert (n <= (Z.succ n)). { unfold Z.succ. smt. }
smt.
Qed. 

#[global]
Hint Resolve Z.le_succ_diag_r: zarith.
#[global]
Hint Resolve Z.le_le_succ_r: zarith.

(** Relating order wrt successor and order wrt predecessor *)

(* Pass *)
Lemma Zgt_succ_pred n m : m > Z.succ n -> Z.pred m > n.
Proof. (* Timeout 20 (time cvc5_abduct 2).
Tactic call ran for 5.603 secs (0.004u,0.016s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
(Z.pred m) = n + 1
n + 1 <= (Z.pred m) *)
intros.
assert (n + 1 <= (Z.pred m)). 
{ unfold Z.pred. (* Timeout 20 (time cvc5_abduct 3).
Tactic call ran for 3.167 secs (0.012u,0.012s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
n + 2 <= m
n + 2 = (Z.succ n)
n + 1 = (Z.succ n) *)
assert (n + 1 = (Z.succ n)). { unfold Z.succ. smt. } smt. }
smt.
Qed.

(* Fail *)
Lemma Zlt_succ_pred n m : Z.succ n < m -> n < Z.pred m.
Proof. (* Timeout 20 (time cvc5_abduct 2).
Tactic call ran for 10.642 secs (0.001u,0.02s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
(Z.pred m) = 1 + n
1 + n <= (Z.pred m) *)
Admitted.

(** Relating strict order and large order on positive *)

(* Pass *)
Lemma Zlt_0_le_0_pred n : 0 < n -> 0 <= Z.pred n.
Proof. (* Timeout 20 (time cvc5_abduct 4).
Tactic call ran for 1.588 secs (0.008u,0.012s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
1 <= (Z.pred n)
n <= (Z.pred n)
0 <= (Z.pred n)
(Z.pred n) + 1 = n *)
assert ((Z.pred n) + 1 = n). { unfold Z.pred. smt. }
smt.
Qed.

(** Special cases of ordered integers *)

(* Fail *)
Lemma Zle_neg_pos : forall p q:positive, Zneg p <= Zpos q.
Proof. (* Timeout 20 (time cvc5_abduct 3).
Tactic call ran for 0.746 secs (0.004u,0.012s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
p + q = 1
p + q = 0
1 <= p + q *)
Admitted.

(* Fail *)
Lemma Zgt_pos_0 : forall p:positive, Zpos p > 0.
Proof. (* Timeout 20 (time cvc5_abduct 2).
Tactic call ran for 0.366 secs (0.002u,0.012s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
1 = p
1 <= p *) 
Admitted.

(* Fail *)
(* weaker but useful (in [Z.pow] for instance) *)
Lemma Zle_0_pos : forall p:positive, 0 <= Zpos p.
Proof. (* Timeout 20 (time cvc5_abduct 3).
Tactic call ran for 0.384 secs (0.u,0.015s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
1 = p
0 = p
1 <= p *) 
Admitted.

(* Fail *)
Lemma Zlt_neg_0 : forall p:positive, Zneg p < 0.
Proof. (* Timeout 20 (time cvc5_abduct 2). 
Tactic call ran for 0.386 secs (0.005u,0.01s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
1 = p
1 <= p *)
Admitted.

(* Fail *)
Lemma Zle_0_nat : forall n:nat, 0 <= Z.of_nat n.
Proof. (* Timeout 20 (time cvc5_abduct 3). 
Tactic call ran for 0.338 secs (0.003u,0.012s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
(Z.of_nat n) = 1
(Z.of_nat n) = 0
0 <= (Z.of_nat n) *)
Admitted.

#[global]
Hint Immediate Z.eq_le_incl: zarith.

(** Derived lemma *)

(* Pass *)
Lemma Zgt_succ_gt_or_eq n m : Z.succ n > m -> n > m \/ m = n.
Proof. (* Timeout 20 (time cvc5_abduct 3).
Tactic call ran for 5.57 secs (0.013u,0.016s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
m <= n
(Z.succ n) <= n
n + 1 = (Z.succ n) *)
assert (n + 1 = (Z.succ n)). { unfold Z.succ. smt. }
smt.
Qed.

(** ** Addition *)
(** Compatibility of addition wrt to order *)

Notation Zplus_lt_le_compat := Z.add_lt_le_mono (only parsing).
Notation Zplus_le_lt_compat := Z.add_le_lt_mono (only parsing).
Notation Zplus_le_compat := Z.add_le_mono (only parsing).
Notation Zplus_lt_compat := Z.add_lt_mono (only parsing).

Lemma Zplus_gt_compat_l n m p : n > m -> p + n > p + m.
Proof. smt. Qed.

Lemma Zplus_gt_compat_r n m p : n > m -> n + p > m + p.
Proof. smt. Qed.

Lemma Zplus_le_compat_l n m p : n <= m -> p + n <= p + m.
Proof. smt. Qed.

Lemma Zplus_le_compat_r n m p : n <= m -> n + p <= m + p.
Proof. smt. Qed.

Lemma Zplus_lt_compat_l n m p : n < m -> p + n < p + m.
Proof. smt. Qed.

Lemma Zplus_lt_compat_r n m p : n < m -> n + p < m + p.
Proof. smt. Qed.

(** Compatibility of addition wrt to being positive *)

Notation Zplus_le_0_compat := Z.add_nonneg_nonneg (only parsing).

(** Simplification of addition wrt to order *)

Lemma Zplus_le_reg_l n m p : p + n <= p + m -> n <= m.
Proof. smt. Qed.

Lemma Zplus_le_reg_r n m p : n + p <= m + p -> n <= m.
Proof. smt. Qed.

Lemma Zplus_lt_reg_l n m p : p + n < p + m -> n < m.
Proof. smt. Qed.

Lemma Zplus_lt_reg_r n m p : n + p < m + p -> n < m.
Proof. smt. Qed.

Lemma Zplus_gt_reg_l n m p : p + n > p + m -> n > m.
Proof. smt. Qed.

Lemma Zplus_gt_reg_r n m p : n + p > m + p -> n > m.
Proof. smt. Qed.

(** ** Multiplication *)
(** Compatibility of multiplication by a positive wrt to order *)

Definition mult := Z.mul.
Lemma Zmult_le_compat_r n m p : n <= m -> 0 <= p -> mult n p <= mult m p.
Proof. intros. (* Timeout 20 (time cvc5_abduct 3).
Tactic call ran for 0.469 secs (0.007u,0.02s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
n = m
m <= n
p + m <= n *)
Admitted.

Lemma Zmult_le_compat_l n m p : n <= m -> 0 <= p -> mult p n <= mult p m.
Proof. intros.  (* Timeout 20 (time cvc5_abduct 6).
Tactic call ran for 11.531 secs (0.018u,0.016s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
n = m
m <= n
p + m <= n
(mult p m) = (mult p n)
p + p + m = n
p + p + m <= n *) 
Admitted.

Lemma Zmult_lt_compat_r n m p : 0 < p -> n < m -> mult n p < mult m p.
Proof. intros. (* Timeout 20 (time cvc5_abduct 1). *) Admitted.

Lemma Zmult_gt_compat_r n m p : p > 0 -> n > m -> mult n p > mult m p.
Proof. intros. (* Timeout 20 (time cvc5_abduct 1). *) Admitted.

Lemma Zmult_gt_0_lt_compat_r n m p : p > 0 -> n < m -> mult n p < mult m p.
Proof. intros. (* Timeout 20 (time cvc5_abduct 1). *) Admitted.

Lemma Zmult_gt_0_le_compat_r n m p : p > 0 -> n <= m -> mult n p <= mult m p.
Proof. intros. (* Timeout 20 (time cvc5_abduct 3). 
Tactic call ran for 3.167 secs (0.008u,0.022s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
n = m
m <= n
p <= 0 || m <= n *)
Admitted.

Lemma Zmult_lt_0_le_compat_r n m p : 0 < p -> n <= m -> mult n p <= mult m p.
Proof. intros. (* Timeout 20 (time cvc5_abduct 4).
Tactic call ran for 5.979 secs (0.004u,0.02s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
n = m
m <= n
p = 0 || m <= n
p <= 0 || m <= n *)
Admitted.

Lemma Zmult_gt_0_lt_compat_l n m p : p > 0 -> n < m -> mult p n < mult p m.
Proof. intros. (* Timeout 20 (time cvc5_abduct 1). *) Admitted.

Lemma Zmult_lt_compat_l n m p : 0 < p -> n < m -> mult p n < mult p m.
Proof. intros. (* Timeout 20 (time cvc5_abduct 1). *) Admitted.

Lemma Zmult_gt_compat_l n m p : p > 0 -> n > m -> mult p n > mult p m.
Proof. intros. (* (Timeout 20 (time cvc5_abduct 1). *) Admitted.

Lemma Zmult_ge_compat_r n m p : n >= m -> p >= 0 -> mult n p >= mult m p.
Proof. intros. (* Timeout 20 (time cvc5_abduct 9).
Tactic call ran for 18.841 secs (0.u,0.061s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
n = m
n <= m
p + n = m
p + n <= m
p + p + n = m
p + p + n <= m
(mult m p) = (mult n p)
(mult m p) <= (mult n p) *)
Admitted.

Lemma Zmult_ge_compat_l n m p : n >= m -> p >= 0 -> mult p n >= mult p m.
Proof. intros. (* Timeout 20 (time cvc5_abduct 7). 
Tactic call ran for 9.265 secs (0.008u,0.027s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
n = m
n <= m
p + n = m
p + n <= m
p + n + p = m
p + n + p <= m
(mult p n) = (mult p m) *)
Admitted.

Lemma Zmult_ge_compat n m p q :
  n >= p -> m >= q -> p >= 0 -> q >= 0 -> mult n m >= mult p q.
Proof. intros. Admitted.

Lemma Zmult_le_compat n m p q :
  n <= p -> m <= q -> 0 <= n -> 0 <= m ->mult n m <= mult p q.
Proof. intros. Admitted.

(** Simplification of multiplication by a positive wrt to being positive *)

Lemma Zmult_gt_0_lt_reg_r n m p : p > 0 -> mult n p < mult m p -> n < m.
Proof. intros. Admitted.

Lemma Zmult_lt_reg_r n m p : 0 < p -> mult n p < mult m p -> n < m.
Proof. intros. Admitted.

Lemma Zmult_le_reg_r n m p : p > 0 -> mult n p <= mult m p -> n <= m.
Proof. intros. Admitted.

Lemma Zmult_lt_0_le_reg_r n m p : 0 < p -> mult n p <= mult m p -> n <= m.
Proof. intros. Admitted.

Lemma Zmult_ge_reg_r n m p : p > 0 -> mult n p >= mult m p -> n >= m.
Proof. Admitted.

Lemma Zmult_gt_reg_r n m p : p > 0 -> mult n p > mult m p -> n > m.
Proof. intros. (* Timeout 20 (time cvc5_abduct 6).
Tactic call ran for 7.902 secs (0.u,0.035s) (failure)
cvc5 returned SAT.
The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
m <= n
m + p = n
m + p <= n
p + p + m <= n
0 = p || m <= n
p <= 0 || m <= n *)
Admitted.

Lemma Zmult_lt_compat n m p q :
  0 <= n < p -> 0 <= m < q -> mult n m < mult p q.
Proof. Admitted.

Lemma Zmult_lt_compat2 n m p q :
  0 < n <= p -> 0 < m < q -> mult n m < mult p q.
Proof.
  intros (Hn, Hnp) (Hm,Hmq).
  apply Z.le_lt_trans with (p * m).
   apply Z.mul_le_mono_pos_r; trivial.
   apply Z.mul_lt_mono_pos_l; Z.order.
Qed.

(** Compatibility of multiplication by a positive wrt to being positive *)

Notation Zmult_le_0_compat := Z.mul_nonneg_nonneg (only parsing).
Notation Zmult_lt_0_compat := Z.mul_pos_pos (only parsing).
Notation Zmult_lt_O_compat := Z.mul_pos_pos (only parsing).

Lemma Zmult_gt_0_compat n m : n > 0 -> m > 0 -> mult n m > 0.
Proof. Admitted.

(* To remove someday ... *)

Lemma Zmult_gt_0_le_0_compat n m : n > 0 -> 0 <= m -> 0 <= mult m n.
Proof.
 Z.swap_greater. intros. apply Z.mul_nonneg_nonneg. trivial.
  now apply Z.lt_le_incl.
Qed.

(** Simplification of multiplication by a positive wrt to being positive *)

Lemma Zmult_le_0_reg_r n m : n > 0 -> 0 <= mult m n -> 0 <= m.
Proof. Admitted.

Lemma Zmult_lt_0_reg_r n m : 0 < n -> 0 < mult m n -> 0 < m.
Proof. Admitted.

Lemma Zmult_gt_0_lt_0_reg_r n m : n > 0 -> 0 < mult m n -> 0 < m.
Proof. Admitted.

Lemma Zmult_gt_0_reg_l n m : n > 0 -> mult n m > 0 -> m > 0.
Proof. Admitted.

(** ** Square *)
(** Simplification of square wrt order *)

Lemma Zlt_square_simpl n m : 0 <= n -> mult m m < mult n n -> m < n.
Proof. Admitted.

Lemma Zgt_square_simpl n m : n >= 0 -> mult n n > mult m m -> n > m.
Proof. Admitted.

(** * Equivalence between inequalities *)

Notation Zle_plus_swap := Z.le_add_le_sub_r (only parsing).
Notation Zlt_plus_swap := Z.lt_add_lt_sub_r (only parsing).
Notation Zlt_minus_simpl_swap := Z.lt_sub_pos (only parsing).

Lemma Zeq_plus_swap n m p : n + p = m <-> n = m - p.
Proof. smt. Qed.

Lemma Zlt_0_minus_lt n m : 0 < n - m -> m < n.
Proof. smt. Qed.

Lemma Zle_0_minus_le n m : 0 <= n - m -> m <= n.
Proof. smt. Qed.

Lemma Zle_minus_le_0 n m : m <= n -> 0 <= n - m.
Proof. smt. Qed.

(** For compatibility *)
Notation Zlt_O_minus_lt := Zlt_0_minus_lt (only parsing).
