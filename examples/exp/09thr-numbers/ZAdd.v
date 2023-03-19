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

Require Export ZBase.
Require Import SMTCoq.SMTCoq.
Module ZAddProp (Import Z : ZAxiomsMiniSig').
Include ZBaseProp Z.

(** Theorems that are either not valid on N or have different proofs
    on N and Z *)

Hint Rewrite opp_0 : nz.

Theorem add_pred_l n m : P n + m == P (n + m).
Proof. Show. Fail (abduce 3). Admitted.

Theorem add_pred_r n m : n + P m == P (n + m).
Proof. Show. Fail (abduce 3). Admitted.

Theorem add_opp_r n m : n + (- m) == n - m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem sub_0_l n : 0 - n == - n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem sub_succ_l n m : S n - m == S (n - m).
Proof. Show. Fail (abduce 3). Admitted.

Theorem sub_pred_l n m : P n - m == P (n - m).
Proof. Show. Fail (abduce 3). Admitted.

Theorem sub_pred_r n m : n - (P m) == S (n - m).
Proof. Show. Fail (abduce 3). Admitted.

Theorem opp_pred n : - (P n) == S (- n).
Proof. Show. Fail (abduce 3). Admitted.

Theorem sub_diag n : n - n == 0.
Proof. Show. Fail (abduce 3). Admitted.

Theorem add_opp_diag_l n : - n + n == 0.
Proof. Show. Fail (abduce 3). Admitted.

Theorem add_opp_diag_r n : n + (- n) == 0.
Proof. Show. Fail (abduce 3). Admitted.

Theorem add_opp_l n m : - m + n == n - m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem add_sub_assoc n m p : n + (m - p) == (n + m) - p.
Proof. Show. Fail (abduce 3). Admitted.

Theorem opp_involutive n : - (- n) == n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem opp_add_distr n m : - (n + m) == - n + (- m).
Proof. Show. Fail (abduce 3). Admitted.

Theorem opp_sub_distr n m : - (n - m) == - n + m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem opp_inj n m : - n == - m -> n == m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem opp_inj_wd n m : - n == - m <-> n == m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem eq_opp_l n m : - n == m <-> n == - m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem eq_opp_r n m : n == - m <-> - n == m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem sub_add_distr n m p : n - (m + p) == (n - m) - p.
Proof. Show. Fail (abduce 3). Admitted.

Theorem sub_sub_distr n m p : n - (m - p) == (n - m) + p.
Proof. Show. Fail (abduce 3). Admitted.

Theorem sub_opp_l n m : - n - m == - m - n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem sub_opp_r n m : n - (- m) == n + m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem add_sub_swap n m p : n + m - p == n - p + m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem sub_cancel_l n m p : n - m == n - p <-> m == p.
Proof. Show. Fail (abduce 3). Admitted.

Theorem sub_cancel_r n m p : n - p == m - p <-> n == m.
Proof. Show. Fail (abduce 3). Admitted.

(** The next several theorems are devoted to moving terms from one
    side of an equation to the other. The name contains the operation
    in the original equation ([add] or [sub]) and the indication
    whether the left or right term is moved. *)

Theorem add_move_l n m p : n + m == p <-> m == p - n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem add_move_r n m p : n + m == p <-> n == p - m.
Proof. Show. Fail (abduce 3). Admitted.

(** The two theorems above do not allow rewriting subformulas of the
    form [n - m == p] to [n == p + m] since subtraction is in the
    right-hand side of the equation. Hence the following two
    theorems. *)

Theorem sub_move_l n m p : n - m == p <-> - m == p - n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem sub_move_r n m p : n - m == p <-> n == p + m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem add_move_0_l n m : n + m == 0 <-> m == - n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem add_move_0_r n m : n + m == 0 <-> n == - m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem sub_move_0_l n m : n - m == 0 <-> - m == - n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem sub_move_0_r n m : n - m == 0 <-> n == m.
Proof. Show. Fail (abduce 3). Admitted.

(** The following section is devoted to cancellation of like
    terms. The name includes the first operator and the position of
    the term being canceled. *)

Theorem add_simpl_l n m : n + m - n == m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem add_simpl_r n m : n + m - m == n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem sub_simpl_l n m : - n - m + n == - m.
Proof. Show. Fail (abduce 3). Admitted.

Theorem sub_simpl_r n m : n - m + m == n.
Proof. Show. Fail (abduce 3). Admitted.

Theorem sub_add n m : m - n + n == m.
Proof. Show. Fail (abduce 3). Admitted.

(** Now we have two sums or differences; the name includes the two
    operators and the position of the terms being canceled *)

Theorem add_add_simpl_l_l n m p : (n + m) - (n + p) == m - p.
Proof. Show. Fail (abduce 3). Admitted.

Theorem add_add_simpl_l_r n m p : (n + m) - (p + n) == m - p.
Proof. Show. Fail (abduce 3). Admitted.

Theorem add_add_simpl_r_l n m p : (n + m) - (m + p) == n - p.
Proof. Show. Fail (abduce 3). Admitted.

Theorem add_add_simpl_r_r n m p : (n + m) - (p + m) == n - p.
Proof. Show. Fail (abduce 3). Admitted.

Theorem sub_add_simpl_r_l n m p : (n - m) + (m + p) == n + p.
Proof. Show. Fail (abduce 3). Admitted.

Theorem sub_add_simpl_r_r n m p : (n - m) + (p + m) == n + p.
Proof. Show. Fail (abduce 3). Admitted.

(** Of course, there are many other variants *)

End ZAddProp.

