(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import BinNat.
Require BinPos Ndec.
Require Export Ring.
Require Import SMTCoq.SMTCoq.
(******************************************************************************)
(* A version of arithmetic on nat (natural numbers) that is better suited to  *)
(* small scale reflection than the Coq Arith library. It contains an          *)
(* extensive equational theory (including, e.g., the AGM inequality), as well *)
(* as support for the ring tactic, and congruence tactics.                    *)
(*   The following operations and notations are provided:                     *)
(*                                                                            *)
(*   successor and predecessor                                                *)
(*     n.+1, n.+2, n.+3, n.+4 and n.-1, n.-2                                  *)
(*     this frees the names "S" and "pred"                                    *)
(*                                                                            *)
(*   basic arithmetic                                                         *)
(*     m + n, m - n, m * n                                                    *)
(*   Important: m - n denotes TRUNCATED subtraction: m - n = 0 if m <= n.     *)
(*   The definitions use the nosimpl tag to prevent undesirable computation   *)
(*   computation during simplification, but remain compatible with the ones   *)
(*   provided in the Coq.Init.Peano prelude.                                  *)
(*     For computation, a module NatTrec rebinds all arithmetic notations     *)
(*   to less convenient but also less inefficient tail-recursive functions;   *)
(*   the auxiliary functions used by these versions are flagged with %Nrec.   *)
(*     Also, there is support for input and output of large nat values.       *)
(*       Num 3 082 241 inputs the number 3082241                              *)
(*         [Num of n]  outputs the value n                                    *)
(*   There are coercions num >-> BinNat.N >-> nat; ssrnat rebinds the scope   *)
(*   delimiter for BinNat.N to %num, as it uses the shorter %N for its own    *)
(*   notations (Peano notations are flagged with %coq_nat).                   *)
(*                                                                            *)
(*   doubling, halving, and parity                                            *)
(*      n.*2, n./2, odd n, uphalf n,  with uphalf n = n.+1./2                 *)
(*   bool coerces to nat so we can write, e.g., n = odd n + n./2.*2.          *)
(*                                                                            *)
(*   iteration                                                                *)
(*             iter n f x0  == f ( .. (f x0))                                 *)
(*             iteri n g x0 == g n.-1 (g ... (g 0 x0))                        *)
(*         iterop n op x x0 == op x (... op x x) (n x's) or x0 if n = 0       *)
(*                                                                            *)
(*   exponentiation, factorial                                                *)
(*        m ^ n, n`!                                                          *)
(*        m ^ 1 is convertible to m, and m ^ 2 to m * m                       *)
(*                                                                            *)
(*   comparison                                                               *)
(*      m <= n, m < n, m >= n, m > n, m == n, m <= n <= p, etc.,              *)
(*   comparisons are BOOLEAN operators, and m == n is the generic eqType      *)
(*   operation.                                                               *)
(*     Most compatibility lemmas are stated as boolean equalities; this keeps *)
(*   the size of the library down. All the inequalities refer to the same     *)
(*   constant "leq"; in particular m < n is identical to m.+1 <= n.           *)
(*                                                                            *)
(* -> patterns for contextual rewriting:                                      *)
(*      leqLHS := (X in (X <= _)%N)%pattern                                   *)
(*      leqRHS := (X in (_ <= X)%N)%pattern                                   *)
(*      ltnLHS := (X in (X < _)%N)%pattern                                    *)
(*      ltnRHS := (X in (_ < X)%N)%pattern                                    *)
(*                                                                            *)
(*   conditionally strict inequality `leqif'                                  *)
(*      m <= n ?= iff condition   ==   (m <= n) and ((m == n) = condition)    *)
(*   This is actually a pair of boolean equalities, so rewriting with an      *)
(*   `leqif' lemma can affect several kinds of comparison. The transitivity   *)
(*   lemma for leqif aggregates the conditions, allowing for arguments of     *)
(*   the form ``m <= n <= p <= m, so equality holds throughout''.             *)
(*                                                                            *)
(*   maximum and minimum                                                      *)
(*      maxn m n, minn m n                                                    *)
(*   Note that maxn m n = m + (n - m), due to the truncating subtraction.     *)
(*   Absolute difference (linear distance) between nats is defined in the int *)
(*   library (in the int.IntDist sublibrary), with the syntax `|m - n|. The   *)
(*   '-' in this notation is the signed integer difference.                   *)
(*                                                                            *)
(*   countable choice                                                         *)
(*     ex_minn : forall P : pred nat, (exists n, P n) -> nat                  *)
(*   This returns the smallest n such that P n holds.                         *)
(*     ex_maxn : forall (P : pred nat) m,                                     *)
(*        (exists n, P n) -> (forall n, P n -> n <= m) -> nat                 *)
(*   This returns the largest n such that P n holds (given an explicit upper  *)
(*   bound).                                                                  *)
(*                                                                            *)
(*  This file adds the following suffix conventions to those documented in    *)
(* ssrbool.v and eqtype.v:                                                    *)
(*   A (infix) -- conjunction, as in                                          *)
(*      ltn_neqAle : (m < n) = (m != n) && (m <= n).                          *)
(*   B -- subtraction, as in subBn : (m - n) - p = m - (n + p).               *)
(*   D -- addition, as in mulnDl : (m + n) * p = m * p + n * p.               *)
(*   M -- multiplication, as in expnMn : (m * n) ^ p = m ^ p * n ^ p.         *)
(*   p (prefix) -- positive, as in                                            *)
(*      eqn_pmul2l : m > 0 -> (m * n1 == m * n2) = (n1 == n2).                *)
(*   P  -- greater than 1, as in                                              *)
(*      ltn_Pmull : 1 < n -> 0 < m -> m < n * m.                              *)
(*   S -- successor, as in addSn : n.+1 + m = (n + m).+1.                     *)
(*   V (infix) -- disjunction, as in                                          *)
(*      leq_eqVlt : (m <= n) = (m == n) || (m < n).                           *)
(*   X - exponentiation, as in lognX : logn p (m ^ n) = logn p m * n in       *)
(*         file prime.v (the suffix is not used in this file).                 *)
(* Suffixes that abbreviate operations (D, B, M and X) are used to abbreviate *)
(* second-rank operations in equational lemma names that describe left-hand   *)
(* sides (e.g., mulnDl); they are not used to abbreviate the main operation   *)
(* of relational lemmas (e.g., leq_add2l).                                    *)
(*   For the asymmetrical exponentiation operator expn (m ^ n) a right suffix *)
(* indicates an operation on the exponent, e.g., expnM : m ^ (n1 * n2) = ...; *)
(* a trailing "n" is used to indicate the left operand, e.g.,                 *)
(* expnMn : (m1 * m2) ^ n = ... The operands of other operators are selected  *)
(* using the l/r suffixes.                                                    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope coq_nat_scope.
Declare Scope nat_rec_scope.

(* Disable Coq prelude hints to improve proof script robustness. *)

#[global] Remove Hints plus_n_O plus_n_Sm mult_n_O mult_n_Sm : core.

(* Declare legacy Arith operators in new scope. *)

Delimit Scope coq_nat_scope with coq_nat.

Notation "m + n" := (plus m n) : coq_nat_scope.
Notation "m - n" := (minus m n) : coq_nat_scope.
Notation "m * n" := (mult m n) : coq_nat_scope.
Notation "m <= n" := (le m n) : coq_nat_scope.
Notation "m < n" := (lt m n) : coq_nat_scope.
Notation "m >= n" := (ge m n) : coq_nat_scope.
Notation "m > n" := (gt m n) : coq_nat_scope.

(* Rebind scope delimiters, reserving a scope for the "recursive",     *)
(* i.e., unprotected version of operators.                             *)

Delimit Scope N_scope with num.
Delimit Scope nat_scope with N.
Delimit Scope nat_rec_scope with Nrec.

(* Postfix notation for the successor and predecessor functions.  *)
(* SSreflect uses "pred" for the generic predicate type, and S as *)
(* a local bound variable.                                        *)

Notation succn := Datatypes.S.
Notation predn := Peano.pred.

Notation "n .+1" := (succn n) (at level 2, left associativity,
  format "n .+1") : nat_scope.
Notation "n .+2" := n.+1.+1 (at level 2, left associativity,
  format "n .+2") : nat_scope.
Notation "n .+3" := n.+2.+1 (at level 2, left associativity,
  format "n .+3") : nat_scope.
Notation "n .+4" := n.+2.+2 (at level 2, left associativity,
  format "n .+4") : nat_scope.

Notation "n .-1" := (predn n) (at level 2, left associativity,
  format "n .-1") : nat_scope.
Notation "n .-2" := n.-1.-1 (at level 2, left associativity,
  format "n .-2") : nat_scope.

Lemma succnK : cancel succn predn. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma succn_inj : injective succn. Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Predeclare postfix doubling/halving operators. *)

Reserved Notation "n .*2" (at level 2, format "n .*2").
Reserved Notation "n ./2" (at level 2, format "n ./2").

(* Canonical comparison and eqType for nat.                                *)

Fixpoint eqn m n {struct m} :=
  match m, n with
  | 0, 0 => true
  | m'.+1, n'.+1 => eqn m' n'
  | _, _ => false
  end.

Lemma eqnP : Equality.axiom eqn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Canonical nat_eqMixin := EqMixin eqnP.
Canonical nat_eqType := Eval hnf in EqType nat nat_eqMixin.

Arguments eqn !m !n.
Arguments eqnP {x y}.

Lemma eqnE : eqn = eq_op. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma eqSS m n : (m.+1 == n.+1) = (m == n). Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nat_irrelevance (x y : nat) (E E' : x = y) : E = E'.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Protected addition, with a more systematic set of lemmas.                *)

Definition addn_rec := plus.
Notation "m + n" := (addn_rec m n) : nat_rec_scope.

Definition addn := nosimpl addn_rec.
Notation "m + n" := (addn m n) : nat_scope.

Lemma addnE : addn = addn_rec. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma plusE : plus = addn. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma add0n : left_id 0 addn.            Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma addSn m n : m.+1 + n = (m + n).+1. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma add1n n : 1 + n = n.+1.            Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addn0 : right_id 0 addn. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addnS m n : m + n.+1 = (m + n).+1. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addSnnS m n : m.+1 + n = m + n.+1. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addnCA : left_commutative addn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addnC : commutative addn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addn1 n : n + 1 = n.+1. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addnA : associative addn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addnAC : right_commutative addn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addnCAC m n p : m + n + p = p + n + m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addnACl m n p: m + n + p = n + (p + m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addnACA : interchange addn addn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addn_eq0 m n : (m + n == 0) = (m == 0) && (n == 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma eqn_add2l p m n : (p + m == p + n) = (m == n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma eqn_add2r p m n : (m + p == n + p) = (m == n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addnI : right_injective addn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addIn : left_injective addn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addn2 m : m + 2 = m.+2. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma add2n m : 2 + m = m.+2. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma addn3 m : m + 3 = m.+3. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma add3n m : 3 + m = m.+3. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma addn4 m : m + 4 = m.+4. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma add4n m : 4 + m = m.+4. Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Protected, structurally decreasing subtraction, and basic lemmas.  *)
(* Further properties depend on ordering conditions.                  *)

Definition subn_rec := minus.
Arguments subn_rec : simpl nomatch.
Notation "m - n" := (subn_rec m n) : nat_rec_scope.

Definition subn := nosimpl subn_rec.
Notation "m - n" := (subn m n) : nat_scope.

Lemma subnE : subn = subn_rec. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma minusE : minus = subn.   Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sub0n : left_zero 0 subn.    Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma subn0 : right_id 0 subn.   Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma subnn : self_inverse 0 subn. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma subSS n m : m.+1 - n.+1 = m - n. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma subn1 n : n - 1 = n.-1.          Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma subn2 n : (n - 2)%N = n.-2.      Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma subnDl p m n : (p + m) - (p + n) = m - n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma subnDr p m n : (m + p) - (n + p) = m - n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addnK n : cancel (addn^~ n) (subn^~ n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addKn n : cancel (addn n) (subn^~ n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma subSnn n : n.+1 - n = 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma subnDA m n p : n - (m + p) = (n - m) - p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma subnAC : right_commutative subn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma subnS m n : m - n.+1 = (m - n).-1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma subSKn m n : (m.+1 - n).-1 = m - n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Integer ordering, and its interaction with the other operations.       *)

Definition leq m n := m - n == 0.

Notation "m <= n" := (leq m n) : nat_scope.
Notation "m < n"  := (m.+1 <= n) : nat_scope.
Notation "m >= n" := (n <= m) (only parsing) : nat_scope.
Notation "m > n"  := (n < m) (only parsing)  : nat_scope.

(* For sorting, etc. *)
Definition geq := [rel m n | m >= n].
Definition ltn := [rel m n | m < n].
Definition gtn := [rel m n | m > n].

Notation "m <= n <= p" := ((m <= n) && (n <= p)) : nat_scope.
Notation "m < n <= p" := ((m < n) && (n <= p)) : nat_scope.
Notation "m <= n < p" := ((m <= n) && (n < p)) : nat_scope.
Notation "m < n < p" := ((m < n) && (n < p)) : nat_scope.

Lemma ltnS m n : (m < n.+1) = (m <= n). Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma leq0n n : 0 <= n.                 Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma ltn0Sn n : 0 < n.+1.              Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma ltn0 n : n < 0 = false.           Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma leqnn n : n <= n.                 Proof. Show. Fail (cvc5_abduct 3). Admitted.
#[global] Hint Resolve leqnn : core.
Lemma ltnSn n : n < n.+1.               Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma eq_leq m n : m = n -> m <= n.     Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma leqnSn n : n <= n.+1.             Proof. Show. Fail (cvc5_abduct 3). Admitted.
#[global] Hint Resolve leqnSn : core.
Lemma leq_pred n : n.-1 <= n.           Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma leqSpred n : n <= n.-1.+1.        Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_predL n : (n.-1 < n) = (0 < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_predRL m n : (m < n.-1) = (m.+1 < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_predK m n : m < n -> n.-1.+1 = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma prednK n : 0 < n -> n.-1.+1 = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leqNgt m n : (m <= n) = ~~ (n < m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leqVgt m n : (m <= n) || (n < m). Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltnNge m n : (m < n) = ~~ (n <= m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltnn n : n < n = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leqn0 n : (n <= 0) = (n == 0).           Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma lt0n n : (0 < n) = (n != 0).             Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma lt0n_neq0 n : 0 < n -> n != 0.           Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma eqn0Ngt n : (n == 0) = ~~ (n > 0).       Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma neq0_lt0n n : (n == 0) = false -> 0 < n. Proof. Show. Fail (cvc5_abduct 3). Admitted.
#[global] Hint Resolve lt0n_neq0 neq0_lt0n : core.

Lemma eqn_leq m n : (m == n) = (m <= n <= m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma anti_leq : antisymmetric leq.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma neq_ltn m n : (m != n) = (m < n) || (n < m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gtn_eqF m n : m < n -> n == m = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_eqF m n : m < n -> m == n = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_geF m n : m < n -> m >= n = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_gtF m n : m <= n -> m > n = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_eqVlt m n : (m <= n) = (m == n) || (m < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_neqAle m n : (m < n) = (m != n) && (m <= n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_trans n m p : m <= n -> n <= p -> m <= p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_ltn_trans n m p : m <= n -> n < p -> m < p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltnW m n : m < n -> m <= n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.
#[global] Hint Resolve ltnW : core.

Lemma leqW m n : m <= n -> m <= n.+1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_trans n m p : m < n -> n < p -> m < p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_total m n : (m <= n) || (m >= n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Helper lemmas to support generalized induction over a nat measure.         *)
(* The idiom for a proof by induction over a measure Mxy : nat involving      *)
(* variables x, y, ... (e.g., size x + size y) is                             *)
(*   have [n leMn] := ubnP Mxy; elim: n => // n IHn in x y ... leMn ... *.    *)
(* after which the current goal (possibly modified by generalizations in the  *)
(* in ... part) can be proven with the extra context assumptions              *)
(*  n : nat                                                                   *)
(*  IHn : forall x y ..., Mxy < n -> ... -> the_initial_goal                  *)
(*  leMn : Mxy < n.+1                                                         *)
(* This is preferable to the legacy idiom relying on numerical occurrence     *)
(* selection, which is fragile if there can be multiple occurrences of x, y,  *)
(* ... in the measure expression Mxy (e.g., in #|y| with x : finType and      *)
(* y : {set x}).                                                              *)
(*  The leMn statement is convertible to Mxy <= n; if it is necessary to      *)
(* have _exactly_ leMn : Mxy <= n, the ltnSE helper lemma may be used as      *)
(* follows                                                                    *)
(*   have [n] := ubnP Mxy; elim: n => // n IHn in x y ... * => /ltnSE-leMn.   *)
(*  We also provide alternative helper lemmas for proofs where the upper      *)
(* bound appears in the goal, and we assume nonstrict (in)equality.           *)
(* In either case the proof will have to dispatch an Mxy = 0 case.            *)
(*  have [n defM] := ubnPleq Mxy; elim: n => [|n IHn] in x y ... defM ... *.  *)
(* yields two subgoals, in which Mxy has been replaced by 0 and n.+1,         *)
(* with the extra assumption defM : Mxy <= 0 / Mxy <= n.+1, respectively.     *)
(* The second goal also has the inductive assumption                          *)
(*   IHn : forall x y ..., Mxy <= n -> ... -> the_initial_goal[n / Mxy].      *)
(* Using ubnPgeq or ubnPeq instead of ubnPleq yields assumptions with         *)
(* Mxy >= 0/n.+1 or Mxy == 0/n.+1 instead of Mxy <= 0/n.+1, respectively.     *)
(* These introduce a different kind of induction; for example ubnPgeq M lets  *)
(* us remember that n < M throughout the induction.                           *)
(*   Finally, the ltn_ind lemma provides a generalized induction view for a   *)
(* property of a single integer (i.e., the case Mxy := x).                    *)
Lemma ubnP m : {n | m < n}.             Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma ltnSE m n : m < n.+1 -> m <= n.   Proof. Show. Fail (cvc5_abduct 3). Admitted.
Variant ubn_leq_spec m : nat -> Type := UbnLeq n of m <= n : ubn_leq_spec m n.
Variant ubn_geq_spec m : nat -> Type := UbnGeq n of m >= n : ubn_geq_spec m n.
Variant ubn_eq_spec m : nat -> Type := UbnEq n of m == n : ubn_eq_spec m n.
Lemma ubnPleq m : ubn_leq_spec m m.    Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma ubnPgeq m : ubn_geq_spec m m.    Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma ubnPeq m : ubn_eq_spec m m.      Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma ltn_ind P : (forall n, (forall m, m < n -> P m) -> P n) -> forall n, P n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Link to the legacy comparison predicates. *)

Lemma leP m n : reflect (m <= n)%coq_nat (m <= n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Arguments leP {m n}.

Lemma le_irrelevance m n le_mn1 le_mn2 : le_mn1 = le_mn2 :> (m <= n)%coq_nat.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltP m n : reflect (m < n)%coq_nat (m < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Arguments ltP {m n}.

Lemma lt_irrelevance m n lt_mn1 lt_mn2 : lt_mn1 = lt_mn2 :> (m < n)%coq_nat.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Monotonicity lemmas *)

Lemma leq_add2l p m n : (p + m <= p + n) = (m <= n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_add2l p m n : (p + m < p + n) = (m < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_add2r p m n : (m + p <= n + p) = (m <= n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_add2r p m n : (m + p < n + p) = (m < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_add m1 m2 n1 n2 : m1 <= n1 -> m2 <= n2 -> m1 + m2 <= n1 + n2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_addl m n : n <= m + n. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_addr m n : n <= n + m. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_addl m n p : m < n -> m < p + n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_addr m n p : m < n -> m < n + p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addn_gt0 m n : (0 < m + n) = (0 < m) || (0 < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma subn_gt0 m n : (0 < n - m) = (m < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma subn_eq0 m n : (m - n == 0) = (m <= n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_subLR m n p : (m - n <= p) = (m <= n + p).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_subr m n : n - m <= n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_subrR m n : (n < n - m) = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_subrR m n : (n <= n - m) = (m == 0) || (n == 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_subrL m n : (n - m < n) = (0 < m) && (0 < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma subnKC m n : m <= n -> m + (n - m) = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addnBn m n : m + (n - m) = m - n + n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma subnK m n : m <= n -> (n - m) + m = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addnBA m n p : p <= n -> m + (n - p) = m + n - p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addnBAC m n p : n <= m -> m - n + p = m + p - n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addnBCA m n p : p <= m -> p <= n -> m + (n - p) = n + (m - p).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addnABC m n p : p <= m -> p <= n -> m + (n - p) = m - p + n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma subnBA m n p : p <= n -> m - (n - p) = m + p - n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma subnA m n p : p <= n -> n <= m -> m - (n - p) = m - n + p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma subKn m n : m <= n -> n - (n - m) = m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma subSn m n : m <= n -> n.+1 - m = (n - m).+1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma subnSK m n : m < n -> (n - m.+1).+1 = n - m. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma predn_sub m n : (m - n).-1 = (m.-1 - n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_sub2r p m n : m <= n -> m - p <= n - p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_sub2l p m n : m <= n -> p - n <= p - m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_sub m1 m2 n1 n2 : m1 <= m2 -> n2 <= n1 -> m1 - n1 <= m2 - n2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_sub2r p m n : p < n -> m < n -> m - p < n - p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_sub2l p m n : m < p -> m < n -> p - n < p - m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_subRL m n p : (n < p - m) = (m + n < p).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_psubRL m n p : 0 < n -> (n <= p - m) = (m + n <= p).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_psubLR m n p : 0 < p -> (m - n < p) = (m < n + p).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_subRL m n p : m <= p -> (n <= p - m) = (m + n <= p).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_subLR m n p : n <= m -> (m - n < p) = (m < n + p).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_subCl m n p : (m - n <= p) = (m - p <= n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_subCr m n p : (p < m - n) = (n < m - p).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_psubCr m n p : 0 < p -> 0 < n -> (p <= m - n) = (n <= m - p).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_psubCl m n p : 0 < p -> 0 < n -> (m - n < p) = (m - p < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_subCr m n p : n <= m -> p <= m -> (p <= m - n) = (n <= m - p).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_subCl m n p : n <= m -> p <= m -> (m - n < p) = (m - p < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_sub2rE p m n : p <= n -> (m - p <= n - p) = (m <= n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_sub2lE m n p : n <= m -> (m - p <= m - n) = (n <= p).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_sub2rE p m n : p <= m -> (m - p < n - p) = (m < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_sub2lE m n p : p <= m -> (m - p < m - n) = (n < p).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Max and min. *)

Definition maxn m n := if m < n then n else m.

Definition minn m n := if m < n then m else n.

Lemma max0n : left_id 0 maxn.  Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma maxn0 : right_id 0 maxn. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma maxnC : commutative maxn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma maxnE m n : maxn m n = m + (n - m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma maxnAC : right_commutative maxn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma maxnA : associative maxn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma maxnCA : left_commutative maxn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma maxnACA : interchange maxn maxn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma maxn_idPl {m n} : reflect (maxn m n = m) (m >= n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma maxn_idPr {m n} : reflect (maxn m n = n) (m <= n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma maxnn : idempotent maxn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_max m n1 n2 : (m <= maxn n1 n2) = (m <= n1) || (m <= n2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma leq_maxl m n : m <= maxn m n. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma leq_maxr m n : n <= maxn m n. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gtn_max m n1 n2 : (m > maxn n1 n2) = (m > n1) && (m > n2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma geq_max m n1 n2 : (m >= maxn n1 n2) = (m >= n1) && (m >= n2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma maxnSS m n : maxn m.+1 n.+1 = (maxn m n).+1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addn_maxl : left_distributive addn maxn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addn_maxr : right_distributive addn maxn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma subn_maxl : left_distributive subn maxn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma min0n : left_zero 0 minn. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma minn0 : right_zero 0 minn. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma minnC : commutative minn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addn_min_max m n : minn m n + maxn m n = m + n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma minnE m n : minn m n = m - (m - n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma minnAC : right_commutative minn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma minnA : associative minn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma minnCA : left_commutative minn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma minnACA : interchange minn minn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma minn_idPl {m n} : reflect (minn m n = m) (m <= n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma minn_idPr {m n} : reflect (minn m n = n) (m >= n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma minnn : idempotent minn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_min m n1 n2 : (m <= minn n1 n2) = (m <= n1) && (m <= n2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gtn_min m n1 n2 : (m > minn n1 n2) = (m > n1) || (m > n2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma geq_min m n1 n2 : (m >= minn n1 n2) = (m >= n1) || (m >= n2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma geq_minl m n : minn m n <= m. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma geq_minr m n : minn m n <= n. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addn_minr : right_distributive addn minn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addn_minl : left_distributive addn minn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma subn_minl : left_distributive subn minn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma minnSS m n : minn m.+1 n.+1 = (minn m n).+1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Quasi-cancellation (really, absorption) lemmas *)
Lemma maxnK m n : minn (maxn m n) m = m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma maxKn m n : minn n (maxn m n) = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma minnK m n : maxn (minn m n) m = m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma minKn m n : maxn n (minn m n) = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Distributivity. *)
Lemma maxn_minl : left_distributive maxn minn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma maxn_minr : right_distributive maxn minn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma minn_maxl : left_distributive minn maxn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma minn_maxr : right_distributive minn maxn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Comparison predicates. *)

Variant leq_xor_gtn m n : nat -> nat -> nat -> nat -> bool -> bool -> Set :=
  | LeqNotGtn of m <= n : leq_xor_gtn m n m m n n true false
  | GtnNotLeq of n < m  : leq_xor_gtn m n n n m m false true.

Lemma leqP m n : leq_xor_gtn m n (minn n m) (minn m n) (maxn n m) (maxn m n)
                                 (m <= n) (n < m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Variant ltn_xor_geq m n : nat -> nat -> nat -> nat -> bool -> bool -> Set :=
  | LtnNotGeq of m < n  : ltn_xor_geq m n m m n n false true
  | GeqNotLtn of n <= m : ltn_xor_geq m n n n m m true false.

Lemma ltnP m n : ltn_xor_geq m n (minn n m) (minn m n) (maxn n m) (maxn m n)
                                 (n <= m) (m < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Variant eqn0_xor_gt0 n : bool -> bool -> Set :=
  | Eq0NotPos of n = 0 : eqn0_xor_gt0 n true false
  | PosNotEq0 of n > 0 : eqn0_xor_gt0 n false true.

Lemma posnP n : eqn0_xor_gt0 n (n == 0) (0 < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Variant compare_nat m n : nat -> nat -> nat -> nat ->
                          bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | CompareNatLt of m < n :
      compare_nat m n m m n n false false false true false true
  | CompareNatGt of m > n :
      compare_nat m n n n m m false false true false true false
  | CompareNatEq of m = n :
      compare_nat m n m m m m true true true true false false.

Lemma ltngtP m n :
  compare_nat m n (minn n m) (minn m n) (maxn n m) (maxn m n)
                  (n == m) (m == n) (n <= m) (m <= n) (n < m) (m < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Eliminating the idiom for structurally decreasing compare and subtract. *)
Lemma subn_if_gt T m n F (E : T) :
  (if m.+1 - n is m'.+1 then F m' else E) = (if n <= m then F (m - n) else E).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Notation leqLHS := (X in (X <= _)%N)%pattern.
Notation leqRHS := (X in (_ <= X)%N)%pattern.
Notation ltnLHS := (X in (X < _)%N)%pattern.
Notation ltnRHS := (X in (_ < X)%N)%pattern.

(* Getting a concrete value from an abstract existence proof. *)

Section ExMinn.

Variable P : pred nat.
Hypothesis exP : exists n, P n.

Inductive acc_nat i : Prop := AccNat0 of P i | AccNatS of acc_nat i.+1.

Lemma find_ex_minn : {m | P m & forall n, P n -> n >= m}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition ex_minn := s2val find_ex_minn.

Inductive ex_minn_spec : nat -> Type :=
  ExMinnSpec m of P m & (forall n, P n -> n >= m) : ex_minn_spec m.

Lemma ex_minnP : ex_minn_spec ex_minn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End ExMinn.

Section ExMaxn.

Variables (P : pred nat) (m : nat).
Hypotheses (exP : exists i, P i) (ubP : forall i, P i -> i <= m).

Lemma ex_maxn_subproof : exists i, P (m - i).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition ex_maxn := m - ex_minn ex_maxn_subproof.

Variant ex_maxn_spec : nat -> Type :=
  ExMaxnSpec i of P i & (forall j, P j -> j <= i) : ex_maxn_spec i.

Lemma ex_maxnP : ex_maxn_spec ex_maxn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End ExMaxn.

Lemma eq_ex_minn P Q exP exQ : P =1 Q -> @ex_minn P exP = @ex_minn Q exQ.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma eq_ex_maxn (P Q : pred nat) m n exP ubP exQ ubQ :
  P =1 Q -> @ex_maxn P m exP ubP = @ex_maxn Q n exQ ubQ.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Section Iteration.

Variable T : Type.
Implicit Types m n : nat.
Implicit Types x y : T.
Implicit Types S : {pred T}.

Definition iter n f x :=
  let fix loop m := if m is i.+1 then f (loop i) else x in loop n.

Definition iteri n f x :=
  let fix loop m := if m is i.+1 then f i (loop i) else x in loop n.

Definition iterop n op x :=
  let f i y := if i is 0 then x else op x y in iteri n f.

Lemma iterSr n f x : iter n.+1 f x = iter n f (f x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma iterS n f x : iter n.+1 f x = f (iter n f x). Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma iterD n m f x : iter (n + m) f x = iter n f (iter m f x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma iteriS n f x : iteri n.+1 f x = f n (iteri n f x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma iteropS idx n op x : iterop n.+1 op x idx = iter n (op x) x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma eq_iter f f' : f =1 f' -> forall n, iter n f =1 iter n f'.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma iter_fix n f x : f x = x -> iter n f x = x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma eq_iteri f f' : f =2 f' -> forall n, iteri n f =1 iteri n f'.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma eq_iterop n op op' : op =2 op' -> iterop n op =2 iterop n op'.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma iter_in f S i : {homo f : x / x \in S} -> {homo iter i f : x / x \in S}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End Iteration.

Lemma iter_succn m n : iter n succn m = m + n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma iter_succn_0 n : iter n succn 0 = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma iter_predn m n : iter n predn m = m - n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Multiplication. *)

Definition muln_rec := mult.
Notation "m * n" := (muln_rec m n) : nat_rec_scope.

Definition muln := nosimpl muln_rec.
Notation "m * n" := (muln m n) : nat_scope.

Lemma multE : mult = muln.     Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma mulnE : muln = muln_rec. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mul0n : left_zero 0 muln.          Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma muln0 : right_zero 0 muln.         Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma mul1n : left_id 1 muln.            Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma mulSn m n : m.+1 * n = n + m * n.  Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma mulSnr m n : m.+1 * n = m * n + n. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulnS m n : m * n.+1 = m + m * n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma mulnSr m n : m * n.+1 = m * n + m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma iter_addn m n p : iter n (addn m) p = m * n + p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma iter_addn_0 m n : iter n (addn m) 0 = m * n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma muln1 : right_id 1 muln.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulnC : commutative muln.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulnDl : left_distributive muln addn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulnDr : right_distributive muln addn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulnBl : left_distributive muln subn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulnBr : right_distributive muln subn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulnA : associative muln.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulnCA : left_commutative muln.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulnAC : right_commutative muln.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulnACA : interchange muln muln.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma muln_eq0 m n : (m * n == 0) = (m == 0) || (n == 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma muln_eq1 m n : (m * n == 1) = (m == 1) && (n == 1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma muln_gt0 m n : (0 < m * n) = (0 < m) && (0 < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_pmull m n : n > 0 -> m <= n * m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_pmulr m n : n > 0 -> m <= m * n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_mul2l m n1 n2 : (m * n1 <= m * n2) = (m == 0) || (n1 <= n2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_mul2r m n1 n2 : (n1 * m <= n2 * m) = (m == 0) || (n1 <= n2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_mul m1 m2 n1 n2 : m1 <= n1 -> m2 <= n2 -> m1 * m2 <= n1 * n2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma eqn_mul2l m n1 n2 : (m * n1 == m * n2) = (m == 0) || (n1 == n2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma eqn_mul2r m n1 n2 : (n1 * m == n2 * m) = (m == 0) || (n1 == n2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_pmul2l m n1 n2 : 0 < m -> (m * n1 <= m * n2) = (n1 <= n2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Arguments leq_pmul2l [m n1 n2].

Lemma leq_pmul2r m n1 n2 : 0 < m -> (n1 * m <= n2 * m) = (n1 <= n2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Arguments leq_pmul2r [m n1 n2].

Lemma eqn_pmul2l m n1 n2 : 0 < m -> (m * n1 == m * n2) = (n1 == n2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Arguments eqn_pmul2l [m n1 n2].

Lemma eqn_pmul2r m n1 n2 : 0 < m -> (n1 * m == n2 * m) = (n1 == n2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Arguments eqn_pmul2r [m n1 n2].

Lemma ltn_mul2l m n1 n2 : (m * n1 < m * n2) = (0 < m) && (n1 < n2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_mul2r m n1 n2 : (n1 * m < n2 * m) = (0 < m) && (n1 < n2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_pmul2l m n1 n2 : 0 < m -> (m * n1 < m * n2) = (n1 < n2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Arguments ltn_pmul2l [m n1 n2].

Lemma ltn_pmul2r m n1 n2 : 0 < m -> (n1 * m < n2 * m) = (n1 < n2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Arguments ltn_pmul2r [m n1 n2].

Lemma ltn_Pmull m n : 1 < n -> 0 < m -> m < n * m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_Pmulr m n : 1 < n -> 0 < m -> m < m * n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_mul m1 m2 n1 n2 : m1 < n1 -> m2 < n2 -> m1 * m2 < n1 * n2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma maxnMr : right_distributive muln maxn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma maxnMl : left_distributive muln maxn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma minnMr : right_distributive muln minn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma minnMl : left_distributive muln minn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma iterM (T : Type) (n m : nat) (f : T -> T) :
  iter (n * m) f =1 iter n (iter m f).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Exponentiation. *)

Definition expn_rec m n := iterop n muln m 1.
Notation "m ^ n" := (expn_rec m n) : nat_rec_scope.
Definition expn := nosimpl expn_rec.
Notation "m ^ n" := (expn m n) : nat_scope.

Lemma expnE : expn = expn_rec. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma expn0 m : m ^ 0 = 1. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma expn1 m : m ^ 1 = m. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma expnS m n : m ^ n.+1 = m * m ^ n. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma expnSr m n : m ^ n.+1 = m ^ n * m. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma iter_muln m n p : iter n (muln m) p = m ^ n * p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma iter_muln_1 m n : iter n (muln m) 1 = m ^ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exp0n n : 0 < n -> 0 ^ n = 0. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exp1n n : 1 ^ n = 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma expnD m n1 n2 : m ^ (n1 + n2) = m ^ n1 * m ^ n2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma expnMn m1 m2 n : (m1 * m2) ^ n = m1 ^ n * m2 ^ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma expnM m n1 n2 : m ^ (n1 * n2) = (m ^ n1) ^ n2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma expnAC m n1 n2 : (m ^ n1) ^ n2 = (m ^ n2) ^ n1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma expn_gt0 m n : (0 < m ^ n) = (0 < m) || (n == 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma expn_eq0 m e : (m ^ e == 0) = (m == 0) && (e > 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_expl m n : 1 < m -> n < m ^ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_exp2l m n1 n2 : 1 < m -> (m ^ n1 <= m ^ n2) = (n1 <= n2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_exp2l m n1 n2 : 1 < m -> (m ^ n1 < m ^ n2) = (n1 < n2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma eqn_exp2l m n1 n2 : 1 < m -> (m ^ n1 == m ^ n2) = (n1 == n2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma expnI m : 1 < m -> injective (expn m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_pexp2l m n1 n2 : 0 < m -> n1 <= n2 -> m ^ n1 <= m ^ n2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_pexp2l m n1 n2 : 0 < m -> m ^ n1 < m ^ n2 -> n1 < n2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_exp2r m n e : e > 0 -> (m ^ e < n ^ e) = (m < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_exp2r m n e : e > 0 -> (m ^ e <= n ^ e) = (m <= n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma eqn_exp2r m n e : e > 0 -> (m ^ e == n ^ e) = (m == n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma expIn e : e > 0 -> injective (expn^~ e).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma iterX (T : Type) (n m : nat) (f : T -> T) :
  iter (n ^ m) f =1 iter m (iter n) f.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Factorial. *)

Fixpoint fact_rec n := if n is n'.+1 then n * fact_rec n' else 1.

Definition factorial := nosimpl fact_rec.

Notation "n `!" := (factorial n) (at level 2, format "n `!") : nat_scope.

Lemma factE : factorial = fact_rec. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma fact0 : 0`! = 1. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma factS n : (n.+1)`!  = n.+1 * n`!. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma fact_gt0 n : n`! > 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma fact_geq n : n <= n`!.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_fact m n : 0 < m -> m < n -> m`! < n`!.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Parity and bits. *)

Coercion nat_of_bool (b : bool) := if b then 1 else 0.

Lemma leq_b1 (b : bool) : b <= 1. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addn_negb (b : bool) : ~~ b + b = 1. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma eqb0 (b : bool) : (b == 0 :> nat) = ~~ b. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma eqb1 (b : bool) : (b == 1 :> nat) = b. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lt0b (b : bool) : (b > 0) = b. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sub1b (b : bool) : 1 - b = ~~ b. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulnb (b1 b2 : bool) : b1 * b2 = b1 && b2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulnbl (b : bool) n : b * n = (if b then n else 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulnbr (b : bool) n : n * b = (if b then n else 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fixpoint odd n := if n is n'.+1 then ~~ odd n' else false.

Lemma oddS n : odd n.+1 = ~~ odd n. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma oddb (b : bool) : odd b = b. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma oddD m n : odd (m + n) = odd m (+) odd n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma oddB m n : n <= m -> odd (m - n) = odd m (+) odd n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma oddN i m : odd m = false -> i <= m -> odd (m - i) = odd i.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma oddM m n : odd (m * n) = odd m && odd n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma oddX m n : odd (m ^ n) = (n == 0) || odd m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Doubling. *)

Fixpoint double_rec n := if n is n'.+1 then n'.*2%Nrec.+2 else 0
where "n .*2" := (double_rec n) : nat_rec_scope.

Definition double := nosimpl double_rec.
Notation "n .*2" := (double n) : nat_scope.

Lemma doubleE : double = double_rec. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma double0 : 0.*2 = 0. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma doubleS n : n.+1.*2 = n.*2.+2. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma double_pred n : n.-1.*2 = n.*2.-2. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addnn n : n + n = n.*2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mul2n m : 2 * m = m.*2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma muln2 m : m * 2 = m.*2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma doubleD m n : (m + n).*2 = m.*2 + n.*2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma doubleB m n : (m - n).*2 = m.*2 - n.*2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_double m n : (m.*2 <= n.*2) = (m <= n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_double m n : (m.*2 < n.*2) = (m < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_Sdouble m n : (m.*2.+1 < n.*2) = (m < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_Sdouble m n : (m.*2 <= n.*2.+1) = (m <= n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma odd_double n : odd n.*2 = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma double_gt0 n : (0 < n.*2) = (0 < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma double_eq0 n : (n.*2 == 0) = (n == 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma doubleMl m n : (m * n).*2 = m.*2 * n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma doubleMr m n : (m * n).*2 = m * n.*2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Halving. *)

Fixpoint half (n : nat) : nat := if n is n'.+1 then uphalf n' else n
with   uphalf (n : nat) : nat := if n is n'.+1 then n'./2.+1 else n
where "n ./2" := (half n) : nat_scope.

Lemma uphalfE n : uphalf n = n.+1./2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma doubleK : cancel double half.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition half_double := doubleK.
Definition double_inj := can_inj doubleK.

Lemma uphalf_double n : uphalf n.*2 = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma uphalf_half n : uphalf n = odd n + n./2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma odd_double_half n : odd n + n./2.*2 = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma halfK n : n./2.*2 = n - odd n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma uphalfK n : (uphalf n).*2 = odd n + n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma odd_halfK n : odd n -> n./2.*2 = n.-1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma even_halfK n : ~~ odd n -> n./2.*2 = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma odd_uphalfK n : odd n -> (uphalf n).*2 = n.+1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma even_uphalfK n : ~~ odd n -> (uphalf n).*2 = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma half_bit_double n (b : bool) : (b + n.*2)./2 = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma halfD m n : (m + n)./2 = (odd m && odd n) + (m./2 + n./2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma half_leq m n : m <= n -> m./2 <= n./2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma geq_half_double m n : (m <= n./2) = (m.*2 <= n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_half_double m n : (m./2 < n) = (m < n.*2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_half_double m n : (m./2 <= n) = (m <= n.*2.+1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gtn_half_double m n : (n < m./2) = (n.*2.+1 < m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma half_gt0 n : (0 < n./2) = (1 < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma uphalf_leq m n : m <= n -> uphalf m <= uphalf n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_uphalf_double m n : (uphalf m <= n) = (m <= n.*2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma geq_uphalf_double m n : (m <= uphalf n) = (m.*2 <= n.+1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gtn_uphalf_double m n : (n < uphalf m) = (n.*2 < m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_uphalf_double m n : (uphalf m < n) = (m.+1 < n.*2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma uphalf_gt0 n : (0 < uphalf n) = (0 < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma odd_geq m n : odd n -> (m <= n) = (m./2.*2 <= n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma odd_ltn m n : odd n -> (n < m) = (n < m./2.*2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma odd_gt0 n : odd n -> n > 0. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma odd_gt2 n : odd n -> n > 1 -> n > 2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Squares and square identities. *)

Lemma mulnn m : m * m = m ^ 2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrnD m n : (m + n) ^ 2 = m ^ 2 + n ^ 2 + 2 * (m * n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrnB m n : n <= m -> (m - n) ^ 2 = m ^ 2 + n ^ 2 - 2 * (m * n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrnD_sub m n : n <= m -> (m + n) ^ 2 - 4 * (m * n) = (m - n) ^ 2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma subn_sqr m n : m ^ 2 - n ^ 2 = (m - n) * (m + n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_sqr m n : (m ^ 2 < n ^ 2) = (m < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_sqr m n : (m ^ 2 <= n ^ 2) = (m <= n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrn_gt0 n : (0 < n ^ 2) = (0 < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma eqn_sqr m n : (m ^ 2 == n ^ 2) = (m == n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrn_inj : injective (expn ^~ 2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Almost strict inequality: an inequality that is strict unless some    *)
(* specific condition holds, such as the Cauchy-Schwartz or the AGM      *)
(* inequality (we only prove the order-2 AGM here; the general one       *)
(* requires sequences).                                                  *)
(*   We formalize the concept as a rewrite multirule, that can be used   *)
(* both to rewrite the non-strict inequality to true, and the equality   *)
(* to the specific condition (for strict inequalities use the ltn_neqAle *)
(* lemma); in addition, the conditional equality also coerces to a       *)
(* non-strict one.                                                       *)

Definition leqif m n C := ((m <= n) * ((m == n) = C))%type.

Notation "m <= n ?= 'iff' C" := (leqif m n C) : nat_scope.

Coercion leq_of_leqif m n C (H : m <= n ?= iff C) := H.1 : m <= n.

Lemma leqifP m n C : reflect (m <= n ?= iff C) (if C then m == n else m < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leqif_refl m C : reflect (m <= m ?= iff C) C.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leqif_trans m1 m2 m3 C12 C23 :
  m1 <= m2 ?= iff C12 -> m2 <= m3 ?= iff C23 -> m1 <= m3 ?= iff C12 && C23.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mono_leqif f : {mono f : m n / m <= n} ->
  forall m n C, (f m <= f n ?= iff C) = (m <= n ?= iff C).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leqif_geq m n : m <= n -> m <= n ?= iff (m >= n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leqif_eq m n : m <= n -> m <= n ?= iff (m == n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma geq_leqif a b C : a <= b ?= iff C -> (b <= a) = C.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_leqif a b C : a <= b ?= iff C -> (a < b) = ~~ C.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltnNleqif x y C : x <= y ?= iff ~~ C -> (x < y) = C.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma eq_leqif x y C : x <= y ?= iff C -> (x == y) = C.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma eqTleqif x y C : x <= y ?= iff C -> C -> x = y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leqif_add m1 n1 C1 m2 n2 C2 :
    m1 <= n1 ?= iff C1 -> m2 <= n2 ?= iff C2 ->
  m1 + m2 <= n1 + n2 ?= iff C1 && C2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leqif_mul m1 n1 C1 m2 n2 C2 :
    m1 <= n1 ?= iff C1 -> m2 <= n2 ?= iff C2 ->
  m1 * m2 <= n1 * n2 ?= iff (n1 * n2 == 0) || (C1 && C2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nat_Cauchy m n : 2 * (m * n) <= m ^ 2 + n ^ 2 ?= iff (m == n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nat_AGM2 m n : 4 * (m * n) <= (m + n) ^ 2 ?= iff (m == n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Section ContraLeq.
Implicit Types (b : bool) (m n : nat) (P : Prop).

Lemma contraTleq b m n : (n < m -> ~~ b) -> (b -> m <= n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma contraTltn b m n : (n <= m -> ~~ b) -> (b -> m < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma contraPleq P m n : (n < m -> ~ P) -> (P -> m <= n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma contraPltn P m n : (n <= m -> ~ P) -> (P -> m < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma contraNleq b m n : (n < m -> b) -> (~~ b -> m <= n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma contraNltn b m n : (n <= m -> b) -> (~~ b -> m < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma contra_not_leq P m n : (n < m -> P) -> (~ P -> m <= n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma contra_not_ltn P m n : (n <= m -> P) -> (~ P -> m < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma contraFleq b m n : (n < m -> b) -> (b = false -> m <= n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma contraFltn b m n : (n <= m -> b) -> (b = false -> m < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma contra_leqT b m n : (~~ b -> m < n) -> (n <= m -> b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma contra_ltnT b m n : (~~ b -> m <= n) -> (n < m -> b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma contra_leqN b m n : (b -> m < n) -> (n <= m -> ~~ b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma contra_ltnN b m n : (b -> m <= n) -> (n < m -> ~~ b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma contra_leq_not P m n : (P -> m < n) -> (n <= m -> ~ P).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma contra_ltn_not P m n : (P -> m <= n) -> (n < m -> ~ P).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma contra_leqF b m n : (b -> m < n) -> (n <= m -> b = false).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma contra_ltnF b m n : (b -> m <= n) -> (n < m -> b = false).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma contra_leq m n p q : (q < p -> n < m) -> (m <= n -> p <= q).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma contra_leq_ltn m n p q : (q <= p -> n < m) -> (m <= n -> p < q).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma contra_ltn_leq m n p q : (q < p -> n <= m) -> (m < n -> p <= q).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma contra_ltn m n p q : (q <= p -> n <= m) -> (m < n -> p < q).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End ContraLeq.

Section Monotonicity.
Variable T : Type.

Lemma homo_ltn_in (D : {pred nat}) (f : nat -> T) (r : T -> T -> Prop) :
  (forall y x z, r x y -> r y z -> r x z) ->
  {in D &, forall i j k, i < k < j -> k \in D} ->
  {in D, forall i, i.+1 \in D -> r (f i) (f i.+1)} ->
  {in D &, {homo f : i j / i < j >-> r i j}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma homo_ltn (f : nat -> T) (r : T -> T -> Prop) :
  (forall y x z, r x y -> r y z -> r x z) ->
  (forall i, r (f i) (f i.+1)) -> {homo f : i j / i < j >-> r i j}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma homo_leq_in (D : {pred nat}) (f : nat -> T) (r : T -> T -> Prop) :
  (forall x, r x x) -> (forall y x z, r x y -> r y z -> r x z) ->
  {in D &, forall i j k, i < k < j -> k \in D} ->
  {in D, forall i, i.+1 \in D -> r (f i) (f i.+1)} ->
  {in D &, {homo f : i j / i <= j >-> r i j}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma homo_leq (f : nat -> T) (r : T -> T -> Prop) :
   (forall x, r x x) -> (forall y x z, r x y -> r y z -> r x z) ->
  (forall i, r (f i) (f i.+1)) -> {homo f : i j / i <= j >-> r i j}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Section NatToNat.
Variable (f : nat -> nat).

(****************************************************************************)
(* This listing of "Let"s factor out the required premises for the          *)
(* subsequent lemmas, putting them in the context so that "done" solves the *)
(* goals quickly                                                            *)
(****************************************************************************)

Let ltn_neqAle := ltn_neqAle.
Let gtn_neqAge x y : (y < x) = (x != y) && (y <= x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Let anti_leq := anti_leq.
Let anti_geq : antisymmetric geq.
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Let leq_total := leq_total.

Lemma ltnW_homo : {homo f : m n / m < n} -> {homo f : m n / m <= n}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_homo_ltn : injective f -> {homo f : m n / m <= n} ->
  {homo f : m n / m < n}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltnW_nhomo : {homo f : m n /~ m < n} -> {homo f : m n /~ m <= n}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_nhomo_ltn : injective f -> {homo f : m n /~ m <= n} ->
  {homo f : m n /~ m < n}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma incn_inj : {mono f : m n / m <= n} -> injective f.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma decn_inj : {mono f : m n /~ m <= n} -> injective f.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leqW_mono : {mono f : m n / m <= n} -> {mono f : m n / m < n}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leqW_nmono : {mono f : m n /~ m <= n} -> {mono f : m n /~ m < n}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_mono : {homo f : m n / m < n} -> {mono f : m n / m <= n}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_nmono : {homo f : m n /~ m < n} -> {mono f : m n /~ m <= n}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Variables (D D' : {pred nat}).

Lemma ltnW_homo_in : {in D & D', {homo f : m n / m < n}} ->
  {in D & D', {homo f : m n / m <= n}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltnW_nhomo_in : {in D & D', {homo f : m n /~ m < n}} ->
                 {in D & D', {homo f : m n /~ m <= n}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_homo_ltn_in : {in D & D', injective f} ->
                        {in D & D', {homo f : m n / m <= n}} ->
  {in D & D', {homo f : m n / m < n}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma inj_nhomo_ltn_in : {in D & D', injective f} ->
                        {in D & D', {homo f : m n /~ m <= n}} ->
  {in D & D', {homo f : m n /~ m < n}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma incn_inj_in : {in D &, {mono f : m n / m <= n}} ->
  {in D &, injective f}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma decn_inj_in : {in D &, {mono f : m n /~ m <= n}} ->
  {in D &, injective f}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leqW_mono_in : {in D &, {mono f : m n / m <= n}} ->
  {in D &, {mono f : m n / m < n}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leqW_nmono_in : {in D &, {mono f : m n /~ m <= n}} ->
  {in D &, {mono f : m n /~ m < n}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_mono_in : {in D &, {homo f : m n / m < n}} ->
  {in D &, {mono f : m n / m <= n}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_nmono_in : {in D &, {homo f : m n /~ m < n}} ->
  {in D &, {mono f : m n /~ m <= n}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End NatToNat.
End Monotonicity.

Lemma leq_pfact : {in [pred n | 0 < n] &, {mono factorial : m n / m <= n}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_fact : {homo factorial : m n / m <= n}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltn_pfact : {in [pred n | 0 < n] &, {mono factorial : m n / m < n}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Support for larger integers. The normal definitions of +, - and even  *)
(* IO are unsuitable for Peano integers larger than 2000 or so because   *)
(* they are not tail-recursive. We provide a workaround module, along    *)
(* with a rewrite multirule to change the tailrec operators to the       *)
(* normal ones. We handle IO via the NatBin module, but provide our      *)
(* own (more efficient) conversion functions.                            *)

Module NatTrec.

(*   Usage:                                             *)
(*     Import NatTrec.                                  *)
(*        in section defining functions, rebinds all    *)
(*        non-tail recursive operators.                 *)
(*     rewrite !trecE.                                  *)
(*        in the correctness proof, restores operators  *)

Fixpoint add m n := if m is m'.+1 then m' + n.+1 else n
where "n + m" := (add n m) : nat_scope.

Fixpoint add_mul m n s := if m is m'.+1 then add_mul m' n (n + s) else s.

Definition mul m n := if m is m'.+1 then add_mul m' n n else 0.

Notation "n * m" := (mul n m) : nat_scope.

Fixpoint mul_exp m n p := if n is n'.+1 then mul_exp m n' (m * p) else p.

Definition exp m n := if n is n'.+1 then mul_exp m n' m else 1.

Notation "n ^ m" := (exp n m) : nat_scope.

Local Notation oddn := odd.
Fixpoint odd n := if n is n'.+2 then odd n' else eqn n 1.

Local Notation doublen := double.
Definition double n := if n is n'.+1 then n' + n.+1 else 0.
Notation "n .*2" := (double n) : nat_scope.

Lemma addE : add =2 addn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma doubleE : double =1 doublen.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma add_mulE n m s : add_mul n m s = addn (muln n m) s.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulE : mul =2 muln.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mul_expE m n p : mul_exp m n p = muln (expn m n) p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma expE : exp =2 expn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma oddE : odd =1 oddn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition trecE := (addE, (doubleE, oddE), (mulE, add_mulE, (expE, mul_expE))).

End NatTrec.

Notation natTrecE := NatTrec.trecE.

Lemma eq_binP : Equality.axiom N.eqb.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Canonical bin_nat_eqMixin := EqMixin eq_binP.
Canonical bin_nat_eqType := Eval hnf in EqType N bin_nat_eqMixin.

Arguments N.eqb !n !m.

Section NumberInterpretation.

Import BinPos.

Section Trec.

Import NatTrec.

Fixpoint nat_of_pos p0 :=
  match p0 with
  | xO p => (nat_of_pos p).*2
  | xI p => (nat_of_pos p).*2.+1
  | xH   => 1
  end.

End Trec.

Local Coercion nat_of_pos : positive >-> nat.

Coercion nat_of_bin b := if b is Npos p then p : nat else 0.

Fixpoint pos_of_nat n0 m0 :=
  match n0, m0 with
  | n.+1, m.+2 => pos_of_nat n m
  | n.+1,    1 => xO (pos_of_nat n n)
  | n.+1,    0 => xI (pos_of_nat n n)
  |    0,    _ => xH
  end.

Definition bin_of_nat n0 := if n0 is n.+1 then Npos (pos_of_nat n n) else 0%num.

Lemma bin_of_natK : cancel bin_of_nat nat_of_bin.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nat_of_binK : cancel nat_of_bin bin_of_nat.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nat_of_succ_pos p : Pos.succ p = p.+1 :> nat.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nat_of_add_pos p q : (p + q)%positive = p + q :> nat.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nat_of_mul_pos p q : (p * q)%positive = p * q :> nat.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nat_of_add_bin b1 b2 : (b1 + b2)%num = b1 + b2 :> nat.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nat_of_mul_bin b1 b2 : (b1 * b2)%num = b1 * b2 :> nat.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nat_of_exp_bin n (b : N) : n ^ b = pow_N 1 muln n b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End NumberInterpretation.

(* Big(ger) nat IO; usage:                              *)
(*     Num 1 072 399                                    *)
(*        to create large numbers for test cases        *)
(* Eval compute in [Num of some expression]             *)
(*        to display the result of an expression that   *)
(*        returns a larger integer.                     *)

Record number : Type := Num {bin_of_number :> N}.

Definition extend_number (nn : number) m := Num (nn * 1000 + bin_of_nat m).

Coercion extend_number : number >-> Funclass.

Canonical number_subType := [newType for bin_of_number].
Definition number_eqMixin := Eval hnf in [eqMixin of number by <:].
Canonical number_eqType := Eval hnf in EqType number number_eqMixin.

Notation "[ 'Num' 'of' e ]" := (Num (bin_of_nat e))
  (at level 0, format "[ 'Num'  'of'  e ]") : nat_scope.

(* Interface to ring/ring_simplify tactics *)

Lemma nat_semi_ring : semi_ring_theory 0 1 addn muln (@eq _).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nat_semi_morph :
  semi_morph 0 1 addn muln (@eq _) 0%num 1%num Nplus Nmult pred1 nat_of_bin.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nat_power_theory : power_theory 1 muln (@eq _) nat_of_bin expn.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Interface to the ring tactic machinery. *)

Fixpoint pop_succn e := if e is e'.+1 then fun n => pop_succn e' n.+1 else id.

Ltac pop_succn e := eval lazy beta iota delta [pop_succn] in (pop_succn e 1).

Ltac nat_litteral e :=
  match pop_succn e with
  | ?n.+1 => constr: (bin_of_nat n)
  |     _ => NotConstant
  end.

Ltac succn_to_add :=
  match goal with
  | |- context G [?e.+1] =>
    let x := fresh "NatLit0" in
    match pop_succn e with
    | ?n.+1 => pose x := n.+1; let G' := context G [x] in change G'
    | _ ?e' ?n => pose x := n; let G' := context G [x + e'] in change G'
    end; succn_to_add; rewrite {}/x
  | _ => idtac
  end.

Add Ring nat_ring_ssr : nat_semi_ring (morphism nat_semi_morph,
   constants [nat_litteral], preprocess [succn_to_add],
   power_tac nat_power_theory [nat_litteral]).

(* A congruence tactic, similar to the boolean one, along with an .+1/+  *)
(* normalization tactic.                                                 *)

Ltac nat_norm :=
  succn_to_add; rewrite ?add0n ?addn0 -?addnA ?(addSn, addnS, add0n, addn0).

Ltac nat_congr := first
 [ apply: (congr1 succn _)
 | apply: (congr1 predn _)
 | apply: (congr1 (addn _) _)
 | apply: (congr1 (subn _) _)
 | apply: (congr1 (addn^~ _) _)
 | match goal with |- (?X1 + ?X2 = ?X3) =>
     symmetry;
     rewrite -1?(addnC X1) -?(addnCA X1);
     apply: (congr1 (addn X1) _);
     symmetry
   end ].

