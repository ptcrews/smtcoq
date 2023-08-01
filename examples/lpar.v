(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2022                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


(* [Require Import SMTCoq.SMTCoq.] loads the SMTCoq library.
   If you are using native-coq instead of Coq 8.11, replace it with:
     Require Import SMTCoq.
   *)
Require Import SMTCoq.SMTCoq.
Require Import Bool.

Require Import ZArith.

Import BVList.BITVECTOR_LIST.
Local Open Scope bv_scope.

Import FArray.
Local Open Scope farray_scope.

Local Open Scope int63_scope.
Local Open Scope Z_scope.

Goal forall (x y z: Z),
    x = y + 1 -> y * z = z * (x - 1).
Proof.
(* smt. *)
Admitted.

Definition mul' := Z.mul.
Notation "x *' y" := (mul' x y) (at level 1).

Goal forall (x y : Z),
  x = y + 1 -> x * x = (y + 1) * x.
Proof. (* smt. *) Admitted.

Goal forall (x y : Z),
  x = y + 1 -> x *' x = (y + 1) *' x.
Proof. smt. Qed.

Goal forall (x y z: Z),
    x = y + 1 -> y *' z = z *' (x - 1).
Proof. (* smt.
CVC4 returned sat. Here is the model:
x := 0
y := -1
z := 1
mul' := fun BOUND_VARIABLE_335 BOUND_VARIABLE_336 => if BOUND_VARIABLE_335 = 1 then if BOUND_VARIABLE_336 = -1 then -2 else 2 else 2 *)
(* 
1. time abduce 3. (with latest cvc5, no ite and or, and core-connective on by default)
Tactic call ran for 14.386 secs (0.016u,0.021s) (failure)
cvc5 returned SAT.
The solver cannot prove the goal, but one 
 of the following hypotheses would make it provable:
z = y
x - 1 = z
(mul' y z) = (mul' z y)

2. time abduce 3. (* with cvc5 previous where grammar has both ITE and OR *)
Tactic call ran for 15.278 secs (0.014u,0.02s) (failure)
cvc5 returned SAT.
The solver cannot prove the goal, but one 
 of the following hypotheses would make it provable:
y = z
z + 1 = x
(multi z y) = (multi y z) 

3. time abduce 4. (* with cvc5-lpar23 where grammar doesn't have ITE *)
Tactic call ran for 28.931 secs (0.02u,0.026s) (failure)
cvc5 returned SAT.
The solver cannot prove the goal, but one 
 of the following hypotheses would make it provable:
y = z
z + 1 = x
x <= y || y = z
(multi y z) = (multi z y)

4. time abduce 3. (* with cvc5-noSygusIte where grammar doesn't have ITE 
and OR *)
Tactic call ran for 20.388 secs (0.007u,0.035s) (failure)
cvc5 returned SAT.
The solver cannot prove the goal, but one 
 of the following hypotheses would make it provable:
y = z
-1 + x = z
(multi z y) = (multi y z) *)
Search (_ * _ = _ * _).
intros. assert ((z *' y) = (y *' z)). 
{ apply Z.mul_comm. } smt.
Qed.

(* Search (_ * _ = _). Search Z.max.
Lemma inj_max n m : 0<=n -> 0<=m ->
 Z.abs_N (Z.max n m) = N.max (Z.abs_N n) (Z.abs_N m).
Proof. (* abduce 3. *)
 intros. rewrite !abs_N_nonneg; trivial. now apply Z2N.inj_max.
 transitivity n; trivial. apply Z.le_max_l.
Qed.*)

(* Require Import List.
Local Open Scope list_scope.
Goal forall (a : A) (l : list A), a :: l ++ [] = [a] -> a :: l = [a].
Proof. (* cvc5_abduct 3.
[] = l
((app (A:=A)) l []) = l
(cons a []) = (cons a l) *)
pose proof app_nil_r. smt.
(* "Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")." *)*)

Goal forall
    (x y: Z),
    x = y + 1 -> x *' y = (x - 1) *' x.
Proof.
(* 
time abduce 1.
Tactic call ran for 1.609 secs (0.017u,0.025s) (failure)
cvc5 returned SAT.
The solver cannot prove the goal, but one 
 of the following hypotheses would make it provable:
(mul' y x) = (mul' x y)

time abduce 2.
Tactic call ran for 44.092 secs (0.007u,0.028s) (failure)
cvc5 returned SAT.
The solver cannot prove the goal, but one 
 of the following hypotheses would make it provable:
(mul' y x) = (mul' x y)
(mul' x - 1 x) = (mul' x y)
Qed.
*)