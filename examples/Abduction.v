(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2021                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


(* [Require Import SMTCoq.SMTCoq.] loads the SMTCoq library.
   If you are using native-coq instead of Coq 8.9, replace it with:
     Require Import SMTCoq.
   *)
Add Rec LoadPath "/home/arjun/Desktop/smtcoq/abduction-arjunvish-smtcoq/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.

Require Import ZArith.

Import BVList.BITVECTOR_LIST.
Local Open Scope bv_scope.

Import FArray.
Local Open Scope farray_scope.

(* Examples that check ZChaff certificates *)

Local Open Scope int63_scope.

(* Abduction examples *)
Local Open Scope Z_scope.

(* #1 From paper *)
Goal forall (x y z : Z), y >= 0  ->  x + y + z >= 0.
Proof. 
  (*cvc4_abduct.*)
  (* cvc5 returned SAT. The goal is invalid, but one of the
     following hypotheses would allow cvc5 to prove the goal:
      z + x = y
      z + x = 0
      z + x = 1
      y <= z + x
      0 <= z + x *)
Admitted.
(* With abduct *)
Goal forall (x y z : Z), y >= 0 -> x + z >= 0 -> x + y + z >= 0.
Proof.
  verit.
Qed.

(* #2 Commutativity *)
Variable f : Z -> Z -> Z.
Goal forall (x y : Z), (f x y) >= 0 -> (f y x) >= 0.
Proof.
  (* cvc4_abduct. *)
  (* cvc5 returned SAT. The goal is invalid, but one of the
     following hypotheses would allow cvc5 to prove the goal:
      x = y
      (f y x) = 0
      (f y x) = 1
      0 <= (f y x)
      1 <= (f y x) *)
Admitted.
(* With abduct *)
Goal forall (x y : Z), (f x y) >= 0 -> (f x y = f y x)
      -> (f y x) >= 0.
Proof.
  verit.
Qed.


(* Possible usage *)
Variables (x y z : Z).
Theorem commf : forall x y, f x y = f y x.
Admitted.
Variable H : f x y >= 0.
Goal f y x >= 0.
Proof.
  (* cvc4_abduct H. *)
  (* cvc5 returned SAT. The goal is invalid, but one of the
     following hypotheses would allow cvc5 to prove the goal:
      x = y
      (f y x) = 0
      (f y x) = 1
      0 <= (f y x)
      1 <= (f y x) *)
  assert (f x y = f y x). { apply commf. }
  verit H.
Qed.