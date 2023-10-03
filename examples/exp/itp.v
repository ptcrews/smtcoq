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

Local Open Scope list_scope.
Import ListNotations.
Variable A : Type.
Goal forall (x : A) (l : list A), [] <> x :: l.
(*
  abduce 1.
  (not (cons x l) = [])
  Takes over ten seconds to find over 1 abduct.
*)
Admitted.

(* #1 From paper *)
Goal forall (x y z : Z), 0 <= y ->  0 <= x + y + z.
Proof. idtac. Print all.
  (*abduce 5.*)
  intros. assert (0 <= z + x). { admit. } smt (H, H0).
  (* cvc5 returned SAT. The goal is invalid, but one of the
     following hypotheses would allow cvc5 to prove the goal:
      z + x = y
      x + y + z = 0
      1 <= z + x
      0 <= z + x
      y <= z + x
      z + x = 1
      z + x = 0 *)
Admitted.
(* With abduct *)
Goal forall (x y z : Z), 0 <= y -> 0 <= x + z -> 0 <= x + y + z.
Proof.
  verit.
Qed.

(* #2 Commutativity *)
Section Comm.
Variable f : Z -> Z -> Z.
Goal forall (x y : Z), (f x y) >= 0 -> (f y x) >= 0.
Proof.
  (* abduce 5. *)
  (* cvc5 returned SAT. The goal is invalid, but one of the
     following hypotheses would allow cvc5 to prove the goal:
      x = y
      (f y x) = 1 + 1
      (f x y) = (f y x)
      1 <= (f y x)
      0 <= (f y x)
      (f y x) = 1
      (f y x) = 0 *)
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
  (* abduce 5. *)
  (* cvc5 returned SAT. The goal is invalid, but one of the
     following hypotheses would allow cvc5 to prove the goal:
      x = y
      (f y x) = 1 + 1
      (f x y) = (f y x)
      1 <= (f y x)
      0 <= (f y x)
      (f y x) = 1
      (f y x) = 0 *)
  assert (f x y = f y x). { apply commf. }
  verit H.
Qed.

(*Takes too long
Goal forall (x y : Z), (f x y) + 2 - y >= 0 -> 
  (f y x)  + 2 - y >= 0.
Proof.
  cvc4_abduct.

Goal forall (x y : Z), (f x y) + 2*x - y >= 0 -> 
  (f y x)  + 2*x - y >= 0.
Proof.
  cvc4_abduct.*)

End Comm.

(* Trans *)
Goal forall (x y z : Z), x <= y -> x <= z.
Proof.
  (* abduce 5. *)
  (* cvc5 returned SAT. The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
      z = x
      y + 1 <= z
      y + 1 = z
      x + 1 = z
      y <= z
      x <= z
      z = y *)
Admitted.

Goal forall (a b c d : Z), a <= c -> a + b <= c + d.
Proof.
  (* abduce 5. *)
  (* cvc5 returned SAT. The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
      d = b
      d + c = b + a
      d + a = b + c
      1 + 1 + b = d
      b + 1 <= d
      b + 1 = d
      b <= d *)
Admitted.

Goal forall (a b c d : bool), (implb a b) && (implb c d) 
  -> (*a && c ->*) b && d.
Proof. 
  (* abduce 5. *)
  (* cvc5 returned SAT. The goal is invalid, but one of the following hypotheses would allow cvc5 to prove the goal:
      a && c
      b && d && a
      b && c && a
      c && d && a
      b && d
      b && c
      a && d*)
Admitted.
