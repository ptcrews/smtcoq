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
Goal forall (x y z : Z), y >= 0 -> x + y + z >= 0.
Proof.
  cvc4.
  (* smt.
     CVC4 returned sat. Here is the model:
     x := 0
     y := 0
     z := -1 *)
Admitted.
(* With abduct *)
(*Goal forall (x y z : Z), y >= 0 -> x + z >= 0 -> x + y + z >= 0.
Proof.
  smt.
Qed.

(* #2 Commutativity *)
Variable f : Z -> Z -> Z.
Goal forall (x y : Z), (f x y) >= 0 -> (f y x) >= 0.
Proof.
  (* smt.
     CVC4 returned sat. Here is the model:
     x := 2
     y := 1
     f := fun BOUND_VARIABLE_298 BOUND_VARIABLE_299 => 
          if BOUND_VARIABLE_298 = 2 then 
            if BOUND_VARIABLE_299 = 1 then 0 else -1 
          else -1 *)
Admitted.
(* With abduct *)
Goal forall (x y : Z), (f x y) >= 0 -> (f x y = f y x)
      -> (f y x) >= 0.
Proof.
  smt.
Qed.*)