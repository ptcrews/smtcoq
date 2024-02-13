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

Add Rec LoadPath "../../../src" as SMTCoq.

Require Import SMTCoq.SMTCoq.
Require Import Bool.

Require Import ZArith.
Require Import Int31.

Local Open Scope int31_scope.

Section TestDistElim1.
     Verit_Checker "./testdistelim_1.smt2" "./testdistelim_1.vtlog".
End TestDistElim1.

(*
  TODO: The following tests segfault; figure out why.
Section TestDistElim2.
     Verit_Checker "./testdistelim_2.smt2" "./testdistelim_2.vtlog".
End TestDistElim2.

Section TestDistElim3.
     Verit_Checker "./testdistelim_3.smt2" "./testdistelim_3.vtlog".
End TestDistElim3.
 *)

Section TestDistElim_Formula.
     Fail Verit_Checker "./testdistelim_formula.smt2" "./testdistelim_formula.vtlog".
End TestDistElim_Formula.
