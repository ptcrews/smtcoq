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

(*
Section TestBvConst.
  Verit_Checker "./testbvconst.smt2" "./testbvconst.vtlog".
End TestBvConst.

Section TestBvNot.
  Verit_Checker "./testbvnot.smt2" "./testbvnot.vtlog".
End TestBvNot.

Section TestBvAnd.
  Verit_Checker "./testbvand.smt2" "./testbvand.vtlog".
End TestBvAnd.

Section TestBitOf.
  Verit_Checker "./testbitof.smt2" "./testbitof.vtlog".
End TestBitOf.
 *)

Section TestBv2.
  Verit_Checker_Debug "./testbv2.1.smt2" "./testbv2.1.vtlog".
End TestBv2.

Section TestBv2.
  Verit_Checker_Debug "./testbv2.smt2" "./testbv2.vtlog".
End TestBv2.

(*
Section TestBv1.
  Verit_Checker_Debug "./tmptest.smt2" "./tmptest.vtlog".
End TestBv1.
*)
