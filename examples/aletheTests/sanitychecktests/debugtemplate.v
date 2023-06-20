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
Add Rec LoadPath "/home/arjun/Desktop/smtcoq-veritAst/smtcoq/src" as SMTCoq.

Require Import SMTCoq.SMTCoq.
Require Import Bool.

Require Import ZArith.
Require Import Int31.

Import BVList.BITVECTOR_LIST.
Local Open Scope bv_scope.

Import FArray.
Local Open Scope farray_scope.

(* Examples that check ZChaff certificates *)

(*Local Open Scope int63_scope.*)
Local Open Scope int31_scope.
Local Open Scope array_scope.
   
Section Checker_SmtEx1Debug.
  Parse_certif_verit t_i1 t_func1 t_atom1 t_form1 root1 used_roots1 trace1 
  "/home/arjun/Desktop/smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test1.smt2" 
  "/home/arjun/Desktop/smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test1.pf".
  (*
  Structures_standard.v
  ---------------------
  Definition trace (step:Type) := ((list step) * step)%type.

  Trace.v
  -------
  Definition _trace_ := Structures.trace step.

  Inductive certif :=
  | Certif : int -> _trace_ step -> int -> certif.
  *)
  Print trace1. 
  
  (* Components of the certificate *)
  Definition nclauses1 := Eval vm_compute in (match trace1 with Certif a _ _ => a end). (* Size of the state *)
  Print nclauses1. (* 5 *)
  Definition c1 := Eval vm_compute in (match trace1 with Certif _ a _ => a end). (* Certificate *)
  Print c1.
  Definition conf1 := Eval vm_compute in (match trace1 with Certif _ _ a => a end). (* Look here in the state for the empty clause*)
  Print conf1. (* 2 *)
  Eval vm_compute in List.length (fst c1).
  (* 37 steps in the certificate *)

  (* Certif after process_proj (from veritAst):
      (h1, AssumeAST, (cl  ((and  (true) (not (true))))), [], [])
      (t2, AndnAST, (cl  ((and  (not (true)) (not (false)))) ((not (not (true)))) ((false))), [], [])
      (t3, CongAST, (cl  (((and  (true) (not (true))) = (and  (true) (false))))), [ t2], [])
      (x18, AndnAST, (cl  ((and  (and  (true) (false)) (not (and  (false))))) ((not (and  (true) (false)))) ((and  (false)))), [], [])
      (x19, AndnAST, (cl  ((and  (and  (false)) (not (and  (true) (false))))) ((not (and  (false)))) ((and  (true) (false)))), [], [])
      (x20, Equn1AST, (cl  (((and  (true) (false)) = (and  (false)))) ((not (and  (true) (false)))) ((not (and  (false))))), [], [])
      (t4, ResoAST, (cl  ((and  (and  (true) (false)) (not (and  (false))))) ((and  (and  (false)) (not (and  (true) (false))))) (((and  (true) (false)) = (and  (false))))), [ x20 x18 x19], [])
      (t5, AndnAST, (cl  ((and  (and  (false)) (not (false)))) ((not (and  (false)))) ((false))), [], [])
      (t6, TransAST, (cl  (((and  (true) (not (true))) = (false)))), [ t3 t4 t5], [])
      (t7, Equp2AST, (cl  ((not ((and  (true) (not (true))) = (false)))) ((not (and  (true) (not (true))))) ((false))), [], [])
      (t8, ThresoAST, (cl  ((false))), [ h1 t6 t7], [])
      (t9, FalsAST, (cl  ((not (false)))), [], [])
      (t10, ResoAST, (cl ), [ t8 t9], [])
      (x23, AndAST, (cl  ((and  (false)))), [ t10], [ 0])
      (x17, AndAST, (cl  ((false))), [ x23], [ 0])
      (x24, AndAST, (cl  ((not (false)))), [ t10], [ 1])
      (x25, ResoAST, (cl ), [ x17 x24], [])
      (x26, AndAST, (cl  ((and  (false)))), [ x25], [ 0])
      (x13, AndAST, (cl  ((false))), [ x26], [ 0])
      (x12, TrueAST, (cl  ((true))), [], [])
      (x14, AndnAST, (cl  ((and  (true) (false))) ((not (false))) ((not (true)))), [], [])
      (x15, ResoAST, (cl  ((and  (true) (false)))), [ x14 x13 x12], [])
      (x27, AndAST, (cl  ((not (and  (true) (false))))), [ x25], [ 1])
      (x28, ResoAST, (cl ), [ x15 x27], [])
      (x29, AndAST, (cl  ((and  (true) (false)))), [ x28], [ 0])
      (x8, AndAST, (cl  ((false))), [ x29], [ 1])
      (x9, AndnAST, (cl  ((and  (false))) ((not (false)))), [], [])
      (x10, ResoAST, (cl  ((and  (false)))), [ x9 x8], [])
      (x30, AndAST, (cl  ((not (and  (false))))), [ x28], [ 1])
      (x31, ResoAST, (cl ), [ x10 x30], [])
      (x32, AndAST, (cl  ((not (true)))), [ x31], [ 0])
      (x2, Impn1AST, (cl  ((imp  (true) (false))) ((true))), [], [])
      (x3, ResoAST, (cl  ((imp  (true) (false)))), [ x32 x2], [])
      (x4, ImpAST, (cl  ((not (true))) ((false))), [ x3], [])
      (x5, TrueAST, (cl  ((true))), [], [])
      (x6, ResoAST, (cl  ((false))), [ x4 x5], [])
      (x33, AndAST, (cl  ((not (false)))), [ x31], [ 1])
      (x34, ResoAST, (cl ), [ x6 x33], [])
  *)

  (* Sanity check that atoms and formulas are well-typed. Must return true *)
  Eval vm_compute in (Form.check_form t_form1 && Atom.check_atom t_atom1 && Atom.wt t_i1 t_func1 t_atom1).
  

  (* States from c1 *)
  
  (* Start state *)
  Definition s0_1 := Eval vm_compute in (add_roots (S.make nclauses1) root1 used_roots1).
  Print s0_1.
  (* s0_1 = ({| [4] |} *)

  Eval vm_compute in List.nth 0 (fst c1) _.
  (* 1. First step:  *)
  Definition s1_1 := Eval vm_compute in (step_checker s0_1 (List.nth 0 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s1_1.
  (* s1_1 = ({|  |} *)

  Eval vm_compute in List.nth 1 (fst c1) _.
  (* 2.  *)
  Definition s2_1 := Eval vm_compute in (step_checker s1_1 (List.nth 1 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s2_1.
  (* s2_1 = ({|  |} *)

  Eval vm_compute in List.nth 2 (fst c1) _.
  (* 3.  *)
  Definition s3_1 := Eval vm_compute in (step_checker s2_1 (List.nth 2 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s3_1.
  (* s3_1 = ({|  |} *)

  Eval vm_compute in List.nth 3 (fst c1) _.
  (* 4.  *)
  Definition s4_1 := Eval vm_compute in (step_checker s3_1 (List.nth 3 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s4_1.
  (* s4_1 = ({|  |} *)

  Eval vm_compute in List.nth 4 (fst c1) _.
  (* 5.  *)
  Definition s5_1 := Eval vm_compute in (step_checker s4_1 (List.nth 4 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s5_1.
  (* s5_1 = ({|  |} *)

  Eval vm_compute in List.nth 5 (fst c1) _.
  (* 6.  *)
  Definition s6_1 := Eval vm_compute in (step_checker s5_1 (List.nth 5 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s6_1.
  (* s6_1 = ({|  |} *)

  Eval vm_compute in List.nth 6 (fst c1) _.
  (* 7.  *)
  Definition s7_1 := Eval vm_compute in (step_checker s6_1 (List.nth 6 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s7_1.
  (* s7_1 = ({|  |} *)

  Eval vm_compute in List.nth 7 (fst c1) _.
  (* 8.  *)
  Definition s8_1 := Eval vm_compute in (step_checker s7_1 (List.nth 7 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s8_1.
  (* s8_1 = ({|  |} *)

  Eval vm_compute in List.nth 8 (fst c1) _.
  (* 9.  *)
  Definition s9_1 := Eval vm_compute in (step_checker s8_1 (List.nth 8 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s9_1.
  (* s9_1 = ({|  |} *)

  Eval vm_compute in List.nth 9 (fst c1) _.
  (* 10.  *)
  Definition s10_1 := Eval vm_compute in (step_checker s9_1 (List.nth 9 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s10_1.
  (* s10_1 = ({|  |} *)

  Eval vm_compute in List.nth 10 (fst c1) _.
  (* 11.  *)
  Definition s11_1 := Eval vm_compute in (step_checker s10_1 (List.nth 10 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s11_1.
  (* s11_1 = ({|  |} *)

  Eval vm_compute in List.nth 11 (fst c1) _.
  (* 12.  *)
  Definition s12_1 := Eval vm_compute in (step_checker s11_1 (List.nth 11 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s12_1.
  (* s12_1 = ({|  |} *)

  Eval vm_compute in List.nth 12 (fst c1) _.
  (* 13.  *)
  Definition s13_1 := Eval vm_compute in (step_checker s12_1 (List.nth 12 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s13_1.
  (* s13_1 = ({|  |} *)

  Eval vm_compute in List.nth 13 (fst c1) _.
  (* 14.  *)
  Definition s14_1 := Eval vm_compute in (step_checker s13_1 (List.nth 13 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s14_1.
  (* s14_1 = ({|  |} *)

  Eval vm_compute in List.nth 14 (fst c1) _.
  (* 15.  *)
  Definition s15_1 := Eval vm_compute in (step_checker s14_1 (List.nth 14 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s15_1.
  (* s15_1 = ({|  |} *)

  Eval vm_compute in List.nth 15 (fst c1) _.
  (* 16.  *)
  Definition s16_1 := Eval vm_compute in (step_checker s15_1 (List.nth 15 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s16_1.
  (* s16_1 = ({|  |} *)

  Eval vm_compute in List.nth 16 (fst c1) _.
  (* 17.  *)
  Definition s17_1 := Eval vm_compute in (step_checker s16_1 (List.nth 16 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s17_1.
  (* s17_1 = ({|  |} *)

  Eval vm_compute in List.nth 17 (fst c1) _.
  (* 18.  *)
  Definition s18_1 := Eval vm_compute in (step_checker s17_1 (List.nth 17 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s18_1.
  (* s18_1 = ({|  |} *)

  Eval vm_compute in List.nth 18 (fst c1) _.
  (* 19.  *)
  Definition s19_1 := Eval vm_compute in (step_checker s18_1 (List.nth 18 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s19_1.
  (* s19_1 = ({|  |} *)

  Eval vm_compute in List.nth 19 (fst c1) _.
  (* 20.  *)
  Definition s20_1 := Eval vm_compute in (step_checker s19_1 (List.nth 19 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s20_1.
  (* s20_1 = ({|  |} *)
  
  Eval vm_compute in List.nth 20 (fst c1) _.
  (* 21.  *)
  Definition s21_1 := Eval vm_compute in (step_checker s20_1 (List.nth 20 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s21_1.
  (* s21_1 = ({|  |} *)
  
  Eval vm_compute in List.nth 21 (fst c1) _.
  (* 22.  *)
  Definition s22_1 := Eval vm_compute in (step_checker s21_1 (List.nth 21 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s22_1.
  (* s22_1 = ({|  |} *)

  Eval vm_compute in List.nth 22 (fst c1) _.
  (* 23.  *)
  Definition s23_1 := Eval vm_compute in (step_checker s22_1 (List.nth 22 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s23_1.
  (* s23_1 = ({|  |} *)

  Eval vm_compute in List.nth 23 (fst c1) _.
  (* 24.  *)
  Definition s24_1 := Eval vm_compute in (step_checker s23_1 (List.nth 23 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s24_1.
  (* s24_1 = ({|  |} *)

  Eval vm_compute in List.nth 24 (fst c1) _.
  (* 25.  *)
  Definition s25_1 := Eval vm_compute in (step_checker s24_1 (List.nth 24 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s25_1.
  (* s25_1 = ({|  |} *)
  
  Eval vm_compute in List.nth 25 (fst c1) _.
  (* 26.  *)
  Definition s26_1 := Eval vm_compute in (step_checker s25_1 (List.nth 25 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s26_1.
  (* s26_1 = ({|  |} *)

  Eval vm_compute in List.nth 26 (fst c1) _.
  (* 27.  *)
  Definition s27_1 := Eval vm_compute in (step_checker s26_1 (List.nth 26 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s27_1.
  (* s27_1 = ({|  |} *)

  Eval vm_compute in List.nth 27 (fst c1) _.
  (* 28.  *)
  Definition s28_1 := Eval vm_compute in (step_checker s27_1 (List.nth 27 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s28_1.
  (* s28_1 = ({|  |} *)

  Eval vm_compute in List.nth 28 (fst c1) _.
  (* 29.  *)
  Definition s29_1 := Eval vm_compute in (step_checker s28_1 (List.nth 28 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s29_1.
  (* s29_1 = ({|  |} *)

  Eval vm_compute in List.nth 29 (fst c1) _.
  (* 30.  *)
  Definition s30_1 := Eval vm_compute in (step_checker s29_1 (List.nth 29 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s30_1.
  (* s30_1 = ({|  |} *)

  Eval vm_compute in List.nth 30 (fst c1) _.
  (* 31.  *)
  Definition s31_1 := Eval vm_compute in (step_checker s30_1 (List.nth 30 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s31_1.
  (* s31_1 = ({|  |} *)

  Eval vm_compute in List.nth 31 (fst c1) _.
  (* 32.  *)
  Definition s32_1 := Eval vm_compute in (step_checker s31_1 (List.nth 31 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s32_1.
  (* s32_1 = ({|  |} *)

  Eval vm_compute in List.nth 32 (fst c1) _.
  (* 33.  *)
  Definition s33_1 := Eval vm_compute in (step_checker s32_1 (List.nth 32 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s33_1.
  (* s33_1 = ({|  |} *)

  Eval vm_compute in List.nth 33 (fst c1) _.
  (* 34.  *)
  Definition s34_1 := Eval vm_compute in (step_checker s33_1 (List.nth 33 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s34_1.
  (* s34_1 = ({|  |} *)

  Eval vm_compute in List.nth 34 (fst c1) _.
  (* 35.  *)
  Definition s35_1 := Eval vm_compute in (step_checker s34_1 (List.nth 34 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s35_1.
  (* s35_1 = ({|  |} *)

  Eval vm_compute in List.nth 35 (fst c1) _.
  (* 36.  *)
  Definition s36_1 := Eval vm_compute in (step_checker s35_1 (List.nth 35 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s36_1.
  (* s36_1 = ({|  |} *)

  Eval vm_compute in List.nth 36 (fst c1) _.
  (* 37.  *)
  Definition s37_1 := Eval vm_compute in (step_checker s36_1 (List.nth 36 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s37_1.
  (* s37_1 = ({|  |} *)

  (* If the main_checker returns true, SMTCoq has successfully managed to check the proof *)
  Eval vm_compute in (euf_checker C.is_false (add_roots (S.make nclauses1) root1 used_roots1) c1 conf1).
End Checker_SmtEx1Debug.