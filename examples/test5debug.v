Add Rec LoadPath "/home/arjun/Desktop/smtcoq-veritAst/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.
Require Import Int31.
Local Open Scope int31_scope.

Section Test5Debug.
  Parse_certif_verit t_i5 t_func5 t_atom5 t_form5 root5 used_roots5 trace5
  "/home/arjun/Desktop/smtcoq-veritAst//smtcoq/examples/test5.smt2"
  "/home/arjun/Desktop/smtcoq-veritAst//smtcoq/examples/test5.vtlog".
  Definition nclauses5 := Eval vm_compute in (match trace5 with Certif a _ _ => a end). (* Size of the state *)
  Print nclauses5. (* 4 *)
  Definition c5 := Eval vm_compute in (match trace5 with Certif _ a _ => a end). (* Certificate *)
  Print c5.
  Definition conf5 := Eval vm_compute in (match trace5 with Certif _ _ a => a end). (* Look here in the state for the empty clause*)
  Print conf5. (* 1 *)
  Eval vm_compute in List.length (fst c5). (* 27 steps in certificate *)
  (* Sanity check that atoms and formulas are well-typed. Must return true *)
  Eval vm_compute in (Form.check_form t_form5 && Atom.check_atom t_atom5 && Atom.wt t_i5 t_func5 t_atom5).

  (* Certif after process_proj (from veritAst):
     (h1, AssumeAST, (cl  ((not (or  op_0 (not op_0))))), [], [])
     (x13, AndnAST, (cl  ((and  (or  op_0 (not op_0)) (not (true)))) ((not (or  op_0 (not op_0)))) ((true))), [], [])
     (x14, AndnAST, (cl  ((and  (true) (not (or  op_0 (not op_0))))) ((not (true))) ((or  op_0 (not op_0)))), [], [])
     (x15, Equn1AST, (cl  (((or  op_0 (not op_0)) = (true))) ((not (or  op_0 (not op_0)))) ((not (true)))), [], [])
     (t2, ResoAST, (cl  ((and  (or  op_0 (not op_0)) (not (true)))) ((and  (true) (not (or  op_0 (not op_0))))) (((or  op_0 (not op_0)) = (true)))), [ x15 x13 x14], [])
     (t3, CongAST, (cl  (((not (or  op_0 (not op_0))) = (not (true))))), [ t2], [])
     (t4, AndnAST, (cl  ((and  (not (true)) (not (false)))) ((not (not (true)))) ((false))), [], [])
     (t5, TransAST, (cl  (((not (or  op_0 (not op_0))) = (false)))), [ t3 t4], [])
     (t6, Equp2AST, (cl  ((not ((not (or  op_0 (not op_0))) = (false)))) ((not (not (or  op_0 (not op_0))))) ((false))), [], [])
     (t8, ThresoAST, (cl  ((not ((not (or  op_0 (not op_0))) = (false)))) ((or  op_0 (not op_0))) ((false))), [ t6], [])
     (t9, ThresoAST, (cl  ((false))), [ h1 t5 t8], [])
     (t10, FalsAST, (cl  ((not (false)))), [], [])
     (t11, ResoAST, (cl ), [ t9 t10], [])
     (x18, AndAST, (cl  ((not (true)))), [ t11], [ 0])
     (x6, Impn1AST, (cl  ((imp  (true) (false))) ((true))), [], [])
     (x7, ResoAST, (cl  ((imp  (true) (false)))), [ x18 x6], [])
     (x8, ImpAST, (cl  ((not (true))) ((false))), [ x7], [])
     (x9, TrueAST, (cl  ((true))), [], [])
     (x10, ResoAST, (cl  ((false))), [ x8 x9], [])
     (x19, AndAST, (cl  ((not (false)))), [ t11], [ 1])
     (x20, ResoAST, (cl ), [ x10 x19], [])
     (x21, AndAST, (cl  ((true))), [ x20], [ 0])
     (x2, OrnAST, (cl  ((or  op_0 (not op_0))) ((not op_0))), [], [ 0])
     (x3, OrnAST, (cl  ((or  op_0 (not op_0))) (op_0)), [], [ 1])
     (x4, ResoAST, (cl  ((or  op_0 (not op_0)))), [ x2 x3], [])
     (x22, AndAST, (cl  ((not (or  op_0 (not op_0))))), [ x20], [ 1])
     (x23, ResoAST, (cl ), [ x4 x22], [])
     (x24, AndAST, (cl  ((or  op_0 (not op_0)))), [ x23], [ 0])
     (x1, TrueAST, (cl  ((true))), [], [])
     (x25, AndAST, (cl  ((not (true)))), [ x23], [ 1])
     (x26, ResoAST, (cl ), [ x1 x25], [])
  *)

  (* States from c5 *)

  (* Start state *)
  Definition s0_5 := Eval vm_compute in (add_roots (S.make nclauses5) root5 used_roots5).
  Print s0_5.
  (* s0_5 = ({| [7] |} *)

  Eval vm_compute in List.nth 0 (fst c5) _.
  (* 1. BuildDef 1 8 *)
  Definition s1_5 := Eval vm_compute in (step_checker s0_5 (List.nth 0 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s1_5.
  (* s1_5 = ({| [7], [0; 7; 8] |} *)

  Eval vm_compute in List.nth 1 (fst c5) _.
  (* 2. BuildDef 2 10 *)
  Definition s2_5 := Eval vm_compute in (step_checker s1_5 (List.nth 1 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s2_5.
  (* s2_5 = ({| [7], [0; 7; 8], [1; 6; 10] |} *)

  Eval vm_compute in List.nth 2 (fst c5) _.
  (* 3. BuildDef 3 12 *)
  Definition s3_5 := Eval vm_compute in (step_checker s2_5 (List.nth 2 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s3_5.
  (* s3_5 = ({| [7], [0; 7; 8], [1; 6; 10], [1; 7; 12] |} *)

  Eval vm_compute in List.nth 3 (fst c5) _.
  (* 4. Res 2 {| 3, 1, 2 |} *)
  Definition s4_5 := Eval vm_compute in (step_checker s3_5 (List.nth 3 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s4_5.
  (* s4_5 = ({| [7], [0; 7; 8], [1; 8; 10; 12], [1; 7; 12] |} *)

  Eval vm_compute in List.nth 4 (fst c5) _.
  (* 5. IffCong 2 [2] 14 *)
  Definition s5_5 := Eval vm_compute in (step_checker s4_5 (List.nth 4 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s5_5.
  (* s5_5 = ({| [7], [0; 7; 8], [0], [1; 7; 12] |} *)

  Eval vm_compute in List.nth 5 (fst c5) _.
  (* 6 *)
  Definition s6_5 := Eval vm_compute in (step_checker s5_5 (List.nth 5 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s6_5.
  (* s6_5 = ({|  |} *)
  Eval vm_compute in List.nth 6 (fst c5) _.
  (* 7 *)
  Definition s7_5 := Eval vm_compute in (step_checker s6_5 (List.nth 6 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s7_5.
  (* s7_5 = ({|  |} *)
  Eval vm_compute in List.nth 7 (fst c5) _.
  (* 8 *)
  Definition s8_5 := Eval vm_compute in (step_checker s7_5 (List.nth 7 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s8_5.
  (* s8_5 = ({|  |} *)
  Eval vm_compute in List.nth 8 (fst c5) _.
  (* 9 *)
  Definition s9_5 := Eval vm_compute in (step_checker s8_5 (List.nth 8 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s9_5.
  (* s9_5 = ({|  |} *)
  Eval vm_compute in List.nth 9 (fst c5) _.
  (* 10 *)
  Definition s10_5 := Eval vm_compute in (step_checker s9_5 (List.nth 9 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s10_5.
  (* s10_5 = ({|  |} *)
  Eval vm_compute in List.nth 10 (fst c5) _.
  (* 11 *)
  Definition s11_5 := Eval vm_compute in (step_checker s10_5 (List.nth 10 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s11_5.
  (* s11_5 = ({|  |} *)
  Eval vm_compute in List.nth 11 (fst c5) _.
  (* 12 *)
  Definition s12_5 := Eval vm_compute in (step_checker s11_5 (List.nth 11 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s12_5.
  (* s12_5 = ({|  |} *)
  Eval vm_compute in List.nth 12 (fst c5) _.
  (* 13 *)
  Definition s13_5 := Eval vm_compute in (step_checker s12_5 (List.nth 12 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s13_5.
  (* s13_5 = ({|  |} *)
  Eval vm_compute in List.nth 13 (fst c5) _.
  (* 14 *)
  Definition s14_5 := Eval vm_compute in (step_checker s13_5 (List.nth 13 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s14_5.
  (* s14_5 = ({|  |} *)
  Eval vm_compute in List.nth 14 (fst c5) _.
  (* 15 *)
  Definition s15_5 := Eval vm_compute in (step_checker s14_5 (List.nth 14 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s15_5.
  (* s15_5 = ({|  |} *)
  Eval vm_compute in List.nth 15 (fst c5) _.
  (* 16 *)
  Definition s16_5 := Eval vm_compute in (step_checker s15_5 (List.nth 15 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s16_5.
  (* s16_5 = ({|  |} *)
  Eval vm_compute in List.nth 16 (fst c5) _.
  (* 17 *)
  Definition s17_5 := Eval vm_compute in (step_checker s16_5 (List.nth 16 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s17_5.
  (* s17_5 = ({|  |} *)
  Eval vm_compute in List.nth 17 (fst c5) _.
  (* 18 *)
  Definition s18_5 := Eval vm_compute in (step_checker s17_5 (List.nth 17 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s18_5.
  (* s18_5 = ({|  |} *)
  Eval vm_compute in List.nth 18 (fst c5) _.
  (* 19 *)
  Definition s19_5 := Eval vm_compute in (step_checker s18_5 (List.nth 18 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s19_5.
  (* s19_5 = ({|  |} *)
  Eval vm_compute in List.nth 19 (fst c5) _.
  (* 20 *)
  Definition s20_5 := Eval vm_compute in (step_checker s19_5 (List.nth 19 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s20_5.
  (* s20_5 = ({|  |} *)
  Eval vm_compute in List.nth 20 (fst c5) _.
  (* 21 *)
  Definition s21_5 := Eval vm_compute in (step_checker s20_5 (List.nth 20 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s21_5.
  (* s21_5 = ({|  |} *)
  Eval vm_compute in List.nth 21 (fst c5) _.
  (* 22 *)
  Definition s22_5 := Eval vm_compute in (step_checker s21_5 (List.nth 21 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s22_5.
  (* s22_5 = ({|  |} *)
  Eval vm_compute in List.nth 22 (fst c5) _.
  (* 23 *)
  Definition s23_5 := Eval vm_compute in (step_checker s22_5 (List.nth 22 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s23_5.
  (* s23_5 = ({|  |} *)
  Eval vm_compute in List.nth 23 (fst c5) _.
  (* 24 *)
  Definition s24_5 := Eval vm_compute in (step_checker s23_5 (List.nth 23 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s24_5.
  (* s24_5 = ({|  |} *)
  Eval vm_compute in List.nth 24 (fst c5) _.
  (* 25 *)
  Definition s25_5 := Eval vm_compute in (step_checker s24_5 (List.nth 24 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s25_5.
  (* s25_5 = ({|  |} *)
  Eval vm_compute in List.nth 25 (fst c5) _.
  (* 26 *)
  Definition s26_5 := Eval vm_compute in (step_checker s25_5 (List.nth 25 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s26_5.
  (* s26_5 = ({|  |} *)
  Eval vm_compute in List.nth 26 (fst c5) _.
  (* 27 *)
  Definition s27_5 := Eval vm_compute in (step_checker s26_5 (List.nth 26 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s27_5.
  (* s27_5 = ({|  |} *)
End Test5Debug.
