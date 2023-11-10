Add Rec LoadPath "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.
Require Import Int31.
Local Open Scope int31_scope.

Section Testcongiffimpl2Debug.
  Parse_certif_verit t_i1 t_func1 t_atom1 t_form1 root1 used_roots1 trace1
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/testcong/congeq/8congiffimpl2/congiffimpl2.smt2"
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/testcong/congeq/8congiffimpl2/congiffimpl2.pf".
  Definition nclauses1 := Eval vm_compute in (match trace1 with Certif a _ _ => a end). (* Size of the state *)
  Print nclauses1.
  Definition c1 := Eval vm_compute in (match trace1 with Certif _ a _ => a end). (* Certificate *)
  Print c1.
  Definition conf1 := Eval vm_compute in (match trace1 with Certif _ _ a => a end). (* Look here in the state for the empty clause*)
  Print conf1.
  Eval vm_compute in List.length (fst c1). (* No. of steps in certificate *)
  (* Sanity check that atoms and formulas are well-typed. Must return true *)
  Eval vm_compute in (Form.check_form t_form1 && Atom.check_atom t_atom1 && Atom.wt t_i1 t_func1 t_atom1).


  (* States from c1 *)

  (* Start state *)
  Definition s0_1 := Eval vm_compute in (add_roots (S.make nclauses1) root1 used_roots1).
  Print s0_1.
  (* s0_1 = ({|  |} *)
  Eval vm_compute in List.nth 0 (fst c1) _.
  (* 1. *)
  Definition s1_1 := Eval vm_compute in (step_checker s0_1 (List.nth 0 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s1_1.
  (* s1_1 = ({|  |} *)

  Eval vm_compute in List.nth 1 (fst c1) _.
  (* 2. *)
  Definition s2_1 := Eval vm_compute in (step_checker s1_1 (List.nth 1 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s2_1.
  (* s2_1 = ({|  |} *)

  Eval vm_compute in List.nth 2 (fst c1) _.
  (* 3. *)
  Definition s3_1 := Eval vm_compute in (step_checker s2_1 (List.nth 2 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s3_1.
  (* s3_1 = ({|  |} *)

  Eval vm_compute in List.nth 3 (fst c1) _.
  (* 4. *)
  Definition s4_1 := Eval vm_compute in (step_checker s3_1 (List.nth 3 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s4_1.
  (* s4_1 = ({|  |} *)

  Eval vm_compute in List.nth 4 (fst c1) _.
  (* 5. *)
  Definition s5_1 := Eval vm_compute in (step_checker s4_1 (List.nth 4 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s5_1.
  (* s5_1 = ({|  |} *)

  Eval vm_compute in List.nth 5 (fst c1) _.
  (* 6. *)
  Definition s6_1 := Eval vm_compute in (step_checker s5_1 (List.nth 5 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s6_1.
  (* s6_1 = ({|  |} *)

  Eval vm_compute in List.nth 6 (fst c1) _.
  (* 7. *)
  Definition s7_1 := Eval vm_compute in (step_checker s6_1 (List.nth 6 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s7_1.
  (* s7_1 = ({|  |} *)

  Eval vm_compute in List.nth 7 (fst c1) _.
  (* 8. *)
  Definition s8_1 := Eval vm_compute in (step_checker s7_1 (List.nth 7 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s8_1.
  (* s8_1 = ({|  |} *)

  Eval vm_compute in List.nth 8 (fst c1) _.
  (* 9. *)
  Definition s9_1 := Eval vm_compute in (step_checker s8_1 (List.nth 8 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s9_1.
  (* s9_1 = ({|  |} *)

  Eval vm_compute in List.nth 9 (fst c1) _.
  (* 10. *)
  Definition s10_1 := Eval vm_compute in (step_checker s9_1 (List.nth 9 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s10_1.
  (* s10_1 = ({|  |} *)

  Eval vm_compute in List.nth 10 (fst c1) _.
  (* 11. *)
  Definition s11_1 := Eval vm_compute in (step_checker s10_1 (List.nth 10 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s11_1.
  (* s11_1 = ({|  |} *)

  Eval vm_compute in List.nth 11 (fst c1) _.
  (* 12. *)
  Definition s12_1 := Eval vm_compute in (step_checker s11_1 (List.nth 11 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s12_1.
  (* s12_1 = ({|  |} *)

  Eval vm_compute in List.nth 12 (fst c1) _.
  (* 13. *)
  Definition s13_1 := Eval vm_compute in (step_checker s12_1 (List.nth 12 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s13_1.
  (* s13_1 = ({|  |} *)

  Eval vm_compute in List.nth 13 (fst c1) _.
  (* 14. *)
  Definition s14_1 := Eval vm_compute in (step_checker s13_1 (List.nth 13 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s14_1.
  (* s14_1 = ({|  |} *)

  Eval vm_compute in List.nth 14 (fst c1) _.
  (* 15. *)
  Definition s15_1 := Eval vm_compute in (step_checker s14_1 (List.nth 14 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s15_1.
  (* s15_1 = ({|  |} *)

  Eval vm_compute in List.nth 15 (fst c1) _.
  (* 16. *)
  Definition s16_1 := Eval vm_compute in (step_checker s15_1 (List.nth 15 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s16_1.
  (* s16_1 = ({|  |} *)

  Eval vm_compute in List.nth 16 (fst c1) _.
  (* 17. *)
  Definition s17_1 := Eval vm_compute in (step_checker s16_1 (List.nth 16 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s17_1.
  (* s17_1 = ({|  |} *)

  Eval vm_compute in List.nth 17 (fst c1) _.
  (* 18. *)
  Definition s18_1 := Eval vm_compute in (step_checker s17_1 (List.nth 17 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s18_1.
  (* s18_1 = ({|  |} *)

  Eval vm_compute in List.nth 18 (fst c1) _.
  (* 19. *)
  Definition s19_1 := Eval vm_compute in (step_checker s18_1 (List.nth 18 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s19_1.
  (* s19_1 = ({|  |} *)

  Eval vm_compute in List.nth 19 (fst c1) _.
  (* 20. *)
  Definition s20_1 := Eval vm_compute in (step_checker s19_1 (List.nth 19 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s20_1.
  (* s20_1 = ({|  |} *)

  Eval vm_compute in List.nth 20 (fst c1) _.
  (* 21. *)
  Definition s21_1 := Eval vm_compute in (step_checker s20_1 (List.nth 20 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s21_1.
  (* s21_1 = ({|  |} *)

  Eval vm_compute in List.nth 21 (fst c1) _.
  (* 22. *)
  Definition s22_1 := Eval vm_compute in (step_checker s21_1 (List.nth 21 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s22_1.
  (* s22_1 = ({|  |} *)

  Eval vm_compute in List.nth 22 (fst c1) _.
  (* 23. *)
  Definition s23_1 := Eval vm_compute in (step_checker s22_1 (List.nth 22 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s23_1.
  (* s23_1 = ({|  |} *)

End Test1Debug.
