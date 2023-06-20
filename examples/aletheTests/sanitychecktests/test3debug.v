Add Rec LoadPath "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.
Require Import Int31.
Local Open Scope int31_scope.

Section Test3Debug.
  Parse_certif_verit t_i3 t_func3 t_atom3 t_form3 root3 used_roots3 trace3
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test3.smt2"
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test3.pf".
  Definition nclauses3 := Eval vm_compute in (match trace3 with Certif a _ _ => a end). (* Size of the state *)
  Print nclauses3.
  Definition c3 := Eval vm_compute in (match trace3 with Certif _ a _ => a end). (* Certificate *)
  Print c3.
  Definition conf3 := Eval vm_compute in (match trace3 with Certif _ _ a => a end). (* Look here in the state for the empty clause*)
  Print conf3.
  Eval vm_compute in List.length (fst c3). (* No. of steps in certificate *)
  (* Sanity check that atoms and formulas are well-typed. Must return true *)
  Eval vm_compute in (Form.check_form t_form3 && Atom.check_atom t_atom3 && Atom.wt t_i3 t_func3 t_atom3).


  (* States from c3 *)

  (* Start state *)
  Definition s0_3 := Eval vm_compute in (add_roots (S.make nclauses3) root3 used_roots3).
  Print s0_3.
  (* s0_3 = ({|  |} *)
  Eval vm_compute in List.nth 0 (fst c3) _.
  (* 1. *)
  Definition s1_3 := Eval vm_compute in (step_checker s0_3 (List.nth 0 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s1_3.
  (* s1_3 = ({|  |} *)

  Eval vm_compute in List.nth 1 (fst c3) _.
  (* 2. *)
  Definition s2_3 := Eval vm_compute in (step_checker s1_3 (List.nth 1 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s2_3.
  (* s2_3 = ({|  |} *)

  Eval vm_compute in List.nth 2 (fst c3) _.
  (* 3. *)
  Definition s3_3 := Eval vm_compute in (step_checker s2_3 (List.nth 2 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s3_3.
  (* s3_3 = ({|  |} *)

  Eval vm_compute in List.nth 3 (fst c3) _.
  (* 4. *)
  Definition s4_3 := Eval vm_compute in (step_checker s3_3 (List.nth 3 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s4_3.
  (* s4_3 = ({|  |} *)

  Eval vm_compute in List.nth 4 (fst c3) _.
  (* 5. *)
  Definition s5_3 := Eval vm_compute in (step_checker s4_3 (List.nth 4 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s5_3.
  (* s5_3 = ({|  |} *)

  Eval vm_compute in List.nth 5 (fst c3) _.
  (* 6. *)
  Definition s6_3 := Eval vm_compute in (step_checker s5_3 (List.nth 5 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s6_3.
  (* s6_3 = ({|  |} *)

  Eval vm_compute in List.nth 6 (fst c3) _.
  (* 7. *)
  Definition s7_3 := Eval vm_compute in (step_checker s6_3 (List.nth 6 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s7_3.
  (* s7_3 = ({|  |} *)

  Eval vm_compute in List.nth 7 (fst c3) _.
  (* 8. *)
  Definition s8_3 := Eval vm_compute in (step_checker s7_3 (List.nth 7 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s8_3.
  (* s8_3 = ({|  |} *)

  Eval vm_compute in List.nth 8 (fst c3) _.
  (* 9. *)
  Definition s9_3 := Eval vm_compute in (step_checker s8_3 (List.nth 8 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s9_3.
  (* s9_3 = ({|  |} *)

  Eval vm_compute in List.nth 9 (fst c3) _.
  (* 10. *)
  Definition s10_3 := Eval vm_compute in (step_checker s9_3 (List.nth 9 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s10_3.
  (* s10_3 = ({|  |} *)

  Eval vm_compute in List.nth 10 (fst c3) _.
  (* 11. *)
  Definition s11_3 := Eval vm_compute in (step_checker s10_3 (List.nth 10 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s11_3.
  (* s11_3 = ({|  |} *)

  Eval vm_compute in List.nth 11 (fst c3) _.
  (* 12. *)
  Definition s12_3 := Eval vm_compute in (step_checker s11_3 (List.nth 11 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s12_3.
  (* s12_3 = ({|  |} *)

  Eval vm_compute in List.nth 12 (fst c3) _.
  (* 13. *)
  Definition s13_3 := Eval vm_compute in (step_checker s12_3 (List.nth 12 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s13_3.
  (* s13_3 = ({|  |} *)

  Eval vm_compute in List.nth 13 (fst c3) _.
  (* 14. *)
  Definition s14_3 := Eval vm_compute in (step_checker s13_3 (List.nth 13 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s14_3.
  (* s14_3 = ({|  |} *)

  Eval vm_compute in List.nth 14 (fst c3) _.
  (* 15. *)
  Definition s15_3 := Eval vm_compute in (step_checker s14_3 (List.nth 14 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s15_3.
  (* s15_3 = ({|  |} *)

  Eval vm_compute in List.nth 15 (fst c3) _.
  (* 16. *)
  Definition s16_3 := Eval vm_compute in (step_checker s15_3 (List.nth 15 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s16_3.
  (* s16_3 = ({|  |} *)

  Eval vm_compute in List.nth 16 (fst c3) _.
  (* 17. *)
  Definition s17_3 := Eval vm_compute in (step_checker s16_3 (List.nth 16 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s17_3.
  (* s17_3 = ({|  |} *)

  Eval vm_compute in List.nth 17 (fst c3) _.
  (* 18. *)
  Definition s18_3 := Eval vm_compute in (step_checker s17_3 (List.nth 17 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s18_3.
  (* s18_3 = ({|  |} *)

  Eval vm_compute in List.nth 18 (fst c3) _.
  (* 19. *)
  Definition s19_3 := Eval vm_compute in (step_checker s18_3 (List.nth 18 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s19_3.
  (* s19_3 = ({|  |} *)

  Eval vm_compute in List.nth 19 (fst c3) _.
  (* 20. *)
  Definition s20_3 := Eval vm_compute in (step_checker s19_3 (List.nth 19 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s20_3.
  (* s20_3 = ({|  |} *)

  Eval vm_compute in List.nth 20 (fst c3) _.
  (* 21. *)
  Definition s21_3 := Eval vm_compute in (step_checker s20_3 (List.nth 20 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s21_3.
  (* s21_3 = ({|  |} *)

  Eval vm_compute in List.nth 21 (fst c3) _.
  (* 22. *)
  Definition s22_3 := Eval vm_compute in (step_checker s21_3 (List.nth 21 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s22_3.
  (* s22_3 = ({|  |} *)

  Eval vm_compute in List.nth 22 (fst c3) _.
  (* 23. *)
  Definition s23_3 := Eval vm_compute in (step_checker s22_3 (List.nth 22 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s23_3.
  (* s23_3 = ({|  |} *)

  Eval vm_compute in List.nth 23 (fst c3) _.
  (* 24. *)
  Definition s24_3 := Eval vm_compute in (step_checker s23_3 (List.nth 23 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s24_3.
  (* s24_3 = ({|  |} *)

  Eval vm_compute in List.nth 24 (fst c3) _.
  (* 25. *)
  Definition s25_3 := Eval vm_compute in (step_checker s24_3 (List.nth 24 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s25_3.
  (* s25_3 = ({|  |} *)

  Eval vm_compute in List.nth 25 (fst c3) _.
  (* 26. *)
  Definition s26_3 := Eval vm_compute in (step_checker s25_3 (List.nth 25 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s26_3.
  (* s26_3 = ({|  |} *)

  Eval vm_compute in List.nth 26 (fst c3) _.
  (* 27. *)
  Definition s27_3 := Eval vm_compute in (step_checker s26_3 (List.nth 26 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s27_3.
  (* s27_3 = ({|  |} *)

  Eval vm_compute in List.nth 27 (fst c3) _.
  (* 28. *)
  Definition s28_3 := Eval vm_compute in (step_checker s27_3 (List.nth 27 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s28_3.
  (* s28_3 = ({|  |} *)

  Eval vm_compute in List.nth 28 (fst c3) _.
  (* 29. *)
  Definition s29_3 := Eval vm_compute in (step_checker s28_3 (List.nth 28 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s29_3.
  (* s29_3 = ({|  |} *)

  Eval vm_compute in List.nth 29 (fst c3) _.
  (* 30. *)
  Definition s30_3 := Eval vm_compute in (step_checker s29_3 (List.nth 29 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s30_3.
  (* s30_3 = ({|  |} *)

  Eval vm_compute in List.nth 30 (fst c3) _.
  (* 31. *)
  Definition s31_3 := Eval vm_compute in (step_checker s30_3 (List.nth 30 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s31_3.
  (* s31_3 = ({|  |} *)

  Eval vm_compute in List.nth 31 (fst c3) _.
  (* 32. *)
  Definition s32_3 := Eval vm_compute in (step_checker s31_3 (List.nth 31 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s32_3.
  (* s32_3 = ({|  |} *)

End Test3Debug.
