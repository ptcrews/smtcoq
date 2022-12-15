Add Rec LoadPath "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.
Require Import Int31.
Local Open Scope int31_scope.

Section Test2Debug.
  Parse_certif_verit t_i2 t_func2 t_atom2 t_form2 root2 used_roots2 trace2
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/test2.smt2"
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/test2.vtlog".
  Definition nclauses2 := Eval vm_compute in (match trace2 with Certif a _ _ => a end). (* Size of the state *)
  Print nclauses2.
  Definition c2 := Eval vm_compute in (match trace2 with Certif _ a _ => a end). (* Certificate *)
  Print c2.
  Definition conf2 := Eval vm_compute in (match trace2 with Certif _ _ a => a end). (* Look here in the state for the empty clause*)
  Print conf2.
  Eval vm_compute in List.length (fst c2). (* No. of steps in certificate *)
  (* Sanity check that atoms and formulas are well-typed. Must return true *)
  Eval vm_compute in (Form.check_form t_form2 && Atom.check_atom t_atom2 && Atom.wt t_i2 t_func2 t_atom2).


  (* States from c2 *)

  (* Start state *)
  Definition s0_2 := Eval vm_compute in (add_roots (S.make nclauses2) root2 used_roots2).
  Print s0_2.
  (* s0_2 = ({|  |} *)
  Eval vm_compute in List.nth 0 (fst c2) _.
  (* 1. *)
  Definition s1_2 := Eval vm_compute in (step_checker s0_2 (List.nth 0 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s1_2.
  (* s1_2 = ({|  |} *)

  Eval vm_compute in List.nth 1 (fst c2) _.
  (* 2. *)
  Definition s2_2 := Eval vm_compute in (step_checker s1_2 (List.nth 1 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s2_2.
  (* s2_2 = ({|  |} *)

  Eval vm_compute in List.nth 2 (fst c2) _.
  (* 3. *)
  Definition s3_2 := Eval vm_compute in (step_checker s2_2 (List.nth 2 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s3_2.
  (* s3_2 = ({|  |} *)

  Eval vm_compute in List.nth 3 (fst c2) _.
  (* 4. *)
  Definition s4_2 := Eval vm_compute in (step_checker s3_2 (List.nth 3 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s4_2.
  (* s4_2 = ({|  |} *)

  Eval vm_compute in List.nth 4 (fst c2) _.
  (* 5. *)
  Definition s5_2 := Eval vm_compute in (step_checker s4_2 (List.nth 4 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s5_2.
  (* s5_2 = ({|  |} *)

  Eval vm_compute in List.nth 5 (fst c2) _.
  (* 6. *)
  Definition s6_2 := Eval vm_compute in (step_checker s5_2 (List.nth 5 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s6_2.
  (* s6_2 = ({|  |} *)

  Eval vm_compute in List.nth 6 (fst c2) _.
  (* 7. *)
  Definition s7_2 := Eval vm_compute in (step_checker s6_2 (List.nth 6 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s7_2.
  (* s7_2 = ({|  |} *)

  Eval vm_compute in List.nth 7 (fst c2) _.
  (* 8. *)
  Definition s8_2 := Eval vm_compute in (step_checker s7_2 (List.nth 7 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s8_2.
  (* s8_2 = ({|  |} *)

  Eval vm_compute in List.nth 8 (fst c2) _.
  (* 9. *)
  Definition s9_2 := Eval vm_compute in (step_checker s8_2 (List.nth 8 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s9_2.
  (* s9_2 = ({|  |} *)

  Eval vm_compute in List.nth 9 (fst c2) _.
  (* 10. *)
  Definition s10_2 := Eval vm_compute in (step_checker s9_2 (List.nth 9 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s10_2.
  (* s10_2 = ({|  |} *)

  Eval vm_compute in List.nth 10 (fst c2) _.
  (* 11. *)
  Definition s11_2 := Eval vm_compute in (step_checker s10_2 (List.nth 10 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s11_2.
  (* s11_2 = ({|  |} *)

  Eval vm_compute in List.nth 11 (fst c2) _.
  (* 12. *)
  Definition s12_2 := Eval vm_compute in (step_checker s11_2 (List.nth 11 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s12_2.
  (* s12_2 = ({|  |} *)

  Eval vm_compute in List.nth 12 (fst c2) _.
  (* 13. *)
  Definition s13_2 := Eval vm_compute in (step_checker s12_2 (List.nth 12 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s13_2.
  (* s13_2 = ({|  |} *)

  Eval vm_compute in List.nth 13 (fst c2) _.
  (* 14. *)
  Definition s14_2 := Eval vm_compute in (step_checker s13_2 (List.nth 13 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s14_2.
  (* s14_2 = ({|  |} *)

  Eval vm_compute in List.nth 14 (fst c2) _.
  (* 15. *)
  Definition s15_2 := Eval vm_compute in (step_checker s14_2 (List.nth 14 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s15_2.
  (* s15_2 = ({|  |} *)

  Eval vm_compute in List.nth 15 (fst c2) _.
  (* 16. *)
  Definition s16_2 := Eval vm_compute in (step_checker s15_2 (List.nth 15 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s16_2.
  (* s16_2 = ({|  |} *)

  Eval vm_compute in List.nth 16 (fst c2) _.
  (* 17. *)
  Definition s17_2 := Eval vm_compute in (step_checker s16_2 (List.nth 16 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s17_2.
  (* s17_2 = ({|  |} *)

  Eval vm_compute in List.nth 17 (fst c2) _.
  (* 18. *)
  Definition s18_2 := Eval vm_compute in (step_checker s17_2 (List.nth 17 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s18_2.
  (* s18_2 = ({|  |} *)

  Eval vm_compute in List.nth 18 (fst c2) _.
  (* 19. *)
  Definition s19_2 := Eval vm_compute in (step_checker s18_2 (List.nth 18 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s19_2.
  (* s19_2 = ({|  |} *)

  Eval vm_compute in List.nth 19 (fst c2) _.
  (* 20. *)
  Definition s20_2 := Eval vm_compute in (step_checker s19_2 (List.nth 19 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s20_2.
  (* s20_2 = ({|  |} *)

  Eval vm_compute in List.nth 20 (fst c2) _.
  (* 21. *)
  Definition s21_2 := Eval vm_compute in (step_checker s20_2 (List.nth 20 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s21_2.
  (* s21_2 = ({|  |} *)

  Eval vm_compute in List.nth 21 (fst c2) _.
  (* 22. *)
  Definition s22_2 := Eval vm_compute in (step_checker s21_2 (List.nth 21 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s22_2.
  (* s22_2 = ({|  |} *)

  Eval vm_compute in List.nth 22 (fst c2) _.
  (* 23. *)
  Definition s23_2 := Eval vm_compute in (step_checker s22_2 (List.nth 22 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s23_2.
  (* s23_2 = ({|  |} *)

  Eval vm_compute in List.nth 23 (fst c2) _.
  (* 24. *)
  Definition s24_2 := Eval vm_compute in (step_checker s23_2 (List.nth 23 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s24_2.
  (* s24_2 = ({|  |} *)

  Eval vm_compute in List.nth 24 (fst c2) _.
  (* 25. *)
  Definition s25_2 := Eval vm_compute in (step_checker s24_2 (List.nth 24 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s25_2.
  (* s25_2 = ({|  |} *)

  Eval vm_compute in List.nth 25 (fst c2) _.
  (* 26. *)
  Definition s26_2 := Eval vm_compute in (step_checker s25_2 (List.nth 25 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s26_2.
  (* s26_2 = ({|  |} *)

  Eval vm_compute in List.nth 26 (fst c2) _.
  (* 27. *)
  Definition s27_2 := Eval vm_compute in (step_checker s26_2 (List.nth 26 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s27_2.
  (* s27_2 = ({|  |} *)

  Eval vm_compute in List.nth 27 (fst c2) _.
  (* 28. *)
  Definition s28_2 := Eval vm_compute in (step_checker s27_2 (List.nth 27 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s28_2.
  (* s28_2 = ({|  |} *)

  Eval vm_compute in List.nth 28 (fst c2) _.
  (* 29. *)
  Definition s29_2 := Eval vm_compute in (step_checker s28_2 (List.nth 28 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s29_2.
  (* s29_2 = ({|  |} *)

  Eval vm_compute in List.nth 29 (fst c2) _.
  (* 30. *)
  Definition s30_2 := Eval vm_compute in (step_checker s29_2 (List.nth 29 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s30_2.
  (* s30_2 = ({|  |} *)

  Eval vm_compute in List.nth 30 (fst c2) _.
  (* 31. *)
  Definition s31_2 := Eval vm_compute in (step_checker s30_2 (List.nth 30 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s31_2.
  (* s31_2 = ({|  |} *)

  Eval vm_compute in List.nth 31 (fst c2) _.
  (* 32. *)
  Definition s32_2 := Eval vm_compute in (step_checker s31_2 (List.nth 31 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s32_2.
  (* s32_2 = ({|  |} *)

  Eval vm_compute in List.nth 32 (fst c2) _.
  (* 33. *)
  Definition s33_2 := Eval vm_compute in (step_checker s32_2 (List.nth 32 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s33_2.
  (* s33_2 = ({|  |} *)

  Eval vm_compute in List.nth 33 (fst c2) _.
  (* 34. *)
  Definition s34_2 := Eval vm_compute in (step_checker s33_2 (List.nth 33 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s34_2.
  (* s34_2 = ({|  |} *)

  Eval vm_compute in List.nth 34 (fst c2) _.
  (* 35. *)
  Definition s35_2 := Eval vm_compute in (step_checker s34_2 (List.nth 34 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s35_2.
  (* s35_2 = ({|  |} *)

  Eval vm_compute in List.nth 35 (fst c2) _.
  (* 36. *)
  Definition s36_2 := Eval vm_compute in (step_checker s35_2 (List.nth 35 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s36_2.
  (* s36_2 = ({|  |} *)

  Eval vm_compute in List.nth 36 (fst c2) _.
  (* 37. *)
  Definition s37_2 := Eval vm_compute in (step_checker s36_2 (List.nth 36 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s37_2.
  (* s37_2 = ({|  |} *)

  Eval vm_compute in List.nth 37 (fst c2) _.
  (* 38. *)
  Definition s38_2 := Eval vm_compute in (step_checker s37_2 (List.nth 37 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s38_2.
  (* s38_2 = ({|  |} *)

  Eval vm_compute in List.nth 38 (fst c2) _.
  (* 39. *)
  Definition s39_2 := Eval vm_compute in (step_checker s38_2 (List.nth 38 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s39_2.
  (* s39_2 = ({|  |} *)

  Eval vm_compute in List.nth 39 (fst c2) _.
  (* 40. *)
  Definition s40_2 := Eval vm_compute in (step_checker s39_2 (List.nth 39 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s40_2.
  (* s40_2 = ({|  |} *)

  Eval vm_compute in List.nth 40 (fst c2) _.
  (* 41. *)
  Definition s41_2 := Eval vm_compute in (step_checker s40_2 (List.nth 40 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s41_2.
  (* s41_2 = ({|  |} *)

End Test2Debug.
