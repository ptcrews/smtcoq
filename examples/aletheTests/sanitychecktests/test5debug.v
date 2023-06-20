Add Rec LoadPath "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.
Require Import Int31.
Local Open Scope int31_scope.

Section Test5Debug.
  Parse_certif_verit t_i5 t_func5 t_atom5 t_form5 root5 used_roots5 trace5
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test5.smt2"
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test5.pf".
  Definition nclauses5 := Eval vm_compute in (match trace5 with Certif a _ _ => a end). (* Size of the state *)
  Print nclauses5.
  Definition c5 := Eval vm_compute in (match trace5 with Certif _ a _ => a end). (* Certificate *)
  Print c5.
  Definition conf5 := Eval vm_compute in (match trace5 with Certif _ _ a => a end). (* Look here in the state for the empty clause*)
  Print conf5.
  Eval vm_compute in List.length (fst c5). (* No. of steps in certificate *)
  (* Sanity check that atoms and formulas are well-typed. Must return true *)
  Eval vm_compute in (Form.check_form t_form5 && Atom.check_atom t_atom5 && Atom.wt t_i5 t_func5 t_atom5).


  (* States from c5 *)

  (* Start state *)
  Definition s0_5 := Eval vm_compute in (add_roots (S.make nclauses5) root5 used_roots5).
  Print s0_5.
  (* s0_5 = ({|  |} *)
  Eval vm_compute in List.nth 0 (fst c5) _.
  (* 1. *)
  Definition s1_5 := Eval vm_compute in (step_checker s0_5 (List.nth 0 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s1_5.
  (* s1_5 = ({|  |} *)

  Eval vm_compute in List.nth 1 (fst c5) _.
  (* 2. *)
  Definition s2_5 := Eval vm_compute in (step_checker s1_5 (List.nth 1 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s2_5.
  (* s2_5 = ({|  |} *)

  Eval vm_compute in List.nth 2 (fst c5) _.
  (* 3. *)
  Definition s3_5 := Eval vm_compute in (step_checker s2_5 (List.nth 2 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s3_5.
  (* s3_5 = ({|  |} *)

  Eval vm_compute in List.nth 3 (fst c5) _.
  (* 4. *)
  Definition s4_5 := Eval vm_compute in (step_checker s3_5 (List.nth 3 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s4_5.
  (* s4_5 = ({|  |} *)

  Eval vm_compute in List.nth 4 (fst c5) _.
  (* 5. *)
  Definition s5_5 := Eval vm_compute in (step_checker s4_5 (List.nth 4 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s5_5.
  (* s5_5 = ({|  |} *)

  Eval vm_compute in List.nth 5 (fst c5) _.
  (* 6. *)
  Definition s6_5 := Eval vm_compute in (step_checker s5_5 (List.nth 5 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s6_5.
  (* s6_5 = ({|  |} *)

  Eval vm_compute in List.nth 6 (fst c5) _.
  (* 7. *)
  Definition s7_5 := Eval vm_compute in (step_checker s6_5 (List.nth 6 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s7_5.
  (* s7_5 = ({|  |} *)

  Eval vm_compute in List.nth 7 (fst c5) _.
  (* 8. *)
  Definition s8_5 := Eval vm_compute in (step_checker s7_5 (List.nth 7 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s8_5.
  (* s8_5 = ({|  |} *)

  Eval vm_compute in List.nth 8 (fst c5) _.
  (* 9. *)
  Definition s9_5 := Eval vm_compute in (step_checker s8_5 (List.nth 8 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s9_5.
  (* s9_5 = ({|  |} *)

  Eval vm_compute in List.nth 9 (fst c5) _.
  (* 10. *)
  Definition s10_5 := Eval vm_compute in (step_checker s9_5 (List.nth 9 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s10_5.
  (* s10_5 = ({|  |} *)

  Eval vm_compute in List.nth 10 (fst c5) _.
  (* 11. *)
  Definition s11_5 := Eval vm_compute in (step_checker s10_5 (List.nth 10 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s11_5.
  (* s11_5 = ({|  |} *)

  Eval vm_compute in List.nth 11 (fst c5) _.
  (* 12. *)
  Definition s12_5 := Eval vm_compute in (step_checker s11_5 (List.nth 11 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s12_5.
  (* s12_5 = ({|  |} *)

  Eval vm_compute in List.nth 12 (fst c5) _.
  (* 13. *)
  Definition s13_5 := Eval vm_compute in (step_checker s12_5 (List.nth 12 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s13_5.
  (* s13_5 = ({|  |} *)

  Eval vm_compute in List.nth 13 (fst c5) _.
  (* 14. *)
  Definition s14_5 := Eval vm_compute in (step_checker s13_5 (List.nth 13 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s14_5.
  (* s14_5 = ({|  |} *)

  Eval vm_compute in List.nth 14 (fst c5) _.
  (* 15. *)
  Definition s15_5 := Eval vm_compute in (step_checker s14_5 (List.nth 14 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s15_5.
  (* s15_5 = ({|  |} *)

  Eval vm_compute in List.nth 15 (fst c5) _.
  (* 16. *)
  Definition s16_5 := Eval vm_compute in (step_checker s15_5 (List.nth 15 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s16_5.
  (* s16_5 = ({|  |} *)

  Eval vm_compute in List.nth 16 (fst c5) _.
  (* 17. *)
  Definition s17_5 := Eval vm_compute in (step_checker s16_5 (List.nth 16 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s17_5.
  (* s17_5 = ({|  |} *)

  Eval vm_compute in List.nth 17 (fst c5) _.
  (* 18. *)
  Definition s18_5 := Eval vm_compute in (step_checker s17_5 (List.nth 17 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s18_5.
  (* s18_5 = ({|  |} *)

  Eval vm_compute in List.nth 18 (fst c5) _.
  (* 19. *)
  Definition s19_5 := Eval vm_compute in (step_checker s18_5 (List.nth 18 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s19_5.
  (* s19_5 = ({|  |} *)

  Eval vm_compute in List.nth 19 (fst c5) _.
  (* 20. *)
  Definition s20_5 := Eval vm_compute in (step_checker s19_5 (List.nth 19 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s20_5.
  (* s20_5 = ({|  |} *)

  Eval vm_compute in List.nth 20 (fst c5) _.
  (* 21. *)
  Definition s21_5 := Eval vm_compute in (step_checker s20_5 (List.nth 20 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s21_5.
  (* s21_5 = ({|  |} *)

  Eval vm_compute in List.nth 21 (fst c5) _.
  (* 22. *)
  Definition s22_5 := Eval vm_compute in (step_checker s21_5 (List.nth 21 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s22_5.
  (* s22_5 = ({|  |} *)

  Eval vm_compute in List.nth 22 (fst c5) _.
  (* 23. *)
  Definition s23_5 := Eval vm_compute in (step_checker s22_5 (List.nth 22 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s23_5.
  (* s23_5 = ({|  |} *)

  Eval vm_compute in List.nth 23 (fst c5) _.
  (* 24. *)
  Definition s24_5 := Eval vm_compute in (step_checker s23_5 (List.nth 23 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s24_5.
  (* s24_5 = ({|  |} *)

  Eval vm_compute in List.nth 24 (fst c5) _.
  (* 25. *)
  Definition s25_5 := Eval vm_compute in (step_checker s24_5 (List.nth 24 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s25_5.
  (* s25_5 = ({|  |} *)

  Eval vm_compute in List.nth 25 (fst c5) _.
  (* 26. *)
  Definition s26_5 := Eval vm_compute in (step_checker s25_5 (List.nth 25 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s26_5.
  (* s26_5 = ({|  |} *)

  Eval vm_compute in List.nth 26 (fst c5) _.
  (* 27. *)
  Definition s27_5 := Eval vm_compute in (step_checker s26_5 (List.nth 26 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s27_5.
  (* s27_5 = ({|  |} *)

  Eval vm_compute in List.nth 27 (fst c5) _.
  (* 28. *)
  Definition s28_5 := Eval vm_compute in (step_checker s27_5 (List.nth 27 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s28_5.
  (* s28_5 = ({|  |} *)

  Eval vm_compute in List.nth 28 (fst c5) _.
  (* 29. *)
  Definition s29_5 := Eval vm_compute in (step_checker s28_5 (List.nth 28 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s29_5.
  (* s29_5 = ({|  |} *)

  Eval vm_compute in List.nth 29 (fst c5) _.
  (* 30. *)
  Definition s30_5 := Eval vm_compute in (step_checker s29_5 (List.nth 29 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s30_5.
  (* s30_5 = ({|  |} *)

  Eval vm_compute in List.nth 30 (fst c5) _.
  (* 31. *)
  Definition s31_5 := Eval vm_compute in (step_checker s30_5 (List.nth 30 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s31_5.
  (* s31_5 = ({|  |} *)

  Eval vm_compute in List.nth 31 (fst c5) _.
  (* 32. *)
  Definition s32_5 := Eval vm_compute in (step_checker s31_5 (List.nth 31 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s32_5.
  (* s32_5 = ({|  |} *)

  Eval vm_compute in List.nth 32 (fst c5) _.
  (* 33. *)
  Definition s33_5 := Eval vm_compute in (step_checker s32_5 (List.nth 32 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s33_5.
  (* s33_5 = ({|  |} *)

  Eval vm_compute in List.nth 33 (fst c5) _.
  (* 34. *)
  Definition s34_5 := Eval vm_compute in (step_checker s33_5 (List.nth 33 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s34_5.
  (* s34_5 = ({|  |} *)

  Eval vm_compute in List.nth 34 (fst c5) _.
  (* 35. *)
  Definition s35_5 := Eval vm_compute in (step_checker s34_5 (List.nth 34 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s35_5.
  (* s35_5 = ({|  |} *)

  Eval vm_compute in List.nth 35 (fst c5) _.
  (* 36. *)
  Definition s36_5 := Eval vm_compute in (step_checker s35_5 (List.nth 35 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s36_5.
  (* s36_5 = ({|  |} *)

  Eval vm_compute in List.nth 36 (fst c5) _.
  (* 37. *)
  Definition s37_5 := Eval vm_compute in (step_checker s36_5 (List.nth 36 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s37_5.
  (* s37_5 = ({|  |} *)

  Eval vm_compute in List.nth 37 (fst c5) _.
  (* 38. *)
  Definition s38_5 := Eval vm_compute in (step_checker s37_5 (List.nth 37 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s38_5.
  (* s38_5 = ({|  |} *)

  Eval vm_compute in List.nth 38 (fst c5) _.
  (* 39. *)
  Definition s39_5 := Eval vm_compute in (step_checker s38_5 (List.nth 38 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s39_5.
  (* s39_5 = ({|  |} *)

  Eval vm_compute in List.nth 39 (fst c5) _.
  (* 40. *)
  Definition s40_5 := Eval vm_compute in (step_checker s39_5 (List.nth 39 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s40_5.
  (* s40_5 = ({|  |} *)

  Eval vm_compute in List.nth 40 (fst c5) _.
  (* 41. *)
  Definition s41_5 := Eval vm_compute in (step_checker s40_5 (List.nth 40 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s41_5.
  (* s41_5 = ({|  |} *)

  Eval vm_compute in List.nth 41 (fst c5) _.
  (* 42. *)
  Definition s42_5 := Eval vm_compute in (step_checker s41_5 (List.nth 41 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s42_5.
  (* s42_5 = ({|  |} *)

  Eval vm_compute in List.nth 42 (fst c5) _.
  (* 43. *)
  Definition s43_5 := Eval vm_compute in (step_checker s42_5 (List.nth 42 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s43_5.
  (* s43_5 = ({|  |} *)

  Eval vm_compute in List.nth 43 (fst c5) _.
  (* 44. *)
  Definition s44_5 := Eval vm_compute in (step_checker s43_5 (List.nth 43 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s44_5.
  (* s44_5 = ({|  |} *)

  Eval vm_compute in List.nth 44 (fst c5) _.
  (* 45. *)
  Definition s45_5 := Eval vm_compute in (step_checker s44_5 (List.nth 44 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s45_5.
  (* s45_5 = ({|  |} *)

  Eval vm_compute in List.nth 45 (fst c5) _.
  (* 46. *)
  Definition s46_5 := Eval vm_compute in (step_checker s45_5 (List.nth 45 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s46_5.
  (* s46_5 = ({|  |} *)

  Eval vm_compute in List.nth 46 (fst c5) _.
  (* 47. *)
  Definition s47_5 := Eval vm_compute in (step_checker s46_5 (List.nth 46 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s47_5.
  (* s47_5 = ({|  |} *)

  Eval vm_compute in List.nth 47 (fst c5) _.
  (* 48. *)
  Definition s48_5 := Eval vm_compute in (step_checker s47_5 (List.nth 47 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s48_5.
  (* s48_5 = ({|  |} *)

End Test5Debug.
