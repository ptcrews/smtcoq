Add Rec LoadPath "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.
Require Import Int31.
Local Open Scope int31_scope.

Section Test1Debug.
  Parse_certif_verit t_i1 t_func1 t_atom1 t_form1 root1 used_roots1 trace1
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test1.smt2"
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test1.pf".
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

  Eval vm_compute in List.nth 23 (fst c1) _.
  (* 24. *)
  Definition s24_1 := Eval vm_compute in (step_checker s23_1 (List.nth 23 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s24_1.
  (* s24_1 = ({|  |} *)

  Eval vm_compute in List.nth 24 (fst c1) _.
  (* 25. *)
  Definition s25_1 := Eval vm_compute in (step_checker s24_1 (List.nth 24 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s25_1.
  (* s25_1 = ({|  |} *)

  Eval vm_compute in List.nth 25 (fst c1) _.
  (* 26. *)
  Definition s26_1 := Eval vm_compute in (step_checker s25_1 (List.nth 25 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s26_1.
  (* s26_1 = ({|  |} *)

  Eval vm_compute in List.nth 26 (fst c1) _.
  (* 27. *)
  Definition s27_1 := Eval vm_compute in (step_checker s26_1 (List.nth 26 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s27_1.
  (* s27_1 = ({|  |} *)

  Eval vm_compute in List.nth 27 (fst c1) _.
  (* 28. *)
  Definition s28_1 := Eval vm_compute in (step_checker s27_1 (List.nth 27 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s28_1.
  (* s28_1 = ({|  |} *)

  Eval vm_compute in List.nth 28 (fst c1) _.
  (* 29. *)
  Definition s29_1 := Eval vm_compute in (step_checker s28_1 (List.nth 28 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s29_1.
  (* s29_1 = ({|  |} *)

  Eval vm_compute in List.nth 29 (fst c1) _.
  (* 30. *)
  Definition s30_1 := Eval vm_compute in (step_checker s29_1 (List.nth 29 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s30_1.
  (* s30_1 = ({|  |} *)

  Eval vm_compute in List.nth 30 (fst c1) _.
  (* 31. *)
  Definition s31_1 := Eval vm_compute in (step_checker s30_1 (List.nth 30 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s31_1.
  (* s31_1 = ({|  |} *)

  Eval vm_compute in List.nth 31 (fst c1) _.
  (* 32. *)
  Definition s32_1 := Eval vm_compute in (step_checker s31_1 (List.nth 31 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s32_1.
  (* s32_1 = ({|  |} *)

  Eval vm_compute in List.nth 32 (fst c1) _.
  (* 33. *)
  Definition s33_1 := Eval vm_compute in (step_checker s32_1 (List.nth 32 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s33_1.
  (* s33_1 = ({|  |} *)

  Eval vm_compute in List.nth 33 (fst c1) _.
  (* 34. *)
  Definition s34_1 := Eval vm_compute in (step_checker s33_1 (List.nth 33 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s34_1.
  (* s34_1 = ({|  |} *)

  Eval vm_compute in List.nth 34 (fst c1) _.
  (* 35. *)
  Definition s35_1 := Eval vm_compute in (step_checker s34_1 (List.nth 34 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s35_1.
  (* s35_1 = ({|  |} *)

  Eval vm_compute in List.nth 35 (fst c1) _.
  (* 36. *)
  Definition s36_1 := Eval vm_compute in (step_checker s35_1 (List.nth 35 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s36_1.
  (* s36_1 = ({|  |} *)

  Eval vm_compute in List.nth 36 (fst c1) _.
  (* 37. *)
  Definition s37_1 := Eval vm_compute in (step_checker s36_1 (List.nth 36 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s37_1.
  (* s37_1 = ({|  |} *)

  Eval vm_compute in List.nth 37 (fst c1) _.
  (* 38. *)
  Definition s38_1 := Eval vm_compute in (step_checker s37_1 (List.nth 37 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s38_1.
  (* s38_1 = ({|  |} *)

  Eval vm_compute in List.nth 38 (fst c1) _.
  (* 39. *)
  Definition s39_1 := Eval vm_compute in (step_checker s38_1 (List.nth 38 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s39_1.
  (* s39_1 = ({|  |} *)

  Eval vm_compute in List.nth 39 (fst c1) _.
  (* 40. *)
  Definition s40_1 := Eval vm_compute in (step_checker s39_1 (List.nth 39 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s40_1.
  (* s40_1 = ({|  |} *)

  Eval vm_compute in List.nth 40 (fst c1) _.
  (* 41. *)
  Definition s41_1 := Eval vm_compute in (step_checker s40_1 (List.nth 40 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s41_1.
  (* s41_1 = ({|  |} *)

  Eval vm_compute in List.nth 41 (fst c1) _.
  (* 42. *)
  Definition s42_1 := Eval vm_compute in (step_checker s41_1 (List.nth 41 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s42_1.
  (* s42_1 = ({|  |} *)

  Eval vm_compute in List.nth 42 (fst c1) _.
  (* 43. *)
  Definition s43_1 := Eval vm_compute in (step_checker s42_1 (List.nth 42 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s43_1.
  (* s43_1 = ({|  |} *)

  Eval vm_compute in List.nth 43 (fst c1) _.
  (* 44. *)
  Definition s44_1 := Eval vm_compute in (step_checker s43_1 (List.nth 43 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s44_1.
  (* s44_1 = ({|  |} *)

  Eval vm_compute in List.nth 44 (fst c1) _.
  (* 45. *)
  Definition s45_1 := Eval vm_compute in (step_checker s44_1 (List.nth 44 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s45_1.
  (* s45_1 = ({|  |} *)

  Eval vm_compute in List.nth 45 (fst c1) _.
  (* 46. *)
  Definition s46_1 := Eval vm_compute in (step_checker s45_1 (List.nth 45 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s46_1.
  (* s46_1 = ({|  |} *)

  Eval vm_compute in List.nth 46 (fst c1) _.
  (* 47. *)
  Definition s47_1 := Eval vm_compute in (step_checker s46_1 (List.nth 46 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s47_1.
  (* s47_1 = ({|  |} *)

  Eval vm_compute in List.nth 47 (fst c1) _.
  (* 48. *)
  Definition s48_1 := Eval vm_compute in (step_checker s47_1 (List.nth 47 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s48_1.
  (* s48_1 = ({|  |} *)

  Eval vm_compute in List.nth 48 (fst c1) _.
  (* 49. *)
  Definition s49_1 := Eval vm_compute in (step_checker s48_1 (List.nth 48 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s49_1.
  (* s49_1 = ({|  |} *)

  Eval vm_compute in List.nth 49 (fst c1) _.
  (* 50. *)
  Definition s50_1 := Eval vm_compute in (step_checker s49_1 (List.nth 49 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s50_1.
  (* s50_1 = ({|  |} *)

  Eval vm_compute in List.nth 50 (fst c1) _.
  (* 51. *)
  Definition s51_1 := Eval vm_compute in (step_checker s50_1 (List.nth 50 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s51_1.
  (* s51_1 = ({|  |} *)

  Eval vm_compute in List.nth 51 (fst c1) _.
  (* 52. *)
  Definition s52_1 := Eval vm_compute in (step_checker s51_1 (List.nth 51 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s52_1.
  (* s52_1 = ({|  |} *)

  Eval vm_compute in List.nth 52 (fst c1) _.
  (* 53. *)
  Definition s53_1 := Eval vm_compute in (step_checker s52_1 (List.nth 52 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s53_1.
  (* s53_1 = ({|  |} *)

  Eval vm_compute in List.nth 53 (fst c1) _.
  (* 54. *)
  Definition s54_1 := Eval vm_compute in (step_checker s53_1 (List.nth 53 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s54_1.
  (* s54_1 = ({|  |} *)

  Eval vm_compute in List.nth 54 (fst c1) _.
  (* 55. *)
  Definition s55_1 := Eval vm_compute in (step_checker s54_1 (List.nth 54 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s55_1.
  (* s55_1 = ({|  |} *)

  Eval vm_compute in List.nth 55 (fst c1) _.
  (* 56. *)
  Definition s56_1 := Eval vm_compute in (step_checker s55_1 (List.nth 55 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s56_1.
  (* s56_1 = ({|  |} *)

  Eval vm_compute in List.nth 56 (fst c1) _.
  (* 57. *)
  Definition s57_1 := Eval vm_compute in (step_checker s56_1 (List.nth 56 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s57_1.
  (* s57_1 = ({|  |} *)

  Eval vm_compute in List.nth 57 (fst c1) _.
  (* 58. *)
  Definition s58_1 := Eval vm_compute in (step_checker s57_1 (List.nth 57 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s58_1.
  (* s58_1 = ({|  |} *)

  Eval vm_compute in List.nth 58 (fst c1) _.
  (* 59. *)
  Definition s59_1 := Eval vm_compute in (step_checker s58_1 (List.nth 58 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s59_1.
  (* s59_1 = ({|  |} *)

  Eval vm_compute in List.nth 59 (fst c1) _.
  (* 60. *)
  Definition s60_1 := Eval vm_compute in (step_checker s59_1 (List.nth 59 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s60_1.
  (* s60_1 = ({|  |} *)

  Eval vm_compute in List.nth 60 (fst c1) _.
  (* 61. *)
  Definition s61_1 := Eval vm_compute in (step_checker s60_1 (List.nth 60 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s61_1.
  (* s61_1 = ({|  |} *)

  Eval vm_compute in List.nth 61 (fst c1) _.
  (* 62. *)
  Definition s62_1 := Eval vm_compute in (step_checker s61_1 (List.nth 61 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s62_1.
  (* s62_1 = ({|  |} *)

  Eval vm_compute in List.nth 62 (fst c1) _.
  (* 63. *)
  Definition s63_1 := Eval vm_compute in (step_checker s62_1 (List.nth 62 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s63_1.
  (* s63_1 = ({|  |} *)

  Eval vm_compute in List.nth 63 (fst c1) _.
  (* 64. *)
  Definition s64_1 := Eval vm_compute in (step_checker s63_1 (List.nth 63 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s64_1.
  (* s64_1 = ({|  |} *)

  Eval vm_compute in List.nth 64 (fst c1) _.
  (* 65. *)
  Definition s65_1 := Eval vm_compute in (step_checker s64_1 (List.nth 64 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s65_1.
  (* s65_1 = ({|  |} *)

  Eval vm_compute in List.nth 65 (fst c1) _.
  (* 66. *)
  Definition s66_1 := Eval vm_compute in (step_checker s65_1 (List.nth 65 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s66_1.
  (* s66_1 = ({|  |} *)

  Eval vm_compute in List.nth 66 (fst c1) _.
  (* 67. *)
  Definition s67_1 := Eval vm_compute in (step_checker s66_1 (List.nth 66 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s67_1.
  (* s67_1 = ({|  |} *)

  Eval vm_compute in List.nth 67 (fst c1) _.
  (* 68. *)
  Definition s68_1 := Eval vm_compute in (step_checker s67_1 (List.nth 67 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s68_1.
  (* s68_1 = ({|  |} *)

  Eval vm_compute in List.nth 68 (fst c1) _.
  (* 69. *)
  Definition s69_1 := Eval vm_compute in (step_checker s68_1 (List.nth 68 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s69_1.
  (* s69_1 = ({|  |} *)

  Eval vm_compute in List.nth 69 (fst c1) _.
  (* 70. *)
  Definition s70_1 := Eval vm_compute in (step_checker s69_1 (List.nth 69 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s70_1.
  (* s70_1 = ({|  |} *)

  Eval vm_compute in List.nth 70 (fst c1) _.
  (* 71. *)
  Definition s71_1 := Eval vm_compute in (step_checker s70_1 (List.nth 70 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s71_1.
  (* s71_1 = ({|  |} *)

  Eval vm_compute in List.nth 71 (fst c1) _.
  (* 72. *)
  Definition s72_1 := Eval vm_compute in (step_checker s71_1 (List.nth 71 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s72_1.
  (* s72_1 = ({|  |} *)

  Eval vm_compute in List.nth 72 (fst c1) _.
  (* 73. *)
  Definition s73_1 := Eval vm_compute in (step_checker s72_1 (List.nth 72 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s73_1.
  (* s73_1 = ({|  |} *)

  Eval vm_compute in List.nth 73 (fst c1) _.
  (* 74. *)
  Definition s74_1 := Eval vm_compute in (step_checker s73_1 (List.nth 73 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s74_1.
  (* s74_1 = ({|  |} *)

  Eval vm_compute in List.nth 74 (fst c1) _.
  (* 75. *)
  Definition s75_1 := Eval vm_compute in (step_checker s74_1 (List.nth 74 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s75_1.
  (* s75_1 = ({|  |} *)

  Eval vm_compute in List.nth 75 (fst c1) _.
  (* 76. *)
  Definition s76_1 := Eval vm_compute in (step_checker s75_1 (List.nth 75 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s76_1.
  (* s76_1 = ({|  |} *)

  Eval vm_compute in List.nth 76 (fst c1) _.
  (* 77. *)
  Definition s77_1 := Eval vm_compute in (step_checker s76_1 (List.nth 76 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s77_1.
  (* s77_1 = ({|  |} *)

  Eval vm_compute in List.nth 77 (fst c1) _.
  (* 78. *)
  Definition s78_1 := Eval vm_compute in (step_checker s77_1 (List.nth 77 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s78_1.
  (* s78_1 = ({|  |} *)

  Eval vm_compute in List.nth 78 (fst c1) _.
  (* 79. *)
  Definition s79_1 := Eval vm_compute in (step_checker s78_1 (List.nth 78 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s79_1.
  (* s79_1 = ({|  |} *)

End Test1Debug.
