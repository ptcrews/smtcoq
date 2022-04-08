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
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritparser/smtcoq/examples/test1.smt2" 
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritparser/smtcoq/examples/test1.vtlog".
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
  Definition nclauses1 := Eval vm_compute in (match trace1 with Certif a _ _ => a end).
  Definition c1 := Eval vm_compute in (match trace1 with Certif _ a _ => a end). (* Certificate *)
  Definition conf1 := Eval vm_compute in (match trace1 with Certif _ _ a => a end). (* Look here in the state for the empty clause*)
  (* list step * step *)
  Print c1. Print conf1.
  Eval vm_compute in List.length (fst c1).
  (* 9 steps in the certificate *)

  (* Sanity check that atoms and formulas are well-typed. Must return true *)
  Eval vm_compute in (Form.check_form t_form1 && Atom.check_atom t_atom1 && Atom.wt t_i1 t_func1 t_atom1).
  

  (* States from c1 *)
  
  (* Start state *)
  Definition s0_1 := Eval vm_compute in (add_roots (S.make nclauses1) root1 used_roots1).
  Print s0_1.
  (* s0_1 = ({| 0 -> (4 :: nil) |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  (* NotSimplify 1 6 *)
  Definition s1_1 := Eval vm_compute in (step_checker s0_1 (List.nth 0 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s1_1.
  (* s1_1 = ({| 0 -> (4 :: nil),  1 -> (6 :: nil) |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  (* IffCong 1 (1 :: nil) 10 *)
  Definition s2_1 := Eval vm_compute in (step_checker s1_1 (List.nth 1 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s2_1.
  (* s2_1 = ({| 0 -> (4 :: nil), 1 -> (10 :: nil) |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  (* AndSimplify 2 14 *)
  Definition s3_1 := Eval vm_compute in (step_checker s2_1 (List.nth 2 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s3_1.
  (* s3_1 = ({| 0 -> (4 :: nil), 1 -> (10 :: nil), 2 -> (14 :: nil) |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  (* AndSimplify 3 16 *)
  Definition s4_1 := Eval vm_compute in (step_checker s3_1 (List.nth 3 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s4_1.
  (* s4_1 = ({| 0 -> (4 :: nil), 1 -> (10 :: nil), 2 -> (14 :: nil), 3 -> (16 :: nil) |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  (* IffTrans 3 (1 :: 2 :: 3 :: nil) 18 *)
  Definition s5_1 := Eval vm_compute in (step_checker s4_1 (List.nth 4 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s5_1.
  (* s5_1 = ({| 0 -> (4 :: nil), 1 -> (10 :: nil), 2 -> (14 :: nil), 3 -> (18 :: nil) |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  (* BuildDef2 2 19 *)
  Definition s6_1 := Eval vm_compute in (step_checker s5_1 (List.nth 5 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s6_1.
  (* s6_1 = ({| 0 -> (4 :: nil), 1 -> (10 :: nil), 2 -> (2 :: 5 :: 19 :: nil), 3 -> (18 :: nil) |}
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  (* Res 0 ({| 0 -> 2, 1 -> 3, 2 -> 0 |}) *)
  Definition s7_1 := Eval vm_compute in (step_checker s6_1 (List.nth 6 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s7_1.
  (* s7_1 = ({| 0 -> (2 :: nil), 1 -> (10 :: nil), 2 -> (2 :: 5 :: 19 :: nil), 3 -> (18 :: nil) |},
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  (* CFalse 3 *)
  Definition s8_1 := Eval vm_compute in (step_checker s7_1 (List.nth 7 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s8_1.
  (* s8_1 = ({| 0 -> (2 :: nil), 1 -> (10 :: nil), 2 -> (2 :: 5 :: 19 :: nil), 3 ->  (3 :: nil) |},
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  (* Res 3 ({| 0 -> 0, 1 -> 3 |}) *)
  Definition s9_1 := Eval vm_compute in (step_checker s8_1 (List.nth 8 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s9_1.
  (* s9_1 = ({| 0 -> (2 :: nil), 1 -> (10 :: nil), 2 -> (2 :: 5 :: 19 :: nil), 3 -> nil |},
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)
  
  (* If the main_checker returns true, SMTCoq has successfully managed to check the proof *)
  Eval vm_compute in (euf_checker C.is_false (add_roots (S.make nclauses1) root1 used_roots1) c1 conf1).
End Checker_SmtEx1Debug.

(*Section Checker_SmtEx1.
  Parse_certif_verit t_i1 t_func1 t_atom1 t_form1 root1 used_roots1 trace1 
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritparser/smtcoq/examples/test1.smt2" 
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritparser/smtcoq/examples/test1.vtlog".
End Checker_SmtEx1.*)

Lemma ex1: negb (true && (negb true)).
Proof.
  verit_bool.
Qed.

Section Checker_SmtEx2Debug.
  Parse_certif_verit t_i2 t_func2 t_atom2 t_form2 root2 used_roots2 trace2 
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritparser/smtcoq/examples/test2.smt2" 
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritparser/smtcoq/examples/test2.vtlog".
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
  Print trace2.
  
  (* Components of the certificate *)
  Definition nclauses2 := Eval vm_compute in (match trace2 with Certif a _ _ => a end).
  Definition c2 := Eval vm_compute in (match trace2 with Certif _ a _ => a end).
  Definition conf2 := Eval vm_compute in (match trace2 with Certif _ _ a => a end).
  (* list step * step *)
  Print c2. Print conf2.
  Eval vm_compute in List.length (fst c2).
  (* 12 steps in the certificate *)

  (* Sanity check that atoms and formulas are well-typed. Must return true *)
  Eval vm_compute in (Form.check_form t_form2 && Atom.check_atom t_atom2 && Atom.wt t_i2 t_func2 t_atom2).


  (* States from c2 *)
  
  (* Start state *)
  Definition s0_2 := Eval vm_compute in (add_roots (S.make nclauses2) root2 used_roots2).
  Print s0_2.
  (* s0_2 = ({| 0 -> (5 :: nil) |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  (* OrSimplify 1 8 *)
  Definition s1_2 := Eval vm_compute in (step_checker s0_2 (List.nth 0 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s1_2.
  (* s1_2 = ({| 0 -> (5 :: nil),  1 -> (8 :: nil) |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  (* OrSimplify 2 10 *)
  Definition s2_2 := Eval vm_compute in (step_checker s1_2 (List.nth 1 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s2_2.
  (* s2_2 = ({| 0 -> (5 :: nil), 1 -> (8 :: nil), 2 -> (10 :: nil) |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  (* IffTrans 2 (1 :: 2 :: nil) 12 *)
  Definition s3_2 := Eval vm_compute in (step_checker s2_2 (List.nth 2 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s3_2.
  (* s3_2 = ({| 0 -> (5 :: nil), 1 -> (8 :: nil), 2 -> (12 :: nil) |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  (* IffCong 2 (2 :: nil) 14 *)
  Definition s4_2 := Eval vm_compute in (step_checker s3_2 (List.nth 3 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s4_2.
  (* s4_2 = ({| 0 -> (5 :: nil), 1 -> (8 :: nil), 2 -> (14 :: nil) |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  (* NotSimplify 1 16 *)
  Definition s5_2 := Eval vm_compute in (step_checker s4_2 (List.nth 4 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s5_2.
  (* s5_2 = ({| 0 -> (5 :: nil), 1 -> (16 :: nil), 2 -> (14 :: nil) |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  (* IffTrans 1 (2 :: 1 :: nil) 18 *)
  Definition s6_2 := Eval vm_compute in (step_checker s5_2 (List.nth 5 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s6_2.
  (* s6_2 = ({| 0 -> (5 :: nil), 1 -> (18 :: nil), 2 -> (14 :: nil) |}
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  (* BuildDef2 2 19 *)
  Definition s7_2 := Eval vm_compute in (step_checker s6_2 (List.nth 6 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s7_2.
  (* s7_2 = ({| 0 -> (5 :: nil), 1 -> (18 :: nil), 2 -> (2 :: 4 :: 19 :: nil) |},
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  (* NotNot 3 5 *)
  Definition s8_2 := Eval vm_compute in (step_checker s7_2 (List.nth 7 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s8_2.
  (* s8_2 = ({| 0 -> (5 :: nil), 1 -> (18 :: nil), 2 -> (2 :: 4 :: 19 :: nil), 3 ->  (4 :: 5 :: nil) |},
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)
  
  (* s8_2 = ({| 0 -> (5 :: nil), 1 -> (18 :: nil), 2 -> (2 :: 4 :: 19 :: nil), 3 ->  (4 :: 21 :: nil) |},
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)
  (* Solution 1: Since we correctly parse double negations as `Fnot2 1`, this step correctly
     constructs `~(Fnot2 1 (T or F))`.
     However, the previous step constructs `[~(T or F) != F, (T or F), F]`
     instead of `[(~T or F) != F, Fnot2 1 (T or F), F]` because 
     `Cnf.check_BuildDef2` constructs the second and third terms of the 
     clause. To change `check_BuildDef2`, we need to be able to hash 
     `Fnot2` terms, which isn't straightforward. *)

  (* Res 3 ({| 0 -> 2, 1 -> 3|}) *)
  Definition s9_2 := Eval vm_compute in (step_checker s8_2 (List.nth 8 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s9_2.
  Eval vm_compute in C.resolve (2 :: 4 :: 19 :: nil) (4 :: 5 :: nil).
  (* Expected output : 2 :: 4 :: 19 :: nil *)
  (* Actual output : 2 :: 4 :: 5 :: 0 :: nil *)
  (* Solution 2: From C.resolve:
     When the clauses being resolved have a common literal, that literal is taken out of consideration for being a pivot.
     Since both clauses have 4, 4 is never eventually compared with 5 for resolution. Perhaps this was an optimization that 
     didn't invalidate proofs when the not_not rule didn't exist, but now we can have proofs where the pivot can appear more 
     than 2 times in the premises for resolution (because of the elimination of double negations in the not_not rule). *)
  (* s8_2 = ({| 0 -> (5 :: nil), 1 -> (18 :: nil), 2 -> (2 :: 4 :: 19 :: nil), 3 ->  (2 :: 4 :: 5 :: 0 :: nil) |},
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)
  
  (* Res 0 ({| 0 -> 3, 1 -> 1, 2 -> 0 |}) *)
  Definition s10_2 := Eval vm_compute in (step_checker s9_2 (List.nth 9 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s10_2.
  (* s8_2 = ({| 0 -> (2 :: 0 :: nil), 1 -> (18 :: nil), 2 -> (2 :: 4 :: 19 :: nil), 3 ->  (2 :: 4 :: 5 :: 0 :: nil) |},
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  (* CFalse 1 *)
  Definition s11_2 := Eval vm_compute in (step_checker s10_2 (List.nth 10 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s11_2.
  (* s8_2 = ({| 0 -> (2 :: 0 :: nil), 1 -> (3 :: nil), 2 -> (2 :: 4 :: 19 :: nil), 3 ->  (2 :: 4 :: 5 :: 0 :: nil) |},
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  (* Res 1 ({| 0 -> 0, 1 -> 1 |}) *)
  Definition s12_2 := Eval vm_compute in (step_checker s11_2 (List.nth 11 (fst c2) (CTrue t_func2 t_atom2 t_form2 0))).
  Print s12_2.
  (* s8_2 = ({| 0 -> (2 :: 0 :: nil), 1 -> (0 :: nil), 2 -> (2 :: 4 :: 19 :: nil), 3 ->  (2 :: 4 :: 5 :: 0 :: nil) |},
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  (* If the main_checker returns true, SMTCoq has successfully managed to check the proof *)
  Eval vm_compute in (euf_checker C.is_false (add_roots (S.make nclauses2) root2 used_roots2) c2 conf2).
End Checker_SmtEx2Debug.

(*
Section Checker_SmtEx2.
  Parse_certif_verit t_i2 t_func2 t_atom2 t_form2 root2 used_roots2 trace2 
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritparser/smtcoq/examples/test2.smt2" 
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritparser/smtcoq/examples/test2.vtlog".
End Checker_SmtEx2.
*)

Lemma ex2: true || false.
Proof.
  verit_bool.
Qed.

Section Checker_SmtEx3.
  Parse_certif_verit t_i3 t_func3 t_atom3 t_form3 root3 used_roots3 trace3
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritparser/smtcoq/examples/test3.smt2" 
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritparser/smtcoq/examples/test3.vtlog".
End Checker_SmtEx3.

Lemma ex3: forall p, negb (p && (negb p)).
Proof.
  verit_bool.
Qed.

Lemma ex4: forall a b c, ((a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a)) = false.
Proof.
  verit_bool.
Qed.

Section Checker_SmtEx5Debug.
  Parse_certif_verit t_i5 t_func5 t_atom5 t_form5 root5 used_roots5 trace5 
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritparser/smtcoq/examples/test5.smt2" 
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritparser/smtcoq/examples/test5.vtlog".
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
  Print trace5. 
  
  (* Components of the certificate *)
  Definition nclauses5 := Eval vm_compute in (match trace5 with Certif a _ _ => a end).
  Definition c5 := Eval vm_compute in (match trace5 with Certif _ a _ => a end).
  Definition conf5 := Eval vm_compute in (match trace5 with Certif _ _ a => a end).
  (* list step * step *)
  Print c5.
  Eval vm_compute in List.length (fst c5).
  (* 10 steps in the certificate *)

  (* Sanity check that atoms and formulas are well-typed. Must return true *)
  Eval vm_compute in (Form.check_form t_form5 && Atom.check_atom t_atom5 && Atom.wt t_i5 t_func5 t_atom5).
  

  (* States from c5 *)
  
  (* Start state *)
  Definition s0_5 := Eval vm_compute in (add_roots (S.make nclauses2) root5 used_roots5).
  Print s0_5.
  (* s0_5 = ({| 0 -> (7 :: nil) |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  (* OrSimplify 1 8 *)
  Definition s1_5 := Eval vm_compute in (step_checker s0_5 (List.nth 0 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s1_5.
  (* s1_5 = ({| 0 -> (7 :: nil),  1 -> (8 :: nil) |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  (* IffCong 1 (1 :: nil) 10 *)
  Definition s2_5 := Eval vm_compute in (step_checker s1_5 (List.nth 1 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s2_5.
  (* s2_5 = ({| 0 -> (7 :: nil), 1 -> (10 :: nil) |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  (* NotSimplify 2 12 *)
  Definition s3_5 := Eval vm_compute in (step_checker s2_5 (List.nth 2 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s3_5.
  (* s3_5 = ({| 0 -> (7 :: nil), 1 -> (10 :: nil), 2 -> (12 :: nil) |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  (* IffTrans 2 (1 :: 2 :: nil) 14 *)
  Definition s4_5 := Eval vm_compute in (step_checker s3_5 (List.nth 3 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s4_5.
  (* s4_5 = ({| 0 -> (7 :: nil), 1 -> (10 :: nil), 2 -> (14 :: nil) |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  (* BuildDef2 1 15 *)
  Definition s5_5 := Eval vm_compute in (step_checker s4_5 (List.nth 4 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s5_5.
  (* s5_5 = ({| 0 -> (7 :: nil), 1 -> (2 :: 16 :: 15 :: nil), 2 -> (14 :: nil) |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  (* NotNot 3 7 *)
  Definition s6_5 := Eval vm_compute in (step_checker s5_5 (List.nth 5 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s6_5.
  (* s6_5 = ({| 0 -> (7 :: nil), 1 -> (2 :: 6 :: 15 :: nil), 2 -> (14 :: nil), 3 -> (0 :: nil) |}
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  (* Res 3 {| 0 -> 1, 1 -> 3 |} *)
  Definition s7_5 := Eval vm_compute in (step_checker s6_5 (List.nth 6 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s7_5.

  (* Res 0 {| 0 -> 3, 1 -> 2 |} *)
  Definition s8_5 := Eval vm_compute in (step_checker s7_5 (List.nth 7 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s8_5.
  
  (* CFalse 2 *)
  Definition s9_5 := Eval vm_compute in (step_checker s8_5 (List.nth 8 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s9_5. 
  
  (* Res 2 {| 0 -> 0, 1 -> 2 |} *)
  Definition s10_5 := Eval vm_compute in (step_checker s9_5 (List.nth 9 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s10_5.

  (* CFalse 1 *)
  Definition s11_5 := Eval vm_compute in (step_checker s10_5 (List.nth 10 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s11_5.

  (* Res 1 ({| 0 -> 0, 1 -> 1 |}) *)
  Definition s12_5 := Eval vm_compute in (step_checker s11_5 (List.nth 11 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
  Print s12_5.

End Checker_SmtEx5Debug.

Lemma ex5: forall p, p || (negb p).
Proof.
  verit_bool.
Qed.


Local Open Scope Z_scope.

Goal forall (a b : Z) (P : Z -> bool) (f : Z -> Z),
  (negb (Z.eqb (f a) b)) || (negb (P (f a))) || (P b).
Proof.
  verit_bool.
Qed.

(* Issue with LIA?
Goal forall b1 b2 x1 x2,
    implb
      (ifb b1
           (ifb b2 (Z.eqb (2*x1+1) (2*x2+1)) (Z.eqb (2*x1+1) (2*x2)))
           (ifb b2 (Z.eqb (2*x1) (2*x2+1)) (Z.eqb (2*x1) (2*x2))))
      ((implb b1 b2) && (implb b2 b1) && (Z.eqb x1 x2)).
Proof.
  verit_bool.
Qed.*)

Goal forall
    (x y: Z)
    (f: Z -> Z),
    x = y + 1 -> f y = f (x - 1).
Proof.
  verit.
Qed.

Section Checker_SmtEx6Debug.
  Parse_certif_verit t_i6 t_func6 t_atom6 t_form6 root6 used_roots6 trace6
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritparser/smtcoq/examples/test6.smt2"
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritparser/smtcoq/examples/test6.vtlog".
  Definition nclauses6 := Eval vm_compute in (match trace6 with Certif a _ _ => a end).
  Definition c6 := Eval vm_compute in (match trace6 with Certif _ a _ => a end). (* Certificate *)
  Definition conf6 := Eval vm_compute in (match trace6 with Certif _ _ a => a end). (* Look here in the state for the empty clause*)
  Eval vm_compute in (Form.check_form t_form6 && Atom.check_atom t_atom6 && Atom.wt t_i6 t_func6 t_atom6).
  Eval vm_compute in List.length (fst c6).
  Definition s0_6 := Eval vm_compute in (add_roots (S.make nclauses6) root6 used_roots6).
  Definition s1_6 := Eval vm_compute in (step_checker s0_6 (List.nth 0 (fst c6) (CTrue t_func6 t_atom6 t_form6 0))).
  Definition s2_6 := Eval vm_compute in (step_checker s1_6 (List.nth 1 (fst c6) (CTrue t_func6 t_atom6 t_form6 0))).
  Definition s3_6 := Eval vm_compute in (step_checker s2_6 (List.nth 2 (fst c6) (CTrue t_func6 t_atom6 t_form6 0))).
  Definition s4_6 := Eval vm_compute in (step_checker s3_6 (List.nth 3 (fst c6) (CTrue t_func6 t_atom6 t_form6 0))).
  Definition s5_6 := Eval vm_compute in (step_checker s4_6 (List.nth 4 (fst c6) (CTrue t_func6 t_atom6 t_form6 0))).
  (* If the main_checker returns true, SMTCoq has successfully managed to check the proof *)
  Eval vm_compute in (euf_checker C.is_false (add_roots (S.make nclauses6) root6 used_roots6) c6 conf6).
End Checker_SmtEx6Debug.

Section Checker_SmtEx7Debug.
  Parse_certif_verit t_i7 t_func7 t_atom7 t_form7 root7 used_roots7 trace7
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritparser/smtcoq/examples/test7.smt2"
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritparser/smtcoq/examples/test7.vtlog".
  Definition nclauses7 := Eval vm_compute in (match trace7 with Certif a _ _ => a end).
  Definition c7 := Eval vm_compute in (match trace7 with Certif _ a _ => a end). (* Certificate *)
  Definition conf7 := Eval vm_compute in (match trace7 with Certif _ _ a => a end). (* Look here in the state for the empty clause*)
  Eval vm_compute in (Form.check_form t_form7 && Atom.check_atom t_atom7 && Atom.wt t_i7 t_func7 t_atom7).
  Eval vm_compute in List.length (fst c7). Print conf7. (*9*)
  
  Definition s0_7 := Eval vm_compute in (add_roots (S.make nclauses7) root7 used_roots7).
  Print s0_7.
  Definition s1_7 := Eval vm_compute in (step_checker s0_7 (List.nth 0 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 0 (fst c7)). Print s1_7.
  Definition s2_7 := Eval vm_compute in (step_checker s1_7 (List.nth 1 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 1 (fst c7)). Print s2_7.
  Definition s3_7 := Eval vm_compute in (step_checker s2_7 (List.nth 2 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 2 (fst c7)). Print s3_7.
  Definition s4_7 := Eval vm_compute in (step_checker s3_7 (List.nth 3 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 3 (fst c7)). Print s4_7.
  Definition s5_7 := Eval vm_compute in (step_checker s4_7 (List.nth 4 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 4 (fst c7)). Print s5_7.
  Definition s6_7 := Eval vm_compute in (step_checker s5_7 (List.nth 5 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 5 (fst c7)). Print s6_7.
  Definition s7_7 := Eval vm_compute in (step_checker s6_7 (List.nth 6 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 6 (fst c7)). Print s7_7.
  Definition s8_7 := Eval vm_compute in (step_checker s7_7 (List.nth 7 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 7 (fst c7)). Print s8_7.
  Definition s9_7 := Eval vm_compute in (step_checker s8_7 (List.nth 8 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 8 (fst c7)). Print s9_7.
  Definition s10_7 := Eval vm_compute in (step_checker s9_7 (List.nth 9 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 9 (fst c7)). Print s10_7.
  Definition s11_7 := Eval vm_compute in (step_checker s10_7 (List.nth 10 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 10 (fst c7)). Print s11_7.
  Definition s12_7 := Eval vm_compute in (step_checker s11_7 (List.nth 11 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 11 (fst c7)). Print s12_7.
  Definition s13_7 := Eval vm_compute in (step_checker s12_7 (List.nth 12 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 12 (fst c7)). Print s13_7.
  Definition s14_7 := Eval vm_compute in (step_checker s13_7 (List.nth 13 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 13 (fst c7)). Print s14_7.
  Definition s15_7 := Eval vm_compute in (step_checker s14_7 (List.nth 14 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 14 (fst c7)). Print s15_7.
  Definition s16_7 := Eval vm_compute in (step_checker s15_7 (List.nth 15 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 15 (fst c7)). Print s16_7.
  Definition s17_7 := Eval vm_compute in (step_checker s16_7 (List.nth 16 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 16 (fst c7)). Print s17_7.
  Definition s18_7 := Eval vm_compute in (step_checker s17_7 (List.nth 17 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 17 (fst c7)). Print s18_7.
  Definition s19_7 := Eval vm_compute in (step_checker s18_7 (List.nth 18 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 18 (fst c7)). Print s19_7.
  Definition s20_7 := Eval vm_compute in (step_checker s19_7 (List.nth 19 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 19 (fst c7)). Print s20_7.
  Definition s21_7 := Eval vm_compute in (step_checker s20_7 (List.nth 20 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 20 (fst c7)). Print s21_7.
  Definition s22_7 := Eval vm_compute in (step_checker s21_7 (List.nth 21 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 21 (fst c7)). Print s22_7.
  Definition s23_7 := Eval vm_compute in (step_checker s22_7 (List.nth 22 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 22 (fst c7)). Print s23_7.
  Definition s24_7 := Eval vm_compute in (step_checker s23_7 (List.nth 23 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 23 (fst c7)). Print s24_7.
  Definition s25_7 := Eval vm_compute in (step_checker s24_7 (List.nth 24 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 24 (fst c7)). Print s25_7.
  Definition s26_7 := Eval vm_compute in (step_checker s25_7 (List.nth 25 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 25 (fst c7)). Print s26_7.
  Definition s27_7 := Eval vm_compute in (step_checker s26_7 (List.nth 26 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 26 (fst c7)). Print s27_7.
  Definition s28_7 := Eval vm_compute in (step_checker s27_7 (List.nth 27 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 27 (fst c7)). Print s28_7.
  Definition s29_7 := Eval vm_compute in (step_checker s28_7 (List.nth 28 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 28 (fst c7)). Print s29_7.
  Definition s30_7 := Eval vm_compute in (step_checker s29_7 (List.nth 29 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 29 (fst c7)). Print s30_7.
  Definition s31_7 := Eval vm_compute in (step_checker s30_7 (List.nth 30 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 30 (fst c7)). Print s31_7.
  Definition s32_7 := Eval vm_compute in (step_checker s31_7 (List.nth 31 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 31 (fst c7)). Print s32_7.
  Definition s33_7 := Eval vm_compute in (step_checker s32_7 (List.nth 32 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 32 (fst c7)). Print s33_7.
  Definition s34_7 := Eval vm_compute in (step_checker s33_7 (List.nth 33 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 33 (fst c7)). Print s34_7.
  Definition s35_7 := Eval vm_compute in (step_checker s34_7 (List.nth 34 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 34 (fst c7)). Print s35_7.
  Definition s36_7 := Eval vm_compute in (step_checker s35_7 (List.nth 35 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 35 (fst c7)). Print s36_7.
  Definition s37_7 := Eval vm_compute in (step_checker s36_7 (List.nth 36 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 36 (fst c7)). Print s37_7.
  Definition s38_7 := Eval vm_compute in (step_checker s37_7 (List.nth 37 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 37 (fst c7)). Print s38_7.
  Definition s39_7 := Eval vm_compute in (step_checker s38_7 (List.nth 38 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 38 (fst c7)). Print s39_7.
  Definition s40_7 := Eval vm_compute in (step_checker s39_7 (List.nth 39 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 39 (fst c7)). Print s40_7.
  Definition s41_7 := Eval vm_compute in (step_checker s40_7 (List.nth 40 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 40 (fst c7)). Print s41_7.
  Definition s42_7 := Eval vm_compute in (step_checker s41_7 (List.nth 41 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 41 (fst c7)). Print s42_7.
  Definition s43_7 := Eval vm_compute in (step_checker s42_7 (List.nth 42 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 42 (fst c7)). Print s43_7.
  Definition s44_7 := Eval vm_compute in (step_checker s43_7 (List.nth 43 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 43 (fst c7)). Print s44_7.
  Definition s45_7 := Eval vm_compute in (step_checker s44_7 (List.nth 44 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 44 (fst c7)). Print s45_7.
  Definition s46_7 := Eval vm_compute in (step_checker s45_7 (List.nth 45 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 45 (fst c7)). Print s46_7.
  Definition s47_7 := Eval vm_compute in (step_checker s46_7 (List.nth 46 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 46 (fst c7)). Print s47_7.
  Definition s48_7 := Eval vm_compute in (step_checker s47_7 (List.nth 47 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 47 (fst c7)). Print s48_7.
  Definition s49_7 := Eval vm_compute in (step_checker s48_7 (List.nth 48 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 48 (fst c7)). Print s49_7.
  Definition s50_7 := Eval vm_compute in (step_checker s49_7 (List.nth 49 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 49 (fst c7)). Print s50_7.
  Definition s51_7 := Eval vm_compute in (step_checker s50_7 (List.nth 50 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 50 (fst c7)). Print s51_7.
  Definition s52_7 := Eval vm_compute in (step_checker s51_7 (List.nth 51 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 51 (fst c7)). Print s52_7.
  Definition s53_7 := Eval vm_compute in (step_checker s52_7 (List.nth 52 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 52 (fst c7)). Print s53_7.
  Definition s54_7 := Eval vm_compute in (step_checker s53_7 (List.nth 53 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 53 (fst c7)). Print s54_7.
  Definition s55_7 := Eval vm_compute in (step_checker s54_7 (List.nth 54 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 54 (fst c7)). Print s55_7.
  Definition s56_7 := Eval vm_compute in (step_checker s55_7 (List.nth 55 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 55 (fst c7)). Print s56_7.
  Definition s57_7 := Eval vm_compute in (step_checker s56_7 (List.nth 56 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 56 (fst c7)). Print s57_7.
  Definition s58_7 := Eval vm_compute in (step_checker s57_7 (List.nth 57 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 57 (fst c7)). Print s58_7.
  Definition s59_7 := Eval vm_compute in (step_checker s58_7 (List.nth 58 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 58 (fst c7)). Print s59_7.
  Definition s60_7 := Eval vm_compute in (step_checker s59_7 (List.nth 59 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 59 (fst c7)). Print s60_7.
  Definition s61_7 := Eval vm_compute in (step_checker s60_7 (List.nth 60 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 60 (fst c7)). Print s61_7.
  Definition s62_7 := Eval vm_compute in (step_checker s61_7 (List.nth 61 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 61 (fst c7)). Print s62_7.
  Definition s63_7 := Eval vm_compute in (step_checker s62_7 (List.nth 62 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 62 (fst c7)). Print s63_7.
  Definition s64_7 := Eval vm_compute in (step_checker s63_7 (List.nth 63 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 63 (fst c7)). Print s64_7.
  Definition s65_7 := Eval vm_compute in (step_checker s64_7 (List.nth 64 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 64 (fst c7)). Print s65_7.
  Definition s66_7 := Eval vm_compute in (step_checker s65_7 (List.nth 65 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 65 (fst c7)). Print s66_7.
  Definition s67_7 := Eval vm_compute in (step_checker s66_7 (List.nth 66 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 66 (fst c7)). Print s67_7.
  Definition s68_7 := Eval vm_compute in (step_checker s67_7 (List.nth 67 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 67 (fst c7)). Print s68_7.
  Definition s69_7 := Eval vm_compute in (step_checker s68_7 (List.nth 68 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 68 (fst c7)). Print s69_7.
  Definition s70_7 := Eval vm_compute in (step_checker s69_7 (List.nth 69 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 69 (fst c7)). Print s70_7.
  Definition s71_7 := Eval vm_compute in (step_checker s70_7 (List.nth 70 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 70 (fst c7)). Print s71_7.
  Definition s72_7 := Eval vm_compute in (step_checker s71_7 (List.nth 71 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 71 (fst c7)). Print s72_7.
  Definition s73_7 := Eval vm_compute in (step_checker s72_7 (List.nth 72 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 72 (fst c7)). Print s73_7.
  Definition s74_7 := Eval vm_compute in (step_checker s73_7 (List.nth 73 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 73 (fst c7)). Print s74_7.
  Definition s75_7 := Eval vm_compute in (step_checker s74_7 (List.nth 74 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 74 (fst c7)). Print s75_7.
  Definition s76_7 := Eval vm_compute in (step_checker s75_7 (List.nth 75 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 75 (fst c7)). Print s76_7.
  Definition s77_7 := Eval vm_compute in (step_checker s76_7 (List.nth 76 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 76 (fst c7)). Print s77_7.
  Definition s78_7 := Eval vm_compute in (step_checker s77_7 (List.nth 77 (fst c7) (CTrue t_func7 t_atom7 t_form7 0))).
  Eval vm_compute in (List.nth 77 (fst c7)). Print s78_7.
  (* If the main_checker returns true, SMTCoq has successfully managed to check the proof *)
  Eval vm_compute in (euf_checker C.is_false (add_roots (S.make nclauses7) root7 used_roots7) c7 conf7).
End Checker_SmtEx7Debug.

Section Checker_SmtEx8Debug.
  Parse_certif_verit t_i8 t_func8 t_atom8 t_form8 root8 used_roots8 trace8
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritparser/smtcoq/examples/test8.smt2"
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritparser/smtcoq/examples/test8.vtlog".
  Definition nclauses8 := Eval vm_compute in (match trace8 with Certif a _ _ => a end).
  Definition c8 := Eval vm_compute in (match trace8 with Certif _ a _ => a end). (* Certificate *)
  Definition conf8 := Eval vm_compute in (match trace8 with Certif _ _ a => a end). (* Look here in the state for the empty clause*)
  Eval vm_compute in (Form.check_form t_form8 && Atom.check_atom t_atom8 && Atom.wt t_i8 t_func8 t_atom8).
  Eval vm_compute in List.length (fst c8).
  Definition s0_8 := Eval vm_compute in (add_roots (S.make nclauses8) root8 used_roots8).
  Definition s1_8 := Eval vm_compute in (step_checker s0_8 (List.nth 0 (fst c8) (CTrue t_func8 t_atom8 t_form8 0))).
  Definition s2_8 := Eval vm_compute in (step_checker s1_8 (List.nth 1 (fst c8) (CTrue t_func8 t_atom8 t_form8 0))).
  Definition s3_8 := Eval vm_compute in (step_checker s2_8 (List.nth 2 (fst c8) (CTrue t_func8 t_atom8 t_form8 0))).
  Definition s4_8 := Eval vm_compute in (step_checker s3_8 (List.nth 3 (fst c8) (CTrue t_func8 t_atom8 t_form8 0))).
  Definition s5_8 := Eval vm_compute in (step_checker s4_8 (List.nth 4 (fst c8) (CTrue t_func8 t_atom8 t_form8 0))).
  Definition s6_8 := Eval vm_compute in (step_checker s5_8 (List.nth 5 (fst c8) (CTrue t_func8 t_atom8 t_form8 0))).
  Definition s7_8 := Eval vm_compute in (step_checker s6_8 (List.nth 6 (fst c8) (CTrue t_func8 t_atom8 t_form8 0))).
  Definition s8_8 := Eval vm_compute in (step_checker s7_8 (List.nth 7 (fst c8) (CTrue t_func8 t_atom8 t_form8 0))).
  Definition s9_8 := Eval vm_compute in (step_checker s8_8 (List.nth 8 (fst c8) (CTrue t_func8 t_atom8 t_form8 0))).
  Definition s10_8 := Eval vm_compute in (step_checker s9_8 (List.nth 9 (fst c8) (CTrue t_func8 t_atom8 t_form8 0))).
  Definition s11_8 := Eval vm_compute in (step_checker s10_8 (List.nth 10 (fst c8) (CTrue t_func8 t_atom8 t_form8 0))).
  Definition s12_8 := Eval vm_compute in (step_checker s11_8 (List.nth 11 (fst c8) (CTrue t_func8 t_atom8 t_form8 0))).
  Definition s13_8 := Eval vm_compute in (step_checker s12_8 (List.nth 12 (fst c8) (CTrue t_func8 t_atom8 t_form8 0))).
  Definition s14_8 := Eval vm_compute in (step_checker s13_8 (List.nth 13 (fst c8) (CTrue t_func8 t_atom8 t_form8 0))).
  Definition s15_8 := Eval vm_compute in (step_checker s14_8 (List.nth 14 (fst c8) (CTrue t_func8 t_atom8 t_form8 0))).
  Definition s16_8 := Eval vm_compute in (step_checker s15_8 (List.nth 15 (fst c8) (CTrue t_func8 t_atom8 t_form8 0))).
  Definition s17_8 := Eval vm_compute in (step_checker s16_8 (List.nth 16 (fst c8) (CTrue t_func8 t_atom8 t_form8 0))).
  Definition s18_8 := Eval vm_compute in (step_checker s17_8 (List.nth 17 (fst c8) (CTrue t_func8 t_atom8 t_form8 0))).
  Definition s19_8 := Eval vm_compute in (step_checker s18_8 (List.nth 18 (fst c8) (CTrue t_func8 t_atom8 t_form8 0))).
  Definition s20_8 := Eval vm_compute in (step_checker s19_8 (List.nth 19 (fst c8) (CTrue t_func8 t_atom8 t_form8 0))).
  (* If the main_checker returns true, SMTCoq has successfully managed to check the proof *)
  Eval vm_compute in (euf_checker C.is_false (add_roots (S.make nclauses8) root8 used_roots8) c8 conf8).
End Checker_SmtEx8Debug.

Variable P : Z -> bool.
Variable a : Z.
Goal (forall (x : Z), P x) -> P a.
Proof. verit. Qed.

Section Subproof1.
  Parse_certif_verit t_i1 t_func1 t_atom1 t_form1 root1 used_roots1 trace1 
  "../examples/subproof.smt2" 
  "../examples/subproof.vtlog".
  Print trace1.
  Definition nclauses1 := Eval vm_compute in (match trace1 with Certif a _ _ => a end).
(* Size of state *)
  Definition c1 := Eval vm_compute in (match trace1 with Certif _ a _ => a end). (* Certificate *)
  Definition conf1 := Eval vm_compute in (match trace1 with Certif _ _ a => a end). (* Look here in the state for the empty clause*)
  Print c1. Print conf1.

  Eval vm_compute in List.length (fst c1).
  (* 7 steps in the certificate *)

  (* Sanity check that atoms and formulas are well-typed. Must return true *)
  Eval vm_compute in (Form.check_form t_form1 && Atom.check_atom t_atom1 && Atom.wt t_i1 t_func1 t_atom1).

  (* States from c1 *)

  (* Start state *)
  Definition s0_1 := Eval vm_compute in (add_roots (S.make nclauses1) root1 used_roots1).
  Print s0_1. Print t_form1. Print t_atom1. Print t_func1.
  (* s0_1 = ({| 0 -> (8 :: nil), 1 -> (5 :: nil) |}, 
    0 :: nil, 3) : PArray.Map.t C.t * C.t * int *)

  (* BuildDef 2 12 *)
  Definition s1_1 := Eval vm_compute in (step_checker s0_1 (List.nth 0 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s1_1. Print t_form1.
  (* s1_1 = ({| 0 -> (8 :: nil),  1 -> (5 :: nil), 2 -> (0 :: nil) |}, 
    0 :: nil, 3) : PArray.Map.t C.t * C.t * int *)

  (* ImmBuildDef 2 2 *)
  Definition s2_1 := Eval vm_compute in (step_checker s1_1 (List.nth 1 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s2_1.
  (* s2_1 = ({| 0 -> ( :: nil), 1 -> ( :: nil) |}, 
    0 :: nil, 3) : PArray.Map.t C.t * C.t * int *)

  (* Res 1 ({| 0 -> 2, 1 -> 0, 2 -> 1 |}) *)
  Definition s3_1 := Eval vm_compute in (step_checker s2_1 (List.nth 2 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s3_1.
  (* s3_1 = ({| 0 -> ( :: nil), 1 -> ( :: nil), 2 -> ( :: nil) |}, 
    0 :: nil, 3) : PArray.Map.t C.t * C.t * int *)

  (* ImmBuildProj 0 1 0 *)
  Definition s4_1 := Eval vm_compute in (step_checker s3_1 (List.nth 3 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s4_1.
  (* s4_1 = ({| 0 -> ( :: nil), 1 -> ( :: nil), 2 -> ( :: nil), 3 -> ( :: nil) |}, 
    0 :: nil, 3) : PArray.Map.t C.t * C.t * int *)

  (* ImmBuildProj 0 0 0 *)
  Definition s5_1 := Eval vm_compute in (step_checker s4_1 (List.nth 4 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s5_1.
  (* s5_1 = ({| 0 -> ( :: nil), 1 -> ( :: nil), 2 -> ( :: nil), 3 -> ( :: nil) |}, 
    0 :: nil, 3) : PArray.Map.t C.t * C.t * int *)

  (* ImmBuildProj 1 1 1 *)
  Definition s6_1 := Eval vm_compute in (step_checker s5_1 (List.nth 5 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s6_1.
  (* s6_1 = ({| 0 -> ( :: nil), 1 -> ( :: nil), 2 -> ( :: nil), 3 -> ( :: nil) |}
    0 :: nil, 3) : PArray.Map.t C.t * C.t * int *)

  (* Res 1 ({| 0 -> 0, 1 -> 1 |}) *)
  Definition s7_1 := Eval vm_compute in (step_checker s6_1 (List.nth 6 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s7_1.
  (* s7_1 = ({| 0 -> ( :: nil), 1 -> ( :: nil), 2 -> ( :: nil), 3 -> ( :: nil) |},
    0 :: nil, 3) : PArray.Map.t C.t * C.t * int *)
Section Subproof.
Verit_Checker "../examples/subproof.smt2" "../examples/subproof.vtlog".
End Subproof.