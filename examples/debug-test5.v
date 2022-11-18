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
   
   Section Checker_SmtEx3.
     Parse_certif_verit t_i3 t_func3 t_atom3 t_form3 root3 used_roots3 trace3
     "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/test3.smt2" 
     "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/test3.vtlog".
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
     Print trace3.

     (* Components of the certificate *)
     Definition nclauses3 := Eval vm_compute in (match trace3 with Certif a _ _ => a end). (* Size of the state *)
     Print nclauses3. (* 4 *)
     Definition c3 := Eval vm_compute in (match trace3 with Certif _ a _ => a end). (* Certificate of type (list step) * step*)
     Print c3.
     Definition conf3 := Eval vm_compute in (match trace3 with Certif _ _ a => a end). (* Look here in the state for the empty clause *)
     Print conf3. (* 1 *)
     
     Eval vm_compute in List.length (fst c3).
     (* 13 steps in the certificate *)
   
     (* Sanity check that atoms and formulas are well-typed. Must return true *)
     Eval vm_compute in (Form.check_form t_form3 && Atom.check_atom t_atom3 && Atom.wt t_i3 t_func3 t_atom3).

     (* States from c3 *)
     
     (* Start state *)
     Definition s0_3 := Eval vm_compute in (add_roots (S.make nclauses3) root3 used_roots3).
     Print s0_3.
     (* s0_3 = ({| 0 -> [6] |}, 
       [0], 4) : PArray.Map.t C.t * C.t * int *)

     Eval vm_compute in List.nth 0 (fst c3) _.
     (* 1. First step: BuildDef 1 8 *)
     Definition s1_3 := Eval vm_compute in (step_checker s0_3 (List.nth 0 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
     Print s1_3.
     (* Resulting state: s1_3 = ({| 0 -> [6],  1 -> [2; 7; 8] |}, 
       [0], 4) : PArray.Map.t C.t * C.t * int *)

     Eval vm_compute in List.nth 1 (fst c3) _.
     (* 2. Res 1 {|0 -> 0, 1 -> 1 |} *)
     Definition s2_3 := Eval vm_compute in (step_checker s1_3 (List.nth 1 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
     Print s2_3.
     (* Resulting state: s2_3 = ({| 0 -> [6],  1 -> [2; 8] |}, 
       [0], 4) : PArray.Map.t C.t * C.t * int *)

     Eval vm_compute in List.nth 2 (fst c3) _.
     (* 3. CFalse 0 *)
     Definition s3_3 := Eval vm_compute in (step_checker s2_3 (List.nth 2 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
     Print s3_3.
     (* Resulting state: s3_3 = ({| 0 -> [3],  1 -> [2; 8] |}, 
       [0], 4) : PArray.Map.t C.t * C.t * int *)

     Eval vm_compute in List.nth 3 (fst c3) _.
     (* 4. Res 1 {| 0 -> 0, 1 -> 1 |} *)
     Definition s4_3 := Eval vm_compute in (step_checker s3_3 (List.nth 3 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
     Print s4_3.
     (* Resulting state: s3_3 = ({| 0 -> [3],  1 -> [8] |}, 
       [0], 4) : PArray.Map.t C.t * C.t * int *)

     Eval vm_compute in List.nth 4 (fst c3) _.
     (* 5. ImmBuildProj 0 1 0 *)
     Definition s5_3 := Eval vm_compute in (step_checker s4_3 (List.nth 4 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
     Print s5_3.
     (* Resulting state: s3_3 = ({| 0 -> [6],  1 -> [8] |}, 
       [0], 4) : PArray.Map.t C.t * C.t * int *)

     Eval vm_compute in List.nth 5 (fst c3) _.
     (* 6. ImmBuildProj 2 0 0 *)
     Definition s6_3 := Eval vm_compute in (step_checker s5_3 (List.nth 5 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
     Print s6_3.
     (* Resulting state: s3_3 = ({| 0 -> [6],  1 -> [8], 2 -> [4] |}, 
       [0], 4) : PArray.Map.t C.t * C.t * int *)

     Eval vm_compute in List.nth 6 (fst c3) _.
     (* 7. ImmBuildProj 0 0 1 *)
     Definition s7_3 := Eval vm_compute in (step_checker s6_3 (List.nth 6 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
     Print s7_3.
     (* Resulting state: s3_3 = ({| 0 -> [5],  1 -> [8], 2 -> [4] |}, 
       [0], 4) : PArray.Map.t C.t * C.t * int *)

     Eval vm_compute in List.nth 7 (fst c3) _.
     (* 8. BuildProj 3 10 0 *)
     Definition s8_3 := Eval vm_compute in (step_checker s7_3 (List.nth 7 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
     Print s8_3.
     (* Resulting state: s3_3 = ({| 0 -> [5],  1 -> [8], 2 -> [4], 3 -> [4; 10] |}, 
       [0], 4) : PArray.Map.t C.t * C.t * int *)

     Eval vm_compute in List.nth 8 (fst c3) _.
     (* 9. Res 3 {| 0 -> 0, 1 -> 3 |} *)
     Definition s9_3 := Eval vm_compute in (step_checker s8_3 (List.nth 8 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
     Print s9_3.
     (* Resulting state: s3_3 = ({| 0 -> [5],  1 -> [8], 2 -> [4], 3 -> [10] |}, 
       [0], 4) : PArray.Map.t C.t * C.t * int *)

     Eval vm_compute in List.nth 9 (fst c3) _.
     (* 10. ImmBuildDef 3 3 *)
     Definition s10_3 := Eval vm_compute in (step_checker s9_3 (List.nth 9 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
     Print s10_3.
     (* Resulting state: s3_3 = ({| 0 -> [5],  1 -> [8], 2 -> [4], 3 -> [2; 5] |}, 
       [0], 4) : PArray.Map.t C.t * C.t * int *)

     Eval vm_compute in List.nth 10 (fst c3) _.
     (* 11. Res 3 {| 0 -> 2, 1 -> 3 |} *)
     Definition s11_3 := Eval vm_compute in (step_checker s10_3 (List.nth 10 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
     Print s11_3.
     (* Resulting state: s3_3 = ({| 0 -> [5],  1 -> [8], 2 -> [4], 3 -> [2] |}, 
       [0], 4) : PArray.Map.t C.t * C.t * int *)

     Eval vm_compute in List.nth 11 (fst c3) _.
     (* 12. ImmBuildProj 1 1 1 *)
     Definition s12_3 := Eval vm_compute in (step_checker s11_3 (List.nth 11 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
     Print s12_3.
     (* Resulting state: s3_3 = ({| 0 -> [5],  1 -> [3], 2 -> [4], 3 -> [2] |}, 
       [0], 4) : PArray.Map.t C.t * C.t * int *)

     Eval vm_compute in List.nth 12 (fst c3) _.
     (* 13. ImmBuildProj 1 1 1 *)
     Definition s13_3 := Eval vm_compute in (step_checker s12_3 (List.nth 12 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
     Print s13_3.
     (* Resulting state: s3_3 = ({| 0 -> [5],  1 -> [], 2 -> [4], 3 -> [2] |}, 
       [0], 4) : PArray.Map.t C.t * C.t * int *)
   (* In the end, the empty clause is in 1, so the certificate checks *)
   End Checker_SmtEx3.

   Lemma ex3: forall p, negb (p && (negb p)).
   Proof.
     verit_bool.
   Qed.

   Section Checker_SmtEx5Debug.
     Parse_certif_verit t_i5 t_func5 t_atom5 t_form5 root5 used_roots5 trace5 
     "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/test5.smt2" 
     "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/test5.vtlog".
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
     Definition nclauses5 := Eval vm_compute in (match trace5 with Certif a _ _ => a end). (* Size of the state *)
     Print nclauses5. (* 4 *)
     Definition c5 := Eval vm_compute in (match trace5 with Certif _ a _ => a end). (* Certificate of type (list step) * step*)
     Print c5.
     Definition conf5 := Eval vm_compute in (match trace5 with Certif _ _ a => a end). (* Look here in the state for the empty clause*)
     Print conf5. (* 2 *)
     
     Eval vm_compute in List.length (fst c5).
     (* 27 steps in the certificate *)
   
     (* Sanity check that atoms and formulas are well-typed. Must return true *)
     Eval vm_compute in (Form.check_form t_form5 && Atom.check_atom t_atom5 && Atom.wt t_i5 t_func5 t_atom5).
     
   
     (* States from c5 *)
     
     (* Start state *)
     Definition s0_5 := Eval vm_compute in (add_roots (S.make nclauses5) root5 used_roots5).
     Print s0_5.
     (* s0_5 = ({| 0 -> [7] |}, 
       [0], 4) : PArray.Map.t C.t * C.t * int *)

     Eval vm_compute in List.nth 0 (fst c5) _.
     (* 1. First step: BuildDef 1 8 *)
     Definition s1_5 := Eval vm_compute in (step_checker s0_5 (List.nth 0 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
     Print s1_5.
     (* Resulting sate: s1_5 = ({| 0 -> [7],  1 -> [0; 7; 8] |}, 
       [0], 4) : PArray.Map.t C.t * C.t * int *)
   
     Eval vm_compute in List.nth 1 (fst c5) _.
     (* 2. BuildDef 2 10 *)
     Definition s2_5 := Eval vm_compute in (step_checker s1_5 (List.nth 1 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
     Print s2_5.
     (* s2_5 = ({| 0 -> [7], 1 -> [0; 7; 8], 2 -> [1; 6; 10] |}, 
       [0], 4) : PArray.Map.t C.t * C.t * int *)
   
     Eval vm_compute in List.nth 2 (fst c5) _.
     (* 3. BuildDef 3 12 *)
     Definition s3_5 := Eval vm_compute in (step_checker s2_5 (List.nth 2 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
     Print s3_5.
     (* s3_5 = ({| 0 -> [7], 1 -> [0; 7; 8], 2 -> [1; 6; 10], 3 -> [1; 7; 12] |}, 
       [0], 4) : PArray.Map.t C.t * C.t * int *)

     Eval vm_compute in List.nth 3 (fst c5) _.
     (* 4. Res 2 {| 0 -> 3, 1 -> 1, 2 -> 2 |} *)
     Definition s4_5 := Eval vm_compute in (step_checker s3_5 (List.nth 3 (fst c5) (CTrue t_func5 t_atom5 t_form5 0))).
     Print s4_5.
     (* s4_5 = ({| 0 -> [7], 1 -> [0; 7; 8], 2 -> [1; 8; 10; 12], 3 -> [1; 7; 12] |}, 
       [0], 4) : PArray.Map.t C.t * C.t * int *)
   End Checker_SmtEx5Debug.
   
   Lemma ex5: forall p, p || (negb p).
   Proof.
     verit_bool.
   Qed.