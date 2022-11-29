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
Add Rec LoadPath "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src" as SMTCoq.

Require Import SMTCoq.SMTCoq.
Require Import Bool.
Require Import Int31.
Local Open Scope int31_scope.

Section Checker_SmtEx3Debug.
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

  (* Certif after process_proj (from veritAst):
      (h1, AssumeAST, (cl  ((and  op_0 (not op_0)))), [], [])
      (t2, AndnAST, (cl  ((and  (and  op_0 (not op_0)) (not (false)))) ((not (and  op_0 (not op_0)))) ((false))), [], [])
      (t3, Equp2AST, (cl  ((not ((and  op_0 (not op_0)) = (false)))) ((not (and  op_0 (not op_0)))) ((false))), [], [])
      (t4, ThresoAST, (cl  ((false))), [ h1 t2 t3], [])
      (t5, FalsAST, (cl  ((not (false)))), [], [])
      (t6, ResoAST, (cl ), [ t4 t5], [])
      (x8, AndAST, (cl  ((and  op_0 (not op_0)))), [ t6], [ 0])
      (x2, AndAST, (cl  (op_0)), [ x8], [ 0])
      (x3, AndAST, (cl  ((not op_0))), [ x8], [ 1])
      (x4, Impn1AST, (cl  ((imp  op_0 (false))) (op_0)), [], [])
      (x5, ResoAST, (cl  ((imp  op_0 (false)))), [ x3 x4], [])
      (x6, ImpAST, (cl  ((not op_0)) ((false))), [ x5], [])
      (x7, ResoAST, (cl  ((false))), [ x2 x6], [])
      (x9, AndAST, (cl  ((not (false)))), [ t6], [ 1])
      (x10, ResoAST, (cl ), [ x7 x9], [])
  *)

  (* Sanity check that atoms and formulas are well-typed. Must return true *)
  Eval vm_compute in (Form.check_form t_form3 && Atom.check_atom t_atom3 && Atom.wt t_i3 t_func3 t_atom3).


  (* States from c3 *)
  
  (* Start state *)
  Definition s0_3 := Eval vm_compute in (add_roots (S.make nclauses3) root3 used_roots3).
  Print s0_3.
  (* s0_3 = ({| [6] |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)
  (* 3 := p ^ ~p *)

  Eval vm_compute in List.nth 0 (fst c3) _.
  (* 1. First step: BuildDef 1 8 *)
  Definition s1_3 := Eval vm_compute in (step_checker s0_3 (List.nth 0 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s1_3.
  (* s1_3 = ({| [6],  [2; 7; 8] |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  Eval vm_compute in List.nth 1 (fst c3) _.
  (* 2. Res 0 {| 1, 0 |} *)
  Definition s2_3 := Eval vm_compute in (step_checker s1_3 (List.nth 1 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s2_3.
  (* s1_3 = ({| [2, 8],  [2; 7; 8] |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  Eval vm_compute in List.nth 2 (fst c3) _.
  (* 3. CFalse 1 *)
  Definition s3_3 := Eval vm_compute in (step_checker s2_3 (List.nth 2 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s3_3.
  (* s1_3 = ({| [2, 8],  [3] |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  Eval vm_compute in List.nth 3 (fst c3) _.
  (* 4. Res 1 {| 0, 1 |} *)
  Definition s4_3 := Eval vm_compute in (step_checker s3_3 (List.nth 3 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s4_3.
  (* s1_3 = ({| [2, 8],  [8] |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  Eval vm_compute in List.nth 4 (fst c3) _.
  (* 5. ImmBuildProj 0 1 0 *)
  Definition s5_3 := Eval vm_compute in (step_checker s4_3 (List.nth 4 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s5_3.
  (* s1_3 = ({| [6], [8] |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  Eval vm_compute in List.nth 5 (fst c3) _.
  (* 6. ImmBuildProj 2 0 0 *)
  Definition s6_3 := Eval vm_compute in (step_checker s5_3 (List.nth 5 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s6_3.
  (* s1_3 = ({| [6], [8], [4] |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  Eval vm_compute in List.nth 6 (fst c3) _.
  (* 7. ImmBuildProj 0 0 1 *)
  Definition s7_3 := Eval vm_compute in (step_checker s6_3 (List.nth 6 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s7_3.
  (* s1_3 = ({| [5], [8], [4] |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  Eval vm_compute in List.nth 7 (fst c3) _.
  (* 8. BuildProj 3 10 0 *)
  Definition s8_3 := Eval vm_compute in (step_checker s7_3 (List.nth 7 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s8_3.
  (* s1_3 = ({| [5], [8], [4], [4; 10] |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  Eval vm_compute in List.nth 8 (fst c3) _.
  (* 9. Res 3 ({| 0, 3 |}) *)
  Definition s9_3 := Eval vm_compute in (step_checker s8_3 (List.nth 8 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s9_3.
  (* s1_3 = ({| [5], [8], [4], [10] |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)
  
  Eval vm_compute in List.nth 9 (fst c3) _.
  (* 10. ImmBuildDef 3 3 *)
  Definition s10_3 := Eval vm_compute in (step_checker s9_3 (List.nth 9 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s10_3.
  (* s1_3 = ({| [5], [8], [4], [2; 5] |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  Eval vm_compute in List.nth 10 (fst c3) _.
  (* 11. Res 3 {| 2, 3, |} *)
  Definition s11_3 := Eval vm_compute in (step_checker s10_3 (List.nth 10 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s11_3.
  (* s1_3 = ({| [5], [8], [4], [2] |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  Eval vm_compute in List.nth 11 (fst c3) _.
  (* 12. ImmBuildProj 1 1 1 *)
  Definition s12_3 := Eval vm_compute in (step_checker s11_3 (List.nth 11 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s12_3.
  (* s1_3 = ({| [5], [3], [4], [2] |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  Eval vm_compute in List.nth 12 (fst c3) _.
  (* 12. Res 1 {| 3, 1 |} *)
  Definition s13_3 := Eval vm_compute in (step_checker s12_3 (List.nth 12 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s13_3.
  (* s1_3 = ({| [5], [], [4], [2] |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)

  (* If the main_checker returns true, SMTCoq has successfully managed to check the proof *)
  Eval vm_compute in (euf_checker C.is_false (add_roots (S.make nclauses3) root3 used_roots3) c3 conf3).
End Checker_SmtEx3Debug.

Lemma ex3: forall p, negb (p && (negb p)).
Proof.
  verit_bool.
Qed.