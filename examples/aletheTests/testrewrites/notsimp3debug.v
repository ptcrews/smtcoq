Add Rec LoadPath "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.
Require Import Int31.
Local Open Scope int31_scope.

Section Testnotsimp3Debug.
  Parse_certif_verit t_i3 t_func3 t_atom3 t_form3 root3 used_roots3 trace3
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/testrewrites/smt/notsimp3.smt2"
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/testrewrites/proof/notsimp3.pf".
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

End Test3Debug.
