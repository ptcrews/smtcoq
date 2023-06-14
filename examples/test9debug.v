Add Rec LoadPath "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.
Require Import Int31.
Local Open Scope int31_scope.

Section Test9Debug.
  Parse_certif_verit t_i9 t_func9 t_atom9 t_form9 root9 used_roots9 trace9
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/test9.smt2"
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/test9.vtlog".
  Definition nclauses9 := Eval vm_compute in (match trace9 with Certif a _ _ => a end). (* Size of the state *)
  Print nclauses9.
  Definition c9 := Eval vm_compute in (match trace9 with Certif _ a _ => a end). (* Certificate *)
  Print c9.
  Definition conf9 := Eval vm_compute in (match trace9 with Certif _ _ a => a end). (* Look here in the state for the empty clause*)
  Print conf9.
  Eval vm_compute in List.length (fst c9). (* No. of steps in certificate *)
  (* Sanity check that atoms and formulas are well-typed. Must return true *)
  Eval vm_compute in (Form.check_form t_form9 && Atom.check_atom t_atom9 && Atom.wt t_i9 t_func9 t_atom9).


  (* States from c9 *)

  (* Start state *)
  Definition s0_9 := Eval vm_compute in (add_roots (S.make nclauses9) root9 used_roots9).
  Print s0_9.
  (* s0_9 = ({|  |} *)
  Eval vm_compute in List.nth 0 (fst c9) _.
  (* 1. *)
  Definition s1_9 := Eval vm_compute in (step_checker s0_9 (List.nth 0 (fst c9) (CTrue t_func9 t_atom9 t_form9 0))).
  Print s1_9.
  (* s1_9 = ({|  |} *)

  Eval vm_compute in List.nth 1 (fst c9) _.
  (* 2. *)
  Definition s2_9 := Eval vm_compute in (step_checker s1_9 (List.nth 1 (fst c9) (CTrue t_func9 t_atom9 t_form9 0))).
  Print s2_9.
  (* s2_9 = ({|  |} *)

  Eval vm_compute in List.nth 2 (fst c9) _.
  (* 3. *)
  Definition s3_9 := Eval vm_compute in (step_checker s2_9 (List.nth 2 (fst c9) (CTrue t_func9 t_atom9 t_form9 0))).
  Print s3_9.
  (* s3_9 = ({|  |} *)

  Eval vm_compute in List.nth 3 (fst c9) _.
  (* 4. *)
  Definition s4_9 := Eval vm_compute in (step_checker s3_9 (List.nth 3 (fst c9) (CTrue t_func9 t_atom9 t_form9 0))).
  Print s4_9.
  (* s4_9 = ({|  |} *)

  Eval vm_compute in List.nth 4 (fst c9) _.
  (* 5. *)
  Definition s5_9 := Eval vm_compute in (step_checker s4_9 (List.nth 4 (fst c9) (CTrue t_func9 t_atom9 t_form9 0))).
  Print s5_9.
  (* s5_9 = ({|  |} *)

  Eval vm_compute in List.nth 5 (fst c9) _.
  (* 6. *)
  Definition s6_9 := Eval vm_compute in (step_checker s5_9 (List.nth 5 (fst c9) (CTrue t_func9 t_atom9 t_form9 0))).
  Print s6_9.
  (* s6_9 = ({|  |} *)

  Eval vm_compute in List.nth 6 (fst c9) _.
  (* 7. *)
  Definition s7_9 := Eval vm_compute in (step_checker s6_9 (List.nth 6 (fst c9) (CTrue t_func9 t_atom9 t_form9 0))).
  Print s7_9.
  (* s7_9 = ({|  |} *)

  Eval vm_compute in List.nth 7 (fst c9) _.
  (* 8. *)
  Definition s8_9 := Eval vm_compute in (step_checker s7_9 (List.nth 7 (fst c9) (CTrue t_func9 t_atom9 t_form9 0))).
  Print s8_9.
  (* s8_9 = ({|  |} *)

  Eval vm_compute in List.nth 8 (fst c9) _.
  (* 9. *)
  Definition s9_9 := Eval vm_compute in (step_checker s8_9 (List.nth 8 (fst c9) (CTrue t_func9 t_atom9 t_form9 0))).
  Print s9_9.
  (* s9_9 = ({|  |} *)

End Test9Debug.
