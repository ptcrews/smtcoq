Add Rec LoadPath "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.
Require Import Int31.
Local Open Scope int31_scope.

Section TestrefleqreflDebug.
  Parse_certif_verit t_i2 t_func2 t_atom2 t_form2 root2 used_roots2 trace2
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/testrewrites/smt/refleqrefl.smt2"
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/testrewrites/proof/refleqrefl.pf".
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

End Test2Debug.
