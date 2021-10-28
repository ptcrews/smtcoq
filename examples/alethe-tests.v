(*                                                                        *)
(**************************************************************************)
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
  Definition c1 := Eval vm_compute in (match trace1 with Certif _ a _ => a end).
  Definition conf1 := Eval vm_compute in (match trace1 with Certif _ _ a => a end).
  (* list step * step *)
  Print c1.
  (* Sanity check that atoms and formulas are well-typed. Must return true *)
  Eval vm_compute in (Form.check_form t_form1 && Atom.check_atom t_atom1 && Atom.wt t_i1 t_func1 t_atom1).
  
  (* States from c1 *)
  Definition s0_1 := Eval vm_compute in (add_roots (S.make nclauses1) root1 used_roots1).
  Print s0_1.
  Definition s1_1 := Eval vm_compute in (step_checker s0_1 (List.nth 0 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s1_1.
  Definition s2_1 := Eval vm_compute in (step_checker s1_1 (List.nth 1 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s2_1.
  Definition s3_1 := Eval vm_compute in (step_checker s2_1 (List.nth 2 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s3_1.
  Definition s4_1 := Eval vm_compute in (step_checker s3_1 (List.nth 3 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s4_1.
  Definition s5_1 := Eval vm_compute in (step_checker s4_1 (List.nth 4 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s5_1.
  Definition s6_1 := Eval vm_compute in (step_checker s5_1 (List.nth 5 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  (*Eval vm_compute in (S.set_resolve s6_1 3 (PArray.set (PArray.set (PArray.make 2 0) 0 2) 1 3)).*)
  Print s6_1.
  Definition s7_1 := Eval vm_compute in (step_checker s6_1 (List.nth 6 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s7_1.
  Definition s8_1 := Eval vm_compute in (step_checker s7_1 (List.nth 7 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s8_1.
(* s8_1 = ({| 0 -> (4 :: nil), 1 -> (10 :: nil), 2 -> (2 :: 0:: 19 :: nil), 3 ->  (3 :: nil) |},
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)
  Definition s9_1 := Eval vm_compute in (step_checker s8_1 (List.nth 8 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s9_1. 
(* s9_1 = ({| 0 -> (4 :: nil), 1 -> (10 :: nil), 2 -> (2 :: 0 :: 19 :: nil), 3 -> 0 :: 19 :: nil |},
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)
  Eval vm_compute in euf_checker (* t_atom t_form *) C.is_false (add_roots (S.make nclauses1) root1 used_roots1) c1 conf1.
  Definition s10_1 := Eval vm_compute in (step_checker s9_1 (List.nth 9 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))). Eval vm_compute in (List.nth 9 (fst c1) (CTrue t_func1 t_atom1 t_form1 0)). Eval vm_compute in List.length (fst c1).
  Print s10_1.
(* s10_1 = ({| 0 -> (0 :: nil), 1 -> (10 :: nil), 2 -> (2 :: 0 :: 19 :: nil), 3 -> 0 :: 19 :: nil |},
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int *)
  (*
  trace1 = 
    Certif (t_i:=t_i1) (t_func:=t_func1) (t_atom:=t_atom1) (t_form:=t_form1) 4
      (NotSimplify (t_i:=t_i1) t_func1 t_atom1 t_form1 1 6 :: 
       IffCong (t_i:=t_i1) t_func1 t_atom1 t_form1 1 (1 :: nil) 10 :: 
       AndSimplify (t_i:=t_i1) t_func1 t_atom1 t_form1 2 14 :: 
       AndSimplify (t_i:=t_i1) t_func1 t_atom1 t_form1 3 16 :: 
       IffTrans (t_i:=t_i1) t_func1 t_atom1 t_form1 3 (1 :: 2 :: 3 :: nil) 18 :: 
       BuildDef2 (t_i:=t_i1) t_func1 t_atom1 t_form1 2 19 :: 
       Hole (t_i:=t_i1) (t_func:=t_func1) (t_atom:=t_atom1) (t_form:=t_form1) 2 (0 :: 3 :: 2 :: nil) (prem:=(4 :: nil) :: (18 :: nil) :: (19 :: 5 :: 2 :: nil) :: nil) (concl:=2 :: nil) ass156637799 :: 
       CFalse (t_i:=t_i1) t_func1 t_atom1 t_form1 3 :: 
       Res (t_i:=t_i1) t_func1 t_atom1 t_form1 3 (PArray.set (PArray.set (PArray.make 2 0) 0 2) 1 3) :: nil,
    Res (t_i:=t_i1) t_func1 t_atom1 t_form1 0 (PArray.make 0 0)) 3
    : certif (t_i:=t_i1) t_func1 t_atom1 t_form1

  s0_1 = ({| 0 -> (4 :: nil) |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int
  s1_1 = ({| 0 -> (4 :: nil),  1 -> (6 :: nil) |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int
  s2_1 = ({| 0 -> (4 :: nil), 1 -> (10 :: nil) |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int
  s3_1 = ({| 0 -> (4 :: nil), 1 -> (10 :: nil), 2 -> (14 :: nil) |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int
  s4_1 = ({| 0 -> (4 :: nil), 1 -> (10 :: nil), 2 -> (14 :: nil), 3 -> (16 :: nil) |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int
  s5_1 = ({| 0 -> (4 :: nil), 1 -> (10 :: nil), 2 -> (14 :: nil), 3 -> (18 :: nil) |}, 
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int
  s6_1 = ({| 0 -> (4 :: nil), 1 -> (10 :: nil), 2 -> (2 :: 5 :: 19 :: nil), 3 -> (18 :: nil) |}
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int
  s7_1 = ({| 0 -> (4 :: nil), 1 -> (10 :: nil), 2 -> (2 :: nil), 3 -> (18 :: nil) |},
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int
  s8_1 = ({| 0 -> (4 :: nil), 1 -> (10 :: nil), 2 -> (2 :: nil), 3 ->  (3 :: nil) |},
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int
  s9_1 = ({| 0 -> (4 :: nil), 1 -> (10 :: nil), 2 -> (2 :: nil), 3 -> nil |},
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int
  s10_1 = ({| 0 -> (0 :: nil), 1 -> (10 :: nil), 2 -> (2 :: nil), 3 -> nil |},
    0 :: nil, 4) : PArray.Map.t C.t * C.t * int
  *)
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

Section Checker_SmtEx2.
  Parse_certif_verit t_i2 t_func2 t_atom2 t_form2 root2 used_roots2 trace2 
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritparser/smtcoq/examples/test2.smt2" 
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritparser/smtcoq/examples/test2.vtlog".
End Checker_SmtEx2.

Lemma ex2: true || false.
Proof.
  verit_bool.
Qed.

(*
Section Checker_SmtEx3.
  Parse_certif_verit t_i3 t_func3 t_atom3 t_form3 root3 used_roots3 trace3
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritparser/smtcoq/examples/test3.smt2" 
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritparser/smtcoq/examples/test3.vtlog".
End Checker_SmtEx3.
*)
Lemma ex3: forall p, negb (p && (negb p)).
Proof.
  verit_bool.
Qed.

Section Checker_SmtEx3Debug.
  Parse_certif_verit t_i3 t_func3 t_atom3 t_form3 root3 used_roots3 trace3
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritparser/smtcoq/examples/test3.smt2" 
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritparser/smtcoq/examples/test3.vtlog".
  Print trace3.
  (* Components of certif*)
  Definition nclauses3 := Eval vm_compute in (match trace3 with Certif a _ _ => a end).
  Definition c3 := Eval vm_compute in (match trace3 with Certif _ a _ => a end).
  Definition conf3 := Eval vm_compute in (match trace3 with Certif _ _ a => a end).
  Eval vm_compute in List.length (fst c3).
  (* Check that this returns true for well-typed *)
  Eval vm_compute in (Form.check_form t_form3 && Atom.check_atom t_atom3 && Atom.wt t_i3 t_func3 t_atom3).
  (* Now, run the checker, step-by=step *)
  (* Step through steps *)
  Definition s0_2 := Eval vm_compute in (add_roots (S.make nclauses3) root3 used_roots3).
  Print s0_2.
  Definition s1_2 := Eval vm_compute in (step_checker s0_2 (List.nth 0 (fst c3) (CTrue t_func3 t_atom3 t_form3 0))).
  Print s1_2.
  (* Problem with call to And_simplify, call the step-checker for And_Simplify *)
  Eval vm_compute in (List.nth 0 (fst c3) (CTrue t_func3 t_atom3 t_form3 0)).
  Eval vm_compute in (Cnf.check_AndSimplify t_form3 8).
  (* Step through check_AndSimplify, check type of Lit.Blit l *)
End Checker_SmtEx3Debug.

Lemma ex4: forall a b c, ((a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a)) = false.
Proof.
  verit_bool.
Qed.

Lemma ex5: false && true -> true || false.
Proof.
  verit_bool.
Qed.

Lemma ex6: forall p, p || (negb p).
Proof.
  verit_bool. Admitted.


Local Open Scope Z_scope.

Goal forall (a b : Z) (P : Z -> bool) (f : Z -> Z),
  (negb (Z.eqb (f a) b)) || (negb (P (f a))) || (P b).
Proof.
  verit_bool.
Qed.

Goal forall b1 b2 x1 x2,
    implb
      (ifb b1
           (ifb b2 (Z.eqb (2*x1+1) (2*x2+1)) (Z.eqb (2*x1+1) (2*x2)))
           (ifb b2 (Z.eqb (2*x1) (2*x2+1)) (Z.eqb (2*x1) (2*x2))))
      ((implb b1 b2) && (implb b2 b1) && (Z.eqb x1 x2)).
Proof.
  verit_bool.
Qed.

Goal forall
    (x y: Z)
    (f: Z -> Z),
    x = y + 1 -> f y = f (x - 1).
Proof.
  verit.
Qed.


(* Some examples of using verit with lemmas. Use <verit H1 .. Hn> to
   temporarily add the lemmas H1 .. Hn to the verit environment.
 *)

Lemma const_fun_is_eq_val_0 :
  forall f : Z -> Z,
    (forall a b, f a =? f b) ->
    forall x, f x =? f 0.
Proof.
  intros f Hf.
  verit Hf.
Qed.

Section With_lemmas.
  Variable f : Z -> Z.
  Variable k : Z.
  Hypothesis f_k_linear : forall x, f (x + 1) =? f x + k.

  Lemma fSS2:
    forall x, f (x + 2) =? f x + 2 * k.
  Proof. verit_no_check f_k_linear. Qed.
End With_lemmas.

(* Instantiating a lemma with multiple quantifiers *)

Section NonLinear.
  Lemma distr_right_inst a b (mult : Z -> Z -> Z) :
    (forall x y z, mult (x + y)  z =? mult x z + mult y z) ->
    (mult (3 + a) b =? mult 3 b + mult a b).
  Proof.
    intro H.
    verit H.
  Qed.
End NonLinear.

(* You can use <Add_lemmas H1 .. Hn> to permanently add the lemmas H1 .. Hn to
   the environment. If you did so in a section then, at the end of the section,
   you should use <Clear_lemmas> to empty the globally added lemmas because
   those lemmas won't be available outside of the section. *)

Section mult3.
  Variable mult3 : Z -> Z.
  Hypothesis mult3_0 : mult3 0 =? 0.
  Hypothesis mult3_Sn : forall n, mult3 (n+1) =? mult3 n + 3.
  Add_lemmas mult3_0 mult3_Sn.

  Lemma mult_3_4_12 : mult3 4 =? 12.
  Proof. verit. Qed.

  Clear_lemmas.
End mult3.


(* Examples of the smt tactic (requires verit and cvc4 in your PATH environment
   variable):
   - propositional logic
   - theory of equality
   - linear integer arithmetic
   - theory of fixed-sized bit-vectors
   - theory of arrays *)

Goal forall a b c, ((a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a)) = false.
Proof.
  smt.
Qed.

Goal forall (a b : Z) (P : Z -> bool) (f : Z -> Z),
  (negb (Z.eqb (f a) b)) || (negb (P (f a))) || (P b).
Proof.
  smt.
Qed.
Goal forall b1 b2 x1 x2,
    implb
      (ifb b1
           (ifb b2 (Z.eqb (2*x1+1) (2*x2+1)) (Z.eqb (2*x1+1) (2*x2)))
           (ifb b2 (Z.eqb (2*x1) (2*x2+1)) (Z.eqb (2*x1) (2*x2))))
      ((implb b1 b2) && (implb b2 b1) && (Z.eqb x1 x2)).
Proof.
  smt.
Qed.

Goal forall
    (x y: Z)
    (f: Z -> Z),
    x = y + 1 -> f y = f (x - 1).
Proof.
  smt.
Qed.

Goal forall (bv1 bv2 bv3: bitvector 4),
    bv1 = #b|0|0|0|0|  /\
    bv2 = #b|1|0|0|0|  /\
    bv3 = #b|1|1|0|0|  ->
    bv_ultP bv1 bv2 /\ bv_ultP bv2 bv3.
Proof.
  smt.
Qed.

Goal forall (a b: farray Z Z) (v w x y z t: Z)
            (r s: bitvector 4)
            (f: Z -> Z)
            (g: farray Z Z -> Z)
            (h: bitvector 4 -> Z),
    a[x <- v] = b /\ a[y <- w] = b ->
    a[z <- w] = b /\ a[t <- v] = b ->
    r = s -> v < x + 10 /\ v > x - 5 ->
    ~ (g a = g b) \/ f (h r) = f (h s).
Proof.
  smt.
Qed.


(* All tactics have a "no_check" variant that is faster but, in case of
   failure, it will only fail at Qed *)

Goal forall (bv1 bv2 bv3: bitvector 4),
    bv1 = #b|0|0|0|0|  /\
    bv2 = #b|1|0|0|0|  /\
    bv3 = #b|1|1|0|0|  ->
    bv_ultP bv1 bv2 /\ bv_ultP bv2 bv3.
Proof.
  smt_no_check.
Qed.

Goal forall (a b: farray Z Z) (v w x y z t: Z)
            (r s: bitvector 4)
            (f: Z -> Z)
            (g: farray Z Z -> Z)
            (h: bitvector 4 -> Z),
    a[x <- v] = b /\ a[y <- w] = b ->
    a[z <- w] = b /\ a[t <- v] = b ->
    r = s -> v < x + 10 /\ v > x - 5 ->
    ~ (g a = g b) \/ f (h r) = f (h s).
Proof.
  smt_no_check.
Qed.


(** SMTCoq also provides conversion tactics, to inject various integer
    types into the type Z supported by SMTCoq. They can be called before
    the standard SMTCoq tactics. **)

Local Open Scope positive_scope.

Goal forall (f : positive -> positive) (x y : positive),
  implb ((x + 3) =? y)
        ((f (x + 3)) <=? (f y))
  = true.
Proof.
  pos_convert.
  verit.
Qed.

Goal forall (f : positive -> positive) (x y : positive),
  implb ((x + 3) =? y)
        ((3 <? y) && ((f (x + 3)) <=? (f y)))
  = true.
Proof.
  pos_convert.
  verit.
Qed.

Local Close Scope positive_scope.

Local Open Scope N_scope.

Goal forall (f : N -> N) (x y : N),
    implb ((x + 3) =? y)
          ((f (x + 3)) <=? (f y))
    = true.
Proof.
  N_convert.
  verit.
Qed.

Goal forall (f : N -> N) (x y : N),
    implb ((x + 3) =? y)
          ((2 <? y) && ((f (x + 3)) <=? (f y)))
    = true.
Proof.
  N_convert.
  verit.
Qed.

Local Close Scope N_scope.

Require Import NPeano.
Local Open Scope nat_scope.

Goal forall (f : nat -> nat) (x y : nat),
    implb (Nat.eqb (x + 3) y)
          ((f (x + 3)) <=? (f y))
    = true.
Proof.
  nat_convert.
  verit.
Qed.

Goal forall (f : nat -> nat) (x y : nat),
    implb (Nat.eqb (x + 3) y)
          ((2 <? y) && ((f (x + 3)) <=? (f y)))
    = true.
Proof.
  nat_convert.
  verit.
Qed.

Local Close Scope nat_scope.

(* An example with all 3 types and a binary function *)
Goal forall f : positive -> nat -> N, forall (x : positive) (y : nat),
  implb (x =? 3)%positive
    (implb (Nat.eqb y 7)
      (implb (f 3%positive 7%nat =? 12)%N
        (f x y =? 12)%N)) = true.
  pos_convert.
  nat_convert.
  N_convert.
  verit.
Qed.

Open Scope Z_scope.


(** Now more insightful examples. The first one automatically proves
    properties in group theory. **)

Section Group.
  Variable G : Type.
  (* We suppose that G has a decidable equality *)
  Variable HG : CompDec G.
  Variable op : G -> G -> G.
  Variable inv : G -> G.
  Variable e : G.

  Local Notation "a ==? b" := (@eqb_of_compdec G HG a b) (at level 60).

  (* We can prove automatically that we have a group if we only have the
     "left" versions of the axioms of a group *)
  Hypothesis associative :
    forall a b c : G, op a (op b c) ==? op (op a b) c.
  Hypothesis inverse :
    forall a : G, op (inv a) a ==? e.
  Hypothesis identity :
    forall a : G, op e a ==? a.
  Add_lemmas associative inverse identity.

  (* The "right" version of inverse *)
  Lemma inverse' :
    forall a : G, op a (inv a) ==? e.
  Proof. smt. Qed.

  (* The "right" version of identity *)
  Lemma identity' :
    forall a : G, op a e ==? a.
  Proof. smt inverse'. Qed.

  (* Some other interesting facts about groups *)
  Lemma unique_identity e':
    (forall z, op e' z ==? z) -> e' ==? e.
  Proof. intros pe'; smt pe'. Qed.

  Lemma simplification_right x1 x2 y:
      op x1 y ==? op x2 y -> x1 ==? x2.
  Proof. intro H. smt_no_check (H, inverse'). Qed.

  Lemma simplification_left x1 x2 y:
      op y x1 ==? op y x2 -> x1 ==? x2.
  Proof. intro H. smt_no_check (H, inverse'). Qed.

  Clear_lemmas.
End Group.


(* A full example coming from CompCert, slightly revisited.
   See: https://hal.inria.fr/inria-00289542
        https://xavierleroy.org/memory-model/doc/Memory.html (Section 3)
 *)
Section CompCert.

  Variable block : Set.
  Hypothesis eq_block : CompDec block.

  Variable mem: Set.
  Hypothesis dec_mem : CompDec mem.
  Variable alloc_block: mem -> Z -> Z -> block.
  Variable alloc_mem: mem -> Z -> Z -> mem.
  Variable valid_block: mem -> block -> bool.

  Hypothesis alloc_valid_block_1:
    forall m lo hi b,
      valid_block (alloc_mem m lo hi) b -> ((b = (alloc_block m lo hi)) \/ valid_block m b).

  Hypothesis alloc_valid_block_2:
    forall m lo hi b,
      ((b = (alloc_block m lo hi)) \/ valid_block m b) -> (valid_block (alloc_mem m lo hi) b).

  Hypothesis alloc_not_valid_block:
    forall m lo hi,
       negb (valid_block m (alloc_block m lo hi)).

  Lemma alloc_valid_block_inv m lo hi b :
    valid_block m b -> valid_block (alloc_mem m lo hi) b.
  Proof.
    intro H. verit (alloc_valid_block_2, H).
  Qed.

  Lemma alloc_not_valid_block_2 m lo hi b' :
    valid_block m b' -> b' <> (alloc_block m lo hi).
  Proof.
    intro H. verit (alloc_not_valid_block, H).
  Qed.

End CompCert.
