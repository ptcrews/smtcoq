(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export BinNums.
Require Import Eqdep_dec EqdepFacts RelationClasses Morphisms Setoid
 Equalities Orders OrdersFacts GenericMinMax Le Plus.
Require Import SMTCoq.SMTCoq.
Require Export BinPosDef.

(**********************************************************************)
(** * Binary positive numbers, operations and properties *)
(**********************************************************************)

(** Initial development by Pierre Crégut, CNET, Lannion, France *)

(** The type [positive] and its constructors [xI] and [xO] and [xH]
    are now defined in [BinNums.v] *)

Local Open Scope positive_scope.

(** Every definitions and early properties about positive numbers
    are placed in a module [Pos] for qualification purpose. *)

Module Pos
 <: UsualOrderedTypeFull
 <: UsualDecidableTypeFull
 <: TotalOrder.

(** * Definitions of operations, now in a separate file *)

Include BinPosDef.Pos.

(** In functor applications that follow, we only inline t and eq *)

Set Inline Level 30.

(** * Logical Predicates *)

Definition eq := @Logic.eq positive.
Definition eq_equiv := @eq_equivalence positive.
Include BackportEq.

Definition lt x y := (x ?= y) = Lt.
Definition gt x y := (x ?= y) = Gt.
Definition le x y := (x ?= y) <> Gt.
Definition ge x y := (x ?= y) <> Lt.

Infix "<=" := le : positive_scope.
Infix "<" := lt : positive_scope.
Infix ">=" := ge : positive_scope.
Infix ">" := gt : positive_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : positive_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : positive_scope.
Notation "x < y < z" := (x < y /\ y < z) : positive_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : positive_scope.

(**********************************************************************)
(** * Properties of operations over positive numbers *)

(** ** Decidability of equality on binary positive numbers *)

Lemma eq_dec : forall x y:positive, {x = y} + {x <> y}.
Proof. Show. Fail (abduce 3). Admitted.

(**********************************************************************)
(** * Properties of successor on binary positive numbers *)

(** ** Specification of [xI] in term of [succ] and [xO] *)

Lemma xI_succ_xO p : p~1 = succ p~0.
Proof. Show. Fail (abduce 3). Admitted.

Lemma succ_discr p : p <> succ p.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Successor and double *)

Lemma pred_double_spec p : pred_double p = pred (p~0).
Proof. Show. Fail (abduce 3). Admitted.

Lemma succ_pred_double p : succ (pred_double p) = p~0.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pred_double_succ p : pred_double (succ p) = p~1.
Proof. Show. Fail (abduce 3). Admitted.

Lemma double_succ p : (succ p)~0 = succ (succ p~0).
Proof. Show. Fail (abduce 3). Admitted.

Lemma pred_double_xO_discr p : pred_double p <> p~0.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Successor and predecessor *)

Lemma succ_not_1 p : succ p <> 1.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pred_succ p : pred (succ p) = p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma succ_pred_or p : p = 1 \/ succ (pred p) = p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma succ_pred p : p <> 1 -> succ (pred p) = p.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Injectivity of successor *)

Lemma succ_inj p q : succ p = succ q -> p = q.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Predecessor to [N] *)

Lemma pred_N_succ p : pred_N (succ p) = Npos p.
Proof. Show. Fail (abduce 3). Admitted.


(**********************************************************************)
(** * Properties of addition on binary positive numbers *)

(** ** Specification of [succ] in term of [add] *)

Lemma add_1_r p : p + 1 = succ p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma add_1_l p : 1 + p = succ p.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Specification of [add_carry] *)

Theorem add_carry_spec p q : add_carry p q = succ (p + q).
Proof. Show. Fail (abduce 3). Admitted.

(** ** Commutativity *)

Theorem add_comm p q : p + q = q + p.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Permutation of [add] and [succ] *)

Theorem add_succ_r p q : p + succ q = succ (p + q).
Proof. Show. Fail (abduce 3). Admitted.

Theorem add_succ_l p q : succ p + q = succ (p + q).
Proof. Show. Fail (abduce 3). Admitted.

(** ** No neutral elements for addition *)
Lemma add_no_neutral p q : q + p <> p.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Simplification *)

Lemma add_carry_add p q r s :
  add_carry p r = add_carry q s -> p + r = q + s.
Proof. Show. Fail (abduce 3). Admitted.

Lemma add_reg_r p q r : p + r = q + r -> p = q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma add_reg_l p q r : p + q = p + r -> q = r.
Proof. Show. Fail (abduce 3). Admitted.

Lemma add_cancel_r p q r : p + r = q + r <-> p = q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma add_cancel_l p q r : r + p = r + q <-> p = q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma add_carry_reg_r p q r :
  add_carry p r = add_carry q r -> p = q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma add_carry_reg_l p q r :
  add_carry p q = add_carry p r -> q = r.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Addition is associative *)

Theorem add_assoc p q r : p + (q + r) = p + q + r.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Commutation of addition and double *)

Lemma add_xO p q : (p + q)~0 = p~0 + q~0.
Proof. Show. Fail (abduce 3). Admitted.

Lemma add_xI_pred_double p q :
  (p + q)~0 = p~1 + pred_double q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma add_xO_pred_double p q :
  pred_double (p + q) = p~0 + pred_double q.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Miscellaneous *)

Lemma add_diag p : p + p = p~0.
Proof. Show. Fail (abduce 3). Admitted.

(**********************************************************************)
(** * Peano induction and recursion on binary positive positive numbers *)

(** The Peano-like recursor function for [positive] (due to Daniel Schepler) *)

Fixpoint peano_rect (P:positive->Type) (a:P 1)
  (f: forall p:positive, P p -> P (succ p)) (p:positive) : P p :=
let f2 := peano_rect (fun p:positive => P (p~0)) (f _ a)
  (fun (p:positive) (x:P (p~0)) => f _ (f _ x))
in
match p with
  | q~1 => f _ (f2 q)
  | q~0 => f2 q
  | 1 => a
end.

Theorem peano_rect_succ (P:positive->Type) (a:P 1)
  (f:forall p, P p -> P (succ p)) (p:positive) :
  peano_rect P a f (succ p) = f _ (peano_rect P a f p).
Proof. Show. Fail (abduce 3). Admitted.

Theorem peano_rect_base (P:positive->Type) (a:P 1)
  (f:forall p, P p -> P (succ p)) :
  peano_rect P a f 1 = a.
Proof. Show. Fail (abduce 3). Admitted.

Definition peano_rec (P:positive->Set) := peano_rect P.

(** Peano induction *)

Definition peano_ind (P:positive->Prop) := peano_rect P.

(** Peano case analysis *)

Theorem peano_case :
  forall P:positive -> Prop,
    P 1 -> (forall n:positive, P (succ n)) -> forall p:positive, P p.
Proof. Show. Fail (abduce 3). Admitted.

(** Earlier, the Peano-like recursor was built and proved in a way due to
    Conor McBride, see "The view from the left" *)

Inductive PeanoView : positive -> Type :=
| PeanoOne : PeanoView 1
| PeanoSucc : forall p, PeanoView p -> PeanoView (succ p).

Fixpoint peanoView_xO p (q:PeanoView p) : PeanoView (p~0) :=
  match q in PeanoView x return PeanoView (x~0) with
    | PeanoOne => PeanoSucc _ PeanoOne
    | PeanoSucc _ q => PeanoSucc _ (PeanoSucc _ (peanoView_xO _ q))
  end.

Fixpoint peanoView_xI p (q:PeanoView p) : PeanoView (p~1) :=
  match q in PeanoView x return PeanoView (x~1) with
    | PeanoOne => PeanoSucc _ (PeanoSucc _ PeanoOne)
    | PeanoSucc _ q => PeanoSucc _ (PeanoSucc _ (peanoView_xI _ q))
  end.

Fixpoint peanoView p : PeanoView p :=
  match p return PeanoView p with
    | 1 => PeanoOne
    | p~0 => peanoView_xO p (peanoView p)
    | p~1 => peanoView_xI p (peanoView p)
  end.

Definition PeanoView_iter (P:positive->Type)
  (a:P 1) (f:forall p, P p -> P (succ p)) :=
  (fix iter p (q:PeanoView p) : P p :=
    match q in PeanoView p return P p with
      | PeanoOne => a
      | PeanoSucc _ q => f _ (iter _ q)
    end).

Theorem eq_dep_eq_positive :
  forall (P:positive->Type) (p:positive) (x y:P p),
    eq_dep positive P p x p y -> x = y.
Proof. Show. Fail (abduce 3). Admitted.

Theorem PeanoViewUnique : forall p (q q':PeanoView p), q = q'.
Proof. Show. Fail (abduce 3). Admitted.

Lemma peano_equiv (P:positive->Type) (a:P 1) (f:forall p, P p -> P (succ p)) p :
   PeanoView_iter P a f p (peanoView p) = peano_rect P a f p.
Proof. Show. Fail (abduce 3). Admitted.

(**********************************************************************)
(** * Properties of multiplication on binary positive numbers *)

(** ** One is neutral for multiplication *)

Lemma mul_1_l p : 1 * p = p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma mul_1_r p : p * 1 = p.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Right reduction properties for multiplication *)

Lemma mul_xO_r p q : p * q~0 = (p * q)~0.
Proof. Show. Fail (abduce 3). Admitted.

Lemma mul_xI_r p q : p * q~1 = p + (p * q)~0.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Commutativity of multiplication *)

Theorem mul_comm p q : p * q = q * p.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Distributivity of multiplication over addition *)

Theorem mul_add_distr_l p q r :
  p * (q + r) = p * q + p * r.
Proof. Show. Fail (abduce 3). Admitted.

Theorem mul_add_distr_r p q r :
  (p + q) * r = p * r + q * r.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Associativity of multiplication *)

Theorem mul_assoc p q r : p * (q * r) = p * q * r.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Successor and multiplication *)

Lemma mul_succ_l p q : (succ p) * q = q + p * q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma mul_succ_r p q : p * (succ q) = p + p * q.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Parity properties of multiplication *)

Lemma mul_xI_mul_xO_discr p q r : p~1 * r <> q~0 * r.
Proof. Show. Fail (abduce 3). Admitted.

Lemma mul_xO_discr p q : p~0 * q <> q.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Simplification properties of multiplication *)

Theorem mul_reg_r p q r : p * r = q * r -> p = q.
Proof. Show. Fail (abduce 3). Admitted.

Theorem mul_reg_l p q r : r * p = r * q -> p = q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma mul_cancel_r p q r : p * r = q * r <-> p = q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma mul_cancel_l p q r : r * p = r * q <-> p = q.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Inversion of multiplication *)

Lemma mul_eq_1_l p q : p * q = 1 -> p = 1.
Proof. Show. Fail (abduce 3). Admitted.

Lemma mul_eq_1_r p q : p * q = 1 -> q = 1.
Proof. Show. Fail (abduce 3). Admitted.

Notation mul_eq_1 := mul_eq_1_l.

(** ** Square *)

Lemma square_xO p : p~0 * p~0 = (p*p)~0~0.
Proof. Show. Fail (abduce 3). Admitted.

Lemma square_xI p : p~1 * p~1 = (p*p+p)~0~1.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Properties of [iter] *)

Lemma iter_swap_gen A B (f:A->B)(g:A->A)(h:B->B) :
 (forall a, f (g a) = h (f a)) -> forall p a,
 f (iter g a p) = iter h (f a) p.
Proof. Show. Fail (abduce 3). Admitted.

Theorem iter_swap :
  forall p (A:Type) (f:A -> A) (x:A),
    iter f (f x) p = f (iter f x p).
Proof. Show. Fail (abduce 3). Admitted.

Theorem iter_succ :
  forall p (A:Type) (f:A -> A) (x:A),
    iter f x (succ p) = f (iter f x p).
Proof. Show. Fail (abduce 3). Admitted.

Theorem iter_succ_r :
  forall p (A:Type) (f:A -> A) (x:A),
    iter f x (succ p) = iter f (f x) p.
Proof. Show. Fail (abduce 3). Admitted.

Theorem iter_add :
  forall p q (A:Type) (f:A -> A) (x:A),
    iter f x (p+q) = iter f (iter f x q) p.
Proof. Show. Fail (abduce 3). Admitted.

Theorem iter_ind (A:Type) (f:A -> A) (a:A) (P:positive -> A -> Prop) :
    P 1 (f a) ->
    (forall p a', P p a' -> P (succ p) (f a')) ->
    forall p, P p (iter f a p).
Proof. Show. Fail (abduce 3). Admitted.

Theorem iter_invariant :
  forall (p:positive) (A:Type) (f:A -> A) (Inv:A -> Prop),
    (forall x:A, Inv x -> Inv (f x)) ->
    forall x:A, Inv x -> Inv (iter f x p).
Proof. Show. Fail (abduce 3). Admitted.

(** ** Properties of power *)

Lemma pow_1_r p : p^1 = p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pow_succ_r p q : p^(succ q) = p * p^q.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Properties of square *)

Lemma square_spec p : square p = p * p.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Properties of [sub_mask] *)

Lemma sub_mask_succ_r p q :
  sub_mask p (succ q) = sub_mask_carry p q.
Proof. Show. Fail (abduce 3). Admitted.

Theorem sub_mask_carry_spec p q :
  sub_mask_carry p q = pred_mask (sub_mask p q).
Proof. Show. Fail (abduce 3). Admitted.

Inductive SubMaskSpec (p q : positive) : mask -> Prop :=
 | SubIsNul : p = q -> SubMaskSpec p q IsNul
 | SubIsPos : forall r, q + r = p -> SubMaskSpec p q (IsPos r)
 | SubIsNeg : forall r, p + r = q -> SubMaskSpec p q IsNeg.

Theorem sub_mask_spec p q : SubMaskSpec p q (sub_mask p q).
Proof. Show. Fail (abduce 3). Admitted.

Theorem sub_mask_nul_iff p q : sub_mask p q = IsNul <-> p = q.
Proof. Show. Fail (abduce 3). Admitted.

Theorem sub_mask_diag p : sub_mask p p = IsNul.
Proof. Show. Fail (abduce 3). Admitted.

Lemma sub_mask_add p q r : sub_mask p q = IsPos r -> q + r = p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma sub_mask_add_diag_l p q : sub_mask (p+q) p = IsPos q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma sub_mask_pos_iff p q r : sub_mask p q = IsPos r <-> q + r = p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma sub_mask_add_diag_r p q : sub_mask p (p+q) = IsNeg.
Proof. Show. Fail (abduce 3). Admitted.

Lemma sub_mask_neg_iff p q : sub_mask p q = IsNeg <-> exists r, p + r = q.
Proof. Show. Fail (abduce 3). Admitted.

(*********************************************************************)
(** * Properties of boolean comparisons *)

Theorem eqb_eq p q : (p =? q) = true <-> p=q.
Proof. Show. Fail (abduce 3). Admitted.

Theorem ltb_lt p q : (p <? q) = true <-> p < q.
Proof. Show. Fail (abduce 3). Admitted.

Theorem leb_le p q : (p <=? q) = true <-> p <= q.
Proof. Show. Fail (abduce 3). Admitted.

(** More about [eqb] *)

Include BoolEqualityFacts.

(**********************************************************************)
(** * Properties of comparison on binary positive numbers *)

(** First, we express [compare_cont] in term of [compare] *)

Definition switch_Eq c c' :=
 match c' with
  | Eq => c
  | Lt => Lt
  | Gt => Gt
 end.

Lemma compare_cont_spec p q c :
  compare_cont c p q = switch_Eq c (p ?= q).
Proof. Show. Fail (abduce 3). Admitted.

(** From this general result, we now describe particular cases
    of [compare_cont p q c = c'] :
    - When [c=Eq], this is directly [compare]
    - When [c<>Eq], we'll show first that [c'<>Eq]
    - That leaves only 4 lemmas for [c] and [c'] being [Lt] or [Gt]
*)

Theorem compare_cont_Eq p q c :
 compare_cont c p q = Eq -> c = Eq.
Proof. Show. Fail (abduce 3). Admitted.

Lemma compare_cont_Lt_Gt p q :
  compare_cont Lt p q = Gt <-> p > q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma compare_cont_Lt_Lt p q :
  compare_cont Lt p q = Lt <-> p <= q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma compare_cont_Gt_Lt p q :
  compare_cont Gt p q = Lt <-> p < q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma compare_cont_Gt_Gt p q :
  compare_cont Gt p q = Gt <-> p >= q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma compare_cont_Lt_not_Lt p q :
  compare_cont Lt p q <> Lt <-> p > q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma compare_cont_Lt_not_Gt p q :
  compare_cont Lt p q <> Gt <-> p <= q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma compare_cont_Gt_not_Lt p q :
  compare_cont Gt p q <> Lt <-> p >= q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma compare_cont_Gt_not_Gt p q :
  compare_cont Gt p q <> Gt <-> p < q.
Proof. Show. Fail (abduce 3). Admitted.

(** We can express recursive equations for [compare] *)

Lemma compare_xO_xO p q : (p~0 ?= q~0) = (p ?= q).
Proof. Show. Fail (abduce 3). Admitted.

Lemma compare_xI_xI p q : (p~1 ?= q~1) = (p ?= q).
Proof. Show. Fail (abduce 3). Admitted.

Lemma compare_xI_xO p q :
 (p~1 ?= q~0) = switch_Eq Gt (p ?= q).
Proof. Show. Fail (abduce 3). Admitted.

Lemma compare_xO_xI p q :
 (p~0 ?= q~1) = switch_Eq Lt (p ?= q).
Proof. Show. Fail (abduce 3). Admitted.

Hint Rewrite compare_xO_xO compare_xI_xI compare_xI_xO compare_xO_xI : compare.

Ltac simpl_compare := autorewrite with compare.
Ltac simpl_compare_in H := autorewrite with compare in H.

(** Relation between [compare] and [sub_mask] *)

Definition mask2cmp (p:mask) : comparison :=
 match p with
  | IsNul => Eq
  | IsPos _ => Gt
  | IsNeg => Lt
 end.

Lemma compare_sub_mask p q : (p ?= q) = mask2cmp (sub_mask p q).
Proof. Show. Fail (abduce 3). Admitted.

(** Alternative characterisation of strict order in term of addition *)

Lemma lt_iff_add p q : p < q <-> exists r, p + r = q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma gt_iff_add p q : p > q <-> exists r, q + r = p.
Proof. Show. Fail (abduce 3). Admitted.

(** Basic facts about [compare_cont] *)

Theorem compare_cont_refl p c :
  compare_cont c p p = c.
Proof. Show. Fail (abduce 3). Admitted.

Lemma compare_cont_antisym p q c :
  CompOpp (compare_cont c p q) = compare_cont (CompOpp c) q p.
Proof. Show. Fail (abduce 3). Admitted.

(** Basic facts about [compare] *)

Lemma compare_eq_iff p q : (p ?= q) = Eq <-> p = q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma compare_antisym p q : (q ?= p) = CompOpp (p ?= q).
Proof. Show. Fail (abduce 3). Admitted.

Lemma compare_lt_iff p q : (p ?= q) = Lt <-> p < q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma compare_le_iff p q : (p ?= q) <> Gt <-> p <= q.
Proof. Show. Fail (abduce 3). Admitted.

(** More properties about [compare] and boolean comparisons,
  including [compare_spec] and [lt_irrefl] and [lt_eq_cases]. *)

Include BoolOrderFacts.

Definition le_lteq := lt_eq_cases.

(** ** Facts about [gt] and [ge] *)

(** The predicates [lt] and [le] are now favored in the statements
  of theorems, the use of [gt] and [ge] is hence not recommended.
  We provide here the bare minimal results to related them with
  [lt] and [le]. *)

Lemma gt_lt_iff p q : p > q <-> q < p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma gt_lt p q : p > q -> q < p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma lt_gt p q : p < q -> q > p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma ge_le_iff p q : p >= q <-> q <= p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma ge_le p q : p >= q -> q <= p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma le_ge p q : p <= q -> q >= p.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Comparison and the successor *)

Lemma compare_succ_r p q :
  switch_Eq Gt (p ?= succ q) = switch_Eq Lt (p ?= q).
Proof. Show. Fail (abduce 3). Admitted.

Lemma compare_succ_l p q :
  switch_Eq Lt (succ p ?= q) = switch_Eq Gt (p ?= q).
Proof. Show. Fail (abduce 3). Admitted.

Theorem lt_succ_r p q : p < succ q <-> p <= q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma lt_succ_diag_r p : p < succ p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma compare_succ_succ p q : (succ p ?= succ q) = (p ?= q).
Proof. Show. Fail (abduce 3). Admitted.

(** ** 1 is the least positive number *)

Lemma le_1_l p : 1 <= p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma nlt_1_r p : ~ p < 1.
Proof. Show. Fail (abduce 3). Admitted.

Lemma lt_1_succ p : 1 < succ p.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Properties of the order *)

Lemma le_nlt p q : p <= q <-> ~ q < p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma lt_nle p q : p < q <-> ~ q <= p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma lt_le_incl p q : p<q -> p<=q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma lt_lt_succ n m : n < m -> n < succ m.
Proof. Show. Fail (abduce 3). Admitted.

Lemma succ_lt_mono n m : n < m <-> succ n < succ m.
Proof. Show. Fail (abduce 3). Admitted.

Lemma succ_le_mono n m : n <= m <-> succ n <= succ m.
Proof. Show. Fail (abduce 3). Admitted.

Lemma lt_trans n m p : n < m -> m < p -> n < p.
Proof. Show. Fail (abduce 3). Admitted.

Theorem lt_ind : forall (A : positive -> Prop) (n : positive),
  A (succ n) ->
    (forall m : positive, n < m -> A m -> A (succ m)) ->
      forall m : positive, n < m -> A m.
Proof. Show. Fail (abduce 3). Admitted.

Instance lt_strorder : StrictOrder lt.
Proof. Show. Fail (abduce 3). Admitted.

Instance lt_compat : Proper (Logic.eq==>Logic.eq==>iff) lt.
Proof. Show. Fail (abduce 3). Admitted.

Lemma lt_total p q : p < q \/ p = q \/ q < p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma le_refl p : p <= p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma le_lt_trans n m p : n <= m -> m < p -> n < p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma lt_le_trans n m p : n < m -> m <= p -> n < p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma le_trans n m p : n <= m -> m <= p -> n <= p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma le_succ_l n m : succ n <= m <-> n < m.
Proof. Show. Fail (abduce 3). Admitted.

Lemma le_antisym p q : p <= q -> q <= p -> p = q.
Proof. Show. Fail (abduce 3). Admitted.

Instance le_preorder : PreOrder le.
Proof. Show. Fail (abduce 3). Admitted.

Instance le_partorder : PartialOrder Logic.eq le.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Comparison and addition *)

Lemma add_compare_mono_l p q r : (p+q ?= p+r) = (q ?= r).
Proof. Show. Fail (abduce 3). Admitted.

Lemma add_compare_mono_r p q r : (q+p ?= r+p) = (q ?= r).
Proof. Show. Fail (abduce 3). Admitted.

(** ** Order and addition *)

Lemma lt_add_diag_r p q : p < p + q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma add_lt_mono_l p q r : q<r <-> p+q < p+r.
Proof. Show. Fail (abduce 3). Admitted.

Lemma add_lt_mono_r p q r : q<r <-> q+p < r+p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma add_lt_mono p q r s : p<q -> r<s -> p+r<q+s.
Proof. Show. Fail (abduce 3). Admitted.

Lemma add_le_mono_l p q r : q<=r <-> p+q<=p+r.
Proof. Show. Fail (abduce 3). Admitted.

Lemma add_le_mono_r p q r : q<=r <-> q+p<=r+p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma add_le_mono p q r s : p<=q -> r<=s -> p+r <= q+s.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Comparison and multiplication *)

Lemma mul_compare_mono_l p q r : (p*q ?= p*r) = (q ?= r).
Proof. Show. Fail (abduce 3). Admitted.

Lemma mul_compare_mono_r p q r : (q*p ?= r*p) = (q ?= r).
Proof. Show. Fail (abduce 3). Admitted.

(** ** Order and multiplication *)

Lemma mul_lt_mono_l p q r : q<r <-> p*q < p*r.
Proof. Show. Fail (abduce 3). Admitted.

Lemma mul_lt_mono_r p q r : q<r <-> q*p < r*p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma mul_lt_mono p q r s : p<q -> r<s -> p*r < q*s.
Proof. Show. Fail (abduce 3). Admitted.

Lemma mul_le_mono_l p q r : q<=r <-> p*q<=p*r.
Proof. Show. Fail (abduce 3). Admitted.

Lemma mul_le_mono_r p q r : q<=r <-> q*p<=r*p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma mul_le_mono p q r s : p<=q -> r<=s -> p*r <= q*s.
Proof. Show. Fail (abduce 3). Admitted.

Lemma lt_add_r p q : p < p+q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma lt_not_add_l p q : ~ p+q < p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pow_gt_1 n p : 1<n -> 1<n^p.
Proof. Show. Fail (abduce 3). Admitted.

(**********************************************************************)
(** * Properties of subtraction on binary positive numbers *)

Lemma sub_1_r p : sub p 1 = pred p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pred_sub p : pred p = sub p 1.
Proof. Show. Fail (abduce 3). Admitted.

Theorem sub_succ_r p q : p - (succ q) = pred (p - q).
Proof. Show. Fail (abduce 3). Admitted.

(** ** Properties of subtraction without underflow *)

Lemma sub_mask_pos' p q :
  q < p -> exists r, sub_mask p q = IsPos r /\ q + r = p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma sub_mask_pos p q :
  q < p -> exists r, sub_mask p q = IsPos r.
Proof. Show. Fail (abduce 3). Admitted.

Theorem sub_add p q : q < p -> (p-q)+q = p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma add_sub p q : (p+q)-q = p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma mul_sub_distr_l p q r : r<q -> p*(q-r) = p*q-p*r.
Proof. Show. Fail (abduce 3). Admitted.

Lemma mul_sub_distr_r p q r : q<p -> (p-q)*r = p*r-q*r.
Proof. Show. Fail (abduce 3). Admitted.

Lemma sub_lt_mono_l p q r: q<p -> p<r -> r-p < r-q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma sub_compare_mono_l p q r :
 q<p -> r<p -> (p-q ?= p-r) = (r ?= q).
Proof. Show. Fail (abduce 3). Admitted.

Lemma sub_compare_mono_r p q r :
 p<q -> p<r -> (q-p ?= r-p) = (q ?= r).
Proof. Show. Fail (abduce 3). Admitted.

Lemma sub_lt_mono_r p q r : q<p -> r<q -> q-r < p-r.
Proof. Show. Fail (abduce 3). Admitted.

Lemma sub_decr n m : m<n -> n-m < n.
Proof. Show. Fail (abduce 3). Admitted.

Lemma add_sub_assoc p q r : r<q -> p+(q-r) = p+q-r.
Proof. Show. Fail (abduce 3). Admitted.

Lemma sub_add_distr p q r : q+r < p -> p-(q+r) = p-q-r.
Proof. Show. Fail (abduce 3). Admitted.

Lemma sub_sub_distr p q r : r<q -> q-r < p -> p-(q-r) = p+r-q.
Proof. Show. Fail (abduce 3). Admitted.

(** Recursive equations for [sub] *)

Lemma sub_xO_xO n m : m<n -> n~0 - m~0 = (n-m)~0.
Proof. Show. Fail (abduce 3). Admitted.

Lemma sub_xI_xI n m : m<n -> n~1 - m~1 = (n-m)~0.
Proof. Show. Fail (abduce 3). Admitted.

Lemma sub_xI_xO n m : m<n -> n~1 - m~0 = (n-m)~1.
Proof. Show. Fail (abduce 3). Admitted.

Lemma sub_xO_xI n m : n~0 - m~1 = pred_double (n-m).
Proof. Show. Fail (abduce 3). Admitted.

(** Properties of subtraction with underflow *)

Lemma sub_mask_neg_iff' p q : sub_mask p q = IsNeg <-> p < q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma sub_mask_neg p q : p<q -> sub_mask p q = IsNeg.
Proof. Show. Fail (abduce 3). Admitted.

Lemma sub_le p q : p<=q -> p-q = 1.
Proof. Show. Fail (abduce 3). Admitted.

Lemma sub_lt p q : p<q -> p-q = 1.
Proof. Show. Fail (abduce 3). Admitted.

Lemma sub_diag p : p-p = 1.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Results concerning [size] and [size_nat] *)

Lemma size_nat_monotone p q : p<q -> (size_nat p <= size_nat q)%nat.
Proof. Show. Fail (abduce 3). Admitted.

Lemma size_gt p : p < 2^(size p).
Proof. Show. Fail (abduce 3). Admitted.

Lemma size_le p : 2^(size p) <= p~0.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Properties of [min] and [max] *)

(** First, the specification *)

Lemma max_l : forall x y, y<=x -> max x y = x.
Proof. Show. Fail (abduce 3). Admitted.

Lemma max_r : forall x y, x<=y -> max x y = y.
Proof. Show. Fail (abduce 3). Admitted.

Lemma min_l : forall x y, x<=y -> min x y = x.
Proof. Show. Fail (abduce 3). Admitted.

Lemma min_r : forall x y, y<=x -> min x y = y.
Proof. Show. Fail (abduce 3). Admitted.

(** We hence obtain all the generic properties of [min] and [max]. *)

Include UsualMinMaxLogicalProperties <+ UsualMinMaxDecProperties.

Ltac order := Private_Tac.order.

(** Minimum, maximum and constant one *)

Lemma max_1_l n : max 1 n = n.
Proof. Show. Fail (abduce 3). Admitted.

Lemma max_1_r n : max n 1 = n.
Proof. Show. Fail (abduce 3). Admitted.

Lemma min_1_l n : min 1 n = 1.
Proof. Show. Fail (abduce 3). Admitted.

Lemma min_1_r n : min n 1 = 1.
Proof. Show. Fail (abduce 3). Admitted.

(** Minimum, maximum and operations (consequences of monotonicity) *)

Lemma succ_max_distr n m : succ (max n m) = max (succ n) (succ m).
Proof. Show. Fail (abduce 3). Admitted.

Lemma succ_min_distr n m : succ (min n m) = min (succ n) (succ m).
Proof. Show. Fail (abduce 3). Admitted.

Lemma add_max_distr_l n m p : max (p + n) (p + m) = p + max n m.
Proof. Show. Fail (abduce 3). Admitted.

Lemma add_max_distr_r n m p : max (n + p) (m + p) = max n m + p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma add_min_distr_l n m p : min (p + n) (p + m) = p + min n m.
Proof. Show. Fail (abduce 3). Admitted.

Lemma add_min_distr_r n m p : min (n + p) (m + p) = min n m + p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma mul_max_distr_l n m p : max (p * n) (p * m) = p * max n m.
Proof. Show. Fail (abduce 3). Admitted.

Lemma mul_max_distr_r n m p : max (n * p) (m * p) = max n m * p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma mul_min_distr_l n m p : min (p * n) (p * m) = p * min n m.
Proof. Show. Fail (abduce 3). Admitted.

Lemma mul_min_distr_r n m p : min (n * p) (m * p) = min n m * p.
Proof. Show. Fail (abduce 3). Admitted.


(** ** Results concerning [iter_op] *)

Lemma iter_op_succ : forall A (op:A->A->A),
 (forall x y z, op x (op y z) = op (op x y) z) ->
 forall p a,
 iter_op op (succ p) a = op a (iter_op op p a).
Proof. Show. Fail (abduce 3). Admitted.

(** ** Results about [of_nat] and [of_succ_nat] *)

Lemma of_nat_succ (n:nat) : of_succ_nat n = of_nat (S n).
Proof. Show. Fail (abduce 3). Admitted.

Lemma pred_of_succ_nat (n:nat) : pred (of_succ_nat n) = of_nat n.
Proof. Show. Fail (abduce 3). Admitted.

Lemma succ_of_nat (n:nat) : n<>O -> succ (of_nat n) = of_succ_nat n.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Correctness proofs for the square root function *)

Inductive SqrtSpec : positive*mask -> positive -> Prop :=
 | SqrtExact s x : x=s*s -> SqrtSpec (s,IsNul) x
 | SqrtApprox s r x : x=s*s+r -> r <= s~0 -> SqrtSpec (s,IsPos r) x.

Lemma sqrtrem_step_spec f g p x :
 (f=xO \/ f=xI) -> (g=xO \/ g=xI) ->
 SqrtSpec p x -> SqrtSpec (sqrtrem_step f g p) (g (f x)).
Proof. Show. Fail (abduce 3). Admitted.

Lemma sqrtrem_spec p : SqrtSpec (sqrtrem p) p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma sqrt_spec p :
 let s := sqrt p in s*s <= p < (succ s)*(succ s).
Proof. Show. Fail (abduce 3). Admitted.

(** ** Correctness proofs for the gcd function *)

Lemma divide_add_cancel_l p q r : (p | r) -> (p | q + r) -> (p | q).
Proof. Show. Fail (abduce 3). Admitted.

Lemma divide_xO_xI p q r : (p | q~0) -> (p | r~1) -> (p | q).
Proof. Show. Fail (abduce 3). Admitted.

Lemma divide_xO_xO p q : (p~0|q~0) <-> (p|q).
Proof. Show. Fail (abduce 3). Admitted.

Lemma divide_mul_l p q r : (p|q) -> (p|q*r).
Proof. Show. Fail (abduce 3). Admitted.

Lemma divide_mul_r p q r : (p|r) -> (p|q*r).
Proof. Show. Fail (abduce 3). Admitted.

(** The first component of ggcd is gcd *)

Lemma ggcdn_gcdn : forall n a b,
  fst (ggcdn n a b) = gcdn n a b.
Proof. Show. Fail (abduce 3). Admitted.

Lemma ggcd_gcd : forall a b, fst (ggcd a b) = gcd a b.
Proof. Show. Fail (abduce 3). Admitted.

(** The other components of ggcd are indeed the correct factors. *)

Ltac destr_pggcdn IHn :=
 match goal with |- context [ ggcdn _ ?x ?y ] =>
  generalize (IHn x y); destruct ggcdn as (?g,(?u,?v)); simpl
 end.

Lemma ggcdn_correct_divisors : forall n a b,
  let '(g,(aa,bb)) := ggcdn n a b in
  a = g*aa /\ b = g*bb.
Proof. Show. Fail (abduce 3). Admitted.

Lemma ggcd_correct_divisors : forall a b,
  let '(g,(aa,bb)) := ggcd a b in
  a=g*aa /\ b=g*bb.
Proof. Show. Fail (abduce 3). Admitted.

(** We can use this fact to prove a part of the gcd correctness *)

Lemma gcd_divide_l : forall a b, (gcd a b | a).
Proof. Show. Fail (abduce 3). Admitted.

Lemma gcd_divide_r : forall a b, (gcd a b | b).
Proof. Show. Fail (abduce 3). Admitted.

(** We now prove directly that gcd is the greatest amongst common divisors *)

Lemma gcdn_greatest : forall n a b, (size_nat a + size_nat b <= n)%nat ->
 forall p, (p|a) -> (p|b) -> (p|gcdn n a b).
Proof. Show. Fail (abduce 3). Admitted.

Lemma gcd_greatest : forall a b p, (p|a) -> (p|b) -> (p|gcd a b).
Proof. Show. Fail (abduce 3). Admitted.

(** As a consequence, the rests after division by gcd are relatively prime *)

Lemma ggcd_greatest : forall a b,
 let (aa,bb) := snd (ggcd a b) in
 forall p, (p|aa) -> (p|bb) -> p=1.
Proof. Show. Fail (abduce 3). Admitted.

End Pos.

Bind Scope positive_scope with Pos.t positive.

(** Exportation of notations *)

Number Notation positive Pos.of_num_int Pos.to_num_uint : positive_scope.

Infix "+" := Pos.add : positive_scope.
Infix "-" := Pos.sub : positive_scope.
Infix "*" := Pos.mul : positive_scope.
Infix "^" := Pos.pow : positive_scope.
Infix "?=" := Pos.compare (at level 70, no associativity) : positive_scope.
Infix "=?" := Pos.eqb (at level 70, no associativity) : positive_scope.
Infix "<=?" := Pos.leb (at level 70, no associativity) : positive_scope.
Infix "<?" := Pos.ltb (at level 70, no associativity) : positive_scope.
Infix "<=" := Pos.le : positive_scope.
Infix "<" := Pos.lt : positive_scope.
Infix ">=" := Pos.ge : positive_scope.
Infix ">" := Pos.gt : positive_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : positive_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : positive_scope.
Notation "x < y < z" := (x < y /\ y < z) : positive_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : positive_scope.

Notation "( p | q )" := (Pos.divide p q) (at level 0) : positive_scope.

(** Compatibility notations *)

Notation positive := positive (only parsing).
Notation positive_rect := positive_rect (only parsing).
Notation positive_rec := positive_rec (only parsing).
Notation positive_ind := positive_ind (only parsing).
Notation xI := xI (only parsing).
Notation xO := xO (only parsing).
Notation xH := xH (only parsing).

Notation IsNul := Pos.IsNul (only parsing).
Notation IsPos := Pos.IsPos (only parsing).
Notation IsNeg := Pos.IsNeg (only parsing).

Notation Pplus := Pos.add (only parsing).
Notation Pplus_carry := Pos.add_carry (only parsing).
Notation Pmult_nat := (Pos.iter_op plus) (only parsing).
Notation nat_of_P := Pos.to_nat (only parsing).
Notation P_of_succ_nat := Pos.of_succ_nat (only parsing).
Notation Pdouble_minus_one := Pos.pred_double (only parsing).
Notation positive_mask := Pos.mask (only parsing).
Notation positive_mask_rect := Pos.mask_rect (only parsing).
Notation positive_mask_ind := Pos.mask_ind (only parsing).
Notation positive_mask_rec := Pos.mask_rec (only parsing).
Notation Pdouble_plus_one_mask := Pos.succ_double_mask (only parsing).
Notation Pdouble_minus_two := Pos.double_pred_mask (only parsing).
Notation Pminus_mask := Pos.sub_mask (only parsing).
Notation Pminus_mask_carry := Pos.sub_mask_carry (only parsing).
Notation Pminus := Pos.sub (only parsing).
Notation Pmult := Pos.mul (only parsing).
Notation iter_pos := @Pos.iter (only parsing).
Notation Psize := Pos.size_nat (only parsing).
Notation Psize_pos := Pos.size (only parsing).
Notation Pcompare x y m := (Pos.compare_cont m x y) (only parsing).
Notation positive_eq_dec := Pos.eq_dec (only parsing).
Notation xI_succ_xO := Pos.xI_succ_xO (only parsing).
Notation Psucc_o_double_minus_one_eq_xO :=
 Pos.succ_pred_double (only parsing).
Notation Pdouble_minus_one_o_succ_eq_xI :=
 Pos.pred_double_succ (only parsing).
Notation xO_succ_permute := Pos.double_succ (only parsing).
Notation double_moins_un_xO_discr :=
 Pos.pred_double_xO_discr (only parsing).
Notation Psucc_not_one := Pos.succ_not_1 (only parsing).
Notation Psucc_pred := Pos.succ_pred_or (only parsing).
Notation Pplus_carry_spec := Pos.add_carry_spec (only parsing).
Notation Pplus_comm := Pos.add_comm (only parsing).
Notation Pplus_succ_permute_r := Pos.add_succ_r (only parsing).
Notation Pplus_succ_permute_l := Pos.add_succ_l (only parsing).
Notation Pplus_no_neutral := Pos.add_no_neutral (only parsing).
Notation Pplus_carry_plus := Pos.add_carry_add (only parsing).
Notation Pplus_reg_r := Pos.add_reg_r (only parsing).
Notation Pplus_reg_l := Pos.add_reg_l (only parsing).
Notation Pplus_carry_reg_r := Pos.add_carry_reg_r (only parsing).
Notation Pplus_carry_reg_l := Pos.add_carry_reg_l (only parsing).
Notation Pplus_assoc := Pos.add_assoc (only parsing).
Notation Pplus_xO := Pos.add_xO (only parsing).
Notation Pplus_xI_double_minus_one := Pos.add_xI_pred_double (only parsing).
Notation Pplus_xO_double_minus_one := Pos.add_xO_pred_double (only parsing).
Notation Pplus_diag := Pos.add_diag (only parsing).
Notation PeanoView := Pos.PeanoView (only parsing).
Notation PeanoOne := Pos.PeanoOne (only parsing).
Notation PeanoSucc := Pos.PeanoSucc (only parsing).
Notation PeanoView_rect := Pos.PeanoView_rect (only parsing).
Notation PeanoView_ind := Pos.PeanoView_ind (only parsing).
Notation PeanoView_rec := Pos.PeanoView_rec (only parsing).
Notation peanoView_xO := Pos.peanoView_xO (only parsing).
Notation peanoView_xI := Pos.peanoView_xI (only parsing).
Notation peanoView := Pos.peanoView (only parsing).
Notation PeanoView_iter := Pos.PeanoView_iter (only parsing).
Notation eq_dep_eq_positive := Pos.eq_dep_eq_positive (only parsing).
Notation PeanoViewUnique := Pos.PeanoViewUnique (only parsing).
Notation Prect := Pos.peano_rect (only parsing).
Notation Prect_succ := Pos.peano_rect_succ (only parsing).
Notation Prect_base := Pos.peano_rect_base (only parsing).
Notation Prec := Pos.peano_rec (only parsing).
Notation Pind := Pos.peano_ind (only parsing).
Notation Pcase := Pos.peano_case (only parsing).
Notation Pmult_1_r := Pos.mul_1_r (only parsing).
Notation Pmult_Sn_m := Pos.mul_succ_l (only parsing).
Notation Pmult_xO_permute_r := Pos.mul_xO_r (only parsing).
Notation Pmult_xI_permute_r := Pos.mul_xI_r (only parsing).
Notation Pmult_comm := Pos.mul_comm (only parsing).
Notation Pmult_plus_distr_l := Pos.mul_add_distr_l (only parsing).
Notation Pmult_plus_distr_r := Pos.mul_add_distr_r (only parsing).
Notation Pmult_assoc := Pos.mul_assoc (only parsing).
Notation Pmult_xI_mult_xO_discr := Pos.mul_xI_mul_xO_discr (only parsing).
Notation Pmult_xO_discr := Pos.mul_xO_discr (only parsing).
Notation Pmult_reg_r := Pos.mul_reg_r (only parsing).
Notation Pmult_reg_l := Pos.mul_reg_l (only parsing).
Notation Pmult_1_inversion_l := Pos.mul_eq_1_l (only parsing).
Notation iter_pos_swap_gen := Pos.iter_swap_gen (only parsing).
Notation iter_pos_swap := Pos.iter_swap (only parsing).
Notation iter_pos_succ := Pos.iter_succ (only parsing).
Notation iter_pos_plus := Pos.iter_add (only parsing).
Notation iter_pos_invariant := Pos.iter_invariant (only parsing).
Notation Pcompare_refl_id := Pos.compare_cont_refl (only parsing).
Notation Pcompare_eq_iff := Pos.compare_eq_iff (only parsing).
Notation Pcompare_Gt_Lt := Pos.compare_cont_Gt_Lt (only parsing).
Notation Pcompare_eq_Lt := Pos.compare_lt_iff (only parsing).
Notation Pcompare_Lt_Gt := Pos.compare_cont_Lt_Gt (only parsing).

Notation Pcompare_antisym := Pos.compare_cont_antisym (only parsing).
Notation ZC1 := Pos.gt_lt (only parsing).
Notation ZC2 := Pos.lt_gt (only parsing).
Notation Pcompare_p_Sp := Pos.lt_succ_diag_r (only parsing).
Notation Pcompare_1 := Pos.nlt_1_r (only parsing).
Notation Plt_1 := Pos.nlt_1_r (only parsing).
Notation Pplus_compare_mono_l := Pos.add_compare_mono_l (only parsing).
Notation Pplus_compare_mono_r := Pos.add_compare_mono_r (only parsing).
Notation Pplus_lt_mono_l := Pos.add_lt_mono_l (only parsing).
Notation Pplus_lt_mono_r := Pos.add_lt_mono_r (only parsing).
Notation Pplus_lt_mono := Pos.add_lt_mono (only parsing).
Notation Pplus_le_mono_l := Pos.add_le_mono_l (only parsing).
Notation Pplus_le_mono_r := Pos.add_le_mono_r (only parsing).
Notation Pplus_le_mono := Pos.add_le_mono (only parsing).
Notation Pmult_compare_mono_l := Pos.mul_compare_mono_l (only parsing).
Notation Pmult_compare_mono_r := Pos.mul_compare_mono_r (only parsing).
Notation Pmult_lt_mono_l := Pos.mul_lt_mono_l (only parsing).
Notation Pmult_lt_mono_r := Pos.mul_lt_mono_r (only parsing).
Notation Pmult_lt_mono := Pos.mul_lt_mono (only parsing).
Notation Pmult_le_mono_l := Pos.mul_le_mono_l (only parsing).
Notation Pmult_le_mono_r := Pos.mul_le_mono_r (only parsing).
Notation Pmult_le_mono := Pos.mul_le_mono (only parsing).
Notation Plt_plus_r := Pos.lt_add_r (only parsing).
Notation Plt_not_plus_l := Pos.lt_not_add_l (only parsing).
Notation Pminus_mask_succ_r := Pos.sub_mask_succ_r (only parsing).
Notation Pminus_mask_carry_spec := Pos.sub_mask_carry_spec (only parsing).
Notation Pminus_succ_r := Pos.sub_succ_r (only parsing).
Notation Pminus_mask_diag := Pos.sub_mask_diag (only parsing).

Notation Pplus_minus_eq := Pos.add_sub (only parsing).
Notation Pmult_minus_distr_l := Pos.mul_sub_distr_l (only parsing).
Notation Pminus_lt_mono_l := Pos.sub_lt_mono_l (only parsing).
Notation Pminus_compare_mono_l := Pos.sub_compare_mono_l (only parsing).
Notation Pminus_compare_mono_r := Pos.sub_compare_mono_r (only parsing).
Notation Pminus_lt_mono_r := Pos.sub_lt_mono_r (only parsing).
Notation Pminus_decr := Pos.sub_decr (only parsing).
Notation Pminus_xI_xI := Pos.sub_xI_xI (only parsing).
Notation Pplus_minus_assoc := Pos.add_sub_assoc (only parsing).
Notation Pminus_plus_distr := Pos.sub_add_distr (only parsing).
Notation Pminus_minus_distr := Pos.sub_sub_distr (only parsing).
Notation Pminus_mask_Lt := Pos.sub_mask_neg (only parsing).
Notation Pminus_Lt := Pos.sub_lt (only parsing).
Notation Pminus_Eq := Pos.sub_diag (only parsing).
Notation Psize_monotone := Pos.size_nat_monotone (only parsing).
Notation Psize_pos_gt := Pos.size_gt (only parsing).
Notation Psize_pos_le := Pos.size_le (only parsing).

(** More complex compatibility facts, expressed as lemmas
    (to preserve scopes for instance) *)

Lemma Peqb_true_eq x y : Pos.eqb x y = true -> x=y.
Proof. Show. Fail (abduce 3). Admitted.
Lemma Pcompare_eq_Gt p q : (p ?= q) = Gt <-> p > q.
Proof. Show. Fail (abduce 3). Admitted.
Lemma Pplus_one_succ_r p : Pos.succ p = p + 1.
Proof (eq_sym (Pos.add_1_r p)).
Lemma Pplus_one_succ_l p : Pos.succ p = 1 + p.
Proof (eq_sym (Pos.add_1_l p)).
Lemma Pcompare_refl p : Pos.compare_cont Eq p p = Eq.
Proof (Pos.compare_cont_refl p Eq).
Lemma Pcompare_Eq_eq : forall p q, Pos.compare_cont Eq p q = Eq -> p = q.
Proof Pos.compare_eq.
Lemma ZC4 p q : Pos.compare_cont Eq p q = CompOpp (Pos.compare_cont Eq q p).
Proof (Pos.compare_antisym q p).
Lemma Ppred_minus p : Pos.pred p = p - 1.
Proof (eq_sym (Pos.sub_1_r p)).

Lemma Pminus_mask_Gt p q :
  p > q ->
  exists h : positive,
   Pos.sub_mask p q = IsPos h /\
   q + h = p /\ (h = 1 \/ Pos.sub_mask_carry p q = IsPos (Pos.pred h)).
Proof. Show. Fail (abduce 3). Admitted.

Lemma Pplus_minus : forall p q, p > q -> q+(p-q) = p.
Proof. Show. Fail (abduce 3). Admitted.

(** Discontinued results of little interest and little/zero use
    in user contributions:

    Pplus_carry_no_neutral
    Pplus_carry_pred_eq_plus
    Pcompare_not_Eq
    Pcompare_Lt_Lt
    Pcompare_Lt_eq_Lt
    Pcompare_Gt_Gt
    Pcompare_Gt_eq_Gt
    Psucc_lt_compat
    Psucc_le_compat
    ZC3
    Pcompare_p_Sq
    Pminus_mask_carry_diag
    Pminus_mask_IsNeg
    ZL10
    ZL11
    double_eq_zero_inversion
    double_plus_one_zero_discr
    double_plus_one_eq_one_inversion
    double_eq_one_discr

    Infix "/" := Pdiv2 : positive_scope.
*)

(** Old stuff, to remove someday *)

Lemma Dcompare : forall r:comparison, r = Eq \/ r = Lt \/ r = Gt.
Proof. Show. Fail (abduce 3). Admitted.

(** Incompatibilities :

 - [(_ ?= _)%positive] expects no arg now, and designates [Pos.compare]
   which is convertible but syntactically distinct to
   [Pos.compare_cont .. .. Eq].

 - [Pmult_nat] cannot be unfolded (unfold [Pos.iter_op] instead).

*)
