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
Require Import BinPos RelationClasses Morphisms Setoid
 Equalities OrdersFacts GenericMinMax Bool NAxioms NMaxMin NProperties.
Require BinNatDef.
Add Rec LoadPath "/home/arjun/Desktop/smtcoq/abduction-arjunvish-smtcoq/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
(**********************************************************************)
(** * Binary natural numbers, operations and properties *)
(**********************************************************************)

(** The type [N] and its constructors [N0] and [Npos] are now
    defined in [BinNums.v] *)

(** Every definitions and properties about binary natural numbers
    are placed in a module [N] for qualification purpose. *)

Local Open Scope N_scope.

(** Every definitions and early properties about positive numbers
    are placed in a module [N] for qualification purpose. *)

Module N
 <: NAxiomsSig
 <: UsualOrderedTypeFull
 <: UsualDecidableTypeFull
 <: TotalOrder.

(** Definitions of operations, now in a separate file *)

Include BinNatDef.N.

(** When including property functors, only inline t eq zero one two *)

Set Inline Level 30.

(** Logical predicates *)

Definition eq := @Logic.eq N.
Definition eq_equiv := @eq_equivalence N.

Definition lt x y := (x ?= y) = Lt.
Definition gt x y := (x ?= y) = Gt.
Definition le x y := (x ?= y) <> Gt.
Definition ge x y := (x ?= y) <> Lt.

Infix "<=" := le : N_scope.
Infix "<" := lt : N_scope.
Infix ">=" := ge : N_scope.
Infix ">" := gt : N_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : N_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : N_scope.
Notation "x < y < z" := (x < y /\ y < z) : N_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : N_scope.

Definition divide p q := exists r, q = r*p.
Notation "( p | q )" := (divide p q) (at level 0) : N_scope.

Definition Even n := exists m, n = 2*m.
Definition Odd n := exists m, n = 2*m+1.

(** Proofs of morphisms, obvious since eq is Leibniz *)

Local Obligation Tactic := simpl_relation.
Program Definition succ_wd : Proper (eq==>eq) succ := _.
Program Definition pred_wd : Proper (eq==>eq) pred := _.
Program Definition add_wd : Proper (eq==>eq==>eq) add := _.
Program Definition sub_wd : Proper (eq==>eq==>eq) sub := _.
Program Definition mul_wd : Proper (eq==>eq==>eq) mul := _.
Program Definition lt_wd : Proper (eq==>eq==>iff) lt := _.
Program Definition div_wd : Proper (eq==>eq==>eq) div := _.
Program Definition mod_wd : Proper (eq==>eq==>eq) modulo := _.
Program Definition pow_wd : Proper (eq==>eq==>eq) pow := _.
Program Definition testbit_wd : Proper (eq==>eq==>Logic.eq) testbit := _.

(** Decidability of equality. *)

Definition eq_dec : forall n m : N, { n = m } + { n <> m }.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Discrimination principle *)

Definition discr n : { p:positive | n = pos p } + { n = 0 }.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Convenient induction principles *)

Definition binary_rect (P:N -> Type) (f0 : P 0)
  (f2 : forall n, P n -> P (double n))
  (fS2 : forall n, P n -> P (succ_double n)) (n : N) : P n :=
 let P' p := P (pos p) in
 let f2' p := f2 (pos p) in
 let fS2' p := fS2 (pos p) in
 match n with
 | 0 => f0
 | pos p => positive_rect P' fS2' f2' (fS2 0 f0) p
 end.

Definition binary_rec (P:N -> Set) := binary_rect P.
Definition binary_ind (P:N -> Prop) := binary_rect P.

(** Peano induction on binary natural numbers *)

Definition peano_rect
  (P : N -> Type) (f0 : P 0)
    (f : forall n : N, P n -> P (succ n)) (n : N) : P n :=
let P' p := P (pos p) in
let f' p := f (pos p) in
match n with
| 0 => f0
| pos p => Pos.peano_rect P' (f 0 f0) f' p
end.

Theorem peano_rect_base P a f : peano_rect P a f 0 = a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem peano_rect_succ P a f n :
 peano_rect P a f (succ n) = f n (peano_rect P a f n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition peano_ind (P : N -> Prop) := peano_rect P.

Definition peano_rec (P : N -> Set) := peano_rect P.

Theorem peano_rec_base P a f : peano_rec P a f 0 = a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem peano_rec_succ P a f n :
 peano_rec P a f (succ n) = f n (peano_rec P a f n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Generic induction / recursion *)

Theorem bi_induction :
  forall A : N -> Prop, Proper (Logic.eq==>iff) A ->
    A 0 -> (forall n, A n <-> A (succ n)) -> forall n : N, A n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition recursion {A} : A -> (N -> A -> A) -> N -> A :=
  peano_rect (fun _ => A).

Instance recursion_wd {A} (Aeq : relation A) :
 Proper (Aeq==>(Logic.eq==>Aeq==>Aeq)==>Logic.eq==>Aeq) recursion.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem recursion_0 {A} (a:A) (f:N->A->A) : recursion a f 0 = a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem recursion_succ {A} (Aeq : relation A) (a : A) (f : N -> A -> A):
 Aeq a a -> Proper (Logic.eq==>Aeq==>Aeq) f ->
  forall n : N, Aeq (recursion a f (succ n)) (f n (recursion a f n)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Specification of constants *)

Lemma one_succ : 1 = succ 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma two_succ : 2 = succ 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition pred_0 : pred 0 = 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Properties of mixed successor and predecessor. *)

Lemma pos_pred_spec p : Pos.pred_N p = pred (pos p).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma succ_pos_spec n : pos (succ_pos n) = succ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pos_pred_succ n : Pos.pred_N (succ_pos n) = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma succ_pos_pred p : succ (Pos.pred_N p) = pos p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Properties of successor and predecessor *)

Theorem pred_succ n : pred (succ n) = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem pred_sub n : pred n = sub n 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem succ_0_discr n : succ n <> 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Specification of addition *)

Theorem add_0_l n : 0 + n = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem add_succ_l n m : succ n + m = succ (n + m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Specification of subtraction. *)

Theorem sub_0_r n : n - 0 = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem sub_succ_r n m : n - succ m = pred (n - m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Specification of multiplication *)

Theorem mul_0_l n : 0 * n = 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem mul_succ_l n m : (succ n) * m = n * m + m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Specification of boolean comparisons. *)

Lemma eqb_eq n m : eqb n m = true <-> n=m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltb_lt n m : (n <? m) = true <-> n < m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leb_le n m : (n <=? m) = true <-> n <= m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Basic properties of comparison *)

Theorem compare_eq_iff n m : (n ?= m) = Eq <-> n = m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem compare_lt_iff n m : (n ?= m) = Lt <-> n < m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem compare_le_iff n m : (n ?= m) <> Gt <-> n <= m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem compare_antisym n m : (m ?= n) = CompOpp (n ?= m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Some more advanced properties of comparison and orders,
    including [compare_spec] and [lt_irrefl] and [lt_eq_cases]. *)

Include BoolOrderFacts.

(** Specification of minimum and maximum *)

Theorem min_l n m : n <= m -> min n m = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem min_r n m : m <= n -> min n m = m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem max_l n m : m <= n -> max n m = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem max_r n m : n <= m -> max n m = m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Specification of lt and le. *)

Lemma lt_succ_r n m : n < succ m <-> n<=m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** We can now derive all properties of basic functions and orders,
    and use these properties for proving the specs of more advanced
    functions. *)

Include NBasicProp <+ UsualMinMaxLogicalProperties <+ UsualMinMaxDecProperties.


(** Properties of [double] and [succ_double] *)

Lemma double_spec n : double n = 2 * n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma succ_double_spec n : succ_double n = 2 * n + 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma double_add n m : double (n+m) = double n + double m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma succ_double_add n m : succ_double (n+m) = double n + succ_double m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma double_mul n m : double (n*m) = double n * m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma succ_double_mul n m :
 succ_double n * m = double n * m + m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma div2_double n : div2 (double n) = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma div2_succ_double n : div2 (succ_double n) = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma double_inj n m : double n = double m -> n = m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma succ_double_inj n m : succ_double n = succ_double m -> n = m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma succ_double_lt n m : n<m -> succ_double n < double m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma double_lt_mono n m : n < m -> double n < double m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma double_le_mono n m : n <= m -> double n <= double m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma succ_double_lt_mono n m : n < m -> succ_double n < succ_double m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma succ_double_le_mono n m : n <= m -> succ_double n <= succ_double m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** 0 is the least natural number *)

Theorem compare_0_r n : (n ?= 0) <> Lt.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Specifications of power *)

Lemma pow_0_r n : n ^ 0 = 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pow_succ_r n p : 0<=p -> n^(succ p) = n * n^p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pow_neg_r n p : p<0 -> n^p = 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Specification of square *)

Lemma square_spec n : square n = n * n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Specification of Base-2 logarithm *)

Lemma size_log2 n : n<>0 -> size n = succ (log2 n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma size_gt n : n < 2^(size n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma size_le n : 2^(size n) <= succ_double n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma log2_spec n : 0 < n ->
 2^(log2 n) <= n < 2^(succ (log2 n)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma log2_nonpos n : n<=0 -> log2 n = 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Specification of parity functions *)

Lemma even_spec n : even n = true <-> Even n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma odd_spec n : odd n = true <-> Odd n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Specification of the euclidean division *)

Theorem pos_div_eucl_spec (a:positive)(b:N) :
  let (q,r) := pos_div_eucl a b in pos a = q * b + r.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem div_eucl_spec a b :
 let (q,r) := div_eucl a b in a = b * q + r.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem div_mod' a b : a = b * (a/b) + (a mod b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition div_mod a b : b<>0 -> a = b * (a/b) + (a mod b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem pos_div_eucl_remainder (a:positive) (b:N) :
  b<>0 -> snd (pos_div_eucl a b) < b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem mod_lt a b : b<>0 -> a mod b < b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem mod_bound_pos a b : 0<=a -> 0<b -> 0 <= a mod b < b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Specification of square root *)

Lemma sqrtrem_sqrt n : fst (sqrtrem n) = sqrt n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrtrem_spec n :
 let (s,r) := sqrtrem n in n = s*s + r /\ r <= 2*s.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrt_spec n : 0<=n ->
 let s := sqrt n in s*s <= n < (succ s)*(succ s).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrt_neg n : n<0 -> sqrt n = 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Specification of gcd *)

(** The first component of ggcd is gcd *)

Lemma ggcd_gcd a b : fst (ggcd a b) = gcd a b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** The other components of ggcd are indeed the correct factors. *)

Lemma ggcd_correct_divisors a b :
  let '(g,(aa,bb)) := ggcd a b in
  a=g*aa /\ b=g*bb.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** We can use this fact to prove a part of the gcd correctness *)

Lemma gcd_divide_l a b : (gcd a b | a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gcd_divide_r a b : (gcd a b | b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** We now prove directly that gcd is the greatest amongst common divisors *)

Lemma gcd_greatest a b c : (c|a) -> (c|b) -> (c|gcd a b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gcd_nonneg a b : 0 <= gcd a b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Specification of bitwise functions *)

(** Correctness proofs for [testbit]. *)

Lemma testbit_even_0 a : testbit (2*a) 0 = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma testbit_odd_0 a : testbit (2*a+1) 0 = true.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma testbit_succ_r_div2 a n : 0<=n ->
 testbit a (succ n) = testbit (div2 a) n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma testbit_odd_succ a n : 0<=n ->
 testbit (2*a+1) (succ n) = testbit a n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma testbit_even_succ a n : 0<=n ->
 testbit (2*a) (succ n) = testbit a n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma testbit_neg_r a n : n<0 -> testbit a n = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Correctness proofs for shifts *)

Lemma shiftr_succ_r a n :
 shiftr a (succ n) = div2 (shiftr a n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma shiftl_succ_r a n :
 shiftl a (succ n) = double (shiftl a n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma shiftr_spec a n m : 0<=m ->
 testbit (shiftr a n) m = testbit a (m+n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma shiftl_spec_high a n m : 0<=m -> n<=m ->
 testbit (shiftl a n) m = testbit a (m-n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma shiftl_spec_low a n m : m<n ->
 testbit (shiftl a n) m = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition div2_spec a : div2 a = shiftr a 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Semantics of bitwise operations *)

Lemma pos_lxor_spec p p' n :
 testbit (Pos.lxor p p') n = xorb (Pos.testbit p n) (Pos.testbit p' n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pos_lor_spec p p' n :
 Pos.testbit (Pos.lor p p') n = (Pos.testbit p n) || (Pos.testbit p' n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pos_land_spec p p' n :
 testbit (Pos.land p p') n = (Pos.testbit p n) && (Pos.testbit p' n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ldiff_spec a a' n :
 testbit (ldiff a a') n = (testbit a n) && negb (testbit a' n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Instantiation of generic properties of advanced functions
    (pow, sqrt, log2, div, gcd, ...) *)

(** In generic statements, the predicates [lt] and [le] have been
  favored, whereas [gt] and [ge] don't even exist in the abstract
  layers. The use of [gt] and [ge] is hence not recommended. We provide
  here the bare minimal results to related them with [lt] and [le]. *)

Lemma gt_lt_iff n m : n > m <-> m < n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gt_lt n m : n > m -> m < n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lt_gt n m : n < m -> m > n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ge_le_iff n m : n >= m <-> m <= n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ge_le n m : n >= m -> m <= n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma le_ge n m : n <= m -> m >= n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Auxiliary results about right shift on positive numbers,
    used in BinInt *)

Lemma pos_pred_shiftl_low : forall p n m, m<n ->
 testbit (Pos.pred_N (Pos.shiftl p n)) m = true.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pos_pred_shiftl_high : forall p n m, n<=m ->
 testbit (Pos.pred_N (Pos.shiftl p n)) m =
 testbit (shiftl (Pos.pred_N p) n) m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pred_div2_up p : Pos.pred_N (Pos.div2_up p) = div2 (Pos.pred_N p).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** ** Properties of [iter] *)

Lemma iter_swap_gen A B (f:A -> B) (g:A -> A) (h:B -> B) :
 (forall a, f (g a) = h (f a)) -> forall n a,
 f (iter n g a) = iter n h (f a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem iter_swap :
  forall n (A:Type) (f:A -> A) (x:A),
    iter n f (f x) = f (iter n f x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem iter_succ :
  forall n (A:Type) (f:A -> A) (x:A),
    iter (succ n) f x = f (iter n f x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem iter_succ_r :
  forall n (A:Type) (f:A -> A) (x:A),
    iter (succ n) f x = iter n f (f x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem iter_add :
  forall p q (A:Type) (f:A -> A) (x:A),
    iter (p+q) f x = iter p f (iter q f x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem iter_ind (A:Type) (f:A -> A) (a:A) (P:N -> A -> Prop) :
    P 0 a ->
    (forall n a', P n a' -> P (succ n) (f a')) ->
    forall n, P n (iter n f a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem iter_invariant :
  forall (n:N) (A:Type) (f:A -> A) (Inv:A -> Prop),
    (forall x:A, Inv x -> Inv (f x)) ->
    forall x:A, Inv x -> Inv (iter n f x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End N.

Bind Scope N_scope with N.t N.

(** Exportation of notations *)

Number Notation N N.of_num_uint N.to_num_uint : N_scope.

Infix "+" := N.add : N_scope.
Infix "-" := N.sub : N_scope.
Infix "*" := N.mul : N_scope.
Infix "^" := N.pow : N_scope.

Infix "?=" := N.compare (at level 70, no associativity) : N_scope.

Infix "<=" := N.le : N_scope.
Infix "<" := N.lt : N_scope.
Infix ">=" := N.ge : N_scope.
Infix ">" := N.gt : N_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : N_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : N_scope.
Notation "x < y < z" := (x < y /\ y < z) : N_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : N_scope.

Infix "=?" := N.eqb (at level 70, no associativity) : N_scope.
Infix "<=?" := N.leb (at level 70, no associativity) : N_scope.
Infix "<?" := N.ltb (at level 70, no associativity) : N_scope.

Infix "/" := N.div : N_scope.
Infix "mod" := N.modulo (at level 40, no associativity) : N_scope.

Notation "( p | q )" := (N.divide p q) (at level 0) : N_scope.

(** Compatibility notations *)

Notation N_rect := N_rect (only parsing).
Notation N_rec := N_rec (only parsing).
Notation N_ind := N_ind (only parsing).
Notation N0 := N0 (only parsing).
Notation Npos := N.pos (only parsing).

Notation Ndouble_plus_one := N.succ_double (only parsing).
Notation Nplus := N.add (only parsing).
Notation Nminus := N.sub (only parsing).
Notation Nmult := N.mul (only parsing).

Notation nat_of_N := N.to_nat (only parsing).
Notation N_of_nat := N.of_nat (only parsing).
Notation Nrect := N.peano_rect (only parsing).
Notation Nrect_base := N.peano_rect_base (only parsing).
Notation Nrect_step := N.peano_rect_succ (only parsing).
Notation Nind := N.peano_ind (only parsing).
Notation Nrec := N.peano_rec (only parsing).
Notation Nrec_base := N.peano_rec_base (only parsing).
Notation Nrec_succ := N.peano_rec_succ (only parsing).

Notation Npred_minus := N.pred_sub (only parsing).
Notation Ppred_N_spec := N.pos_pred_spec (only parsing).
Notation Ppred_Nsucc := N.pos_pred_succ (only parsing).
Notation Nplus_0_l := N.add_0_l (only parsing).
Notation Nplus_0_r := N.add_0_r (only parsing).
Notation Nplus_comm := N.add_comm (only parsing).
Notation Nplus_assoc := N.add_assoc (only parsing).
Notation Nplus_succ := N.add_succ_l (only parsing).
Notation Nsucc_0 := N.succ_0_discr (only parsing).
Notation Nminus_N0_Nle := N.sub_0_le (only parsing).
Notation Nminus_0_r := N.sub_0_r (only parsing).
Notation Nminus_succ_r:= N.sub_succ_r (only parsing).
Notation Nmult_0_l := N.mul_0_l (only parsing).
Notation Nmult_1_l := N.mul_1_l (only parsing).
Notation Nmult_1_r := N.mul_1_r (only parsing).
Notation Nmult_comm := N.mul_comm (only parsing).
Notation Nmult_assoc := N.mul_assoc (only parsing).
Notation Nmult_plus_distr_r := N.mul_add_distr_r (only parsing).
Notation Nle_0 := N.le_0_l (only parsing).
Notation Ncompare_Eq_eq := N.compare_eq (only parsing).
Notation Ncompare_eq_correct := N.compare_eq_iff (only parsing).
Notation Nle_lteq := N.lt_eq_cases (only parsing).
Notation Ncompare_0 := N.compare_0_r (only parsing).
Notation Ndouble_div2 := N.div2_double (only parsing).
Notation Ndouble_plus_one_div2 := N.div2_succ_double (only parsing).
Notation Ndouble_plus_one_inj := N.succ_double_inj (only parsing).
Notation Nlt_not_eq := N.lt_neq (only parsing).
Notation Ngt_Nlt := N.gt_lt (only parsing).

(** More complex compatibility facts, expressed as lemmas
    (to preserve scopes for instance) *)

Lemma Nplus_reg_l n m p : n + m = n + p -> m = p.
Proof (proj1 (N.add_cancel_l m p n)).
Lemma Nmult_Sn_m n m : N.succ n * m = m + n * m.
Proof (eq_trans (N.mul_succ_l n m) (N.add_comm _ _)).
Lemma Nmult_plus_distr_l n m p : p * (n + m) = p * n + p * m.
Proof (N.mul_add_distr_l p n m).
Lemma Nmult_reg_r n m p : p <> 0 -> n * p = m * p -> n = m.
Proof (fun H => proj1 (N.mul_cancel_r n m p H)).
Lemma Ncompare_antisym n m : CompOpp (n ?= m) = (m ?= n).
Proof (eq_sym (N.compare_antisym n m)).

Definition N_ind_double a P f0 f2 fS2 := N.binary_ind P f0 f2 fS2 a.
Definition N_rec_double a P f0 f2 fS2 := N.binary_rec P f0 f2 fS2 a.

(** Not kept : Ncompare_n_Sm Nplus_lt_cancel_l *)
