(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import ZArith_base.
Require Import ZArithRing.
Require Import Zcomplements.
Require Import Zdiv.
Require Import Wf_nat.
Add Rec LoadPath "/home/arjun/Desktop/smtcoq/abduction-arjunvish-smtcoq/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
(** For compatibility reasons, this Open Scope isn't local as it should *)

Open Scope Z_scope.

(** This file contains some notions of number theory upon Z numbers:
     - a divisibility predicate [Z.divide]
     - a gcd predicate [gcd]
     - Euclid algorithm [euclid]
     - a relatively prime predicate [rel_prime]
     - a prime predicate [prime]
     - properties of the efficient [Z.gcd] function
*)

(** The former specialized inductive predicate [Z.divide] is now
    a generic existential predicate. *)

(** Its former constructor is now a pseudo-constructor. *)

Definition Zdivide_intro a b q (H:b=q*a) : Z.divide a b := ex_intro _ q H.

(** Results concerning divisibility*)

Notation Zone_divide := Z.divide_1_l (only parsing).
Notation Zdivide_0 := Z.divide_0_r (only parsing).
Notation Zmult_divide_compat_l := Z.mul_divide_mono_l (only parsing).
Notation Zmult_divide_compat_r := Z.mul_divide_mono_r (only parsing).
Notation Zdivide_plus_r := Z.divide_add_r (only parsing).
Notation Zdivide_minus_l := Z.divide_sub_r (only parsing).
Notation Zdivide_mult_l := Z.divide_mul_l (only parsing).
Notation Zdivide_mult_r := Z.divide_mul_r (only parsing).
Notation Zdivide_factor_r := Z.divide_factor_l (only parsing).
Notation Zdivide_factor_l := Z.divide_factor_r (only parsing).

Lemma Zdivide_opp_r a b : (a | b) -> (a | - b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zdivide_opp_r_rev a b : (a | - b) -> (a | b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zdivide_opp_l a b : (a | b) -> (- a | b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zdivide_opp_l_rev a b : (- a | b) -> (a | b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Zdivide_Zabs_l a b : (Z.abs a | b) -> (a | b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Zdivide_Zabs_inv_l a b : (a | b) -> (Z.abs a | b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

#[global]
Hint Resolve Z.divide_refl Z.divide_1_l Z.divide_0_r: zarith.
#[global]
Hint Resolve Z.mul_divide_mono_l Z.mul_divide_mono_r: zarith.
#[global]
Hint Resolve Z.divide_add_r Zdivide_opp_r Zdivide_opp_r_rev Zdivide_opp_l
  Zdivide_opp_l_rev Z.divide_sub_r Z.divide_mul_l Z.divide_mul_r
  Z.divide_factor_l Z.divide_factor_r: zarith.

(** Auxiliary result. *)

Lemma Zmult_one x y : x >= 0 -> x * y = 1 -> x = 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Only [1] and [-1] divide [1]. *)

Notation Zdivide_1 := Z.divide_1_r (only parsing).

(** If [a] divides [b] and [b<>0] then [|a| <= |b|]. *)

Lemma Zdivide_bounds a b : (a | b) -> b <> 0 -> Z.abs a <= Z.abs b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** [Z.divide] can be expressed using [Z.modulo]. *)

Lemma Zmod_divide : forall a b, b<>0 -> a mod b = 0 -> (b | a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zdivide_mod : forall a b, (b | a) -> a mod b = 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** [Z.divide] is hence decidable *)

Lemma Zdivide_dec a b : {(a | b)} + {~ (a | b)}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Z_lt_neq {x y: Z} : x < y -> y <> x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Zdivide_Zdiv_eq a b : 0 < a -> (a | b) ->  b = a * (b / a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Zdivide_Zdiv_eq_2 a b c :
 0 < a -> (a | b) -> (c * b) / a = c * (b / a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Zdivide_le: forall a b : Z,
 0 <= a -> 0 < b -> (a | b) ->  a <= b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Zdivide_Zdiv_lt_pos a b :
 1 < a -> 0 < b -> (a | b) ->  0 < b / a < b .
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zmod_div_mod n m a:
 0 < n -> 0 < m -> (n | m) -> a mod n = (a mod m) mod n.
Proof with auto using Z_lt_neq.
  intros H1 H2 (p,Hp).
  rewrite (Z.div_mod a m) at 1...
  rewrite Hp at 1.
  rewrite Z.mul_shuffle0, Z.add_comm, Z.mod_add...
Qed.

Lemma Zmod_divide_minus a b c:
 0 < b -> a mod b = c -> (b | a - c).
Proof with auto using Z_lt_neq.
  intros H H1. apply Z.mod_divide...
  rewrite Zminus_mod.
  rewrite H1. rewrite <- (Z.mod_small c b) at 1.
  rewrite Z.sub_diag, Z.mod_0_l...
  subst. now apply Z.mod_pos_bound.
Qed.

Lemma Zdivide_mod_minus a b c:
 0 <= c < b -> (b | a - c) -> a mod b = c.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** * Greatest common divisor (gcd). *)

(** There is no unicity of the gcd; hence we define the predicate
    [Zis_gcd a b g] expressing that [g] is a gcd of [a] and [b].
    (We show later that the [gcd] is actually unique if we discard its sign.) *)

Inductive Zis_gcd (a b g:Z) : Prop :=
 Zis_gcd_intro :
  (g | a) ->
  (g | b) ->
  (forall x, (x | a) -> (x | b) -> (x | g)) ->
  Zis_gcd a b g.

(** Trivial properties of [gcd] *)

Lemma Zis_gcd_sym : forall a b d, Zis_gcd a b d -> Zis_gcd b a d.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zis_gcd_0 : forall a, Zis_gcd a 0 a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zis_gcd_1 : forall a, Zis_gcd a 1 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zis_gcd_refl : forall a, Zis_gcd a a a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zis_gcd_minus : forall a b d, Zis_gcd a (- b) d -> Zis_gcd b a d.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zis_gcd_opp : forall a b d, Zis_gcd a b d -> Zis_gcd b a (- d).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zis_gcd_0_abs a : Zis_gcd 0 a (Z.abs a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

#[global]
Hint Resolve Zis_gcd_sym Zis_gcd_0 Zis_gcd_minus Zis_gcd_opp: zarith.

Theorem Zis_gcd_unique: forall a b c d : Z,
 Zis_gcd a b c -> Zis_gcd a b d ->  c = d \/ c = (- d).
Proof. Show. Fail (cvc5_abduct 3). Admitted.


(** * Extended Euclid algorithm. *)

(** Euclid's algorithm to compute the [gcd] mainly relies on
    the following property. *)

Lemma Zis_gcd_for_euclid :
  forall a b d q:Z, Zis_gcd b (a - q * b) d -> Zis_gcd a b d.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zis_gcd_for_euclid2 :
  forall b d q r:Z, Zis_gcd r b d -> Zis_gcd b (b * q + r) d.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** We implement the extended version of Euclid's algorithm,
    i.e. the one computing Bezout's coefficients as it computes
    the [gcd]. We follow the algorithm given in Knuth's
    "Art of Computer Programming", vol 2, page 325. *)

Section extended_euclid_algorithm.

  Variables a b : Z.

  (** The specification of Euclid's algorithm is the existence of
      [u], [v] and [d] such that [ua+vb=d] and [(gcd a b d)]. *)

  Inductive Euclid : Set :=
    Euclid_intro :
    forall u v d:Z, u * a + v * b = d -> Zis_gcd a b d -> Euclid.

  (** The recursive part of Euclid's algorithm uses well-founded
      recursion of non-negative integers. It maintains 6 integers
      [u1,u2,u3,v1,v2,v3] such that the following invariant holds:
      [u1*a+u2*b=u3] and [v1*a+v2*b=v3] and [gcd(u3,v3)=gcd(a,b)].
      *)

  Lemma euclid_rec :
    forall v3:Z,
      0 <= v3 ->
      forall u1 u2 u3 v1 v2:Z,
	u1 * a + u2 * b = u3 ->
	v1 * a + v2 * b = v3 ->
	(forall d:Z, Zis_gcd u3 v3 d -> Zis_gcd a b d) -> Euclid.
  Proof. Show. Fail (cvc5_abduct 3). Admitted.

  (** We get Euclid's algorithm by applying [euclid_rec] on
      [1,0,a,0,1,b] when [b>=0] and [1,0,a,0,-1,-b] when [b<0]. *)

  Lemma euclid : Euclid.
  Proof. Show. Fail (cvc5_abduct 3). Admitted.

End extended_euclid_algorithm.

Theorem Zis_gcd_uniqueness_apart_sign :
  forall a b d d':Z, Zis_gcd a b d -> Zis_gcd a b d' -> d = d' \/ d = - d'.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** * Bezout's coefficients *)

Inductive Bezout (a b d:Z) : Prop :=
  Bezout_intro : forall u v:Z, u * a + v * b = d -> Bezout a b d.

(** Existence of Bezout's coefficients for the [gcd] of [a] and [b] *)

Lemma Zis_gcd_bezout : forall a b d:Z, Zis_gcd a b d -> Bezout a b d.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** gcd of [ca] and [cb] is [c gcd(a,b)]. *)

Lemma Zis_gcd_mult :
  forall a b c d:Z, Zis_gcd a b d -> Zis_gcd (c * a) (c * b) (c * d).
Proof. Show. Fail (cvc5_abduct 3). Admitted.


(** * Relative primality *)

Definition rel_prime (a b:Z) : Prop := Zis_gcd a b 1.

(** Bezout's theorem: [a] and [b] are relatively prime if and
    only if there exist [u] and [v] such that [ua+vb = 1]. *)

Lemma rel_prime_bezout : forall a b:Z, rel_prime a b -> Bezout a b 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma bezout_rel_prime : forall a b:Z, Bezout a b 1 -> rel_prime a b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Gauss's theorem: if [a] divides [bc] and if [a] and [b] are
    relatively prime, then [a] divides [c]. *)

Theorem Gauss : forall a b c:Z, (a | b * c) -> rel_prime a b -> (a | c).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** If [a] is relatively prime to [b] and [c], then it is to [bc] *)

Lemma rel_prime_mult :
  forall a b c:Z, rel_prime a b -> rel_prime a c -> rel_prime a (b * c).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rel_prime_cross_prod :
  forall a b c d:Z,
    rel_prime a b ->
    rel_prime c d -> b > 0 -> d > 0 -> a * d = b * c -> a = c /\ b = d.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** After factorization by a gcd, the original numbers are relatively prime. *)

Lemma Zis_gcd_rel_prime :
  forall a b g:Z,
    b > 0 -> g >= 0 -> Zis_gcd a b g -> rel_prime (a / g) (b / g).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem rel_prime_sym: forall a b, rel_prime a b -> rel_prime b a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem rel_prime_div: forall p q r,
 rel_prime p q -> (r | p) -> rel_prime r q.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem rel_prime_1: forall n, rel_prime 1 n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem not_rel_prime_0: forall n, 1 < n -> ~ rel_prime 0 n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem rel_prime_mod: forall p q, 0 < q ->
 rel_prime p q -> rel_prime (p mod q) q.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem rel_prime_mod_rev: forall p q, 0 < q ->
 rel_prime (p mod q) q -> rel_prime p q.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Zrel_prime_neq_mod_0: forall a b, 1 < b -> rel_prime a b -> a mod b <> 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** * Primality *)

Inductive prime (p:Z) : Prop :=
  prime_intro :
    1 < p -> (forall n:Z, 1 <= n < p -> rel_prime n p) -> prime p.

(** The sole divisors of a prime number [p] are [-1], [1], [p] and [-p]. *)

Lemma prime_divisors :
  forall p:Z,
    prime p -> forall a:Z, (a | p) -> a = -1 \/ a = 1 \/ a = p \/ a = - p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** A prime number is relatively prime with any number it does not divide *)

Lemma prime_rel_prime :
  forall p:Z, prime p -> forall a:Z, ~ (p | a) -> rel_prime p a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

#[global]
Hint Resolve prime_rel_prime: zarith.

(** As a consequence, a prime number is relatively prime with smaller numbers *)

Theorem rel_prime_le_prime:
 forall a p, prime p -> 1 <=  a < p -> rel_prime a p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** If a prime [p] divides [ab] then it divides either [a] or [b] *)

Lemma prime_mult :
  forall p:Z, prime p -> forall a b:Z, (p | a * b) -> (p | a) \/ (p | b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma not_prime_0: ~ prime 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma not_prime_1: ~ prime 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma prime_2: prime 2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem prime_3: prime 3.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem prime_ge_2 p : prime p ->  2 <= p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition prime' p := 1<p /\ (forall n, 1<n<p -> ~ (n|p)).

Lemma Z_0_1_more x : 0<=x -> x=0 \/ x=1 \/ 1<x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem prime_alt p : prime' p <-> prime p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem square_not_prime: forall a, ~ prime (a * a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem prime_div_prime: forall p q,
 prime p -> prime q -> (p | q) -> p = q.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** we now prove that [Z.gcd] is indeed a gcd in
   the sense of [Zis_gcd]. *)

Notation Zgcd_is_pos := Z.gcd_nonneg (only parsing).

Lemma Zgcd_is_gcd : forall a b, Zis_gcd a b (Z.gcd a b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Zgcd_spec : forall x y : Z, {z : Z | Zis_gcd x y z /\ 0 <= z}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Zdivide_Zgcd: forall p q r : Z,
 (p | q) -> (p | r) -> (p | Z.gcd q r).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Zis_gcd_gcd: forall a b c : Z,
 0 <= c ->  Zis_gcd a b c -> Z.gcd a b = c.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Notation Zgcd_inv_0_l := Z.gcd_eq_0_l (only parsing).
Notation Zgcd_inv_0_r := Z.gcd_eq_0_r (only parsing).

Theorem Zgcd_div_swap0 : forall a b : Z,
 0 < Z.gcd a b ->
 0 < b ->
 (a / Z.gcd a b) * b = a * (b/Z.gcd a b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Zgcd_div_swap : forall a b c : Z,
 0 < Z.gcd a b ->
 0 < b ->
 (c * a) / Z.gcd a b * b = c * a * (b/Z.gcd a b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zgcd_ass a b c : Z.gcd (Z.gcd a b) c = Z.gcd a (Z.gcd b c).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Notation Zgcd_Zabs := Z.gcd_abs_l (only parsing).
Notation Zgcd_0 := Z.gcd_0_r (only parsing).
Notation Zgcd_1 := Z.gcd_1_r (only parsing).

#[global]
Hint Resolve Z.gcd_0_r Z.gcd_1_r : zarith.

Theorem Zgcd_1_rel_prime : forall a b,
 Z.gcd a b = 1 <-> rel_prime a b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition rel_prime_dec: forall a b,
 { rel_prime a b }+{ ~ rel_prime a b }.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition prime_dec_aux:
 forall p m,
  { forall n, 1 < n < m -> rel_prime n p } +
  { exists n, 1 < n < m  /\ ~ rel_prime n p }.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition prime_dec: forall p, { prime p }+{ ~ prime p }.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem not_prime_divide:
 forall p, 1 < p -> ~ prime p -> exists n, 1 < n < p  /\ (n | p).
Proof. Show. Fail (cvc5_abduct 3). Admitted.
