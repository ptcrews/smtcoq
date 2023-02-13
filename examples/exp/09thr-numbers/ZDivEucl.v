(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import ZAxioms ZMulOrder ZSgnAbs NZDiv.
Add Rec LoadPath "/home/arjun/Desktop/smtcoq/abduction-arjunvish-smtcoq/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
(** * Euclidean Division for integers, Euclid convention

    We use here the "usual" formulation of the Euclid Theorem
    [forall a b, b<>0 -> exists r q, a = b*q+r /\ 0 <= r < |b| ]

    The outcome of the modulo function is hence always positive.
    This corresponds to convention "E" in the following paper:

    R. Boute, "The Euclidean definition of the functions div and mod",
    ACM Transactions on Programming Languages and Systems,
    Vol. 14, No.2, pp. 127-144, April 1992.

    See files [ZDivTrunc] and [ZDivFloor] for others conventions.

    We simply extend NZDiv with a bound for modulo that holds
    regardless of the sign of a and b. This new specification
    subsume mod_bound_pos, which nonetheless stays there for
    subtyping. Note also that ZAxiomSig now already contain
    a div and a modulo (that follow the Floor convention).
    We just ignore them here.
*)

Module Type EuclidSpec (Import A : ZAxiomsSig')(Import B : DivMod A).
 Axiom mod_always_pos : forall a b, b ~= 0 -> 0 <= B.modulo a b < abs b.
End EuclidSpec.

Module Type ZEuclid (Z:ZAxiomsSig) := NZDiv.NZDiv Z <+ EuclidSpec Z.

Module ZEuclidProp
 (Import A : ZAxiomsSig')
 (Import B : ZMulOrderProp A)
 (Import C : ZSgnAbsProp A B)
 (Import D : ZEuclid A).

 (** We put notations in a scope, to avoid warnings about
     redefinitions of notations *)
 Declare Scope euclid.
 Infix "/" := D.div : euclid.
 Infix "mod" := D.modulo : euclid.
 Local Open Scope euclid.

 Module Import Private_NZDiv := Nop <+ NZDivProp A D B.

(** Another formulation of the main equation *)

Lemma mod_eq :
 forall a b, b~=0 -> a mod b == a - b*(a/b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Ltac pos_or_neg a :=
 let LT := fresh "LT" in
 let LE := fresh "LE" in
 destruct (le_gt_cases 0 a) as [LE|LT]; [|rewrite <- opp_pos_neg in LT].

(** Uniqueness theorems *)

Theorem div_mod_unique : forall b q1 q2 r1 r2 : t,
  0<=r1<abs b -> 0<=r2<abs b ->
  b*q1+r1 == b*q2+r2 -> q1 == q2 /\ r1 == r2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem div_unique:
 forall a b q r, 0<=r<abs b -> a == b*q + r -> q == a/b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem mod_unique:
 forall a b q r, 0<=r<abs b -> a == b*q + r -> r == a mod b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Sign rules *)

Lemma div_opp_r : forall a b, b~=0 -> a/(-b) == -(a/b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mod_opp_r : forall a b, b~=0 -> a mod (-b) == a mod b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma div_opp_l_z : forall a b, b~=0 -> a mod b == 0 ->
 (-a)/b == -(a/b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma div_opp_l_nz : forall a b, b~=0 -> a mod b ~= 0 ->
 (-a)/b == -(a/b)-sgn b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mod_opp_l_z : forall a b, b~=0 -> a mod b == 0 ->
 (-a) mod b == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mod_opp_l_nz : forall a b, b~=0 -> a mod b ~= 0 ->
 (-a) mod b == abs b - (a mod b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma div_opp_opp_z : forall a b, b~=0 -> a mod b == 0 ->
 (-a)/(-b) == a/b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma div_opp_opp_nz : forall a b, b~=0 -> a mod b ~= 0 ->
 (-a)/(-b) == a/b + sgn(b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mod_opp_opp_z : forall a b, b~=0 -> a mod b == 0 ->
 (-a) mod (-b) == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mod_opp_opp_nz : forall a b, b~=0 -> a mod b ~= 0 ->
 (-a) mod (-b) == abs b - a mod b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** A division by itself returns 1 *)

Lemma div_same : forall a, a~=0 -> a/a == 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mod_same : forall a, a~=0 -> a mod a == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** A division of a small number by a bigger one yields zero. *)

Theorem div_small: forall a b, 0<=a<b -> a/b == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Same situation, in term of modulo: *)

Theorem mod_small: forall a b, 0<=a<b -> a mod b == a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** * Basic values of divisions and modulo. *)

Lemma div_0_l: forall a, a~=0 -> 0/a == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mod_0_l: forall a, a~=0 -> 0 mod a == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma div_1_r: forall a, a/1 == a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mod_1_r: forall a, a mod 1 == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma div_1_l: forall a, 1<a -> 1/a == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mod_1_l: forall a, 1<a -> 1 mod a == 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma div_mul : forall a b, b~=0 -> (a*b)/b == a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mod_mul : forall a b, b~=0 -> (a*b) mod b == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem div_unique_exact a b q: b~=0 -> a == b*q -> q == a/b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** * Order results about mod and div *)

(** A modulo cannot grow beyond its starting point. *)

Theorem mod_le: forall a b, 0<=a -> b~=0 -> a mod b <= a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem div_pos : forall a b, 0<=a -> 0<b -> 0<= a/b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma div_str_pos : forall a b, 0<b<=a -> 0 < a/b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma div_small_iff : forall a b, b~=0 -> (a/b==0 <-> 0<=a<abs b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mod_small_iff : forall a b, b~=0 -> (a mod b == a <-> 0<=a<abs b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** As soon as the divisor is strictly greater than 1,
    the division is strictly decreasing. *)

Lemma div_lt : forall a b, 0<a -> 1<b -> a/b < a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** [le] is compatible with a positive division. *)

Lemma div_le_mono : forall a b c, 0<c -> a<=b -> a/c <= b/c.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** In this convention, [div] performs Rounding-Toward-Bottom
    when divisor is positive, and Rounding-Toward-Top otherwise.

    Since we cannot speak of rational values here, we express this
    fact by multiplying back by [b], and this leads to a nice
    unique statement.
*)

Lemma mul_div_le : forall a b, b~=0 -> b*(a/b) <= a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Giving a reversed bound is slightly more complex *)

Lemma mul_succ_div_gt: forall a b, 0<b -> a < b*(S (a/b)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mul_pred_div_gt: forall a b, b<0 -> a < b*(P (a/b)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** NB: The three previous properties could be used as
    specifications for [div]. *)

(** Inequality [mul_div_le] is exact iff the modulo is zero. *)

Lemma div_exact : forall a b, b~=0 -> (a == b*(a/b) <-> a mod b == 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Some additional inequalities about div. *)

Theorem div_lt_upper_bound:
  forall a b q, 0<b -> a < b*q -> a/b < q.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem div_le_upper_bound:
  forall a b q, 0<b -> a <= b*q -> a/b <= q.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem div_le_lower_bound:
  forall a b q, 0<b -> b*q <= a -> q <= a/b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** A division respects opposite monotonicity for the divisor *)

Lemma div_le_compat_l: forall p q r, 0<=p -> 0<q<=r -> p/r <= p/q.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** * Relations between usual operations and mod and div *)

Lemma mod_add : forall a b c, c~=0 ->
 (a + b * c) mod c == a mod c.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma div_add : forall a b c, c~=0 ->
 (a + b * c) / c == a / c + b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma div_add_l: forall a b c, b~=0 ->
 (a * b + c) / b == a + c / b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Cancellations. *)

(** With the current convention, the following isn't always true
    when [c<0]: [-3*-1 / -2*-1 = 3/2 = 1] while [-3/-2 = 2] *)

Lemma div_mul_cancel_r : forall a b c, b~=0 -> 0<c ->
 (a*c)/(b*c) == a/b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma div_mul_cancel_l : forall a b c, b~=0 -> 0<c ->
 (c*a)/(c*b) == a/b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mul_mod_distr_l: forall a b c, b~=0 -> 0<c ->
  (c*a) mod (c*b) == c * (a mod b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mul_mod_distr_r: forall a b c, b~=0 -> 0<c ->
  (a*c) mod (b*c) == (a mod b) * c.
Proof. Show. Fail (cvc5_abduct 3). Admitted.


(** Operations modulo. *)

Theorem mod_mod: forall a n, n~=0 ->
 (a mod n) mod n == a mod n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mul_mod_idemp_l : forall a b n, n~=0 ->
 ((a mod n)*b) mod n == (a*b) mod n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mul_mod_idemp_r : forall a b n, n~=0 ->
 (a*(b mod n)) mod n == (a*b) mod n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem mul_mod: forall a b n, n~=0 ->
 (a * b) mod n == ((a mod n) * (b mod n)) mod n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma add_mod_idemp_l : forall a b n, n~=0 ->
 ((a mod n)+b) mod n == (a+b) mod n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma add_mod_idemp_r : forall a b n, n~=0 ->
 (a+(b mod n)) mod n == (a+b) mod n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem add_mod: forall a b n, n~=0 ->
 (a+b) mod n == (a mod n + b mod n) mod n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** With the current convention, the following result isn't always
    true with a negative intermediate divisor. For instance
    [ 3/(-2)/(-2) = 1 <> 0 = 3 / (-2*-2) ] and
    [ 3/(-2)/2 = -1 <> 0 = 3 / (-2*2) ]. *)

Lemma div_div : forall a b c, 0<b -> c~=0 ->
 (a/b)/c == a/(b*c).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Similarly, the following result doesn't always hold when [b<0].
    For instance [3 mod (-2*-2)) = 3] while
    [3 mod (-2) + (-2)*((3/-2) mod -2) = -1]. *)

Lemma mod_mul_r : forall a b c, 0<b -> c~=0 ->
 a mod (b*c) == a mod b + b*((a/b) mod c).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mod_div: forall a b, b~=0 ->
 a mod b / b == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** A last inequality: *)

Theorem div_mul_le:
 forall a b c, 0<=a -> 0<b -> 0<=c -> c*(a/b) <= (c*a)/b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** mod is related to divisibility *)

Lemma mod_divides : forall a b, b~=0 ->
 (a mod b == 0 <-> (b|a)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End ZEuclidProp.
