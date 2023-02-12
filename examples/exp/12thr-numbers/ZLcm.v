(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import ZAxioms ZMulOrder ZSgnAbs ZGcd ZDivTrunc ZDivFloor.
Add Rec LoadPath "/home/arjun/Desktop/smtcoq/abduction-arjunvish-smtcoq/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
(** * Least Common Multiple *)

(** Unlike other functions around, we will define lcm below instead of
  axiomatizing it. Indeed, there is no "prior art" about lcm in the
  standard library to be compliant with, and the generic definition
  of lcm via gcd is quite reasonable.

  By the way, we also state here some combined properties of div/mod
  and quot/rem and gcd.
*)

Module Type ZLcmProp
 (Import A : ZAxiomsSig')
 (Import B : ZMulOrderProp A)
 (Import C : ZSgnAbsProp A B)
 (Import D : ZDivProp A B C)
 (Import E : ZQuotProp A B C)
 (Import F : ZGcdProp A B C).

(** The two notions of division are equal on non-negative numbers *)

Lemma quot_div_nonneg : forall a b, 0<=a -> 0<b -> a÷b == a/b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rem_mod_nonneg : forall a b, 0<=a -> 0<b -> a rem b == a mod b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** We can use the sign rule to have an relation between divisions. *)

Lemma quot_div : forall a b, b~=0 ->
 a÷b == (sgn a)*(sgn b)*(abs a / abs b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rem_mod : forall a b, b~=0 ->
 a rem b == (sgn a) * ((abs a) mod (abs b)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Modulo and remainder are null at the same place,
    and this correspond to the divisibility relation. *)

Lemma mod_divide : forall a b, b~=0 -> (a mod b == 0 <-> (b|a)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rem_divide : forall a b, b~=0 -> (a rem b == 0 <-> (b|a)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rem_mod_eq_0 : forall a b, b~=0 -> (a rem b == 0 <-> a mod b == 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** When division is exact, div and quot agree *)

Lemma quot_div_exact : forall a b, b~=0 -> (b|a) -> a÷b == a/b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma divide_div_mul_exact : forall a b c, b~=0 -> (b|a) ->
 (c*a)/b == c*(a/b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma divide_quot_mul_exact : forall a b c, b~=0 -> (b|a) ->
 (c*a)÷b == c*(a÷b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Gcd of divided elements, for exact divisions *)

Lemma gcd_div_factor : forall a b c, 0<c -> (c|a) -> (c|b) ->
 gcd (a/c) (b/c) == (gcd a b)/c.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gcd_quot_factor : forall a b c, 0<c -> (c|a) -> (c|b) ->
 gcd (a÷c) (b÷c) == (gcd a b)÷c.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gcd_div_gcd : forall a b g, g~=0 -> g == gcd a b ->
 gcd (a/g) (b/g) == 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gcd_quot_gcd : forall a b g, g~=0 -> g == gcd a b ->
 gcd (a÷g) (b÷g) == 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** The following equality is crucial for Euclid algorithm *)

Lemma gcd_mod : forall a b, b~=0 -> gcd (a mod b) b == gcd b a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gcd_rem : forall a b, b~=0 -> gcd (a rem b) b == gcd b a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** We now define lcm thanks to gcd:

    lcm a b = a * (b / gcd a b)
            = (a / gcd a b) * b
            = (a*b) / gcd a b

   We had an abs in order to have an always-nonnegative lcm,
   in the spirit of gcd. Nota: [lcm 0 0] should be 0, which
   isn't guarantee with the third equation above.
*)

Definition lcm a b := abs (a*(b/gcd a b)).

Instance lcm_wd : Proper (eq==>eq==>eq) lcm.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lcm_equiv1 : forall a b, gcd a b ~= 0 ->
  a * (b / gcd a b) == (a*b)/gcd a b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lcm_equiv2 : forall a b, gcd a b ~= 0 ->
  (a / gcd a b) * b == (a*b)/gcd a b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gcd_div_swap : forall a b,
 (a / gcd a b) * b == a * (b / gcd a b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma divide_lcm_l : forall a b, (a | lcm a b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma divide_lcm_r : forall a b, (b | lcm a b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma divide_div : forall a b c, a~=0 -> (a|b) -> (b|c) -> (b/a|c/a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lcm_least : forall a b c,
 (a | c) -> (b | c) -> (lcm a b | c).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lcm_nonneg : forall a b, 0 <= lcm a b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lcm_comm : forall a b, lcm a b == lcm b a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lcm_divide_iff : forall n m p,
  (lcm n m | p) <-> (n | p) /\ (m | p).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lcm_unique : forall n m p,
 0<=p -> (n|p) -> (m|p) ->
 (forall q, (n|q) -> (m|q) -> (p|q)) ->
 lcm n m == p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lcm_unique_alt : forall n m p, 0<=p ->
 (forall q, (p|q) <-> (n|q) /\ (m|q)) ->
 lcm n m == p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lcm_assoc : forall n m p, lcm n (lcm m p) == lcm (lcm n m) p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lcm_0_l : forall n, lcm 0 n == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lcm_0_r : forall n, lcm n 0 == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lcm_1_l_nonneg : forall n, 0<=n -> lcm 1 n == n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lcm_1_r_nonneg : forall n, 0<=n -> lcm n 1 == n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lcm_diag_nonneg : forall n, 0<=n -> lcm n n == n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lcm_eq_0 : forall n m, lcm n m == 0 <-> n == 0 \/ m == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma divide_lcm_eq_r : forall n m, 0<=m -> (n|m) -> lcm n m == m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma divide_lcm_iff : forall n m, 0<=m -> ((n|m) <-> lcm n m == m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lcm_opp_l : forall n m, lcm (-n) m == lcm n m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lcm_opp_r : forall n m, lcm n (-m) == lcm n m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lcm_abs_l : forall n m, lcm (abs n) m == lcm n m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lcm_abs_r : forall n m, lcm n (abs m) == lcm n m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lcm_1_l : forall n, lcm 1 n == abs n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lcm_1_r : forall n, lcm n 1 == abs n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lcm_diag : forall n, lcm n n == abs n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lcm_mul_mono_l :
  forall n m p, lcm (p * n) (p * m) == abs p * lcm n m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lcm_mul_mono_l_nonneg :
 forall n m p, 0<=p -> lcm (p*n) (p*m) == p * lcm n m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lcm_mul_mono_r :
 forall n m p, lcm (n * p) (m * p) == lcm n m * abs p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lcm_mul_mono_r_nonneg :
 forall n m p, 0<=p -> lcm (n*p) (m*p) == lcm n m * p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gcd_1_lcm_mul : forall n m, n~=0 -> m~=0 ->
 (gcd n m == 1 <-> lcm n m == abs (n*m)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End ZLcmProp.
