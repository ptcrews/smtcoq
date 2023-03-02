(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import ZArith_base ZArithRing Lia Zcomplements Zdiv Znumtheory.
Require Export Zpower.
Local Open Scope Z_scope.
Require Import SMTCoq.SMTCoq.
(** Properties of the power function over [Z] *)

(** Nota: the usual properties of [Z.pow] are now already provided
    by [BinInt.Z]. Only remain here some compatibility elements,
    as well as more specific results about power and modulo and/or
    primality. *)

Lemma Zpower_pos_1_r x : Z.pow_pos x 1 = x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zpower_pos_1_l p : Z.pow_pos 1 p = 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zpower_pos_0_l p : Z.pow_pos 0 p = 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zpower_pos_pos x p : 0 < x -> 0 < Z.pow_pos x p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Notation Zpower_1_r := Z.pow_1_r (only parsing).
Notation Zpower_1_l := Z.pow_1_l (only parsing).
Notation Zpower_0_l := Z.pow_0_l' (only parsing).
Notation Zpower_0_r := Z.pow_0_r (only parsing).
Notation Zpower_2 := Z.pow_2_r (only parsing).
Notation Zpower_gt_0 := Z.pow_pos_nonneg (only parsing).
Notation Zpower_ge_0 := Z.pow_nonneg (only parsing).
Notation Zpower_Zabs := Z.abs_pow (only parsing).
Notation Zpower_Zsucc := Z.pow_succ_r (only parsing).
Notation Zpower_mult := Z.pow_mul_r (only parsing).
Notation Zpower_le_monotone2 := Z.pow_le_mono_r (only parsing).

Theorem Zpower_le_monotone a b c :
 0 < a -> 0 <= b <= c -> a^b <= a^c.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Zpower_lt_monotone a b c :
 1 < a -> 0 <= b < c -> a^b < a^c.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Zpower_gt_1 x y : 1 < x -> 0 < y -> 1 < x^y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Zmult_power p q r : 0 <= r -> (p*q)^r = p^r * q^r.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

#[global]
Hint Resolve Z.pow_nonneg Z.pow_pos_nonneg : zarith.

Theorem Zpower_le_monotone3 a b c :
 0 <= c -> 0 <= a <= b -> a^c <= b^c.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zpower_le_monotone_inv a b c :
  1 < a -> 0 < b -> a^b <= a^c -> b <= c.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Notation Zpower_nat_Zpower := Zpower_nat_Zpower (only parsing).

Theorem Zpower2_lt_lin n : 0 <= n -> n < 2^n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Zpower2_le_lin n : 0 <= n -> n <= 2^n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zpower2_Psize n p :
  Zpos p < 2^(Z.of_nat n) <-> (Pos.size_nat p <= n)%nat.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** * Z.pow and modulo *)

Theorem Zpower_mod p q n :
  0 < n -> (p^q) mod n = ((p mod n)^q) mod n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** A direct way to compute Z.pow modulo **)

Fixpoint Zpow_mod_pos (a: Z)(m: positive)(n : Z) : Z :=
  match m with
   | xH => a mod n
   | xO m' =>
      let z := Zpow_mod_pos a m' n in
      match z with
       | 0 => 0
       | _ => (z * z) mod n
      end
   | xI m' =>
      let z := Zpow_mod_pos a m' n in
      match z with
       | 0 => 0
       | _ => (z * z * a) mod n
      end
  end.

Definition Zpow_mod a m n :=
  match m with
   | 0 => 1 mod n
   | Zpos p => Zpow_mod_pos a p n
   | Zneg p => 0
  end.

Theorem Zpow_mod_pos_correct a m n :
 n <> 0 -> Zpow_mod_pos a m n = (Z.pow_pos a m) mod n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Zpow_mod_correct a m n :
 n <> 0 -> Zpow_mod a m n = (a ^ m) mod n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Complements about power and number theory. *)

Lemma Zpower_divide p q : 0 < q -> (p | p ^ q).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem rel_prime_Zpower_r i p q :
 0 <= i -> rel_prime p q -> rel_prime p (q^i).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem rel_prime_Zpower i j p q :
 0 <= i ->  0 <= j -> rel_prime p q -> rel_prime (p^i) (q^j).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem prime_power_prime p q n :
 0 <= n -> prime p -> prime q -> (p | q^n) -> p = q.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Zdivide_power_2 x p n :
 0 <= n -> 0 <= x -> prime p -> (x | p^n) -> exists m, x = p^m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** * Z.square: a direct definition of [z^2] *)

Notation Psquare_correct := Pos.square_spec (only parsing).
Notation Zsquare_correct := Z.square_spec (only parsing).
