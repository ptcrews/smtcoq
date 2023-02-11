(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************)
(*           The Calculus of Inductive Constructions            *)
(*                       COQ v5.10                              *)
(*                                                              *)
(* Laurent Arditi.  Laboratoire I3S. CNRS ura 1376.             *)
(* Universite de Nice - Sophia Antipolis                        *)
(* arditi@unice.fr, http://wwwi3s.unice.fr/~arditi/lolo.html    *)
(*                                                              *)
(* date: may 1995                                               *)
(* file: Arith_compl.v                                          *)
(* contents: additionnal lemmas on plus,mult,minus,le...        *)
(* definitions of 2^ and factorial, lemmas about them           *)
(****************************************************************)


Require Export Plus.
Require Export Mult.
Require Import Minus.
Require Export Lt.
Require Export Le.
Require Export Gt.
Add Rec LoadPath "/home/arjun/Desktop/smtcoq/abduction-arjunvish-smtcoq/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
(****************************************************************)
(* Complements sur plus et mult *)

Lemma plus_n_SO : forall x : nat, x + 1 = S x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma plus_permute2 : forall x y z : nat, x + y + z = x + z + y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mult_sym : forall a b : nat, a * b = b * a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mult_permute : forall a b c : nat, a * b * c = a * c * b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.


Lemma plus_n_n : (n:nat)((plus n n)=(mult n (S (S O)))).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma plus_O_O : forall n m : nat, n + m = 0 -> n = 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mult_plus_distr2 : forall n m p : nat, n * (m + p) = n * m + n * p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(****************************************************************)
(* La fonction puissance de 2 *)

Fixpoint power2 (n : nat) : nat :=
  match n with
  | O => 1
  | S x => power2 x + power2 x
  end.

Lemma power2_eq2 : forall x : nat, power2 (S x) = power2 x + power2 x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma power2_SO : ((S (S O))=(power2 (S O))).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma power2_plus : forall x y : nat, power2 (x + y) = power2 x * power2 y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(****************************************************************)
(* Complements sur Lt Le Gt... *)

Theorem le_plus_n_m : forall n m : nat, n <= m -> n + n <= m + m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem lt_plus_n_m : forall n m : nat, n < m -> S (n + n) < m + m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma le_plus_lem1 : forall a b c : nat, a <= b -> c + a <= c + b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma le_plus_lem2 : forall a b c : nat, c + a <= c + b -> a <= b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gt_double : forall a b : nat, a + a > b + b -> a > b. 
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gt_double_inv : forall a b : nat, a > b -> a + a > b + b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gt_double_n_S : forall a b : nat, a > b -> a + a > S (b + b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gt_double_S_n : forall a b : nat, a > b -> S (a + a) > b + b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(****************************************************************)
(* Complements sur minus *)

Lemma minus_le_O : forall a b : nat, a <= b -> a - b = 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma minus_n_SO : forall n : nat, n - 1 = pred n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma minus_le_lem2c : forall a b : nat, a - S b <= a - b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma minus_le_lem2 : forall a b : nat, a - b <= a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma minus_minus_lem1 : forall a b : nat, a - b - a = 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma minus_minus_lem2 : forall a b : nat, b <= a -> a - (a - b) = b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma le_minus_minus : forall a b c : nat, c <= b -> a - b <= a - c.
Proof. Show. Fail (cvc5_abduct 3). Admitted.