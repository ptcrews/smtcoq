(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Binary Integers : Parity and Division by Two *)
(** Initial author : Pierre Crégut (CNET, Lannion, France) *)

(** THIS FILE IS DEPRECATED.
    It is now almost entirely made of compatibility formulations
    for results already present in BinInt.Z. *)

Require Import BinInt.
Require Import SMTCoq.SMTCoq.
Open Scope Z_scope.

(** Historical formulation of even and odd predicates, based on
    case analysis. We now rather recommend using [Z.Even] and
    [Z.Odd], which are based on the exist predicate. *)

Definition Zeven (z:Z) :=
  match z with
    | Z0 => True
    | Zpos (xO _) => True
    | Zneg (xO _) => True
    | _ => False
  end.

Definition Zodd (z:Z) :=
  match z with
    | Zpos xH => True
    | Zneg xH => True
    | Zpos (xI _) => True
    | Zneg (xI _) => True
    | _ => False
  end.

Lemma Zeven_equiv z : Zeven z <-> Z.Even z.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zodd_equiv z : Zodd z <-> Z.Odd z.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Zeven_ex_iff n : Zeven n <-> exists m, n = 2*m.
Proof (Zeven_equiv n).

Theorem Zodd_ex_iff n : Zodd n <-> exists m, n = 2*m + 1.
Proof (Zodd_equiv n).

(** Boolean tests of parity (now in BinInt.Z) *)

Notation Zeven_bool := Z.even (only parsing).
Notation Zodd_bool := Z.odd (only parsing).

Lemma Zeven_bool_iff n : Z.even n = true <-> Zeven n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zodd_bool_iff n : Z.odd n = true <-> Zodd n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Ltac boolify_even_odd := rewrite <- ?Zeven_bool_iff, <- ?Zodd_bool_iff.

Lemma Zodd_even_bool n : Z.odd n = negb (Z.even n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zeven_odd_bool n : Z.even n = negb (Z.odd n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition Zeven_odd_dec n : {Zeven n} + {Zodd n}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition Zeven_dec n : {Zeven n} + {~ Zeven n}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition Zodd_dec n : {Zodd n} + {~ Zodd n}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zeven_not_Zodd n : Zeven n -> ~ Zodd n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zodd_not_Zeven n : Zodd n -> ~ Zeven n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zeven_Sn n : Zodd n -> Zeven (Z.succ n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zodd_Sn n : Zeven n -> Zodd (Z.succ n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zeven_pred n : Zodd n -> Zeven (Z.pred n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zodd_pred n : Zeven n -> Zodd (Z.pred n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

#[global]
Hint Unfold Zeven Zodd: zarith.

Notation Zeven_bool_succ := Z.even_succ (only parsing).
Notation Zeven_bool_pred := Z.even_pred (only parsing).
Notation Zodd_bool_succ := Z.odd_succ (only parsing).
Notation Zodd_bool_pred := Z.odd_pred (only parsing).

(******************************************************************)
(** * Definition of [Z.quot2], [Z.div2] and properties wrt [Zeven]
  and [Zodd] *)

(** Properties of [Z.div2] *)

Lemma Zdiv2_odd_eqn n : n = 2*(Z.div2 n) + if Z.odd n then 1 else 0.
Proof (Z.div2_odd n).

Lemma Zeven_div2 n : Zeven n -> n = 2 * Z.div2 n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zodd_div2 n : Zodd n -> n = 2 * Z.div2 n + 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Properties of [Z.quot2] *)

(** TODO: move to Numbers someday *)

Lemma Zquot2_odd_eqn n : n = 2*(Z.quot2 n) + if Z.odd n then Z.sgn n else 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zeven_quot2 n : Zeven n -> n = 2 * Z.quot2 n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zodd_quot2 n : n >= 0 -> Zodd n -> n = 2 * Z.quot2 n + 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zodd_quot2_neg n : n <= 0 -> Zodd n -> n = 2 * Z.quot2 n - 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zquot2_opp n : Z.quot2 (-n) = - Z.quot2 n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zquot2_quot n : Z.quot2 n = n ÷ 2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** More properties of parity *)

Lemma Z_modulo_2 n : {y | n = 2 * y} + {y | n = 2 * y + 1}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Zsplit2 n :
 {p : Z * Z | let (x1, x2) := p in n = x1 + x2 /\ (x1 = x2 \/ x2 = x1 + 1)}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Zeven_ex n : Zeven n -> exists m, n = 2 * m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Zodd_ex n : Zodd n -> exists m, n = 2 * m + 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Zeven_2p p : Zeven (2 * p).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Zodd_2p_plus_1 p : Zodd (2 * p + 1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Zeven_plus_Zodd a b : Zeven a -> Zodd b -> Zodd (a + b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Zeven_plus_Zeven a b : Zeven a -> Zeven b -> Zeven (a + b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Zodd_plus_Zeven a b : Zodd a -> Zeven b -> Zodd (a + b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Zodd_plus_Zodd a b : Zodd a -> Zodd b -> Zeven (a + b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Zeven_mult_Zeven_l a b : Zeven a -> Zeven (a * b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Zeven_mult_Zeven_r a b : Zeven b -> Zeven (a * b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Theorem Zodd_mult_Zodd a b : Zodd a -> Zodd b -> Zodd (a * b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* for compatibility *)
Close Scope Z_scope.
