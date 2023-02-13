(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Square Root Function *)

Require Import NZAxioms NZMulOrder.
Add Rec LoadPath "/home/arjun/Desktop/smtcoq/abduction-arjunvish-smtcoq/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
(** Interface of a sqrt function, then its specification on naturals *)

Module Type Sqrt (Import A : Typ).
 Parameter Inline sqrt : t -> t.
End Sqrt.

Module Type SqrtNotation (A : Typ)(Import B : Sqrt A).
 Notation "√ x" := (sqrt x) (at level 6).
End SqrtNotation.

Module Type Sqrt' (A : Typ) := Sqrt A <+ SqrtNotation A.

Module Type NZSqrtSpec (Import A : NZOrdAxiomsSig')(Import B : Sqrt' A).
 Axiom sqrt_spec : forall a, 0<=a -> √a * √a <= a < S (√a) * S (√a).
 Axiom sqrt_neg : forall a, a<0 -> √a == 0.
End NZSqrtSpec.

Module Type NZSqrt (A : NZOrdAxiomsSig) := Sqrt A <+ NZSqrtSpec A.
Module Type NZSqrt' (A : NZOrdAxiomsSig) := Sqrt' A <+ NZSqrtSpec A.

(** Derived properties of power *)

Module Type NZSqrtProp
 (Import A : NZOrdAxiomsSig')
 (Import B : NZSqrt' A)
 (Import C : NZMulOrderProp A).

Local Notation "a ²" := (a*a) (at level 5, no associativity, format "a ²").

(** First, sqrt is non-negative *)

Lemma sqrt_spec_nonneg : forall b,
 b² < (S b)² -> 0 <= b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrt_nonneg : forall a, 0<=√a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** The spec of sqrt indeed determines it *)

Lemma sqrt_unique : forall a b, b² <= a < (S b)² -> √a == b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Hence sqrt is a morphism *)

Instance sqrt_wd : Proper (eq==>eq) sqrt.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** An alternate specification *)

Lemma sqrt_spec_alt : forall a, 0<=a -> exists r,
 a == (√a)² + r /\ 0 <= r <= 2*√a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrt_unique' : forall a b c, 0<=c<=2*b ->
 a == b² + c -> √a == b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Sqrt is exact on squares *)

Lemma sqrt_square : forall a, 0<=a -> √(a²) == a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Sqrt and predecessors of squares *)

Lemma sqrt_pred_square : forall a, 0<a -> √(P a²) == P a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Sqrt is a monotone function (but not a strict one) *)

Lemma sqrt_le_mono : forall a b, a <= b -> √a <= √b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** No reverse result for <=, consider for instance √2 <= √1 *)

Lemma sqrt_lt_cancel : forall a b, √a < √b -> a < b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** When left side is a square, we have an equivalence for <= *)

Lemma sqrt_le_square : forall a b, 0<=a -> 0<=b -> (b²<=a <-> b <= √a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** When right side is a square, we have an equivalence for < *)

Lemma sqrt_lt_square : forall a b, 0<=a -> 0<=b -> (a<b² <-> √a < b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Sqrt and basic constants *)

Lemma sqrt_0 : √0 == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrt_1 : √1 == 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrt_2 : √2 == 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrt_pos : forall a, 0 < √a <-> 0 < a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrt_lt_lin : forall a, 1<a -> √a<a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrt_le_lin : forall a, 0<=a -> √a<=a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Sqrt and multiplication. *)

(** Due to rounding error, we don't have the usual √(a*b) = √a*√b
    but only lower and upper bounds. *)

Lemma sqrt_mul_below : forall a b, √a * √b <= √(a*b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrt_mul_above : forall a b, 0<=a -> 0<=b -> √(a*b) < S (√a) * S (√b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** And we can't find better approximations in general.
    - The lower bound is exact for squares
    - Concerning the upper bound, for any c>0, take a=b=c²-1,
      then √(a*b) = c² -1 while S √a = S √b = c
*)

(** Sqrt and successor :
    - the sqrt function climbs by at most 1 at a time
    - otherwise it stays at the same value
    - the +1 steps occur for squares
*)

Lemma sqrt_succ_le : forall a, 0<=a -> √(S a) <= S (√a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrt_succ_or : forall a, 0<=a -> √(S a) == S (√a) \/ √(S a) == √a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrt_eq_succ_iff_square : forall a, 0<=a ->
 (√(S a) == S (√a) <-> exists b, 0<b /\ S a == b²).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Sqrt and addition *)

Lemma sqrt_add_le : forall a b, √(a+b) <= √a + √b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** convexity inequality for sqrt: sqrt of middle is above middle
    of square roots. *)

Lemma add_sqrt_le : forall a b, 0<=a -> 0<=b -> √a + √b <= √(2*(a+b)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End NZSqrtProp.

Module Type NZSqrtUpProp
 (Import A : NZDecOrdAxiomsSig')
 (Import B : NZSqrt' A)
 (Import C : NZMulOrderProp A)
 (Import D : NZSqrtProp A B C).

(** * [sqrt_up] : a square root that rounds up instead of down *)

Local Notation "a ²" := (a*a) (at level 5, no associativity, format "a ²").

(** For once, we define instead of axiomatizing, thanks to sqrt *)

Definition sqrt_up a :=
 match compare 0 a with
  | Lt => S √(P a)
  | _ => 0
 end.

Local Notation "√° a" := (sqrt_up a) (at level 6, no associativity).

Lemma sqrt_up_eqn0 : forall a, a<=0 -> √°a == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrt_up_eqn : forall a, 0<a -> √°a == S √(P a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrt_up_spec : forall a, 0<a -> (P √°a)² < a <= (√°a)².
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** First, [sqrt_up] is non-negative *)

Lemma sqrt_up_nonneg : forall a, 0<=√°a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** [sqrt_up] is a morphism *)

Instance sqrt_up_wd : Proper (eq==>eq) sqrt_up.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** The spec of [sqrt_up] indeed determines it *)

Lemma sqrt_up_unique : forall a b, 0<b -> (P b)² < a <= b² -> √°a == b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** [sqrt_up] is exact on squares *)

Lemma sqrt_up_square : forall a, 0<=a -> √°(a²) == a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** [sqrt_up] and successors of squares *)

Lemma sqrt_up_succ_square : forall a, 0<=a -> √°(S a²) == S a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Basic constants *)

Lemma sqrt_up_0 : √°0 == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrt_up_1 : √°1 == 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrt_up_2 : √°2 == 2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(**  Links between sqrt and [sqrt_up] *)

Lemma le_sqrt_sqrt_up : forall a, √a <= √°a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma le_sqrt_up_succ_sqrt : forall a, √°a <= S (√a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrt_sqrt_up_spec : forall a, 0<=a -> (√a)² <= a <= (√°a)².
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrt_sqrt_up_exact :
 forall a, 0<=a -> (√a == √°a <-> exists b, 0<=b /\ a == b²).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** [sqrt_up] is a monotone function (but not a strict one) *)

Lemma sqrt_up_le_mono : forall a b, a <= b -> √°a <= √°b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** No reverse result for <=, consider for instance √°3 <= √°2 *)

Lemma sqrt_up_lt_cancel : forall a b, √°a < √°b -> a < b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** When left side is a square, we have an equivalence for < *)

Lemma sqrt_up_lt_square : forall a b, 0<=a -> 0<=b -> (b² < a <-> b < √°a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** When right side is a square, we have an equivalence for <= *)

Lemma sqrt_up_le_square : forall a b, 0<=a -> 0<=b -> (a <= b² <-> √°a <= b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrt_up_pos : forall a, 0 < √°a <-> 0 < a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrt_up_lt_lin : forall a, 2<a -> √°a < a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrt_up_le_lin : forall a, 0<=a -> √°a<=a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** [sqrt_up] and multiplication. *)

(** Due to rounding error, we don't have the usual [√(a*b) = √a*√b]
    but only lower and upper bounds. *)

Lemma sqrt_up_mul_above : forall a b, 0<=a -> 0<=b -> √°(a*b) <= √°a * √°b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrt_up_mul_below : forall a b, 0<a -> 0<b -> (P √°a)*(P √°b) < √°(a*b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** And we can't find better approximations in general.
    - The upper bound is exact for squares
    - Concerning the lower bound, for any c>0, take [a=b=c²+1],
      then [√°(a*b) = c²+1] while [P √°a = P √°b = c]
*)

(** [sqrt_up] and successor :
    - the [sqrt_up] function climbs by at most 1 at a time
    - otherwise it stays at the same value
    - the +1 steps occur after squares
*)

Lemma sqrt_up_succ_le : forall a, 0<=a -> √°(S a) <= S (√°a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrt_up_succ_or : forall a, 0<=a -> √°(S a) == S (√°a) \/ √°(S a) == √°a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrt_up_eq_succ_iff_square : forall a, 0<=a ->
 (√°(S a) == S (√°a) <-> exists b, 0<=b /\ a == b²).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** [sqrt_up] and addition *)

Lemma sqrt_up_add_le : forall a b, √°(a+b) <= √°a + √°b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Convexity-like inequality for [sqrt_up]: [sqrt_up] of middle is above middle
    of square roots. We cannot say more, for instance take a=b=2, then
    2+2 <= S 3 *)

Lemma add_sqrt_up_le : forall a b, 0<=a -> 0<=b -> √°a + √°b <= S √°(2*(a+b)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End NZSqrtUpProp.
