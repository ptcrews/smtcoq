(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Base-2 Logarithm *)

Require Import NZAxioms NZMulOrder NZPow.
Add Rec LoadPath "/home/arjun/Desktop/smtcoq/abduction-arjunvish-smtcoq/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
(** Interface of a log2 function, then its specification on naturals *)

Module Type Log2 (Import A : Typ).
 Parameter Inline log2 : t -> t.
End Log2.

Module Type NZLog2Spec (A : NZOrdAxiomsSig')(B : Pow' A)(C : Log2 A).
 Import A B C.
 Axiom log2_spec : forall a, 0<a -> 2^(log2 a) <= a < 2^(S (log2 a)).
 Axiom log2_nonpos : forall a, a<=0 -> log2 a == 0.
End NZLog2Spec.

Module Type NZLog2 (A : NZOrdAxiomsSig)(B : Pow A) := Log2 A <+ NZLog2Spec A B.

(** Derived properties of logarithm *)

Module Type NZLog2Prop
 (Import A : NZOrdAxiomsSig')
 (Import B : NZPow' A)
 (Import C : NZLog2 A B)
 (Import D : NZMulOrderProp A)
 (Import E : NZPowProp A B D).

(** log2 is always non-negative *)

Lemma log2_nonneg : forall a, 0 <= log2 a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** A tactic for proving positivity and non-negativity *)

Ltac order_pos :=
((apply add_pos_pos || apply add_nonneg_nonneg ||
  apply mul_pos_pos || apply mul_nonneg_nonneg ||
  apply pow_nonneg || apply pow_pos_nonneg ||
  apply log2_nonneg || apply (le_le_succ_r 0));
 order_pos) (* in case of success of an apply, we recurse *)
|| order'.  (* otherwise *)

(** The spec of log2 indeed determines it *)

Lemma log2_unique : forall a b, 0<=b -> 2^b<=a<2^(S b) -> log2 a == b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Hence log2 is a morphism. *)

Instance log2_wd : Proper (eq==>eq) log2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** An alternate specification *)

Lemma log2_spec_alt : forall a, 0<a -> exists r,
 a == 2^(log2 a) + r /\ 0 <= r < 2^(log2 a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma log2_unique' : forall a b c, 0<=b -> 0<=c<2^b ->
 a == 2^b + c -> log2 a == b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** log2 is exact on powers of 2 *)

Lemma log2_pow2 : forall a, 0<=a -> log2 (2^a) == a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** log2 and predecessors of powers of 2 *)

Lemma log2_pred_pow2 : forall a, 0<a -> log2 (P (2^a)) == P a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** log2 and basic constants *)

Lemma log2_1 : log2 1 == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma log2_2 : log2 2 == 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** log2 n is strictly positive for 1<n *)

Lemma log2_pos : forall a, 1<a -> 0 < log2 a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Said otherwise, log2 is null only below 1 *)

Lemma log2_null : forall a, log2 a == 0 <-> a <= 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** log2 is a monotone function (but not a strict one) *)

Lemma log2_le_mono : forall a b, a<=b -> log2 a <= log2 b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** No reverse result for <=, consider for instance log2 3 <= log2 2 *)

Lemma log2_lt_cancel : forall a b, log2 a < log2 b -> a < b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** When left side is a power of 2, we have an equivalence for <= *)

Lemma log2_le_pow2 : forall a b, 0<a -> (2^b<=a <-> b <= log2 a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** When right side is a square, we have an equivalence for < *)

Lemma log2_lt_pow2 : forall a b, 0<a -> (a<2^b <-> log2 a < b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Comparing log2 and identity *)

Lemma log2_lt_lin : forall a, 0<a -> log2 a < a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma log2_le_lin : forall a, 0<=a -> log2 a <= a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Log2 and multiplication. *)

(** Due to rounding error, we don't have the usual
    [log2 (a*b) = log2 a + log2 b] but we may be off by 1 at most *)

Lemma log2_mul_below : forall a b, 0<a -> 0<b ->
 log2 a + log2 b <= log2 (a*b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma log2_mul_above : forall a b, 0<=a -> 0<=b ->
 log2 (a*b) <= log2 a + log2 b + 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** And we can't find better approximations in general.
    - The lower bound is exact for powers of 2.
    - Concerning the upper bound, for any c>1, take a=b=2^c-1,
      then log2 (a*b) = c+c -1 while (log2 a) = (log2 b) = c-1
*)

(** At least, we get back the usual equation when we multiply by 2 (or 2^k) *)

Lemma log2_mul_pow2 : forall a b, 0<a -> 0<=b -> log2 (a*2^b) == b + log2 a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma log2_double : forall a, 0<a -> log2 (2*a) == S (log2 a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Two numbers with same log2 cannot be far away. *)

Lemma log2_same : forall a b, 0<a -> 0<b -> log2 a == log2 b -> a < 2*b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Log2 and successor :
    - the log2 function climbs by at most 1 at a time
    - otherwise it stays at the same value
    - the +1 steps occur for powers of two
*)

Lemma log2_succ_le : forall a, log2 (S a) <= S (log2 a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma log2_succ_or : forall a,
 log2 (S a) == S (log2 a) \/ log2 (S a) == log2 a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma log2_eq_succ_is_pow2 : forall a,
 log2 (S a) == S (log2 a) -> exists b, S a == 2^b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma log2_eq_succ_iff_pow2 : forall a, 0<a ->
 (log2 (S a) == S (log2 a) <-> exists b, S a == 2^b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma log2_succ_double : forall a, 0<a -> log2 (2*a+1) == S (log2 a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Log2 and addition *)

Lemma log2_add_le : forall a b, a~=1 -> b~=1 -> log2 (a+b) <= log2 a + log2 b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** The sum of two log2 is less than twice the log2 of the sum.
    The large inequality is obvious thanks to monotonicity.
    The strict one requires some more work. This is almost
    a convexity inequality for points [2a], [2b] and their middle [a+b] :
    ideally, we would have [2*log(a+b) >= log(2a)+log(2b) = 2+log a+log b].
    Here, we cannot do better: consider for instance a=2 b=4, then 1+2<2*2
*)

Lemma add_log2_lt : forall a b, 0<a -> 0<b ->
 log2 a + log2 b < 2 * log2 (a+b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End NZLog2Prop.

Module NZLog2UpProp
 (Import A : NZDecOrdAxiomsSig')
 (Import B : NZPow' A)
 (Import C : NZLog2 A B)
 (Import D : NZMulOrderProp A)
 (Import E : NZPowProp A B D)
 (Import F : NZLog2Prop A B C D E).

(** * [log2_up] : a binary logarithm that rounds up instead of down *)

(** For once, we define instead of axiomatizing, thanks to log2 *)

Definition log2_up a :=
 match compare 1 a with
  | Lt => S (log2 (P a))
  | _ => 0
 end.

Lemma log2_up_eqn0 : forall a, a<=1 -> log2_up a == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma log2_up_eqn : forall a, 1<a -> log2_up a == S (log2 (P a)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma log2_up_spec : forall a, 1<a ->
 2^(P (log2_up a)) < a <= 2^(log2_up a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma log2_up_nonpos : forall a, a<=0 -> log2_up a == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Instance log2_up_wd : Proper (eq==>eq) log2_up.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** [log2_up] is always non-negative *)

Lemma log2_up_nonneg : forall a, 0 <= log2_up a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** The spec of [log2_up] indeed determines it *)

Lemma log2_up_unique : forall a b, 0<b -> 2^(P b)<a<=2^b -> log2_up a == b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** [log2_up] is exact on powers of 2 *)

Lemma log2_up_pow2 : forall a, 0<=a -> log2_up (2^a) == a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** [log2_up] and successors of powers of 2 *)

Lemma log2_up_succ_pow2 : forall a, 0<=a -> log2_up (S (2^a)) == S a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Basic constants *)

Lemma log2_up_1 : log2_up 1 == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma log2_up_2 : log2_up 2 == 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Links between log2 and [log2_up] *)

Lemma le_log2_log2_up : forall a, log2 a <= log2_up a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma le_log2_up_succ_log2 : forall a, log2_up a <= S (log2 a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma log2_log2_up_spec : forall a, 0<a ->
 2^log2 a <= a <= 2^log2_up a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma log2_log2_up_exact :
 forall a, 0<a -> (log2 a == log2_up a <-> exists b, a == 2^b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** [log2_up] n is strictly positive for 1<n *)

Lemma log2_up_pos : forall a, 1<a -> 0 < log2_up a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Said otherwise, [log2_up] is null only below 1 *)

Lemma log2_up_null : forall a, log2_up a == 0 <-> a <= 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** [log2_up] is a monotone function (but not a strict one) *)

Lemma log2_up_le_mono : forall a b, a<=b -> log2_up a <= log2_up b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** No reverse result for <=, consider for instance log2_up 4 <= log2_up 3 *)

Lemma log2_up_lt_cancel : forall a b, log2_up a < log2_up b -> a < b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** When left side is a power of 2, we have an equivalence for < *)

Lemma log2_up_lt_pow2 : forall a b, 0<a -> (2^b<a <-> b < log2_up a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** When right side is a square, we have an equivalence for <= *)

Lemma log2_up_le_pow2 : forall a b, 0<a -> (a<=2^b <-> log2_up a <= b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Comparing [log2_up] and identity *)

Lemma log2_up_lt_lin : forall a, 0<a -> log2_up a < a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma log2_up_le_lin : forall a, 0<=a -> log2_up a <= a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** [log2_up] and multiplication. *)

(** Due to rounding error, we don't have the usual
    [log2_up (a*b) = log2_up a + log2_up b] but we may be off by 1 at most *)

Lemma log2_up_mul_above : forall a b, 0<=a -> 0<=b ->
  log2_up (a*b) <= log2_up a + log2_up b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma log2_up_mul_below : forall a b, 0<a -> 0<b ->
 log2_up a + log2_up b <= S (log2_up (a*b)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** And we can't find better approximations in general.
    - The upper bound is exact for powers of 2.
    - Concerning the lower bound, for any c>1, take a=b=2^c+1,
      then [log2_up (a*b) = c+c +1] while [(log2_up a) = (log2_up b) = c+1]
*)

(** At least, we get back the usual equation when we multiply by 2 (or 2^k) *)

Lemma log2_up_mul_pow2 : forall a b, 0<a -> 0<=b ->
 log2_up (a*2^b) == b + log2_up a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma log2_up_double : forall a, 0<a -> log2_up (2*a) == S (log2_up a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Two numbers with same [log2_up] cannot be far away. *)

Lemma log2_up_same : forall a b, 0<a -> 0<b -> log2_up a == log2_up b -> a < 2*b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** [log2_up] and successor :
    - the [log2_up] function climbs by at most 1 at a time
    - otherwise it stays at the same value
    - the +1 steps occur after powers of two
*)

Lemma log2_up_succ_le : forall a, log2_up (S a) <= S (log2_up a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma log2_up_succ_or : forall a,
 log2_up (S a) == S (log2_up a) \/ log2_up (S a) == log2_up a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma log2_up_eq_succ_is_pow2 : forall a,
 log2_up (S a) == S (log2_up a) -> exists b, a == 2^b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma log2_up_eq_succ_iff_pow2 : forall a, 0<a ->
 (log2_up (S a) == S (log2_up a) <-> exists b, a == 2^b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma log2_up_succ_double : forall a, 0<a ->
 log2_up (2*a+1) == 2 + log2 a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** [log2_up] and addition *)

Lemma log2_up_add_le : forall a b, a~=1 -> b~=1 ->
 log2_up (a+b) <= log2_up a + log2_up b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** The sum of two [log2_up] is less than twice the [log2_up] of the sum.
    The large inequality is obvious thanks to monotonicity.
    The strict one requires some more work. This is almost
    a convexity inequality for points [2a], [2b] and their middle [a+b] :
    ideally, we would have [2*log(a+b) >= log(2a)+log(2b) = 2+log a+log b].
    Here, we cannot do better: consider for instance a=3 b=5, then 2+3<2*3
*)

Lemma add_log2_up_lt : forall a b, 0<a -> 0<b ->
 log2_up a + log2_up b < 2 * log2_up (a+b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End NZLog2UpProp.

