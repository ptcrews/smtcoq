(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import
 Bool ZAxioms ZMulOrder ZPow ZDivFloor ZSgnAbs ZParity NZLog.
Add Rec LoadPath "/home/arjun/Desktop/smtcoq/abduction-arjunvish-smtcoq/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
(** Derived properties of bitwise operations *)

Module Type ZBitsProp
 (Import A : ZAxiomsSig')
 (Import B : ZMulOrderProp A)
 (Import C : ZParityProp A B)
 (Import D : ZSgnAbsProp A B)
 (Import E : ZPowProp A B C D)
 (Import F : ZDivProp A B D)
 (Import G : NZLog2Prop A A A B E).

Include BoolEqualityFacts A.

Ltac order_nz := try apply pow_nonzero; order'.
Ltac order_pos' := try apply abs_nonneg; order_pos.
Hint Rewrite div_0_l mod_0_l div_1_r mod_1_r : nz.

(** Some properties of power and division *)

Lemma pow_sub_r : forall a b c, a~=0 -> 0<=c<=b -> a^(b - c) == a^b / a^c.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pow_div_l : forall a b c, b~=0 -> 0<=c -> a mod b == 0 ->
 (a/b)^c == a^c / b^c.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** An injection from bits [true] and [false] to numbers 1 and 0.
    We declare it as a (local) coercion for shorter statements. *)

Definition b2z (b:bool) := if b then 1 else 0.
Local Coercion b2z : bool >-> t.

Instance b2z_wd : Proper (Logic.eq ==> eq) b2z := _.

Lemma exists_div2 a : exists a' (b:bool), a == 2*a' + b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** We can compact [testbit_odd_0] [testbit_even_0]
    [testbit_even_succ] [testbit_odd_succ] in only two lemmas. *)

Lemma testbit_0_r a (b:bool) : testbit (2*a+b) 0 = b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma testbit_succ_r a (b:bool) n : 0<=n ->
 testbit (2*a+b) (succ n) = testbit a n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Alternative characterisations of [testbit] *)

(** This concise equation could have been taken as specification
   for testbit in the interface, but it would have been hard to
   implement with little initial knowledge about div and mod *)

Lemma testbit_spec' a n : 0<=n -> a.[n] == (a / 2^n) mod 2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** This characterisation that uses only basic operations and
   power was initially taken as specification for testbit.
   We describe [a] as having a low part and a high part, with
   the corresponding bit in the middle. This characterisation
   is moderatly complex to implement, but also moderately
   usable... *)

Lemma testbit_spec a n : 0<=n ->
  exists l h, 0<=l<2^n /\ a == l + (a.[n] + 2*h)*2^n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma testbit_true : forall a n, 0<=n ->
 (a.[n] = true <-> (a / 2^n) mod 2 == 1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma testbit_false : forall a n, 0<=n ->
 (a.[n] = false <-> (a / 2^n) mod 2 == 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma testbit_eqb : forall a n, 0<=n ->
 a.[n] = eqb ((a / 2^n) mod 2) 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Results about the injection [b2z] *)

Lemma b2z_inj : forall (a0 b0:bool), a0 == b0 -> a0 = b0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma add_b2z_double_div2 : forall (a0:bool) a, (a0+2*a)/2 == a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma add_b2z_double_bit0 : forall (a0:bool) a, (a0+2*a).[0] = a0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma b2z_div2 : forall (a0:bool), a0/2 == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma b2z_bit0 : forall (a0:bool), a0.[0] = a0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** The specification of testbit by low and high parts is complete *)

Lemma testbit_unique : forall a n (a0:bool) l h,
 0<=l<2^n -> a == l + (a0 + 2*h)*2^n -> a.[n] = a0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** All bits of number 0 are 0 *)

Lemma bits_0 : forall n, 0.[n] = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** For negative numbers, we are actually doing two's complement *)

Lemma bits_opp : forall a n, 0<=n -> (-a).[n] = negb (P a).[n].
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** All bits of number (-1) are 1 *)

Lemma bits_m1 : forall n, 0<=n -> (-1).[n] = true.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Various ways to refer to the lowest bit of a number *)

Lemma bit0_odd : forall a, a.[0] = odd a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma bit0_eqb : forall a, a.[0] = eqb (a mod 2) 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma bit0_mod : forall a, a.[0] == a mod 2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Hence testing a bit is equivalent to shifting and testing parity *)

Lemma testbit_odd : forall a n, a.[n] = odd (a>>n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** [log2] gives the highest nonzero bit of positive numbers *)

Lemma bit_log2 : forall a, 0<a -> a.[log2 a] = true.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma bits_above_log2 : forall a n, 0<=a -> log2 a < n ->
 a.[n] = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Hence the number of bits of [a] is [1+log2 a]
    (see [Pos.size_nat] and [Pos.size]).
*)

(** For negative numbers, things are the other ways around:
    log2 gives the highest zero bit (for numbers below -1).
*)

Lemma bit_log2_neg : forall a, a < -1 -> a.[log2 (P (-a))] = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma bits_above_log2_neg : forall a n, a < 0 -> log2 (P (-a)) < n ->
 a.[n] = true.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Accessing a high enough bit of a number gives its sign *)

Lemma bits_iff_nonneg : forall a n, log2 (abs a) < n ->
 (0<=a <-> a.[n] = false).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma bits_iff_nonneg' : forall a,
 0<=a <-> a.[S (log2 (abs a))] = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma bits_iff_nonneg_ex : forall a,
 0<=a <-> (exists k, forall m, k<m -> a.[m] = false).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma bits_iff_neg : forall a n, log2 (abs a) < n ->
 (a<0 <-> a.[n] = true).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma bits_iff_neg' : forall a, a<0 <-> a.[S (log2 (abs a))] = true.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma bits_iff_neg_ex : forall a,
 a<0 <-> (exists k, forall m, k<m -> a.[m] = true).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Testing bits after division or multiplication by a power of two *)

Lemma div2_bits : forall a n, 0<=n -> (a/2).[n] = a.[S n].
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma div_pow2_bits : forall a n m, 0<=n -> 0<=m -> (a/2^n).[m] = a.[m+n].
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma double_bits_succ : forall a n, (2*a).[S n] = a.[n].
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma double_bits : forall a n, (2*a).[n] = a.[P n].
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mul_pow2_bits_add : forall a n m, 0<=n -> (a*2^n).[n+m] = a.[m].
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mul_pow2_bits : forall a n m, 0<=n -> (a*2^n).[m] = a.[m-n].
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mul_pow2_bits_low : forall a n m, m<n -> (a*2^n).[m] = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Selecting the low part of a number can be done by a modulo *)

Lemma mod_pow2_bits_high : forall a n m, 0<=n<=m ->
 (a mod 2^n).[m] = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mod_pow2_bits_low : forall a n m, m<n ->
 (a mod 2^n).[m] = a.[m].
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** We now prove that having the same bits implies equality.
    For that we use a notion of equality over functional
    streams of bits. *)

Definition eqf (f g:t -> bool) := forall n:t, f n = g n.

Instance eqf_equiv : Equivalence eqf.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Local Infix "===" := eqf (at level 70, no associativity).

Instance testbit_eqf : Proper (eq==>eqf) testbit.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Only zero corresponds to the always-false stream. *)

Lemma bits_inj_0 :
 forall a, (forall n, a.[n] = false) -> a == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** If two numbers produce the same stream of bits, they are equal. *)

Lemma bits_inj : forall a b, testbit a === testbit b -> a == b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma bits_inj_iff : forall a b, testbit a === testbit b <-> a == b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** In fact, checking the bits at positive indexes is enough. *)

Lemma bits_inj' : forall a b,
 (forall n, 0<=n -> a.[n] = b.[n]) -> a == b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma bits_inj_iff' : forall a b, (forall n, 0<=n -> a.[n] = b.[n]) <-> a == b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Tactic Notation "bitwise" "as" simple_intropattern(m) simple_intropattern(Hm)
  := apply bits_inj'; intros m Hm; autorewrite with bitwise.

Ltac bitwise := bitwise as ?m ?Hm.

Hint Rewrite lxor_spec lor_spec land_spec ldiff_spec bits_0 : bitwise.

(** The streams of bits that correspond to a numbers are
  exactly the ones which are stationary after some point. *)

Lemma are_bits : forall (f:t->bool), Proper (eq==>Logic.eq) f ->
 ((exists n, forall m, 0<=m -> f m = n.[m]) <->
  (exists k, forall m, k<=m -> f m = f k)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** * Properties of shifts *)

(** First, a unified specification for [shiftl] : the [shiftl_spec]
   below (combined with [testbit_neg_r]) is equivalent to
   [shiftl_spec_low] and [shiftl_spec_high]. *)

Lemma shiftl_spec : forall a n m, 0<=m -> (a << n).[m] = a.[m-n].
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** A shiftl by a negative number is a shiftr, and vice-versa *)

Lemma shiftr_opp_r : forall a n, a >> (-n) == a << n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma shiftl_opp_r : forall a n, a << (-n) == a >> n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Shifts correspond to multiplication or division by a power of two *)

Lemma shiftr_div_pow2 : forall a n, 0<=n -> a >> n == a / 2^n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma shiftr_mul_pow2 : forall a n, n<=0 -> a >> n == a * 2^(-n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma shiftl_mul_pow2 : forall a n, 0<=n -> a << n == a * 2^n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma shiftl_div_pow2 : forall a n, n<=0 -> a << n == a / 2^(-n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Shifts are morphisms *)

Instance shiftr_wd : Proper (eq==>eq==>eq) shiftr.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Instance shiftl_wd : Proper (eq==>eq==>eq) shiftl.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** We could also have specified shiftl with an addition on the left. *)

Lemma shiftl_spec_alt : forall a n m, 0<=n -> (a << n).[m+n] = a.[m].
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Chaining several shifts. The only case for which
    there isn't any simple expression is a true shiftr
    followed by a true shiftl.
*)

Lemma shiftl_shiftl : forall a n m, 0<=n ->
 (a << n) << m == a << (n+m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma shiftr_shiftl_l : forall a n m, 0<=n ->
 (a << n) >> m == a << (n-m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma shiftr_shiftl_r : forall a n m, 0<=n ->
 (a << n) >> m == a >> (m-n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma shiftr_shiftr : forall a n m, 0<=m ->
 (a >> n) >> m == a >> (n+m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** shifts and constants *)

Lemma shiftl_1_l : forall n, 1 << n == 2^n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma shiftl_0_r : forall a, a << 0 == a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma shiftr_0_r : forall a, a >> 0 == a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma shiftl_0_l : forall n, 0 << n == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma shiftr_0_l : forall n, 0 >> n == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma shiftl_eq_0_iff : forall a n, 0<=n -> (a << n == 0 <-> a == 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma shiftr_eq_0_iff : forall a n,
 a >> n == 0 <-> a==0 \/ (0<a /\ log2 a < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma shiftr_eq_0 : forall a n, 0<=a -> log2 a < n -> a >> n == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Properties of [div2]. *)

Lemma div2_div : forall a, div2 a == a/2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Instance div2_wd : Proper (eq==>eq) div2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma div2_odd : forall a, a == 2*(div2 a) + odd a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Properties of [lxor] and others, directly deduced
    from properties of [xorb] and others. 

Instance lxor_wd : Proper (eq ==> eq ==> eq) lxor.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Instance land_wd : Proper (eq ==> eq ==> eq) land.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Instance lor_wd : Proper (eq ==> eq ==> eq) lor.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Instance ldiff_wd : Proper (eq ==> eq ==> eq) ldiff.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lxor_eq : forall a a', lxor a a' == 0 -> a == a'.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lxor_nilpotent : forall a, lxor a a == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lxor_eq_0_iff : forall a a', lxor a a' == 0 <-> a == a'.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lxor_0_l : forall a, lxor 0 a == a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lxor_0_r : forall a, lxor a 0 == a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lxor_comm : forall a b, lxor a b == lxor b a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lxor_assoc :
 forall a b c, lxor (lxor a b) c == lxor a (lxor b c).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lor_0_l : forall a, lor 0 a == a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lor_0_r : forall a, lor a 0 == a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lor_comm : forall a b, lor a b == lor b a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lor_assoc :
 forall a b c, lor a (lor b c) == lor (lor a b) c.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lor_diag : forall a, lor a a == a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lor_eq_0_l : forall a b, lor a b == 0 -> a == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lor_eq_0_iff : forall a b, lor a b == 0 <-> a == 0 /\ b == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma land_0_l : forall a, land 0 a == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma land_0_r : forall a, land a 0 == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma land_comm : forall a b, land a b == land b a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma land_assoc :
 forall a b c, land a (land b c) == land (land a b) c.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma land_diag : forall a, land a a == a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ldiff_0_l : forall a, ldiff 0 a == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ldiff_0_r : forall a, ldiff a 0 == a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ldiff_diag : forall a, ldiff a a == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lor_land_distr_l : forall a b c,
 lor (land a b) c == land (lor a c) (lor b c).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lor_land_distr_r : forall a b c,
 lor a (land b c) == land (lor a b) (lor a c).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma land_lor_distr_l : forall a b c,
 land (lor a b) c == lor (land a c) (land b c).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma land_lor_distr_r : forall a b c,
 land a (lor b c) == lor (land a b) (land a c).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ldiff_ldiff_l : forall a b c,
 ldiff (ldiff a b) c == ldiff a (lor b c).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lor_ldiff_and : forall a b,
 lor (ldiff a b) (land a b) == a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma land_ldiff : forall a b,
 land (ldiff a b) b == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Properties of [setbit] and [clearbit] *)

Definition setbit a n := lor a (1 << n).
Definition clearbit a n := ldiff a (1 << n).

Lemma setbit_spec' : forall a n, setbit a n == lor a (2^n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma clearbit_spec' : forall a n, clearbit a n == ldiff a (2^n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Instance setbit_wd : Proper (eq==>eq==>eq) setbit.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Instance clearbit_wd : Proper (eq==>eq==>eq) clearbit.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pow2_bits_true : forall n, 0<=n -> (2^n).[n] = true.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pow2_bits_false : forall n m, n~=m -> (2^n).[m] = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pow2_bits_eqb : forall n m, 0<=n -> (2^n).[m] = eqb n m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma setbit_eqb : forall a n m, 0<=n ->
 (setbit a n).[m] = eqb n m || a.[m].
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma setbit_iff : forall a n m, 0<=n ->
 ((setbit a n).[m] = true <-> n==m \/ a.[m] = true).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma setbit_eq : forall a n, 0<=n -> (setbit a n).[n] = true.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma setbit_neq : forall a n m, 0<=n -> n~=m ->
 (setbit a n).[m] = a.[m].
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma clearbit_eqb : forall a n m,
 (clearbit a n).[m] = a.[m] && negb (eqb n m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma clearbit_iff : forall a n m,
 (clearbit a n).[m] = true <-> a.[m] = true /\ n~=m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma clearbit_eq : forall a n, (clearbit a n).[n] = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma clearbit_neq : forall a n m, n~=m ->
 (clearbit a n).[m] = a.[m].
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Shifts of bitwise operations *)

Lemma shiftl_lxor : forall a b n,
 (lxor a b) << n == lxor (a << n) (b << n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma shiftr_lxor : forall a b n,
 (lxor a b) >> n == lxor (a >> n) (b >> n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma shiftl_land : forall a b n,
 (land a b) << n == land (a << n) (b << n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma shiftr_land : forall a b n,
 (land a b) >> n == land (a >> n) (b >> n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma shiftl_lor : forall a b n,
 (lor a b) << n == lor (a << n) (b << n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma shiftr_lor : forall a b n,
 (lor a b) >> n == lor (a >> n) (b >> n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma shiftl_ldiff : forall a b n,
 (ldiff a b) << n == ldiff (a << n) (b << n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma shiftr_ldiff : forall a b n,
 (ldiff a b) >> n == ldiff (a >> n) (b >> n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** For integers, we do have a binary complement function *)

Definition lnot a := P (-a).

Instance lnot_wd : Proper (eq==>eq) lnot.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lnot_spec : forall a n, 0<=n -> (lnot a).[n] = negb a.[n].
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lnot_involutive : forall a, lnot (lnot a) == a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lnot_0 : lnot 0 == -1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lnot_m1 : lnot (-1) == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Complement and other operations *)

Lemma lor_m1_r : forall a, lor a (-1) == -1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lor_m1_l : forall a, lor (-1) a == -1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma land_m1_r : forall a, land a (-1) == a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma land_m1_l : forall a, land (-1) a == a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ldiff_m1_r : forall a, ldiff a (-1) == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ldiff_m1_l : forall a, ldiff (-1) a == lnot a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lor_lnot_diag : forall a, lor a (lnot a) == -1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma add_lnot_diag : forall a, a + lnot a == -1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ldiff_land : forall a b, ldiff a b == land a (lnot b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma land_lnot_diag : forall a, land a (lnot a) == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lnot_lor : forall a b, lnot (lor a b) == land (lnot a) (lnot b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lnot_land : forall a b, lnot (land a b) == lor (lnot a) (lnot b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lnot_ldiff : forall a b, lnot (ldiff a b) == lor (lnot a) b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lxor_lnot_lnot : forall a b, lxor (lnot a) (lnot b) == lxor a b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lnot_lxor_l : forall a b, lnot (lxor a b) == lxor (lnot a) b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lnot_lxor_r : forall a b, lnot (lxor a b) == lxor a (lnot b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lxor_m1_r : forall a, lxor a (-1) == lnot a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lxor_m1_l : forall a, lxor (-1) a == lnot a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lxor_lor : forall a b, land a b == 0 ->
 lxor a b == lor a b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lnot_shiftr : forall a n, 0<=n -> lnot (a >> n) == (lnot a) >> n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** [(ones n)] is [2^n-1], the number with [n] digits 1 *)

Definition ones n := P (1<<n).

Instance ones_wd : Proper (eq==>eq) ones.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ones_equiv : forall n, ones n == P (2^n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ones_add : forall n m, 0<=n -> 0<=m ->
 ones (m+n) == 2^m * ones n + ones m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ones_div_pow2 : forall n m, 0<=m<=n -> ones n / 2^m == ones (n-m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ones_mod_pow2 : forall n m, 0<=m<=n -> (ones n) mod (2^m) == ones m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ones_spec_low : forall n m, 0<=m<n -> (ones n).[m] = true.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ones_spec_high : forall n m, 0<=n<=m -> (ones n).[m] = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ones_spec_iff : forall n m, 0<=n ->
 ((ones n).[m] = true <-> 0<=m<n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lor_ones_low : forall a n, 0<=a -> log2 a < n ->
 lor a (ones n) == ones n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma land_ones : forall a n, 0<=n -> land a (ones n) == a mod 2^n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma land_ones_low : forall a n, 0<=a -> log2 a < n ->
 land a (ones n) == a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ldiff_ones_r : forall a n, 0<=n ->
 ldiff a (ones n) == (a >> n) << n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ldiff_ones_r_low : forall a n, 0<=a -> log2 a < n ->
 ldiff a (ones n) == 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ldiff_ones_l_low : forall a n, 0<=a -> log2 a < n ->
 ldiff (ones n) a == lxor a (ones n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Bitwise operations and sign *)

Lemma shiftl_nonneg : forall a n, 0 <= (a << n) <-> 0 <= a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma shiftl_neg : forall a n, (a << n) < 0 <-> a < 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma shiftr_nonneg : forall a n, 0 <= (a >> n) <-> 0 <= a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma shiftr_neg : forall a n, (a >> n) < 0 <-> a < 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma div2_nonneg : forall a, 0 <= div2 a <-> 0 <= a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma div2_neg : forall a, div2 a < 0 <-> a < 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lor_nonneg : forall a b, 0 <= lor a b <-> 0<=a /\ 0<=b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lor_neg : forall a b, lor a b < 0 <-> a < 0 \/ b < 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lnot_nonneg : forall a, 0 <= lnot a <-> a < 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lnot_neg : forall a, lnot a < 0 <-> 0 <= a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma land_nonneg : forall a b, 0 <= land a b <-> 0<=a \/ 0<=b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma land_neg : forall a b, land a b < 0 <-> a < 0 /\ b < 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ldiff_nonneg : forall a b, 0 <= ldiff a b <-> 0<=a \/ b<0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ldiff_neg : forall a b, ldiff a b < 0 <-> a<0 /\ 0<=b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lxor_nonneg : forall a b, 0 <= lxor a b <-> (0<=a <-> 0<=b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Bitwise operations and log2 *)

Lemma log2_bits_unique : forall a n,
 a.[n] = true ->
 (forall m, n<m -> a.[m] = false) ->
 log2 a == n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma log2_shiftr : forall a n, 0<a -> log2 (a >> n) == max 0 (log2 a - n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma log2_shiftl : forall a n, 0<a -> 0<=n -> log2 (a << n) == log2 a + n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma log2_shiftl' : forall a n, 0<a -> log2 (a << n) == max 0 (log2 a + n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma log2_lor : forall a b, 0<=a -> 0<=b ->
 log2 (lor a b) == max (log2 a) (log2 b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma log2_land : forall a b, 0<=a -> 0<=b ->
 log2 (land a b) <= min (log2 a) (log2 b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma log2_lxor : forall a b, 0<=a -> 0<=b ->
 log2 (lxor a b) <= max (log2 a) (log2 b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Bitwise operations and arithmetical operations *)

Local Notation xor3 a b c := (xorb (xorb a b) c).
Local Notation lxor3 a b c := (lxor (lxor a b) c).
Local Notation nextcarry a b c := ((a&&b) || (c && (a||b))).
Local Notation lnextcarry a b c := (lor (land a b) (land c (lor a b))).

Lemma add_bit0 : forall a b, (a+b).[0] = xorb a.[0] b.[0].
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma add3_bit0 : forall a b c,
 (a+b+c).[0] = xor3 a.[0] b.[0] c.[0].
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma add3_bits_div2 : forall (a0 b0 c0 : bool),
 (a0 + b0 + c0)/2 == nextcarry a0 b0 c0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma add_carry_div2 : forall a b (c0:bool),
 (a + b + c0)/2 == a/2 + b/2 + nextcarry a.[0] b.[0] c0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** The main result concerning addition: we express the bits of the sum
  in term of bits of [a] and [b] and of some carry stream which is also
  recursively determined by another equation.
*)

Lemma add_carry_bits_aux : forall n, 0<=n ->
 forall a b (c0:bool), -(2^n) <= a < 2^n -> -(2^n) <= b < 2^n ->
  exists c,
   a+b+c0 == lxor3 a b c /\ c/2 == lnextcarry a b c /\ c.[0] = c0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma add_carry_bits : forall a b (c0:bool), exists c,
 a+b+c0 == lxor3 a b c /\ c/2 == lnextcarry a b c /\ c.[0] = c0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Particular case : the second bit of an addition *)

Lemma add_bit1 : forall a b,
 (a+b).[1] = xor3 a.[1] b.[1] (a.[0] && b.[0]).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** In an addition, there will be no carries iff there is
  no common bits in the numbers to add *)

Lemma nocarry_equiv : forall a b c,
 c/2 == lnextcarry a b c -> c.[0] = false ->
 (c == 0 <-> land a b == 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** When there is no common bits, the addition is just a xor *)

Lemma add_nocarry_lxor : forall a b, land a b == 0 ->
 a+b == lxor a b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** A null [ldiff] implies being smaller *)

Lemma ldiff_le : forall a b, 0<=b -> ldiff a b == 0 -> 0 <= a <= b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Subtraction can be a ldiff when the opposite ldiff is null. *)

Lemma sub_nocarry_ldiff : forall a b, ldiff b a == 0 ->
 a-b == ldiff a b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Adding numbers with no common bits cannot lead to a much bigger number *)

Lemma add_nocarry_lt_pow2 : forall a b n, land a b == 0 ->
 a < 2^n -> b < 2^n -> a+b < 2^n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma add_nocarry_mod_lt_pow2 : forall a b n, 0<=n -> land a b == 0 ->
 a mod 2^n + b mod 2^n < 2^n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End ZBitsProp.
*)