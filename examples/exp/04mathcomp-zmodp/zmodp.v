(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
From mathcomp Require Import fintype bigop finset prime fingroup.
From mathcomp Require Import ssralg finalg countalg.
Require Import SMTCoq.SMTCoq.
(******************************************************************************)
(*  Definition of the additive group and ring Zp, represented as 'I_p         *)
(******************************************************************************)
(* Definitions:                                                               *)
(* From fintype.v:                                                            *)
(*     'I_p == the subtype of integers less than p, taken here as the type of *)
(*             the integers mod p.                                            *)
(* This file:                                                                 *)
(*     inZp == the natural projection from nat into the integers mod p,       *)
(*             represented as 'I_p. Here p is implicit, but MUST be of the    *)
(*             form n.+1.                                                     *)
(* The operations:                                                            *)
(*      Zp0 == the identity element for addition                              *)
(*      Zp1 == the identity element for multiplication, and a generator of    *)
(*             additive group                                                 *)
(*   Zp_opp == inverse function for addition                                  *)
(*   Zp_add == addition                                                       *)
(*   Zp_mul == multiplication                                                 *)
(*   Zp_inv == inverse function for multiplication                            *)
(* Note that while 'I_n.+1 has canonical finZmodType and finGroupType         *)
(* structures, only 'I_n.+2 has a canonical ring structure (it has, in fact,  *)
(* a canonical finComUnitRing structure), and hence an associated             *)
(* multiplicative unit finGroupType. To mitigate the issues caused by the     *)
(* trivial "ring" (which is, indeed is NOT a ring in the ssralg/finalg        *)
(* formalization), we define additional notation:                             *)
(*       'Z_p == the type of integers mod (max p 2); this is always a proper  *)
(*               ring, by constructions. Note that 'Z_p is provably equal to  *)
(*               'I_p if p > 1, and convertible to 'I_p if p is of the form   *)
(*               n.+2.                                                        *)
(*       Zp p == the subgroup of integers mod (max p 1) in 'Z_p; this is thus *)
(*               all of 'Z_p if p > 1, and else the trivial group.            *)
(* units_Zp p == the group of all units of 'Z_p -- i.e., the group of         *)
(*               (multiplicative) automorphisms of Zp p.                      *)
(* We show that Zp and units_Zp are abelian, and compute their orders.        *)
(* We use a similar technique to represent the prime fields:                  *)
(*        'F_p == the finite field of integers mod the first prime divisor of *)
(*                maxn p 2. This is provably equal to 'Z_p and 'I_p if p is   *)
(*                provably prime, and indeed convertible to the above if p is *)
(*                a concrete prime such as 2, 5 or 23.                        *)
(* Note finally that due to the canonical structures it is possible to use    *)
(* 0%R instead of Zp0, and 1%R instead of Zp1 (for the latter, p must be of   *)
(* the form n.+2, and 1%R : nat will simplify to 1%N).                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section ZpDef.

(***********************************************************************)
(*                                                                     *)
(*  Mod p arithmetic on the finite set {0, 1, 2, ..., p - 1}           *)
(*                                                                     *)
(***********************************************************************)

Variable p' : nat.
Local Notation p := p'.+1.

Implicit Types x y z : 'I_p.

(* Standard injection; val (inZp i) = i %% p *)
Definition inZp i := Ordinal (ltn_pmod i (ltn0Sn p')).
Lemma modZp x : x %% p = x.
Proof. Show. Fail (abduce 3). Admitted.
Lemma valZpK x : inZp x = x.
Proof. Show. Fail (abduce 3). Admitted.

(* Operations *)
Definition Zp0 : 'I_p := ord0.
Definition Zp1 := inZp 1.
Definition Zp_opp x := inZp (p - x).
Definition Zp_add x y := inZp (x + y).
Definition Zp_mul x y := inZp (x * y).
Definition Zp_inv x := if coprime p x then inZp (egcdn x p).1 else x.

(* Additive group structure. *)

Lemma Zp_add0z : left_id Zp0 Zp_add.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zp_addNz : left_inverse Zp0 Zp_opp Zp_add.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zp_addA : associative Zp_add.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zp_addC : commutative Zp_add.
Proof. Show. Fail (abduce 3). Admitted.

Definition Zp_zmodMixin := ZmodMixin Zp_addA Zp_addC Zp_add0z Zp_addNz.
Canonical Zp_zmodType := Eval hnf in ZmodType 'I_p Zp_zmodMixin.
Canonical Zp_finZmodType := Eval hnf in [finZmodType of 'I_p].
Canonical Zp_baseFinGroupType := Eval hnf in [baseFinGroupType of 'I_p for +%R].
Canonical Zp_finGroupType := Eval hnf in [finGroupType of 'I_p for +%R].

(* Ring operations *)

Lemma Zp_mul1z : left_id Zp1 Zp_mul.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zp_mulC : commutative Zp_mul.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zp_mulz1 : right_id Zp1 Zp_mul.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zp_mulA : associative Zp_mul.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zp_mul_addr : right_distributive Zp_mul Zp_add.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zp_mul_addl : left_distributive Zp_mul Zp_add.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zp_mulVz x : coprime p x -> Zp_mul (Zp_inv x) x = Zp1.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zp_mulzV x : coprime p x -> Zp_mul x (Zp_inv x) = Zp1.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zp_intro_unit x y : Zp_mul y x = Zp1 -> coprime p x.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zp_inv_out x : ~~ coprime p x -> Zp_inv x = x.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zp_mulrn x n : x *+ n = inZp (x * n).
Proof. Show. Fail (abduce 3). Admitted.

Import GroupScope.

Lemma Zp_mulgC : @commutative 'I_p _ mulg.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zp_abelian : abelian [set: 'I_p].
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zp_expg x n : x ^+ n = inZp (x * n).
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zp1_expgz x : Zp1 ^+ x = x.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zp_cycle : setT = <[Zp1]>.
Proof. Show. Fail (abduce 3). Admitted.

Lemma order_Zp1 : #[Zp1] = p.
Proof. Show. Fail (abduce 3). Admitted.

End ZpDef.

Arguments Zp0 {p'}.
Arguments Zp1 {p'}.
Arguments inZp {p'} i.
Arguments valZpK {p'} x.

(* We redefine fintype.ord1 to specialize it with 0 instead of ord0 *)
(* since 'I_n is now canonically a zmodType  *)
Lemma ord1 : all_equal_to (0 : 'I_1).
Proof. Show. Fail (abduce 3). Admitted.

Lemma lshift0 m n : lshift m (0 : 'I_n.+1) = (0 : 'I_(n + m).+1).
Proof. Show. Fail (abduce 3). Admitted.

Lemma rshift1 n : @rshift 1 n =1 lift (0 : 'I_n.+1).
Proof. Show. Fail (abduce 3). Admitted.

Lemma split1 n i :
  split (i : 'I_(1 + n)) = oapp (@inr _ _) (inl _ 0) (unlift 0 i).
Proof. Show. Fail (abduce 3). Admitted.

Lemma big_ord1 R idx (op : @Monoid.law R idx) F :
  \big[op/idx]_(i < 1) F i = F 0.
Proof. Show. Fail (abduce 3). Admitted.

Lemma big_ord1_cond R idx (op : @Monoid.law R idx) P F :
  \big[op/idx]_(i < 1 | P i) F i = if P 0 then F 0 else idx.
Proof. Show. Fail (abduce 3). Admitted.

Section ZpRing.

Variable p' : nat.
Local Notation p := p'.+2.

Lemma Zp_nontrivial : Zp1 != 0 :> 'I_p. Proof. Show. Fail (abduce 3). Admitted.

Definition Zp_ringMixin :=
  ComRingMixin (@Zp_mulA _) (@Zp_mulC _) (@Zp_mul1z _) (@Zp_mul_addl _)
               Zp_nontrivial.
Canonical Zp_ringType := Eval hnf in RingType 'I_p Zp_ringMixin.
Canonical Zp_finRingType := Eval hnf in [finRingType of 'I_p].
Canonical Zp_comRingType := Eval hnf in ComRingType 'I_p (@Zp_mulC _).
Canonical Zp_finComRingType := Eval hnf in [finComRingType of 'I_p].

Definition Zp_unitRingMixin :=
  ComUnitRingMixin (@Zp_mulVz _) (@Zp_intro_unit _) (@Zp_inv_out _).
Canonical Zp_unitRingType := Eval hnf in UnitRingType 'I_p Zp_unitRingMixin.
Canonical Zp_finUnitRingType := Eval hnf in [finUnitRingType of 'I_p].
Canonical Zp_comUnitRingType := Eval hnf in [comUnitRingType of 'I_p].
Canonical Zp_finComUnitRingType := Eval hnf in [finComUnitRingType of 'I_p].

Lemma Zp_nat n : n%:R = inZp n :> 'I_p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma natr_Zp (x : 'I_p) : x%:R = x.
Proof. Show. Fail (abduce 3). Admitted.

Lemma natr_negZp (x : 'I_p) : (- x)%:R = - x.
Proof. Show. Fail (abduce 3). Admitted.

Import GroupScope.

Lemma unit_Zp_mulgC : @commutative {unit 'I_p} _ mulg.
Proof. Show. Fail (abduce 3). Admitted.

Lemma unit_Zp_expg (u : {unit 'I_p}) n :
  val (u ^+ n) = inZp (val u ^ n) :> 'I_p.
Proof. Show. Fail (abduce 3). Admitted.

End ZpRing.

Definition Zp_trunc p := p.-2.

Notation "''Z_' p" := 'I_(Zp_trunc p).+2
  (at level 8, p at level 2, format "''Z_' p") : type_scope.
Notation "''F_' p" := 'Z_(pdiv p)
  (at level 8, p at level 2, format "''F_' p") : type_scope.

Arguments natr_Zp {p'} x.

Section Groups.

Variable p : nat.

Definition Zp := if p > 1 then [set: 'Z_p] else 1%g.
Definition units_Zp := [set: {unit 'Z_p}].

Lemma Zp_cast : p > 1 -> (Zp_trunc p).+2 = p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma val_Zp_nat (p_gt1 : p > 1) n : (n%:R : 'Z_p) = (n %% p)%N :> nat.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zp_nat_mod (p_gt1 : p > 1)m : (m %% p)%:R = m%:R :> 'Z_p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma char_Zp : p > 1 -> p%:R = 0 :> 'Z_p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma unitZpE x : p > 1 -> ((x%:R : 'Z_p) \is a GRing.unit) = coprime p x.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zp_group_set : group_set Zp.
Proof. Show. Fail (abduce 3). Admitted.
Canonical Zp_group := Group Zp_group_set.

Lemma card_Zp : p > 0 -> #|Zp| = p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma mem_Zp x : p > 1 -> x \in Zp. Proof. Show. Fail (abduce 3). Admitted.

Canonical units_Zp_group := [group of units_Zp].

Lemma card_units_Zp : p > 0 -> #|units_Zp| = totient p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma units_Zp_abelian : abelian units_Zp.
Proof. Show. Fail (abduce 3). Admitted.

End Groups.

(* Field structure for primes. *)

Section PrimeField.

Open Scope ring_scope.

Variable p : nat.

Section F_prime.

Hypothesis p_pr : prime p.

Lemma Fp_Zcast : (Zp_trunc (pdiv p)).+2 = (Zp_trunc p).+2.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Fp_cast : (Zp_trunc (pdiv p)).+2 = p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma card_Fp : #|'F_p| = p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma val_Fp_nat n : (n%:R : 'F_p) = (n %% p)%N :> nat.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Fp_nat_mod m : (m %% p)%:R = m%:R :> 'F_p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma char_Fp : p \in [char 'F_p].
Proof. Show. Fail (abduce 3). Admitted.

Lemma char_Fp_0 : p%:R = 0 :> 'F_p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma unitFpE x : ((x%:R : 'F_p) \is a GRing.unit) = coprime p x.
Proof. Show. Fail (abduce 3). Admitted.

End F_prime.

Lemma Fp_fieldMixin : GRing.Field.mixin_of [the unitRingType of 'F_p].
Proof. Show. Fail (abduce 3). Admitted.

Definition Fp_idomainMixin := FieldIdomainMixin Fp_fieldMixin.

Canonical Fp_idomainType := Eval hnf in IdomainType 'F_p  Fp_idomainMixin.
Canonical Fp_finIdomainType := Eval hnf in [finIdomainType of 'F_p].
Canonical Fp_fieldType := Eval hnf in FieldType 'F_p Fp_fieldMixin.
Canonical Fp_finFieldType := Eval hnf in [finFieldType of 'F_p].
Canonical Fp_decFieldType :=
  Eval hnf in [decFieldType of 'F_p for Fp_finFieldType].

End PrimeField.

Canonical Zp_countZmodType m := [countZmodType of 'I_m.+1].
Canonical Zp_countRingType m := [countRingType of 'I_m.+2].
Canonical Zp_countComRingType m := [countComRingType of 'I_m.+2].
Canonical Zp_countUnitRingType m := [countUnitRingType of 'I_m.+2].
Canonical Zp_countComUnitRingType m := [countComUnitRingType of 'I_m.+2].
Canonical Fp_countIdomainType p := [countIdomainType of 'F_p].
Canonical Fp_countFieldType p := [countFieldType of 'F_p].
Canonical Fp_countDecFieldType p := [countDecFieldType of 'F_p].

