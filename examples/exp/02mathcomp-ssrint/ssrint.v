(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import fintype finfun bigop order ssralg countalg ssrnum.
From mathcomp Require Import poly.
Add Rec LoadPath "/home/arjun/Desktop/smtcoq/abduction-arjunvish-smtcoq/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
(******************************************************************************)
(* This file develops a basic theory of signed integers, defining:            *)
(*         int == the type of signed integers, with two constructors Posz for *)
(*                non-negative integers and Negz for negative integers. It    *)
(*                supports the realDomainType interface (and its parents).    *)
(*        n%:Z == explicit cast from nat to int (:= Posz n); displayed as n.  *)
(*                However (Posz m = Posz n) is displayed as (m = n :> int)    *)
(*                (and so are ==, != and <>)                                  *)
(*                Lemma NegzE : turns (Negz n) into - n.+1%:Z.                *)
(*    <number> == <number> as an int with <number> an optional minus sign     *)
(*                followed by a sequence of digits. This notation is in       *)
(*                int_scope (delimited with %Z).                              *)
(*      x *~ m == m times x, with m : int;                                    *)
(*                convertible to x *+ n if m is Posz n                        *)
(*                convertible to x *- n.+1 if m is Negz n.                    *)
(*       m%:~R == the image of m : int in a generic ring (:= 1 *~ m).         *)
(*    <number> == <number>%:~R with <number> an optional minus sign followed  *)
(*                by a sequence of digits. This notation is in ring_scope     *)
(*                (delimited with %R).                                        *)
(*       x ^ m == x to the m, with m : int;                                   *)
(*                convertible to x ^+ n if m is Posz n                        *)
(*                convertible to x ^- n.+1 if m is Negz n.                    *)
(*       sgz x == sign of x : R,                                              *)
(*                equals (0 : int) if and only x == 0,                        *)
(*                equals (1 : int) if x is positive                           *)
(*                and (-1 : int) otherwise.                                   *)
(*      `|m|%N == the n : nat such that `|m|%R = n%:Z, for m : int.           *)
(*  `|m - n|%N == the distance between m and n; the '-' is specialized to     *)
(*                the int type, so m and n can be either of type nat or int   *)
(*                thanks to the Posz coercion; m and n are however parsed in  *)
(*                the %N scope. The IntDist submodule provides this notation  *)
(*                and the corresponding theory independently of the rest of   *)
(*                of the int and ssralg libraries (and notations).            *)
(* Warning: due to the declaration of Posz as a coercion, two terms might be  *)
(* displayed the same while not being convertible, for instance:              *)
(* (Posz (x - y)) and (Posz x) - (Posz y) for x, y : nat.                     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope int_scope.
Declare Scope distn_scope.
Declare Scope rat_scope.

Reserved Notation "n %:Z" (at level 2, left associativity, format "n %:Z").
Reserved Notation "n = m :> 'int'"
  (at level 70, m at next level, format "n  =  m  :>  'int'").
Reserved Notation "n == m :> 'int'"
  (at level 70, m at next level, format "n  ==  m  :>  'int'").
Reserved Notation "n != m :> 'int'"
  (at level 70, m at next level, format "n  !=  m  :>  'int'").
Reserved Notation "n <> m :> 'int'"
  (at level 70, m at next level, format "n  <>  m  :>  'int'").

Import Order.TTheory GRing.Theory Num.Theory.
Delimit Scope int_scope with Z.
Local Open Scope int_scope.

(* Defining int *)
Variant int : Set := Posz of nat | Negz of nat.
(* This must be deferred to module DistInt to work around the design flaws of *)
(* the Coq module system.                                                     *)
(* Coercion Posz : nat >-> int. *)

Notation "n %:Z" := (Posz n) (only parsing) : int_scope.
Notation "n %:Z" := (Posz n) (only parsing) : ring_scope.

Notation "n = m :> 'int'"  := (@eq int n%Z m%Z) (only parsing)  : ring_scope.
Notation "n = m :> 'int'"  := (Posz n = Posz m) (only printing)  : ring_scope.
Notation "n == m :> 'int'" := ((n%Z : int) == (m%Z : int)) (only parsing)
  : ring_scope.
Notation "n == m :> 'int'" := (Posz n == Posz m) (only printing) : ring_scope.
Notation "n != m :> 'int'" := ((n%Z : int) != (m%Z : int)) (only parsing)
  : ring_scope.
Notation "n != m :> 'int'" := (Posz n != Posz m) (only printing) : ring_scope.
Notation "n <> m :> 'int'" := (not (@eq int n%Z m%Z)) (only parsing)
  : ring_scope.
Notation "n <> m :> 'int'" := (Posz n <> Posz m) (only printing) : ring_scope.

Definition parse_int (x : Number.int) : int :=
  match x with
  | Number.IntDecimal (Decimal.Pos u) => Posz (Nat.of_uint u)
  | Number.IntDecimal (Decimal.Neg u) => Negz (Nat.of_uint u).-1
  | Number.IntHexadecimal (Hexadecimal.Pos u) => Posz (Nat.of_hex_uint u)
  | Number.IntHexadecimal (Hexadecimal.Neg u) => Negz (Nat.of_hex_uint u).-1
  end.

Definition print_int (x : int) : Number.int :=
  match x with
  | Posz n => Number.IntDecimal (Decimal.Pos (Nat.to_uint n))
  | Negz n => Number.IntDecimal (Decimal.Neg (Nat.to_uint n.+1))
  end.

Number Notation int parse_int print_int : int_scope.

Definition natsum_of_int (m : int) : nat + nat :=
  match m with Posz p => inl _ p | Negz n => inr _ n end.

Definition int_of_natsum (m : nat + nat) :=
  match m with inl p => Posz p | inr n => Negz n end.

Lemma natsum_of_intK : cancel natsum_of_int int_of_natsum.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition int_eqMixin := CanEqMixin natsum_of_intK.
Definition int_countMixin := CanCountMixin natsum_of_intK.
Definition int_choiceMixin := CountChoiceMixin int_countMixin.
Canonical int_eqType := Eval hnf in EqType int int_eqMixin.
Canonical int_choiceType := Eval hnf in ChoiceType int int_choiceMixin.
Canonical int_countType := Eval hnf in CountType int int_countMixin.

Lemma eqz_nat (m n : nat) : (m%:Z == n%:Z) = (m == n). Proof. Show. Fail (cvc5_abduct 3). Admitted.

Module intZmod.
Section intZmod.

Definition addz (m n : int) :=
  match m, n with
    | Posz m', Posz n' => Posz (m' + n')
    | Negz m', Negz n' => Negz (m' + n').+1
    | Posz m', Negz n' => if n' < m' then Posz (m' - n'.+1) else Negz (n' - m')
    | Negz n', Posz m' => if n' < m' then Posz (m' - n'.+1) else Negz (n' - m')
  end.

Definition oppz m := nosimpl
  match m with
    | Posz n => if n is (n'.+1)%N then Negz n' else Posz 0
    | Negz n => Posz (n.+1)%N
  end.

Local Notation "-%Z" := (@oppz) : int_scope.
Local Notation "- x" := (oppz x) : int_scope.
Local Notation "+%Z" := (@addz) : int_scope.
Local Notation "x + y" := (addz x y) : int_scope.
Local Notation "x - y" := (x + - y) : int_scope.

Lemma PoszD : {morph Posz : m n / (m + n)%N >-> m + n}. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Local Coercion Posz : nat >-> int.

Lemma NegzE (n : nat) : Negz n = - n.+1. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma int_rect (P : int -> Type) :
  P 0 -> (forall n : nat, P n -> P (n.+1))
  -> (forall n : nat, P (- n) -> P (- (n.+1)))
  -> forall n : int, P n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition int_rec := int_rect.
Definition int_ind := int_rect.

Variant int_spec (x : int) : int -> Type :=
| ZintNull of x = 0 : int_spec x 0
| ZintPos n of x = n.+1 : int_spec x n.+1
| ZintNeg n of x = - (n.+1)%:Z : int_spec x (- n.+1).

Lemma intP x : int_spec x x. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addzC : commutative addz.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma add0z : left_id 0 addz. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma oppzK : involutive oppz. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma oppz_add : {morph oppz : m n / m + n}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma add1Pz (n : int) : 1 + (n - 1) = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma subSz1 (n : int) : 1 + n - 1 = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addSnz (m : nat) (n : int) : (m.+1%N) + n = 1 + (m + n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addSz (m n : int) : (1 + m) + n = 1 + (m + n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addPz (m n : int) : (m - 1) + n = (m + n) - 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addzA : associative addz.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addNz : left_inverse (0:int) oppz addz. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma predn_int (n : nat) : 0 < n -> n.-1%:Z = n - 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition Mixin := ZmodMixin addzA addzC add0z addNz.

End intZmod.
End intZmod.

Canonical int_ZmodType := ZmodType int intZmod.Mixin.

Local Open Scope ring_scope.

Section intZmoduleTheory.

Local Coercion Posz : nat >-> int.

Lemma PoszD : {morph Posz : n m / (n + m)%N >-> n + m}. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma NegzE (n : nat) : Negz n = -(n.+1)%:Z. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma int_rect (P : int -> Type) :
  P 0 -> (forall n : nat, P n -> P (n.+1)%N)
  -> (forall n : nat, P (- (n%:Z)) -> P (- (n.+1%N%:Z)))
  -> forall n : int, P n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition int_rec := int_rect.
Definition int_ind := int_rect.

Variant int_spec (x : int) : int -> Type :=
| ZintNull : int_spec x 0
| ZintPos n : int_spec x n.+1
| ZintNeg n : int_spec x (- (n.+1)%:Z).

Lemma intP x : int_spec x x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition oppz_add := (@opprD [zmodType of int]).

Lemma subzn (m n : nat) : (n <= m)%N -> m%:Z - n%:Z = (m - n)%N.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma subzSS (m n : nat) : m.+1%:Z - n.+1%:Z = m%:Z - n%:Z.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End intZmoduleTheory.

Module intRing.
Section intRing.

Local Coercion Posz : nat >-> int.

Definition mulz (m n : int) :=
  match m, n with
    | Posz m', Posz n' => (m' * n')%N%:Z
    | Negz m', Negz n' => (m'.+1%N * n'.+1%N)%N%:Z
    | Posz m', Negz n' => - (m' * (n'.+1%N))%N%:Z
    | Negz n', Posz m' => - (m' * (n'.+1%N))%N%:Z
  end.

Local Notation "*%Z" := (@mulz) : int_scope.
Local Notation "x * y" := (mulz x y) : int_scope.

Lemma mul0z : left_zero 0 *%Z.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulzC : commutative mulz.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulz0 : right_zero 0 *%Z.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulzN (m n : int) : (m * (- n))%Z = - (m * n)%Z.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulNz (m n : int) : ((- m) * n)%Z = - (m * n)%Z.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulzA : associative mulz.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mul1z : left_id 1%Z mulz.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulzS (x : int) (n : nat) : (x * n.+1%:Z)%Z = x + (x * n)%Z.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulz_addl : left_distributive mulz (+%R).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nonzero1z : 1%Z != 0. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition comMixin := ComRingMixin mulzA mulzC mul1z mulz_addl nonzero1z.

End intRing.
End intRing.

Canonical int_Ring := Eval hnf in RingType int intRing.comMixin.
Canonical int_comRing := Eval hnf in ComRingType int intRing.mulzC.

Section intRingTheory.

Implicit Types m n : int.
Local Coercion Posz : nat >-> int.

Lemma PoszM : {morph Posz : n m / (n * m)%N >-> n * m}. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma intS (n : nat) : n.+1%:Z = 1 + n%:Z. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma predn_int (n : nat) : (0 < n)%N -> n.-1%:Z = n%:Z - 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End intRingTheory.

Module intUnitRing.
Section intUnitRing.
Implicit Types m n : int.
Local Coercion Posz : nat >-> int.

Definition unitz := [qualify a n : int | (n == 1) || (n == -1)].
Definition invz n : int := n.

Lemma mulVz : {in unitz, left_inverse 1%R invz *%R}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulzn_eq1 m (n : nat) : (m * n == 1) = (m == 1) && (n == 1%N).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma unitzPl m n : n * m = 1 -> m \is a unitz.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma invz_out : {in [predC unitz], invz =1 id}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma idomain_axiomz m n : m * n = 0 -> (m == 0) || (n == 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition comMixin := ComUnitRingMixin mulVz unitzPl invz_out.

End intUnitRing.
End intUnitRing.

Canonical int_unitRingType :=
  Eval hnf in UnitRingType int intUnitRing.comMixin.
Canonical int_comUnitRing := Eval hnf in [comUnitRingType of int].
Canonical int_idomainType :=
  Eval hnf in IdomainType int intUnitRing.idomain_axiomz.

Canonical int_countZmodType := [countZmodType of int].
Canonical int_countRingType := [countRingType of int].
Canonical int_countComRingType := [countComRingType of int].
Canonical int_countUnitRingType := [countUnitRingType of int].
Canonical int_countComUnitRingType := [countComUnitRingType of int].
Canonical int_countIdomainType := [countIdomainType of int].

Definition absz m := match m with Posz p => p | Negz n => n.+1 end.
Notation "m - n" :=
  (@GRing.add int_ZmodType m%N (@GRing.opp int_ZmodType n%N)) : distn_scope.
Arguments absz m%distn_scope.
Local Notation "`| m |" := (absz m) : nat_scope.

Module intOrdered.
Section intOrdered.
Implicit Types m n p : int.
Local Coercion Posz : nat >-> int.

Local Notation normz m := (absz m)%:Z.

Definition lez m n :=
  match m, n with
    | Posz m', Posz n' => (m' <= n')%N
    | Posz m', Negz n' => false
    | Negz m', Posz n' => true
    | Negz m', Negz n' => (n' <= m')%N
  end.

Definition ltz m n :=
  match m, n with
    | Posz m', Posz n' => (m' < n')%N
    | Posz m', Negz n' => false
    | Negz m', Posz n' => true
    | Negz m', Negz n' => (n' < m')%N
  end.

Fact lez_add m n : lez 0 m -> lez 0 n -> lez 0 (m + n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact lez_mul m n : lez 0 m -> lez 0 n -> lez 0 (m * n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact lez_anti m : lez 0 m -> lez m 0 -> m = 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma subz_ge0 m n : lez 0 (n - m) = lez m n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact lez_total m n : lez m n || lez n m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact normzN m : normz (- m) = normz m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact gez0_norm m : lez 0 m -> normz m = m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact ltz_def m n : (ltz m n) = (n != m) && (lez m n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition Mixin : realLeMixin int_idomainType :=
  RealLeMixin
    lez_add lez_mul lez_anti subz_ge0 (lez_total 0) normzN gez0_norm ltz_def.

End intOrdered.
End intOrdered.

Canonical int_porderType := POrderType ring_display int intOrdered.Mixin.
Canonical int_latticeType := LatticeType int intOrdered.Mixin.
Canonical int_distrLatticeType := DistrLatticeType int intOrdered.Mixin.
Canonical int_orderType := OrderType int intOrdered.lez_total.
Canonical int_numDomainType := NumDomainType int intOrdered.Mixin.
Canonical int_normedZmodType := NormedZmodType int int intOrdered.Mixin.
Canonical int_realDomainType := [realDomainType of int].

Section intOrderedTheory.

Local Coercion Posz : nat >-> int.
Implicit Types m n p : nat.
Implicit Types x y z : int.

Lemma lez_nat m n : (m <= n :> int) = (m <= n)%N. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltz_nat  m n : (m < n :> int) = (m < n)%N.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition ltez_nat := (lez_nat, ltz_nat).

Lemma leNz_nat m n : (- m%:Z <= n). Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltNz_nat m n : (- m%:Z < n) = (m != 0%N) || (n != 0%N).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition lteNz_nat := (leNz_nat, ltNz_nat).

Lemma lezN_nat m n : (m%:Z <= - n%:Z) = (m == 0%N) && (n == 0%N).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltzN_nat m n : (m%:Z < - n%:Z) = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma le0z_nat n : 0 <= n :> int. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lez0_nat n : n <= 0 :> int = (n == 0%N :> nat). Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition ltezN_nat := (lezN_nat, ltzN_nat).
Definition ltez_natE := (ltez_nat, lteNz_nat, ltezN_nat, le0z_nat, lez0_nat).

Lemma gtz0_ge1 x : (0 < x) = (1 <= x). Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lez_add1r x y : (1 + x <= y) = (x < y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lez_addr1 x y : (x + 1 <= y) = (x < y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltz_add1r x y : (x < 1 + y) = (x <= y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltz_addr1 x y : (x < y + 1) = (x <= y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End intOrderedTheory.

Bind Scope ring_scope with int.

(* definition of intmul *)
Definition intmul (R : zmodType) (x : R) (n : int) := nosimpl
  match n with
    | Posz n => (x *+ n)%R
    | Negz n => (x *- (n.+1))%R
  end.

Notation "*~%R" := (@intmul _) (at level 0, format " *~%R") : fun_scope.
Notation "x *~ n" := (intmul x n)
  (at level 40, left associativity, format "x  *~  n") : ring_scope.
Notation intr := ( *~%R 1).
Notation "n %:~R" := (1 *~ n)%R
  (at level 2, left associativity, format "n %:~R")  : ring_scope.

Lemma pmulrn (R : zmodType) (x : R) (n : nat) : x *+ n = x *~ n%:Z.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nmulrn (R : zmodType) (x : R) (n : nat) : x *- n = x *~ - n%:Z.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Variant Iintmul := IIntmul : Ione -> int -> Iintmul.

Definition parse (x : Number.int) : Iintmul :=
  let i :=
    match x with
    | Number.IntDecimal (Decimal.Pos u) => Posz (Nat.of_uint u)
    | Number.IntDecimal (Decimal.Neg u) => Negz (Nat.of_uint u).-1
    | Number.IntHexadecimal (Hexadecimal.Pos u) => Posz (Nat.of_hex_uint u)
    | Number.IntHexadecimal (Hexadecimal.Neg u) => Negz (Nat.of_hex_uint u).-1
    end in
  IIntmul IOne i.

Definition print (x : Iintmul) : Number.int :=
  match x with
  | IIntmul IOne (Posz n) => Number.IntDecimal (Decimal.Pos (Nat.to_uint n))
  | IIntmul IOne (Negz n) => Number.IntDecimal (Decimal.Neg (Nat.to_uint n.+1))
  end.

Arguments GRing.one {R}.
Set Warnings "-via-type-remapping,-via-type-mismatch".
Number Notation Idummy_placeholder parse print (via Iintmul
  mapping [[intmul] => IIntmul, [GRing.one] => IOne])
  : ring_scope.
Set Warnings "via-type-remapping,via-type-mismatch".
Arguments GRing.one : clear implicits.

Section ZintLmod.

Definition zmodule (M : Type) : Type := M.
Local Notation "M ^z" := (zmodule M) (at level 2, format "M ^z") : type_scope.
Local Coercion Posz : nat >-> int.

Variable M : zmodType.

Implicit Types m n : int.
Implicit Types x y z : M.

Fact mulrzA_C m n x : (x *~ n) *~ m = x *~ (m * n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact mulrzAC m n x : (x *~ n) *~ m = (x *~ m) *~ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact mulr1z (x : M) : x *~ 1 = x. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact mulrzDr m : {morph ( *~%R^~ m : M -> M) : x y / x + y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulrzBl_nat (m n : nat) x : x *~ (m%:Z - n%:Z) = x *~ m - x *~ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact mulrzDl x : {morph *~%R x : m n / m + n}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition Mint_LmodMixin :=
  @LmodMixin _ [zmodType of M] (fun n x => x *~ n)
   mulrzA_C mulr1z mulrzDr mulrzDl.
Canonical Mint_LmodType := LmodType int M^z Mint_LmodMixin.

Lemma scalezrE n x : n *: (x : M^z) = x *~ n. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulrzA x m n :  x *~ (m * n) = x *~ m *~ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulr0z x : x *~ 0 = 0. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mul0rz n : 0 *~ n = 0 :> M.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulrNz x n : x *~ (- n) = - (x *~ n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulrN1z x : x *~ (- 1) = - x. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulNrz x n : (- x) *~ n = - (x *~ n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulrzBr x m n : x *~ (m - n) = x *~ m - x *~ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulrzBl x y n : (x - y) *~ n = x *~ n - y *~ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulrz_nat (n : nat) x : x *~ n%:R = x *+ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulrz_sumr : forall x I r (P : pred I) F,
  x *~ (\sum_(i <- r | P i) F i) = \sum_(i <- r | P i) x *~ F i.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulrz_suml : forall n I r (P : pred I) (F : I -> M),
  (\sum_(i <- r | P i) F i) *~ n= \sum_(i <- r | P i) F i *~ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Canonical intmul_additive x := Additive (@mulrzBr x).

End ZintLmod.

Lemma ffunMzE (I : finType) (M : zmodType) (f : {ffun I -> M}) z x :
  (f *~ z) x = f x *~ z.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma intz (n : int) : n%:~R = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma natz (n : nat) : n%:R = n%:Z :> int.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Section RintMod.

Local Coercion Posz : nat >-> int.
Variable R : ringType.

Implicit Types m n : int.
Implicit Types x y z : R.

Lemma mulrzAl n x y : (x *~ n) * y = (x * y) *~ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulrzAr n x y : x * (y *~ n) = (x * y) *~ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulrzl x n : n%:~R * x = x *~ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulrzr x n : x * n%:~R = x *~ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulNrNz n x : (-x) *~ (-n) = x *~ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulrbz x (b : bool) : x *~ b = (if b then x else 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma intrD m n : (m + n)%:~R = m%:~R + n%:~R :> R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma intrM m n : (m * n)%:~R = m%:~R * n%:~R :> R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma intmul1_is_rmorphism : rmorphism ( *~%R (1 : R)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Canonical intmul1_rmorphism := RMorphism intmul1_is_rmorphism.

Lemma mulr2z n : n *~ 2 = n + n. Proof. Show. Fail (cvc5_abduct 3). Admitted.

End RintMod.

Lemma mulrzz m n : m *~ n = m * n. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulz2 n : n * 2%:Z = n + n. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mul2z n : 2%:Z * n = n + n. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Section LMod.

Variable R : ringType.
Variable V : (lmodType R).
Local Coercion Posz : nat >-> int.

Implicit Types m n : int.
Implicit Types x y z : R.
Implicit Types u v w : V.

Lemma scaler_int n v : n%:~R *: v = v *~ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma scalerMzl a v n : (a *: v) *~ n = (a *~ n) *: v.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma scalerMzr a v n : (a *: v) *~ n = a *: (v *~ n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End LMod.

Lemma mulrz_int (M : zmodType) (n : int) (x : M) : x *~ n%:~R = x *~ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Section MorphTheory.
Local Coercion Posz : nat >-> int.
Section Additive.
Variables (U V : zmodType) (f : {additive U -> V}).

Lemma raddfMz n : {morph f : x / x *~ n}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End Additive.

Section Multiplicative.

Variables (R S : ringType) (f : {rmorphism R -> S}).

Lemma rmorphMz : forall n, {morph f : x / x *~ n}. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rmorph_int : forall n, f n%:~R = n%:~R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End Multiplicative.

Section Linear.

Variable R : ringType.
Variables (U V : lmodType R) (f : {linear U -> V}).

Lemma linearMn : forall n, {morph f : x / x *~ n}. Proof. Show. Fail (cvc5_abduct 3). Admitted.

End Linear.

Lemma raddf_int_scalable (aV rV : lmodType int) (f : {additive aV -> rV}) :
  scalable f.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Section Zintmul1rMorph.

Variable R : ringType.

Lemma commrMz (x y : R) n : GRing.comm x y -> GRing.comm x (y *~ n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma commr_int (x : R) n : GRing.comm x n%:~R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End Zintmul1rMorph.

Section ZintBigMorphism.

Variable R : ringType.

Lemma sumMz : forall I r (P : pred I) F,
 (\sum_(i <- r | P i) F i)%N%:~R = \sum_(i <- r | P i) ((F i)%:~R) :> R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma prodMz : forall I r (P : pred I) F,
 (\prod_(i <- r | P i) F i)%N%:~R = \prod_(i <- r | P i) ((F i)%:~R) :> R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End ZintBigMorphism.

Section Frobenius.

Variable R : ringType.
Implicit Types x y : R.

Variable p : nat.
Hypothesis charFp : p \in [char R].

Local Notation "x ^f" := (Frobenius_aut charFp x).

Lemma Frobenius_autMz x n : (x *~ n)^f = x^f *~ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Frobenius_aut_int n : (n%:~R)^f = n%:~R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End Frobenius.

Section NumMorphism.

Section PO.

Variables (R : numDomainType).

Implicit Types n m : int.
Implicit Types x y : R.

Lemma rmorphzP (f : {rmorphism int -> R}) : f =1 ( *~%R 1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* intmul and ler/ltr *)
Lemma ler_pmulz2r n (hn : 0 < n) : {mono *~%R^~ n :x y / x <= y :> R}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_pmulz2r n (hn : 0 < n) : {mono *~%R^~ n : x y / x < y :> R}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_nmulz2r n (hn : n < 0) : {mono *~%R^~ n : x y /~ x <= y :> R}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_nmulz2r n (hn : n < 0) : {mono *~%R^~ n : x y /~ x < y :> R}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_wpmulz2r n (hn : 0 <= n) : {homo *~%R^~ n : x y / x <= y :> R}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_wnmulz2r n (hn : n <= 0) : {homo *~%R^~ n : x y /~ x <= y :> R}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulrz_ge0 x n (x0 : 0 <= x) (n0 : 0 <= n) : 0 <= x *~ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulrz_le0 x n (x0 : x <= 0) (n0 : n <= 0) : 0 <= x *~ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulrz_ge0_le0 x n (x0 : 0 <= x) (n0 : n <= 0) : x *~ n <= 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulrz_le0_ge0 x n (x0 : x <= 0) (n0 : 0 <= n) : x *~ n <= 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pmulrz_lgt0 x n (n0 : 0 < n) : 0 < x *~ n = (0 < x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nmulrz_lgt0 x n (n0 : n < 0) : 0 < x *~ n = (x < 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pmulrz_llt0 x n (n0 : 0 < n) : x *~ n < 0 = (x < 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nmulrz_llt0 x n (n0 : n < 0) : x *~ n < 0 = (0 < x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pmulrz_lge0 x n (n0 : 0 < n) : 0 <= x *~ n = (0 <= x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nmulrz_lge0 x n (n0 : n < 0) : 0 <= x *~ n = (x <= 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pmulrz_lle0 x n (n0 : 0 < n) : x *~ n <= 0 = (x <= 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nmulrz_lle0 x n (n0 : n < 0) : x *~ n <= 0 = (0 <= x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_wpmulz2l x (hx : 0 <= x) : {homo *~%R x : x y / x <= y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_wnmulz2l x (hx : x <= 0) : {homo *~%R x : x y /~ x <= y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_pmulz2l x (hx : 0 < x) : {mono *~%R x : x y / x <= y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_nmulz2l x (hx : x < 0) : {mono *~%R x : x y /~ x <= y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_pmulz2l x (hx : 0 < x) : {mono *~%R x : x y / x < y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_nmulz2l x (hx : x < 0) : {mono *~%R x : x y /~ x < y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pmulrz_rgt0 x n (x0 : 0 < x) : 0 < x *~ n = (0 < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nmulrz_rgt0 x n (x0 : x < 0) : 0 < x *~ n = (n < 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pmulrz_rlt0 x n (x0 : 0 < x) : x *~ n < 0 = (n < 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nmulrz_rlt0 x n (x0 : x < 0) : x *~ n < 0 = (0 < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pmulrz_rge0 x n (x0 : 0 < x) : 0 <= x *~ n = (0 <= n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nmulrz_rge0 x n (x0 : x < 0) : 0 <= x *~ n = (n <= 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pmulrz_rle0 x n (x0 : 0 < x) : x *~ n <= 0 = (n <= 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nmulrz_rle0 x n (x0 : x < 0) : x *~ n <= 0 = (0 <= n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulrIz x (hx : x != 0) : injective ( *~%R x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_int m n : (m%:~R <= n%:~R :> R) = (m <= n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_int m n : (m%:~R < n%:~R :> R) = (m < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma eqr_int m n : (m%:~R == n%:~R :> R) = (m == n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler0z n : (0 <= n%:~R :> R) = (0 <= n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr0z n : (0 < n%:~R :> R) = (0 < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lerz0 n : (n%:~R <= 0 :> R) = (n <= 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltrz0 n : (n%:~R < 0 :> R) = (n < 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler1z (n : int) : (1 <= n%:~R :> R) = (1 <= n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr1z (n : int) : (1 < n%:~R :> R) = (1 < n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lerz1 n : (n%:~R <= 1 :> R) = (n <= 1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltrz1 n : (n%:~R < 1 :> R) = (n < 1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma intr_eq0 n : (n%:~R == 0 :> R) = (n == 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulrz_eq0 x n : (x *~ n == 0) = ((n == 0) || (x == 0)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulrz_neq0 x n : x *~ n != 0 = ((n != 0) && (x != 0)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma realz n : (n%:~R : R) \in Num.real.
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Hint Resolve realz : core.

Definition intr_inj := @mulrIz 1 (oner_neq0 R).

End PO.

End NumMorphism.

End MorphTheory.

Arguments intr_inj {R} [x1 x2].

Definition exprz (R : unitRingType) (x : R) (n : int) := nosimpl
  match n with
    | Posz n => x ^+ n
    | Negz n => x ^- (n.+1)
  end.

Notation "x ^ n" := (exprz x n) : ring_scope.

Section ExprzUnitRing.

Variable R : unitRingType.
Implicit Types x y : R.
Implicit Types m n : int.
Local Coercion Posz : nat >-> int.

Lemma exprnP x (n : nat) : x ^+ n = x ^ n. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exprnN x (n : nat) : x ^- n = x ^ -n%:Z.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma expr0z x : x ^ 0 = 1. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma expr1z x : x ^ 1 = x. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exprN1 x : x ^ (-1) = x^-1. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma invr_expz x n : (x ^ n)^-1 = x ^ (- n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exprz_inv x n : (x^-1) ^ n = x ^ (- n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exp1rz n : 1 ^ n = 1 :> R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exprSz x (n : nat) : x ^ n.+1 = x * x ^ n. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exprSzr x (n : nat) : x ^ n.+1 = x ^ n * x. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact exprzD_nat x (m n : nat) : x ^ (m%:Z + n) = x ^ m * x ^ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact exprzD_Nnat x (m n : nat) : x ^ (-m%:Z + -n%:Z) = x ^ (-m%:Z) * x ^ (-n%:Z).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exprzD_ss x m n : (0 <= m) && (0 <= n) || (m <= 0) && (n <= 0)
  ->  x ^ (m + n) = x ^ m * x ^ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exp0rz n : 0 ^ n = (n == 0)%:~R :> R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma commrXz x y n : GRing.comm x y -> GRing.comm x (y ^ n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exprMz_comm x y n : x \is a GRing.unit -> y \is a GRing.unit ->
  GRing.comm x y -> (x * y) ^ n = x ^ n * y ^ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma commrXz_wmulls x y n :
  0 <= n -> GRing.comm x y -> (x * y) ^ n = x ^ n * y ^ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma unitrXz x n (ux : x \is a GRing.unit) : x ^ n \is a GRing.unit.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exprzDr x (ux : x \is a GRing.unit) m n : x ^ (m + n) = x ^ m * x ^ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exprz_exp x m n : (x ^ m) ^ n = (x ^ (m * n)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exprzAC x m n : (x ^ m) ^ n = (x ^ n) ^ m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exprz_out x n (nux : x \isn't a GRing.unit) (hn : 0 <= n) :
  x ^ (- n) = x ^ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End ExprzUnitRing.

Section Exprz_Zint_UnitRing.

Variable R : unitRingType.
Implicit Types x y : R.
Implicit Types m n : int.
Local Coercion Posz : nat >-> int.

Lemma exprz_pmulzl x m n : 0 <= n -> (x *~ m) ^ n = x ^ n *~ (m ^ n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exprz_pintl m n (hn : 0 <= n) : m%:~R ^ n = (m ^ n)%:~R :> R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exprzMzl x m n (ux : x \is a GRing.unit) (um : m%:~R \is a @GRing.unit R):
   (x *~ m) ^ n = (m%:~R ^ n) * x ^ n :> R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma expNrz x n : (- x) ^ n = (-1) ^ n * x ^ n :> R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma unitr_n0expz x n :
  n != 0 -> (x ^ n \is a GRing.unit) = (x \is a GRing.unit).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma intrV (n : int) :
  n \in [:: 0; 1; -1] -> n%:~R ^-1 = n%:~R :> R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rmorphXz (R' : unitRingType) (f : {rmorphism R -> R'}) n :
  {in GRing.unit, {morph f : x / x ^ n}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End Exprz_Zint_UnitRing.

Section ExprzIdomain.

Variable R : idomainType.
Implicit Types x y : R.
Implicit Types m n : int.
Local Coercion Posz : nat >-> int.

Lemma expfz_eq0 x n : (x ^ n == 0) = (n != 0) && (x == 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma expfz_neq0 x n : x != 0 -> x ^ n != 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exprzMl x y n (ux : x \is a GRing.unit) (uy : y \is a GRing.unit) :
  (x * y) ^ n = x ^ n * y ^ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma expfV (x : R) (i : int) : (x ^ i) ^-1 = (x ^-1) ^ i.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End ExprzIdomain.

Section ExprzField.

Variable F : fieldType.
Implicit Types x y : F.
Implicit Types m n : int.
Local Coercion Posz : nat >-> int.

Lemma expfzDr x m n : x != 0 -> x ^ (m + n) = x ^ m * x ^ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma expfz_n0addr x m n : m + n != 0 -> x ^ (m + n) = x ^ m * x ^ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma expfzMl x y n : (x * y) ^ n = x ^ n * y ^ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma fmorphXz (R : unitRingType) (f : {rmorphism F -> R}) n :
  {morph f : x / x ^ n}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End ExprzField.

Section ExprzOrder.

Variable R : realFieldType.
Implicit Types x y : R.
Implicit Types m n : int.
Local Coercion Posz : nat >-> int.

(* ler and exprz *)
Lemma exprz_ge0 n x (hx : 0 <= x) : (0 <= x ^ n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exprz_gt0 n x (hx : 0 < x) : (0 < x ^ n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition exprz_gte0 := (exprz_ge0, exprz_gt0).

Lemma ler_wpiexpz2l x (x0 : 0 <= x) (x1 : x <= 1) :
  {in >= 0 &, {homo (exprz x) : x y /~ x <= y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_wniexpz2l x (x0 : 0 <= x) (x1 : x <= 1) :
  {in < 0 &, {homo (exprz x) : x y /~ x <= y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact ler_wpeexpz2l x (x1 : 1 <= x) :
  {in >= 0 &, {homo (exprz x) : x y / x <= y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact ler_wneexpz2l x (x1 : 1 <= x) :
  {in <= 0 &, {homo (exprz x) : x y / x <= y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_weexpz2l x (x1 : 1 <= x) : {homo (exprz x) : x y / x <= y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pexprz_eq1 x n (x0 : 0 <= x) : (x ^ n == 1) = ((n == 0) || (x == 1)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ieexprIz x (x0 : 0 < x) (nx1 : x != 1) : injective (exprz x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_piexpz2l x (x0 : 0 < x) (x1 : x < 1) :
  {in >= 0 &, {mono (exprz x) : x y /~ x <= y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_piexpz2l x (x0 : 0 < x) (x1 : x < 1) :
  {in >= 0 &, {mono (exprz x) : x y /~ x < y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_niexpz2l x (x0 : 0 < x) (x1 : x < 1) :
  {in < 0 &, {mono (exprz x) : x y /~ x <= y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_niexpz2l x (x0 : 0 < x) (x1 : x < 1) :
  {in < 0 &, {mono (exprz x) : x y /~ x < y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_eexpz2l x (x1 : 1 < x) : {mono (exprz x) : x y / x <= y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_eexpz2l x (x1 : 1 < x) : {mono (exprz x) : x y / x < y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_wpexpz2r n (hn : 0 <= n) :
{in >= 0 & , {homo ((@exprz R)^~ n) : x y / x <= y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_wnexpz2r n (hn : n <= 0) :
{in > 0 & , {homo ((@exprz R)^~ n) : x y /~ x <= y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pexpIrz n (n0 : n != 0) : {in >= 0 &, injective ((@exprz R)^~ n)}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nexpIrz n (n0 : n != 0) : {in <= 0 &, injective ((@exprz R)^~ n)}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_pexpz2r n (hn : 0 < n) :
  {in >= 0 & , {mono ((@exprz R)^~ n) : x y / x <= y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_pexpz2r n (hn : 0 < n) :
  {in >= 0 & , {mono ((@exprz R)^~ n) : x y / x < y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_nexpz2r n (hn : n < 0) :
  {in > 0 & , {mono ((@exprz R)^~ n) : x y /~ x <= y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_nexpz2r n (hn : n < 0) :
  {in > 0 & , {mono ((@exprz R)^~ n) : x y /~ x < y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma eqr_expz2 n x y : n != 0 -> 0 <= x -> 0 <= y ->
  (x ^ n == y ^ n) = (x == y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End ExprzOrder.

Local Notation sgr := Num.sg.

Section Sgz.

Variable R : numDomainType.
Implicit Types x y z : R.
Implicit Types m n p : int.
Local Coercion Posz : nat >-> int.

Definition sgz x : int := if x == 0 then 0 else if x < 0 then -1 else 1.

Lemma sgz_def x : sgz x = (-1) ^+ (x < 0)%R *+ (x != 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgrEz x : sgr x = (sgz x)%:~R. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gtr0_sgz x : 0 < x -> sgz x = 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr0_sgz x : x < 0 -> sgz x = -1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgz0 : sgz (0 : R) = 0. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma sgz1 : sgz (1 : R) = 1. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma sgzN1 : sgz (-1 : R) = -1. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition sgzE := (sgz0, sgz1, sgzN1).

Lemma sgz_sgr x : sgz (sgr x) = sgz x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normr_sgz x : `|sgz x| = (x != 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normr_sg x : `|sgr x| = (x != 0)%:~R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End Sgz.

Section MoreSgz.

Variable R : numDomainType.

Lemma sgz_int m : sgz (m%:~R : R) = sgz m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgrz (n : int) : sgr n = sgz n. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma intr_sg m : (sgr m)%:~R = sgr (m%:~R) :> R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgz_id (x : R) : sgz (sgz x) = sgz x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End MoreSgz.

Section SgzReal.

Variable R : realDomainType.
Implicit Types x y z : R.
Implicit Types m n p : int.
Local Coercion Posz : nat >-> int.

Lemma sgz_cp0 x :
  ((sgz x == 1) = (0 < x)) *
  ((sgz x == -1) = (x < 0)) *
  ((sgz x == 0) = (x == 0)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Variant sgz_val x : bool -> bool -> bool -> bool -> bool -> bool
  -> bool -> bool -> bool -> bool -> bool -> bool
  -> bool -> bool -> bool -> bool -> bool -> bool
  -> R -> R -> int -> Set :=
  | SgzNull of x = 0 : sgz_val x true true true true false false
    true false false true false false true false false true false false 0 0 0
  | SgzPos of x > 0 : sgz_val x false false true false false true
    false false true false false true false false true false false true x 1 1
  | SgzNeg of x < 0 : sgz_val x false true false false true false
    false true false false true false false true false false true false (-x) (-1) (-1).

Lemma sgzP x :
  sgz_val x (0 == x) (x <= 0) (0 <= x) (x == 0) (x < 0) (0 < x)
  (0 == sgr x) (-1 == sgr x) (1 == sgr x)
  (sgr x == 0)  (sgr x == -1) (sgr x == 1)
  (0 == sgz x) (-1 == sgz x) (1 == sgz x)
  (sgz x == 0)  (sgz x == -1) (sgz x == 1) `|x| (sgr x) (sgz x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgzN x : sgz (- x) = - sgz x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulz_sg x : sgz x * sgz x = (x != 0)%:~R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulz_sg_eq1 x y : (sgz x * sgz y == 1) = (x != 0) && (sgz x == sgz y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulz_sg_eqN1 x y : (sgz x * sgz y == -1) = (x != 0) && (sgz x == - sgz y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Lemma muls_eqA x y z : sgr x != 0 -> *)
(*   (sgr y * sgr z == sgr x) = ((sgr y * sgr x == sgr z) && (sgr z != 0)). *)
(* Proof. Show. Fail (cvc5_abduct 3). Admitted. *)

Lemma sgzM x y : sgz (x * y) = sgz x  * sgz y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgzX (n : nat) x : sgz (x ^+ n) = (sgz x) ^+ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgz_eq0 x : (sgz x == 0) = (x == 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgz_odd (n : nat) x : x != 0 -> (sgz x) ^+ n = (sgz x) ^+ (odd n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgz_gt0 x : (sgz x > 0) = (x > 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgz_lt0 x : (sgz x < 0) = (x < 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgz_ge0 x : (sgz x >= 0) = (x >= 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgz_le0 x : (sgz x <= 0) = (x <= 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgz_smul x y : sgz (y *~ (sgz x)) = (sgz x) * (sgz y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgrMz m x : sgr (x *~ m) = sgr x *~ sgr m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End SgzReal.

Lemma sgz_eq (R R' : realDomainType) (x : R) (y : R') :
  (sgz x == sgz y) = ((x == 0) == (y == 0)) && ((0 < x) == (0 < y)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma intr_sign (R : ringType) s : ((-1) ^+ s)%:~R = (-1) ^+ s :> R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Section Absz.

Implicit Types m n p : int.
Open Scope nat_scope.
Local Coercion Posz : nat >-> int.

Lemma absz_nat (n : nat) : `|n| = n. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma abszE (m : int) : `|m| = `|m|%R :> int. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma absz0 : `|0%R| = 0. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma abszN m : `|- m| = `|m|. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma absz_eq0 m : (`|m| == 0) = (m == 0%R). Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma absz_gt0 m : (`|m| > 0) = (m != 0%R). Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma absz1 : `|1%R| = 1. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma abszN1 : `|-1%R| = 1. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma absz_id m : `|(`|m|)| = `|m|. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma abszM m1 m2 : `|(m1 * m2)%R| = `|m1| * `|m2|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma abszX (n : nat) m : `|m ^+ n| = `|m| ^ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma absz_sg m : `|sgr m| = (m != 0%R). Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gez0_abs m : (0 <= m)%R -> `|m| = m :> int.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gtz0_abs m : (0 < m)%R -> `|m| = m :> int.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lez0_abs m : (m <= 0)%R -> `|m| = - m :> int.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltz0_abs m : (m < 0)%R -> `|m| = - m :> int.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lez_abs m : m <= `|m|%N :> int.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma absz_sign s : `|(-1) ^+ s| = 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma abszMsign s m : `|((-1) ^+ s * m)%R| = `|m|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulz_sign_abs m : ((-1) ^+ (m < 0)%R * `|m|%:Z)%R = m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulz_Nsign_abs m : ((-1) ^+ (0 < m)%R * `|m|%:Z)%R = - m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma intEsign  m : m = ((-1) ^+ (m < 0)%R * `|m|%:Z)%R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma abszEsign m : `|m|%:Z = ((-1) ^+ (m < 0)%R * m)%R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma intEsg m : m = (sgz m * `|m|%:Z)%R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma abszEsg m : (`|m|%:Z = sgz m * m)%R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End Absz.

Section MoreAbsz.
Variable R : numDomainType.
Implicit Type i : int.

Lemma mulr_absz (x : R) i : x *+ `|i| = x *~ `|i|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma natr_absz i : `|i|%:R = `|i|%:~R :> R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End MoreAbsz.

Module Export IntDist.

Notation "m - n" :=
  (@GRing.add int_ZmodType m%N (@GRing.opp int_ZmodType n%N)) : distn_scope.
Arguments absz m%distn_scope.
Notation "`| m |" := (absz m) : nat_scope.
Coercion Posz : nat >-> int.

Section Distn.

Open Scope nat_scope.
Implicit Type m : int.
Implicit Types n d : nat.

Lemma distnC m1 m2 : `|m1 - m2| = `|m2 - m1|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma distnDl d n1 n2 : `|d + n1 - (d + n2)| = `|n1 - n2|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma distnDr d n1 n2 : `|n1 + d - (n2 + d)| = `|n1 - n2|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma distnEr n1 n2 : n1 <= n2 -> `|n1 - n2| = n2 - n1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma distnEl n1 n2 : n2 <= n1 -> `|n1 - n2| = n1 - n2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma distn0 n : `|n - 0| = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma dist0n n : `|0 - n| = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma distnn m : `|m - m| = 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma distn_eq0 n1 n2 : (`|n1 - n2| == 0) = (n1 == n2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma distnS n : `|n - n.+1| = 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma distSn n : `|n.+1 - n| = 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma distn_eq1 n1 n2 :
  (`|n1 - n2| == 1) = (if n1 < n2 then n1.+1 == n2 else n1 == n2.+1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leq_add_dist  m1 m2 m3 : `|m1 - m3| <= `|m1 - m2| + `|m2 - m3|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Most of this Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leqif_add_dist n1 n2 n3 :
  `|n1 - n3| <= `|n1 - n2| + `|n2 - n3|
             ?= iff (n1 <= n2 <= n3) || (n3 <= n2 <= n1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrn_dist n1 n2 : `|n1 - n2| ^ 2 + 2 * (n1 * n2) = n1 ^ 2 + n2 ^ 2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End Distn.

End IntDist.

Section NormInt.

Variable R : numDomainType.

Lemma intr_norm m : `|m|%:~R = `|m%:~R : R|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normrMz m (x : R) : `|x *~ m| = `|x| *~ `|m|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma expN1r (i : int) : (-1 : R) ^ i = (-1) ^+ `|i|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End NormInt.

Section PolyZintRing.

Variable R : ringType.
Implicit Types x y z: R.
Implicit Types m n : int.
Implicit Types i j k : nat.
Implicit Types p q r : {poly R}.

Lemma coefMrz p n i : (p *~ n)`_i = (p`_i *~ n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma polyCMz n : {morph (@polyC R) : c / c *~ n}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma hornerMz n p x : (p *~ n).[x] = p.[x] *~ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma horner_int n x : (n%:~R : {poly R}).[x] = n%:~R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma derivMz n p : (p *~ n)^`() = p^`() *~ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulpz p n : p *~ n = n%:~R *: p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End PolyZintRing.

Section ZnatPred.

Definition Znat := [qualify a n : int | 0 <= n].
Fact Znat_key : pred_key Znat. by []. Qed.
Canonical Znat_keyd := KeyedQualifier Znat_key.

Lemma Znat_def n : (n \is a Znat) = (0 <= n). Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Znat_semiring_closed : semiring_closed Znat.
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Canonical Znat_addrPred := AddrPred Znat_semiring_closed.
Canonical Znat_mulrPred := MulrPred Znat_semiring_closed.
Canonical Znat_semiringPred := SemiringPred Znat_semiring_closed.

Lemma ZnatP (m : int) : reflect (exists n : nat, m = n) (m \is a Znat).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End ZnatPred.

Section rpred.

Lemma rpredMz M S (addS : @zmodPred M S) (kS : keyed_pred addS) m :
  {in kS, forall u, u *~ m \in kS}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rpred_int R S (ringS : @subringPred R S) (kS : keyed_pred ringS) m :
  m%:~R \in kS.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rpredZint (R : ringType) (M : lmodType R) S
                 (addS : @zmodPred M S) (kS : keyed_pred addS) m :
  {in kS, forall u, m%:~R *: u \in kS}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rpredXz R S (divS : @divrPred R S) (kS : keyed_pred divS) m :
  {in kS, forall x, x ^ m \in kS}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rpredXsign R S (divS : @divrPred R S) (kS : keyed_pred divS) n x :
  (x ^ ((-1) ^+ n) \in kS) = (x \in kS).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End rpred.
