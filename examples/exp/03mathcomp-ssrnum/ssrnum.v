(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import ssrAC div fintype path bigop order finset fingroup.
From mathcomp Require Import ssralg poly.
Require Import SMTCoq.SMTCoq.
(******************************************************************************)
(* This file defines some classes to manipulate number structures, i.e        *)
(* structures with an order and a norm. To use this file, insert              *)
(* "Import Num.Theory." before your scripts. You can also "Import Num.Def."   *)
(* to enjoy shorter notations (e.g., minr instead of Num.min, lerif instead   *)
(* of Num.leif, etc.).                                                        *)
(*                                                                            *)
(*   * NumDomain (Integral domain with an order and a norm)                   *)
(*    numDomainType == interface for a num integral domain.                   *)
(*   NumDomainType T m                                                        *)
(*                  == packs the num mixin into a numDomainType. The carrier  *)
(*                     T must have an integral domain and a partial order     *)
(*                     structures.                                            *)
(*   [numDomainType of T for S]                                               *)
(*                  == T-clone of the numDomainType structure S.              *)
(*   [numDomainType of T]                                                     *)
(*                  == clone of a canonical numDomainType structure on T.     *)
(*                                                                            *)
(*   * NormedZmodule (Zmodule with a norm)                                    *)
(*   normedZmodType R                                                         *)
(*                  == interface for a normed Zmodule structure indexed by    *)
(*                     numDomainType R.                                       *)
(*   NormedZmodType R T m                                                     *)
(*                  == pack the normed Zmodule mixin into a normedZmodType.   *)
(*                     The carrier T must have an integral domain structure.  *)
(*   [normedZmodType R of T for S]                                            *)
(*                  == T-clone of the normedZmodType R structure S.           *)
(*   [normedZmodType R of T]                                                  *)
(*                  == clone of a canonical normedZmodType R structure on T.  *)
(*                                                                            *)
(*   * NumField (Field with an order and a norm)                              *)
(*     numFieldType == interface for a num field.                             *)
(*   [numFieldType of T]                                                      *)
(*                  == clone of a canonical numFieldType structure on T.      *)
(*                                                                            *)
(*   * NumClosedField (Partially ordered Closed Field with conjugation)       *)
(*   numClosedFieldType                                                       *)
(*                  == interface for a closed field with conj.                *)
(*   NumClosedFieldType T r                                                   *)
(*                  == packs the real closed axiom r into a                   *)
(*                     numClosedFieldType. The carrier T must have a closed   *)
(*                     field type structure.                                  *)
(*   [numClosedFieldType of T]                                                *)
(*                  == clone of a canonical numClosedFieldType structure on T.*)
(*   [numClosedFieldType of T for S]                                          *)
(*                  == T-clone of the numClosedFieldType structure S.         *)
(*                                                                            *)
(*   * RealDomain (Num domain where all elements are positive or negative)    *)
(*   realDomainType == interface for a real integral domain.                  *)
(*   [realDomainType of T]                                                    *)
(*                  == clone of a canonical realDomainType structure on T.    *)
(*                                                                            *)
(*   * RealField (Num Field where all elements are positive or negative)      *)
(*    realFieldType == interface for a real field.                            *)
(*   [realFieldType of T]                                                     *)
(*                  == clone of a canonical realFieldType structure on T.     *)
(*                                                                            *)
(*   * ArchiField (A Real Field with the archimedean axiom)                   *)
(*   archiFieldType == interface for an archimedean field.                    *)
(*   ArchiFieldType T r                                                       *)
(*                  == packs the archimedean axiom r into an archiFieldType.  *)
(*                     The carrier T must have a real field type structure.   *)
(*   [archiFieldType of T for S]                                              *)
(*                  == T-clone of the archiFieldType structure S.             *)
(*   [archiFieldType of T]                                                    *)
(*                  == clone of a canonical archiFieldType structure on T.    *)
(*                                                                            *)
(*   * RealClosedField (Real Field with the real closed axiom)                *)
(*          rcfType == interface for a real closed field.                     *)
(*      RcfType T r == packs the real closed axiom r into a rcfType.          *)
(*                     The carrier T must have a real field type structure.   *)
(*   [rcfType of T] == clone of a canonical realClosedFieldType structure on  *)
(*                     T.                                                     *)
(*   [rcfType of T for S]                                                     *)
(*                  == T-clone of the realClosedFieldType structure S.        *)
(*                                                                            *)
(* The ordering symbols and notations (<, <=, >, >=, _ <= _ ?= iff _,         *)
(* _ < _ ?<= if _, >=<, and ><) and lattice operations (meet and join)        *)
(* defined in order.v are redefined for the ring_display in the ring_scope    *)
(* (%R). 0-ary ordering symbols for the ring_display have the suffix "%R",    *)
(* e.g., <%R. All the other ordering notations are the same as order.v.       *)
(*                                                                            *)
(* Over these structures, we have the following operations                    *)
(*             `|x| == norm of x.                                             *)
(*         Num.sg x == sign of x: equal to 0 iff x = 0, to 1 iff x > 0, and   *)
(*                     to -1 in all other cases (including x < 0).            *)
(*  x \is a Num.pos <=> x is positive (:= x > 0).                             *)
(*  x \is a Num.neg <=> x is negative (:= x < 0).                             *)
(* x \is a Num.nneg <=> x is positive or 0 (:= x >= 0).                       *)
(* x \is a Num.real <=> x is real (:= x >= 0 or x < 0).                       *)
(*      Num.bound x == in archimedean fields, and upper bound for x, i.e.,    *)
(*                     and n such that `|x| < n%:R.                           *)
(*       Num.sqrt x == in a real-closed field, a positive square root of x if *)
(*                     x >= 0, or 0 otherwise.                                *)
(* For numeric algebraically closed fields we provide the generic definitions *)
(*         'i == the imaginary number (:= sqrtC (-1)).                        *)
(*      'Re z == the real component of z.                                     *)
(*      'Im z == the imaginary component of z.                                *)
(*        z^* == the complex conjugate of z (:= conjC z).                     *)
(*    sqrtC z == a nonnegative square root of z, i.e., 0 <= sqrt x if 0 <= x. *)
(*  n.-root z == more generally, for n > 0, an nth root of z, chosen with a   *)
(*               minimal non-negative argument for n > 1 (i.e., with a        *)
(*               maximal real part subject to a nonnegative imaginary part).  *)
(*               Note that n.-root (-1) is a primitive 2nth root of unity,    *)
(*               an thus not equal to -1 for n odd > 1 (this will be shown in *)
(*               file cyclotomic.v).                                          *)
(*                                                                            *)
(* - list of prefixes :                                                       *)
(*   p : positive                                                             *)
(*   n : negative                                                             *)
(*   sp : strictly positive                                                   *)
(*   sn : strictly negative                                                   *)
(*   i : interior = in [0, 1] or ]0, 1[                                       *)
(*   e : exterior = in [1, +oo[ or ]1; +oo[                                   *)
(*   w : non strict (weak) monotony                                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "n .-root" (at level 2, format "n .-root").
Reserved Notation "'i" (at level 0).
Reserved Notation "'Re z" (at level 10, z at level 8).
Reserved Notation "'Im z" (at level 10, z at level 8).

Local Open Scope order_scope.
Local Open Scope ring_scope.
Import Order.TTheory GRing.Theory.

Fact ring_display : unit. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Module Num.

Record normed_mixin_of (R T : zmodType)
       (Rorder : Order.POrder.mixin_of (Equality.class R))
       (le_op := Order.POrder.le Rorder)
  := NormedMixin {
  norm_op : T -> R;
  _ : forall x y, le_op (norm_op (x + y)) (norm_op x + norm_op y);
  _ : forall x, norm_op x = 0 -> x = 0;
  _ : forall x n, norm_op (x *+ n) = norm_op x *+ n;
  _ : forall x, norm_op (- x) = norm_op x;
}.

Record mixin_of (R : ringType)
       (Rorder : Order.POrder.mixin_of (Equality.class R))
       (le_op := Order.POrder.le Rorder) (lt_op := Order.POrder.lt Rorder)
       (normed : @normed_mixin_of R R Rorder) (norm_op := norm_op normed)
  := Mixin {
  _ : forall x y, lt_op 0 x -> lt_op 0 y -> lt_op 0 (x + y);
  _ : forall x y, le_op 0 x -> le_op 0 y -> le_op x y || le_op y x;
  _ : {morph norm_op : x y / x * y};
  _ : forall x y, (le_op x y) = (norm_op (y - x) == y - x);
}.

Local Notation ring_for T b := (@GRing.Ring.Pack T b).

Module NumDomain.

Section ClassDef.
Set Primitive Projections.
Record class_of T := Class {
  base : GRing.IntegralDomain.class_of T;
  order_mixin : Order.POrder.mixin_of (Equality.class (ring_for T base));
  normed_mixin : normed_mixin_of (ring_for T base) order_mixin;
  mixin : mixin_of normed_mixin;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> GRing.IntegralDomain.class_of.
Local Coercion order_base T (class_of_T : class_of T) :=
  @Order.POrder.Class _ class_of_T (order_mixin class_of_T).

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c  as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Definition pack (b0 : GRing.IntegralDomain.class_of _) om0
           (nm0 : @normed_mixin_of (ring_for T b0) (ring_for T b0) om0)
           (m0 : @mixin_of (ring_for T b0) om0 nm0) :=
  fun bT (b : GRing.IntegralDomain.class_of T)
      & phant_id (@GRing.IntegralDomain.class bT) b =>
  fun om & phant_id om0 om =>
  fun nm & phant_id nm0 nm =>
  fun m & phant_id m0 m =>
  @Pack T (@Class T b om nm m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @GRing.Zmodule.Pack cT class.
Definition ringType := @GRing.Ring.Pack cT class.
Definition comRingType := @GRing.ComRing.Pack cT class.
Definition unitRingType := @GRing.UnitRing.Pack cT class.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT class.
Definition idomainType := @GRing.IntegralDomain.Pack cT class.
Definition porderType := @Order.POrder.Pack ring_display cT class.
Definition porder_zmodType := @GRing.Zmodule.Pack porderType class.
Definition porder_ringType := @GRing.Ring.Pack porderType class.
Definition porder_comRingType := @GRing.ComRing.Pack porderType class.
Definition porder_unitRingType := @GRing.UnitRing.Pack porderType class.
Definition porder_comUnitRingType := @GRing.ComUnitRing.Pack porderType class.
Definition porder_idomainType := @GRing.IntegralDomain.Pack porderType class.

End ClassDef.

Module Exports.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion base  : class_of >-> GRing.IntegralDomain.class_of.
Coercion order_base : class_of >-> Order.POrder.class_of.
Coercion normed_mixin : class_of >-> normed_mixin_of.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion porderType : type >-> Order.POrder.type.
Canonical porderType.
Canonical porder_zmodType.
Canonical porder_ringType.
Canonical porder_comRingType.
Canonical porder_unitRingType.
Canonical porder_comUnitRingType.
Canonical porder_idomainType.
Notation numDomainType := type.
Notation NumDomainType T m := (@pack T _ _ _ m _ _ id _ id _ id _ id).
Notation "[ 'numDomainType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'numDomainType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'numDomainType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'numDomainType'  'of'  T ]") : form_scope.
End Exports.

End NumDomain.
Import NumDomain.Exports.

Local Notation num_for T b := (@NumDomain.Pack T b).

Module NormedZmodule.

Section ClassDef.

Variable R : numDomainType.

Set Primitive Projections.
Record class_of (T : Type) := Class {
  base : GRing.Zmodule.class_of T;
  mixin : @normed_mixin_of R (@GRing.Zmodule.Pack T base) (NumDomain.class R);
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> GRing.Zmodule.class_of.
Local Coercion mixin : class_of >-> normed_mixin_of.

Structure type (phR : phant R) :=
  Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.

Variables (phR : phant R) (T : Type) (cT : type phR).

Definition class := let: Pack _ c := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack phR T c.
Definition pack b0 (m0 : @normed_mixin_of R (@GRing.Zmodule.Pack T b0)
                                          (NumDomain.class R)) :=
  Pack phR (@Class T b0 m0).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @GRing.Zmodule.Pack cT class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.Zmodule.class_of.
Coercion mixin : class_of >-> normed_mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Notation normedZmodType R := (type (Phant R)).
Notation NormedZmodType R T m := (@pack _ (Phant R) T _ m).
Notation NormedZmodMixin := Mixin.
Notation "[ 'normedZmodType' R 'of' T 'for' cT ]" :=
  (@clone _ (Phant R) T cT _ idfun)
  (at level 0, format "[ 'normedZmodType'  R  'of'  T  'for'  cT ]") :
  form_scope.
Notation "[ 'normedZmodType' R 'of' T ]" := (@clone _ (Phant R) T _ _ id)
  (at level 0, format "[ 'normedZmodType'  R  'of'  T ]") : form_scope.
End Exports.

End NormedZmodule.
Import NormedZmodule.Exports.

Module NumDomain_joins.
Import NumDomain.
Section NumDomain_joins.

Variables (T : Type) (cT : type).

Notation class := (class cT).
Definition normedZmodType : normedZmodType cT :=
  @NormedZmodule.Pack
     cT (Phant cT) cT (NormedZmodule.Class (NumDomain.normed_mixin class)).
Definition normedZmod_ringType := @GRing.Ring.Pack normedZmodType class.
Definition normedZmod_comRingType := @GRing.ComRing.Pack normedZmodType class.
Definition normedZmod_unitRingType := @GRing.UnitRing.Pack normedZmodType class.
Definition normedZmod_comUnitRingType :=
  @GRing.ComUnitRing.Pack normedZmodType class.
Definition normedZmod_idomainType :=
  @GRing.IntegralDomain.Pack normedZmodType class.
Definition normedZmod_porderType :=
  @Order.POrder.Pack ring_display normedZmodType class.

End NumDomain_joins.

Module Exports.
Coercion normedZmodType : type >-> NormedZmodule.type.
Canonical normedZmodType.
Canonical normedZmod_ringType.
Canonical normedZmod_comRingType.
Canonical normedZmod_unitRingType.
Canonical normedZmod_comUnitRingType.
Canonical normedZmod_idomainType.
Canonical normedZmod_porderType.
End Exports.
End NumDomain_joins.
Export NumDomain_joins.Exports.

Module Import Def.

Definition normr (R : numDomainType) (T : normedZmodType R) : T -> R :=
  nosimpl (norm_op (NormedZmodule.class T)).
Arguments normr {R T} x.

Notation ler := (@Order.le ring_display _) (only parsing).
Notation "@ 'ler' R" := (@Order.le ring_display R)
  (at level 10, R at level 8, only parsing) : fun_scope.
Notation ltr := (@Order.lt ring_display _) (only parsing).
Notation "@ 'ltr' R" := (@Order.lt ring_display R)
  (at level 10, R at level 8, only parsing) : fun_scope.
Notation ger := (@Order.ge ring_display _) (only parsing).
Notation "@ 'ger' R" := (@Order.ge ring_display R)
  (at level 10, R at level 8, only parsing) : fun_scope.
Notation gtr := (@Order.gt ring_display _) (only parsing).
Notation "@ 'gtr' R" := (@Order.gt ring_display R)
  (at level 10, R at level 8, only parsing) : fun_scope.
Notation lerif := (@Order.leif ring_display _) (only parsing).
Notation "@ 'lerif' R" := (@Order.leif ring_display R)
  (at level 10, R at level 8, only parsing) : fun_scope.
Notation lterif := (@Order.lteif ring_display _) (only parsing).
Notation "@ 'lteif' R" := (@Order.lteif ring_display R)
  (at level 10, R at level 8, only parsing) : fun_scope.
Notation comparabler := (@Order.comparable ring_display _) (only parsing).
Notation "@ 'comparabler' R" := (@Order.comparable ring_display R)
  (at level 10, R at level 8, only parsing) : fun_scope.
Notation maxr := (@Order.max ring_display _).
Notation "@ 'maxr' R" := (@Order.max ring_display R)
    (at level 10, R at level 8, only parsing) : fun_scope.
Notation minr := (@Order.min ring_display _).
Notation "@ 'minr' R" := (@Order.min ring_display R)
  (at level 10, R at level 8, only parsing) : fun_scope.

Section Def.
Context {R : numDomainType}.
Implicit Types (x : R).

Definition sgr x : R := if x == 0 then 0 else if x < 0 then -1 else 1.
Definition Rpos : qualifier 0 R := [qualify x : R | 0 < x].
Definition Rneg : qualifier 0 R := [qualify x : R | x < 0].
Definition Rnneg : qualifier 0 R := [qualify x : R | 0 <= x].
Definition Rreal : qualifier 0 R := [qualify x : R | (0 <= x) || (x <= 0)].

End Def. End Def.

(* Shorter qualified names, when Num.Def is not imported. *)
Notation norm := normr (only parsing).
Notation le := ler (only parsing).
Notation lt := ltr (only parsing).
Notation ge := ger (only parsing).
Notation gt := gtr (only parsing).
Notation leif := lerif (only parsing).
Notation lteif := lterif (only parsing).
Notation comparable := comparabler (only parsing).
Notation sg := sgr.
Notation max := maxr.
Notation min := minr.
Notation pos := Rpos.
Notation neg := Rneg.
Notation nneg := Rnneg.
Notation real := Rreal.

Module Keys. Section Keys.
Variable R : numDomainType.
Fact Rpos_key : pred_key (@pos R). Proof. Show. Fail (cvc5_abduct 3). Admitted.
Definition Rpos_keyed := KeyedQualifier Rpos_key.
Fact Rneg_key : pred_key (@real R). Proof. Show. Fail (cvc5_abduct 3). Admitted.
Definition Rneg_keyed := KeyedQualifier Rneg_key.
Fact Rnneg_key : pred_key (@nneg R). Proof. Show. Fail (cvc5_abduct 3). Admitted.
Definition Rnneg_keyed := KeyedQualifier Rnneg_key.
Fact Rreal_key : pred_key (@real R). Proof. Show. Fail (cvc5_abduct 3). Admitted.
Definition Rreal_keyed := KeyedQualifier Rreal_key.
End Keys. End Keys.

(* (Exported) symbolic syntax. *)
Module Import Syntax.
Import Def Keys.

Notation "`| x |" := (norm x) : ring_scope.

Notation "<=%R" := le : fun_scope.
Notation ">=%R" := ge : fun_scope.
Notation "<%R" := lt : fun_scope.
Notation ">%R" := gt : fun_scope.
Notation "<?=%R" := leif : fun_scope.
Notation "<?<=%R" := lteif : fun_scope.
Notation ">=<%R" := comparable : fun_scope.
Notation "><%R" := (fun x y => ~~ (comparable x y)) : fun_scope.

Notation "<= y" := (ge y) : ring_scope.
Notation "<= y :> T" := (<= (y : T)) (only parsing) : ring_scope.
Notation ">= y"  := (le y) : ring_scope.
Notation ">= y :> T" := (>= (y : T)) (only parsing) : ring_scope.

Notation "< y" := (gt y) : ring_scope.
Notation "< y :> T" := (< (y : T)) (only parsing) : ring_scope.
Notation "> y" := (lt y) : ring_scope.
Notation "> y :> T" := (> (y : T)) (only parsing) : ring_scope.

Notation "x <= y" := (le x y) : ring_scope.
Notation "x <= y :> T" := ((x : T) <= (y : T)) (only parsing) : ring_scope.
Notation "x >= y" := (y <= x) (only parsing) : ring_scope.
Notation "x >= y :> T" := ((x : T) >= (y : T)) (only parsing) : ring_scope.

Notation "x < y"  := (lt x y) : ring_scope.
Notation "x < y :> T" := ((x : T) < (y : T)) (only parsing) : ring_scope.
Notation "x > y"  := (y < x) (only parsing) : ring_scope.
Notation "x > y :> T" := ((x : T) > (y : T)) (only parsing) : ring_scope.

Notation "x <= y <= z" := ((x <= y) && (y <= z)) : ring_scope.
Notation "x < y <= z" := ((x < y) && (y <= z)) : ring_scope.
Notation "x <= y < z" := ((x <= y) && (y < z)) : ring_scope.
Notation "x < y < z" := ((x < y) && (y < z)) : ring_scope.

Notation "x <= y ?= 'iff' C" := (lerif x y C) : ring_scope.
Notation "x <= y ?= 'iff' C :> R" := ((x : R) <= (y : R) ?= iff C)
  (only parsing) : ring_scope.

Notation "x < y ?<= 'if' C" := (lterif x y C) : ring_scope.
Notation "x < y ?<= 'if' C :> R" := ((x : R) < (y : R) ?<= if C)
  (only parsing) : ring_scope.

Notation ">=< y" := [pred x | comparable x y] : ring_scope.
Notation ">=< y :> T" := (>=< (y : T)) (only parsing) : ring_scope.
Notation "x >=< y" := (comparable x y) : ring_scope.

Notation ">< y" := [pred x | ~~ comparable x y] : ring_scope.
Notation ">< y :> T" := (>< (y : T)) (only parsing) : ring_scope.
Notation "x >< y" := (~~ (comparable x y)) : ring_scope.

Canonical Rpos_keyed.
Canonical Rneg_keyed.
Canonical Rnneg_keyed.
Canonical Rreal_keyed.

Export Order.POCoercions.

End Syntax.

Section ExtensionAxioms.

Variable R : numDomainType.

Definition real_axiom : Prop := forall x : R, x \is real.

Definition archimedean_axiom : Prop := forall x : R, exists ub, `|x| < ub%:R.

Definition real_closed_axiom : Prop :=
  forall (p : {poly R}) (a b : R),
    a <= b -> p.[a] <= 0 <= p.[b] -> exists2 x, a <= x <= b & root p x.

End ExtensionAxioms.

(* The rest of the numbers interface hierarchy. *)
Module NumField.

Section ClassDef.

Set Primitive Projections.
Record class_of R := Class {
  base  : NumDomain.class_of R;
  mixin : GRing.Field.mixin_of (num_for R base);
}.
Unset Primitive Projections.
Local Coercion base : class_of >-> NumDomain.class_of.
Local Coercion base2 R (c : class_of R) : GRing.Field.class_of _ :=
  GRing.Field.Class (@mixin _ c).

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition pack :=
  fun bT b & phant_id (NumDomain.class bT) (b : NumDomain.class_of T) =>
  fun mT m & phant_id (GRing.Field.mixin (GRing.Field.class mT)) m =>
  Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @GRing.Zmodule.Pack cT class.
Definition ringType := @GRing.Ring.Pack cT class.
Definition comRingType := @GRing.ComRing.Pack cT class.
Definition unitRingType := @GRing.UnitRing.Pack cT class.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT class.
Definition idomainType := @GRing.IntegralDomain.Pack cT class.
Definition porderType := @Order.POrder.Pack ring_display cT class.
Definition numDomainType := @NumDomain.Pack cT class.
Definition fieldType := @GRing.Field.Pack cT class.
Definition normedZmodType := NormedZmodType numDomainType cT class.
Definition porder_fieldType := @GRing.Field.Pack porderType class.
Definition normedZmod_fieldType := @GRing.Field.Pack normedZmodType class.
Definition numDomain_fieldType := @GRing.Field.Pack numDomainType class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> NumDomain.class_of.
Coercion base2 : class_of >-> GRing.Field.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion porderType : type >-> Order.POrder.type.
Canonical porderType.
Coercion numDomainType : type >-> NumDomain.type.
Canonical numDomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion normedZmodType : type >-> NormedZmodule.type.
Canonical normedZmodType.
Canonical porder_fieldType.
Canonical normedZmod_fieldType.
Canonical numDomain_fieldType.
Notation numFieldType := type.
Notation "[ 'numFieldType' 'of' T ]" := (@pack T _ _ id _ _ id)
  (at level 0, format "[ 'numFieldType'  'of'  T ]") : form_scope.
End Exports.

End NumField.
Import NumField.Exports.

Module ClosedField.

Section ClassDef.

Record imaginary_mixin_of (R : numDomainType) := ImaginaryMixin {
  imaginary : R;
  conj_op : {rmorphism R -> R};
  _ : imaginary ^+ 2 = - 1;
  _ : forall x, x * conj_op x = `|x| ^+ 2;
}.

Set Primitive Projections.
Record class_of R := Class {
  base : NumField.class_of R;
  decField_mixin : GRing.DecidableField.mixin_of (num_for R base);
  closedField_axiom : GRing.ClosedField.axiom (num_for R base);
  conj_mixin  : imaginary_mixin_of (num_for R base);
}.
Unset Primitive Projections.
Local Coercion base : class_of >-> NumField.class_of.
Local Coercion base2 R (c : class_of R) : GRing.ClosedField.class_of R :=
  @GRing.ClosedField.Class
    R (@GRing.DecidableField.Class R (base c) (@decField_mixin _ c))
    (@closedField_axiom _ c).

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone := fun b & phant_id class (b : class_of T) => Pack b.
Definition pack :=
  fun bT b & phant_id (NumField.class bT) (b : NumField.class_of T) =>
  fun mT dec closed
      & phant_id (GRing.ClosedField.class mT)
                 (@GRing.ClosedField.Class
                    _ (@GRing.DecidableField.Class _ b dec) closed) =>
  fun mc => Pack (@Class T b dec closed mc).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @GRing.Zmodule.Pack cT class.
Definition ringType := @GRing.Ring.Pack cT class.
Definition comRingType := @GRing.ComRing.Pack cT class.
Definition unitRingType := @GRing.UnitRing.Pack cT class.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT class.
Definition idomainType := @GRing.IntegralDomain.Pack cT class.
Definition porderType := @Order.POrder.Pack ring_display cT class.
Definition numDomainType := @NumDomain.Pack cT class.
Definition fieldType := @GRing.Field.Pack cT class.
Definition numFieldType := @NumField.Pack cT class.
Definition decFieldType := @GRing.DecidableField.Pack cT class.
Definition closedFieldType := @GRing.ClosedField.Pack cT class.
Definition normedZmodType := NormedZmodType numDomainType cT class.
Definition porder_decFieldType := @GRing.DecidableField.Pack porderType class.
Definition normedZmod_decFieldType :=
  @GRing.DecidableField.Pack normedZmodType class.
Definition numDomain_decFieldType :=
  @GRing.DecidableField.Pack numDomainType class.
Definition numField_decFieldType :=
  @GRing.DecidableField.Pack numFieldType class.
Definition porder_closedFieldType := @GRing.ClosedField.Pack porderType class.
Definition normedZmod_closedFieldType :=
  @GRing.ClosedField.Pack normedZmodType class.
Definition numDomain_closedFieldType :=
  @GRing.ClosedField.Pack numDomainType class.
Definition numField_closedFieldType :=
  @GRing.ClosedField.Pack numFieldType class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> NumField.class_of.
Coercion base2 : class_of >-> GRing.ClosedField.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion porderType : type >-> Order.POrder.type.
Canonical porderType.
Coercion numDomainType : type >-> NumDomain.type.
Canonical numDomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion decFieldType : type >-> GRing.DecidableField.type.
Canonical decFieldType.
Coercion numFieldType : type >-> NumField.type.
Canonical numFieldType.
Coercion closedFieldType : type >-> GRing.ClosedField.type.
Canonical closedFieldType.
Coercion normedZmodType : type >-> NormedZmodule.type.
Canonical normedZmodType.
Canonical porder_decFieldType.
Canonical normedZmod_decFieldType.
Canonical numDomain_decFieldType.
Canonical numField_decFieldType.
Canonical porder_closedFieldType.
Canonical normedZmod_closedFieldType.
Canonical numDomain_closedFieldType.
Canonical numField_closedFieldType.
Notation numClosedFieldType := type.
Notation NumClosedFieldType T m := (@pack T _ _ id _ _ _ id m).
Notation "[ 'numClosedFieldType' 'of' T 'for' cT ]" := (@clone T cT _ id)
  (at level 0, format "[ 'numClosedFieldType'  'of'  T  'for' cT ]") :
                                                         form_scope.
Notation "[ 'numClosedFieldType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'numClosedFieldType'  'of'  T ]") : form_scope.
End Exports.

End ClosedField.
Import ClosedField.Exports.

Module RealDomain.

Section ClassDef.

Set Primitive Projections.
Record class_of R := Class {
  base   : NumDomain.class_of R;
  nmixin : Order.Lattice.mixin_of base;
  lmixin : Order.DistrLattice.mixin_of (Order.Lattice.Class nmixin);
  tmixin : Order.Total.mixin_of base;
}.
Unset Primitive Projections.
Local Coercion base : class_of >-> NumDomain.class_of.
Local Coercion base2 T (c : class_of T) : Order.Total.class_of T :=
  @Order.Total.Class _ (@Order.DistrLattice.Class _ _ (lmixin c)) (@tmixin _ c).

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition pack :=
  fun bT b & phant_id (NumDomain.class bT) (b : NumDomain.class_of T) =>
  fun mT n l m &
      phant_id (@Order.Total.class ring_display mT)
               (@Order.Total.Class T (@Order.DistrLattice.Class
                                        T (@Order.Lattice.Class T b n) l) m) =>
  Pack (@Class T b n l m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @GRing.Zmodule.Pack cT class.
Definition ringType := @GRing.Ring.Pack cT class.
Definition comRingType := @GRing.ComRing.Pack cT class.
Definition unitRingType := @GRing.UnitRing.Pack cT class.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT class.
Definition idomainType := @GRing.IntegralDomain.Pack cT class.
Definition porderType := @Order.POrder.Pack ring_display cT class.
Definition latticeType := @Order.Lattice.Pack ring_display cT class.
Definition distrLatticeType := @Order.DistrLattice.Pack ring_display cT class.
Definition orderType := @Order.Total.Pack ring_display cT class.
Definition numDomainType := @NumDomain.Pack cT class.
Definition normedZmodType := NormedZmodType numDomainType cT class.
Definition zmod_latticeType := @Order.Lattice.Pack ring_display zmodType class.
Definition ring_latticeType := @Order.Lattice.Pack ring_display ringType class.
Definition comRing_latticeType :=
  @Order.Lattice.Pack ring_display comRingType class.
Definition unitRing_latticeType :=
  @Order.Lattice.Pack ring_display unitRingType class.
Definition comUnitRing_latticeType :=
  @Order.Lattice.Pack ring_display comUnitRingType class.
Definition idomain_latticeType :=
  @Order.Lattice.Pack ring_display idomainType class.
Definition normedZmod_latticeType :=
  @Order.Lattice.Pack ring_display normedZmodType class.
Definition numDomain_latticeType :=
  @Order.Lattice.Pack ring_display numDomainType class.
Definition zmod_distrLatticeType :=
  @Order.DistrLattice.Pack ring_display zmodType class.
Definition ring_distrLatticeType :=
  @Order.DistrLattice.Pack ring_display ringType class.
Definition comRing_distrLatticeType :=
  @Order.DistrLattice.Pack ring_display comRingType class.
Definition unitRing_distrLatticeType :=
  @Order.DistrLattice.Pack ring_display unitRingType class.
Definition comUnitRing_distrLatticeType :=
  @Order.DistrLattice.Pack ring_display comUnitRingType class.
Definition idomain_distrLatticeType :=
  @Order.DistrLattice.Pack ring_display idomainType class.
Definition normedZmod_distrLatticeType :=
  @Order.DistrLattice.Pack ring_display normedZmodType class.
Definition numDomain_distrLatticeType :=
  @Order.DistrLattice.Pack ring_display numDomainType class.
Definition zmod_orderType := @Order.Total.Pack ring_display zmodType class.
Definition ring_orderType := @Order.Total.Pack ring_display ringType class.
Definition comRing_orderType :=
  @Order.Total.Pack ring_display comRingType class.
Definition unitRing_orderType :=
  @Order.Total.Pack ring_display unitRingType class.
Definition comUnitRing_orderType :=
  @Order.Total.Pack ring_display comUnitRingType class.
Definition idomain_orderType :=
  @Order.Total.Pack ring_display idomainType class.
Definition normedZmod_orderType :=
  @Order.Total.Pack ring_display normedZmodType class.
Definition numDomain_orderType :=
  @Order.Total.Pack ring_display numDomainType class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> NumDomain.class_of.
Coercion base2 : class_of >-> Order.Total.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion porderType : type >-> Order.POrder.type.
Canonical porderType.
Coercion numDomainType : type >-> NumDomain.type.
Canonical numDomainType.
Coercion latticeType : type >-> Order.Lattice.type.
Canonical latticeType.
Coercion distrLatticeType : type >-> Order.DistrLattice.type.
Canonical distrLatticeType.
Coercion orderType : type >-> Order.Total.type.
Canonical orderType.
Coercion normedZmodType : type >-> NormedZmodule.type.
Canonical normedZmodType.
Canonical zmod_latticeType.
Canonical ring_latticeType.
Canonical comRing_latticeType.
Canonical unitRing_latticeType.
Canonical comUnitRing_latticeType.
Canonical idomain_latticeType.
Canonical normedZmod_latticeType.
Canonical numDomain_latticeType.
Canonical zmod_distrLatticeType.
Canonical ring_distrLatticeType.
Canonical comRing_distrLatticeType.
Canonical unitRing_distrLatticeType.
Canonical comUnitRing_distrLatticeType.
Canonical idomain_distrLatticeType.
Canonical normedZmod_distrLatticeType.
Canonical numDomain_distrLatticeType.
Canonical zmod_orderType.
Canonical ring_orderType.
Canonical comRing_orderType.
Canonical unitRing_orderType.
Canonical comUnitRing_orderType.
Canonical idomain_orderType.
Canonical normedZmod_orderType.
Canonical numDomain_orderType.
Notation realDomainType := type.
Notation "[ 'realDomainType' 'of' T ]" := (@pack T _ _ id _ _ _ _ id)
  (at level 0, format "[ 'realDomainType'  'of'  T ]") : form_scope.
End Exports.

End RealDomain.
Import RealDomain.Exports.

Module RealField.

Section ClassDef.

Set Primitive Projections.
Record class_of R := Class {
  base  : NumField.class_of R;
  nmixin : Order.Lattice.mixin_of base;
  lmixin : Order.DistrLattice.mixin_of (Order.Lattice.Class nmixin);
  tmixin : Order.Total.mixin_of base;
}.
Unset Primitive Projections.
Local Coercion base : class_of >-> NumField.class_of.
Local Coercion base2 R (c : class_of R) : RealDomain.class_of R :=
  @RealDomain.Class _ _ (nmixin c) (lmixin c) (@tmixin R c).

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition pack :=
  fun bT (b : NumField.class_of T) & phant_id (NumField.class bT) b =>
  fun mT n l t
      & phant_id (RealDomain.class mT) (@RealDomain.Class T b n l t) =>
  Pack (@Class T b n l t).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @GRing.Zmodule.Pack cT class.
Definition ringType := @GRing.Ring.Pack cT class.
Definition comRingType := @GRing.ComRing.Pack cT class.
Definition unitRingType := @GRing.UnitRing.Pack cT class.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT class.
Definition idomainType := @GRing.IntegralDomain.Pack cT class.
Definition porderType := @Order.POrder.Pack ring_display cT class.
Definition numDomainType := @NumDomain.Pack cT class.
Definition latticeType := @Order.Lattice.Pack ring_display cT class.
Definition distrLatticeType := @Order.DistrLattice.Pack ring_display cT class.
Definition orderType := @Order.Total.Pack ring_display cT class.
Definition realDomainType := @RealDomain.Pack cT class.
Definition fieldType := @GRing.Field.Pack cT class.
Definition numFieldType := @NumField.Pack cT class.
Definition normedZmodType := NormedZmodType numDomainType cT class.
Definition field_latticeType :=
  @Order.Lattice.Pack ring_display fieldType class.
Definition field_distrLatticeType :=
  @Order.DistrLattice.Pack ring_display fieldType class.
Definition field_orderType := @Order.Total.Pack ring_display fieldType class.
Definition field_realDomainType := @RealDomain.Pack fieldType class.
Definition numField_latticeType :=
  @Order.Lattice.Pack ring_display numFieldType class.
Definition numField_distrLatticeType :=
  @Order.DistrLattice.Pack ring_display numFieldType class.
Definition numField_orderType :=
  @Order.Total.Pack ring_display numFieldType class.
Definition numField_realDomainType := @RealDomain.Pack numFieldType class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> NumField.class_of.
Coercion base2 : class_of >-> RealDomain.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion porderType : type >-> Order.POrder.type.
Canonical porderType.
Coercion numDomainType : type >-> NumDomain.type.
Canonical numDomainType.
Coercion latticeType : type >-> Order.Lattice.type.
Canonical latticeType.
Coercion distrLatticeType : type >-> Order.DistrLattice.type.
Canonical distrLatticeType.
Coercion orderType : type >-> Order.Total.type.
Canonical orderType.
Coercion realDomainType : type >-> RealDomain.type.
Canonical realDomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion numFieldType : type >-> NumField.type.
Canonical numFieldType.
Coercion normedZmodType : type >-> NormedZmodule.type.
Canonical normedZmodType.
Canonical field_latticeType.
Canonical field_distrLatticeType.
Canonical field_orderType.
Canonical field_realDomainType.
Canonical numField_latticeType.
Canonical numField_distrLatticeType.
Canonical numField_orderType.
Canonical numField_realDomainType.
Notation realFieldType := type.
Notation "[ 'realFieldType' 'of' T ]" := (@pack T _ _ id _ _ _ _ id)
  (at level 0, format "[ 'realFieldType'  'of'  T ]") : form_scope.
End Exports.

End RealField.
Import RealField.Exports.

Module ArchimedeanField.

Section ClassDef.

Set Primitive Projections.
Record class_of R := Class {
  base : RealField.class_of R;
  mixin : archimedean_axiom (num_for R base)
}.
Unset Primitive Projections.
Local Coercion base : class_of >-> RealField.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Definition pack b0 (m0 : archimedean_axiom (num_for T b0)) :=
  fun bT b & phant_id (RealField.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @GRing.Zmodule.Pack cT class.
Definition ringType := @GRing.Ring.Pack cT class.
Definition comRingType := @GRing.ComRing.Pack cT class.
Definition unitRingType := @GRing.UnitRing.Pack cT class.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT class.
Definition idomainType := @GRing.IntegralDomain.Pack cT class.
Definition porderType := @Order.POrder.Pack ring_display cT class.
Definition latticeType := @Order.Lattice.Pack ring_display cT class.
Definition distrLatticeType := @Order.DistrLattice.Pack ring_display cT class.
Definition orderType := @Order.Total.Pack ring_display cT class.
Definition numDomainType := @NumDomain.Pack cT class.
Definition realDomainType := @RealDomain.Pack cT class.
Definition fieldType := @GRing.Field.Pack cT class.
Definition numFieldType := @NumField.Pack cT class.
Definition realFieldType := @RealField.Pack cT class.
Definition normedZmodType := NormedZmodType numDomainType cT class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> RealField.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion porderType : type >-> Order.POrder.type.
Canonical porderType.
Coercion latticeType : type >-> Order.Lattice.type.
Canonical latticeType.
Coercion distrLatticeType : type >-> Order.DistrLattice.type.
Canonical distrLatticeType.
Coercion orderType : type >-> Order.Total.type.
Canonical orderType.
Coercion numDomainType : type >-> NumDomain.type.
Canonical numDomainType.
Coercion realDomainType : type >-> RealDomain.type.
Canonical realDomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion numFieldType : type >-> NumField.type.
Canonical numFieldType.
Coercion realFieldType : type >-> RealField.type.
Canonical realFieldType.
Coercion normedZmodType : type >-> NormedZmodule.type.
Canonical normedZmodType.
Notation archiFieldType := type.
Notation ArchiFieldType T m := (@pack T _ m _ _ id _ id).
Notation "[ 'archiFieldType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'archiFieldType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'archiFieldType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'archiFieldType'  'of'  T ]") : form_scope.
End Exports.

End ArchimedeanField.
Import ArchimedeanField.Exports.

Module RealClosedField.

Section ClassDef.

Set Primitive Projections.
Record class_of R := Class {
  base : RealField.class_of R;
  mixin : real_closed_axiom (num_for R base)
}.
Unset Primitive Projections.
Local Coercion base : class_of >-> RealField.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Definition pack b0 (m0 : real_closed_axiom (num_for T b0)) :=
  fun bT b & phant_id (RealField.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @GRing.Zmodule.Pack cT class.
Definition ringType := @GRing.Ring.Pack cT class.
Definition comRingType := @GRing.ComRing.Pack cT class.
Definition unitRingType := @GRing.UnitRing.Pack cT class.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT class.
Definition idomainType := @GRing.IntegralDomain.Pack cT class.
Definition porderType := @Order.POrder.Pack ring_display cT class.
Definition latticeType := @Order.Lattice.Pack ring_display cT class.
Definition distrLatticeType := @Order.DistrLattice.Pack ring_display cT class.
Definition orderType := @Order.Total.Pack ring_display cT class.
Definition numDomainType := @NumDomain.Pack cT class.
Definition realDomainType := @RealDomain.Pack cT class.
Definition fieldType := @GRing.Field.Pack cT class.
Definition numFieldType := @NumField.Pack cT class.
Definition realFieldType := @RealField.Pack cT class.
Definition normedZmodType := NormedZmodType numDomainType cT class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> RealField.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion porderType : type >-> Order.POrder.type.
Canonical porderType.
Coercion latticeType : type >-> Order.Lattice.type.
Canonical latticeType.
Coercion distrLatticeType : type >-> Order.DistrLattice.type.
Canonical distrLatticeType.
Coercion orderType : type >-> Order.Total.type.
Canonical orderType.
Coercion numDomainType : type >-> NumDomain.type.
Canonical numDomainType.
Coercion realDomainType : type >-> RealDomain.type.
Canonical realDomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion numFieldType : type >-> NumField.type.
Canonical numFieldType.
Coercion realFieldType : type >-> RealField.type.
Canonical realFieldType.
Coercion normedZmodType : type >-> NormedZmodule.type.
Canonical normedZmodType.
Notation rcfType := Num.RealClosedField.type.
Notation RcfType T m := (@pack T _ m _ _ id _ id).
Notation "[ 'rcfType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'rcfType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'rcfType' 'of' T ]" :=  (@clone T _ _ id)
  (at level 0, format "[ 'rcfType'  'of'  T ]") : form_scope.
End Exports.

End RealClosedField.
Import RealClosedField.Exports.

(* The elementary theory needed to support the definition of the derived      *)
(* operations for the extensions described above.                             *)
Module Import Internals.

Section NormedZmodule.
Variables (R : numDomainType) (V : normedZmodType R).
Implicit Types (l : R) (x y : V).

Lemma ler_norm_add x y : `|x + y| <= `|x| + `|y|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normr0_eq0 x : `|x| = 0 -> x = 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normrMn x n : `|x *+ n| = `|x| *+ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normrN x : `|- x| = `|x|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End NormedZmodule.

Section NumDomain.
Variable R : numDomainType.
Implicit Types x y : R.

(* Lemmas from the signature *)

Lemma addr_gt0 x y : 0 < x -> 0 < y -> 0 < x + y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ger_leVge x y : 0 <= x -> 0 <= y -> (x <= y) || (y <= x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normrM : {morph norm : x y / (x : R) * y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_def x y : (x <= y) = (`|y - x| == y - x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Basic consequences (just enough to get predicate closure properties). *)

Lemma ger0_def x : (0 <= x) = (`|x| == x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma subr_ge0 x y : (0 <= x - y) = (y <= x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma oppr_ge0 x : (0 <= - x) = (x <= 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler01 : 0 <= 1 :> R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr01 : 0 < 1 :> R. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma le0r x : (0 <= x) = (x == 0) || (0 < x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addr_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x + y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pmulr_rgt0 x y : 0 < x -> (0 < x * y) = (0 < y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Closure properties of the real predicates. *)

Lemma posrE x : (x \is pos) = (0 < x). Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma nnegrE x : (x \is nneg) = (0 <= x). Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma realE x : (x \is real) = (0 <= x) || (x <= 0). Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact pos_divr_closed : divr_closed (@pos R).
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Canonical pos_mulrPred := MulrPred pos_divr_closed.
Canonical pos_divrPred := DivrPred pos_divr_closed.

Fact nneg_divr_closed : divr_closed (@nneg R).
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Canonical nneg_mulrPred := MulrPred nneg_divr_closed.
Canonical nneg_divrPred := DivrPred nneg_divr_closed.

Fact nneg_addr_closed : addr_closed (@nneg R).
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Canonical nneg_addrPred := AddrPred nneg_addr_closed.
Canonical nneg_semiringPred := SemiringPred nneg_divr_closed.

Fact real_oppr_closed : oppr_closed (@real R).
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Canonical real_opprPred := OpprPred real_oppr_closed.

Fact real_addr_closed : addr_closed (@real R).
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Canonical real_addrPred := AddrPred real_addr_closed.
Canonical real_zmodPred := ZmodPred real_oppr_closed.

Fact real_divr_closed : divr_closed (@real R).
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Canonical real_mulrPred := MulrPred real_divr_closed.
Canonical real_smulrPred := SmulrPred real_divr_closed.
Canonical real_divrPred := DivrPred real_divr_closed.
Canonical real_sdivrPred := SdivrPred real_divr_closed.
Canonical real_semiringPred := SemiringPred real_divr_closed.
Canonical real_subringPred := SubringPred real_divr_closed.
Canonical real_divringPred := DivringPred real_divr_closed.

End NumDomain.

Lemma num_real (R : realDomainType) (x : R) : x \is real.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact archi_bound_subproof (R : archiFieldType) : archimedean_axiom R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Section RealClosed.
Variable R : rcfType.

Lemma poly_ivt : real_closed_axiom R. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact sqrtr_subproof (x : R) :
  exists2 y, 0 <= y & (if 0 <= x then y ^+ 2 == x else y == 0) : bool.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End RealClosed.

End Internals.

Module PredInstances.

Canonical pos_mulrPred.
Canonical pos_divrPred.

Canonical nneg_addrPred.
Canonical nneg_mulrPred.
Canonical nneg_divrPred.
Canonical nneg_semiringPred.

Canonical real_addrPred.
Canonical real_opprPred.
Canonical real_zmodPred.
Canonical real_mulrPred.
Canonical real_smulrPred.
Canonical real_divrPred.
Canonical real_sdivrPred.
Canonical real_semiringPred.
Canonical real_subringPred.
Canonical real_divringPred.

End PredInstances.

Module Import ExtraDef.

Definition archi_bound {R} x := sval (sigW (@archi_bound_subproof R x)).

Definition sqrtr {R} x := s2val (sig2W (@sqrtr_subproof R x)).

End ExtraDef.

Notation bound := archi_bound.
Notation sqrt := sqrtr.

Module Import Theory.

Section NumIntegralDomainTheory.

Variable R : numDomainType.
Implicit Types (V : normedZmodType R) (x y z t : R).

(* Lemmas from the signature (reexported from internals). *)

Definition ler_norm_add V (x y : V) : `|x + y| <= `|x| + `|y| :=
  ler_norm_add x y.
Definition addr_gt0 x y : 0 < x -> 0 < y -> 0 < x + y := @addr_gt0 R x y.
Definition normr0_eq0 V (x : V) : `|x| = 0 -> x = 0 := @normr0_eq0 R V x.
Definition ger_leVge x y : 0 <= x -> 0 <= y -> (x <= y) || (y <= x) :=
  @ger_leVge R x y.
Definition normrM : {morph norm : x y / (x : R) * y} := @normrM R.
Definition ler_def x y : (x <= y) = (`|y - x| == y - x) := ler_def x y.
Definition normrMn V (x : V) n : `|x *+ n| = `|x| *+ n := normrMn x n.
Definition normrN V (x : V) : `|- x| = `|x| := normrN x.

(* Predicate definitions. *)

Lemma posrE x : (x \is pos) = (0 < x). Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma negrE x : (x \is neg) = (x < 0). Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma nnegrE x : (x \is nneg) = (0 <= x). Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma realE x : (x \is real) = (0 <= x) || (x <= 0). Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* General properties of <= and < *)

Lemma lt0r x : (0 < x) = (x != 0) && (0 <= x). Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma le0r x : (0 <= x) = (x == 0) || (0 < x). Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lt0r_neq0 (x : R) : 0 < x -> x != 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr0_neq0 (x : R) : x < 0 -> x != 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pmulr_rgt0 x y : 0 < x -> (0 < x * y) = (0 < y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pmulr_rge0 x y : 0 < x -> (0 <= x * y) = (0 <= y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Integer comparisons and characteristic 0. *)
Lemma ler01 : 0 <= 1 :> R. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma ltr01 : 0 < 1 :> R. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma ler0n n : 0 <= n%:R :> R. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Hint Resolve ler01 ltr01 ler0n : core.
Lemma ltr0Sn n : 0 < n.+1%:R :> R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma ltr0n n : (0 < n%:R :> R) = (0 < n)%N.
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Hint Resolve ltr0Sn : core.

Lemma pnatr_eq0 n : (n%:R == 0 :> R) = (n == 0)%N.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma char_num : [char R] =i pred0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Properties of the norm. *)

Lemma ger0_def x : (0 <= x) = (`|x| == x). Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma normr_idP {x} : reflect (`|x| = x) (0 <= x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma ger0_norm x : 0 <= x -> `|x| = x. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma normr1 : `|1 : R| = 1. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma normr_nat n : `|n%:R : R| = n%:R. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normr_prod I r (P : pred I) (F : I -> R) :
  `|\prod_(i <- r | P i) F i| = \prod_(i <- r | P i) `|F i|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normrX n x : `|x ^+ n| = `|x| ^+ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normr_unit : {homo (@norm R R) : x / x \is a GRing.unit}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normrV : {in GRing.unit, {morph (@norm R R) : x / x ^-1}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normrN1 : `|-1 : R| = 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma big_real x0 op I (P : pred I) F (s : seq I) :
  {in real &, forall x y, op x y \is real} -> x0 \is real ->
  {in P, forall i, F i \is real} -> \big[op/x0]_(i <- s | P i) F i \is real.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sum_real I (P : pred I) (F : I -> R) (s : seq I) :
  {in P, forall i, F i \is real} -> \sum_(i <- s | P i) F i \is real.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma prod_real I (P : pred I) (F : I -> R) (s : seq I) :
  {in P, forall i, F i \is real} -> \prod_(i <- s | P i) F i \is real.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Section NormedZmoduleTheory.

Variable V : normedZmodType R.
Implicit Types (v w : V).

Lemma normr0 : `|0 : V| = 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normr0P v : reflect (`|v| = 0) (v == 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition normr_eq0 v := sameP (`|v| =P 0) (normr0P v).

Lemma distrC v w : `|v - w| = `|w - v|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normr_id v : `| `|v| | = `|v|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normr_ge0 v : 0 <= `|v|. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normr_le0 v : `|v| <= 0 = (v == 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normr_lt0 v : `|v| < 0 = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normr_gt0 v : `|v| > 0 = (v != 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition normrE := (normr_id, normr0, normr1, normrN1, normr_ge0, normr_eq0,
  normr_lt0, normr_le0, normr_gt0, normrN).

End NormedZmoduleTheory.

Lemma ler0_def x : (x <= 0) = (`|x| == - x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler0_norm x : x <= 0 -> `|x| = - x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition gtr0_norm x (hx : 0 < x) := ger0_norm (ltW hx).
Definition ltr0_norm x (hx : x < 0) := ler0_norm (ltW hx).

(* Comparision to 0 of a difference *)

Lemma subr_ge0 x y : (0 <= y - x) = (x <= y). Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma subr_gt0 x y : (0 < y - x) = (x < y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma subr_le0  x y : (y - x <= 0) = (y <= x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma subr_lt0  x y : (y - x < 0) = (y < x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition subr_lte0 := (subr_le0, subr_lt0).
Definition subr_gte0 := (subr_ge0, subr_gt0).
Definition subr_cp0 := (subr_lte0, subr_gte0).

(* Comparability in a numDomain *)

Lemma comparable0r x : (0 >=< x)%R = (x \is Num.real). Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma comparabler0 x : (x >=< 0)%R = (x \is Num.real).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma subr_comparable0 x y : (x - y >=< 0)%R = (x >=< y)%R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma comparablerE x y : (x >=< y)%R = (x - y \is Num.real).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma  comparabler_trans : transitive (comparable : rel R).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Ordered ring properties. *)

Definition lter01 := (ler01, ltr01).

Lemma addr_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x + y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End NumIntegralDomainTheory.

Arguments ler01 {R}.
Arguments ltr01 {R}.
Arguments normr_idP {R x}.
Arguments normr0P {R V v}.
#[global] Hint Resolve ler01 ltr01 ltr0Sn ler0n : core.
#[global] Hint Extern 0 (is_true (0 <= norm _)) => apply: normr_ge0 : core.

Lemma normr_nneg (R : numDomainType) (x : R) : `|x| \is Num.nneg.
Proof. Show. Fail (cvc5_abduct 3). Admitted.
#[global] Hint Resolve normr_nneg : core.

Section NumDomainOperationTheory.

Variable R : numDomainType.
Implicit Types x y z t : R.

(* Comparision and opposite. *)

Lemma ler_opp2 : {mono -%R : x y /~ x <= y :> R}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Hint Resolve ler_opp2 : core.
Lemma ltr_opp2 : {mono -%R : x y /~ x < y :> R}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Hint Resolve ltr_opp2 : core.
Definition lter_opp2 := (ler_opp2, ltr_opp2).

Lemma ler_oppr x y : (x <= - y) = (y <= - x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_oppr x y : (x < - y) = (y < - x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition lter_oppr := (ler_oppr, ltr_oppr).

Lemma ler_oppl x y : (- x <= y) = (- y <= x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_oppl x y : (- x < y) = (- y < x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition lter_oppl := (ler_oppl, ltr_oppl).

Lemma oppr_ge0 x : (0 <= - x) = (x <= 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma oppr_gt0 x : (0 < - x) = (x < 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition oppr_gte0 := (oppr_ge0, oppr_gt0).

Lemma oppr_le0 x : (- x <= 0) = (0 <= x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma oppr_lt0 x : (- x < 0) = (0 < x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gtr_opp x : 0 < x -> - x < x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition oppr_lte0 := (oppr_le0, oppr_lt0).
Definition oppr_cp0 := (oppr_gte0, oppr_lte0).
Definition lter_oppE := (oppr_cp0, lter_opp2).

Lemma ge0_cp x : 0 <= x -> (- x <= 0) * (- x <= x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gt0_cp x : 0 < x ->
  (0 <= x) * (- x <= 0) * (- x <= x) * (- x < 0) * (- x < x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma le0_cp x : x <= 0 -> (0 <= - x) * (x <= - x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lt0_cp x :
  x < 0 -> (x <= 0) * (0 <= - x) * (x <= - x) * (0 < - x) * (x < - x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Properties of the real subset. *)

Lemma ger0_real x : 0 <= x -> x \is real.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler0_real x : x <= 0 -> x \is real.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gtr0_real x : 0 < x -> x \is real.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr0_real x : x < 0 -> x \is real.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real0 : 0 \is @real R. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Hint Resolve real0 : core.

Lemma real1 : 1 \is @real R. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Hint Resolve real1 : core.

Lemma realn n : n%:R \is @real R. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_leVge x y : x <= 0 -> y <= 0 -> (x <= y) || (y <= x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_leVge x y : x \is real -> y \is real -> (x <= y) || (y <= x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_comparable x y : x \is real -> y \is real -> x >=< y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma realB : {in real &, forall x y, x - y \is real}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma realN : {mono (@GRing.opp R) : x /  x \is real}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma realBC x y : (x - y \is real) = (y - x \is real).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma realD : {in real &, forall x y, x + y \is real}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* dichotomy and trichotomy *)

Variant ler_xor_gt (x y : R) : R -> R -> R -> R -> R -> R ->
    bool -> bool -> Set :=
  | LerNotGt of x <= y : ler_xor_gt x y x x y y (y - x) (y - x) true false
  | GtrNotLe of y < x  : ler_xor_gt x y y y x x (x - y) (x - y) false true.

Variant ltr_xor_ge (x y : R) : R -> R -> R -> R -> R -> R ->
    bool -> bool -> Set :=
  | LtrNotGe of x < y  : ltr_xor_ge x y x x y y (y - x) (y - x) false true
  | GerNotLt of y <= x : ltr_xor_ge x y y y x x (x - y) (x - y) true false.

Variant comparer x y : R -> R -> R -> R -> R -> R ->
    bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | ComparerLt of x < y : comparer x y x x y y (y - x) (y - x)
    false false false true false true
  | ComparerGt of x > y : comparer x y y y x x (x - y) (x - y)
    false false true false true false
  | ComparerEq of x = y : comparer x y x x x x 0 0
    true true true true false false.

Lemma real_leP x y : x \is real -> y \is real ->
  ler_xor_gt x y (min y x) (min x y) (max y x) (max x y)
                 `|x - y| `|y - x| (x <= y) (y < x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_ltP x y : x \is real -> y \is real ->
  ltr_xor_ge x y (min y x) (min x y) (max y x) (max x y)
             `|x - y| `|y - x| (y <= x) (x < y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_ltNge : {in real &, forall x y, (x < y) = ~~ (y <= x)}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_leNgt : {in real &, forall x y, (x <= y) = ~~ (y < x)}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_ltgtP x y : x \is real -> y \is real ->
  comparer x y (min y x) (min x y) (max y x) (max x y) `|x - y| `|y - x|
               (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Variant ger0_xor_lt0 (x : R) : R -> R -> R -> R -> R ->
    bool -> bool -> Set :=
  | Ger0NotLt0 of 0 <= x : ger0_xor_lt0 x 0 0 x x x false true
  | Ltr0NotGe0 of x < 0  : ger0_xor_lt0 x x x 0 0 (- x) true false.

Variant ler0_xor_gt0 (x : R) : R -> R -> R -> R -> R ->
   bool -> bool -> Set :=
  | Ler0NotLe0 of x <= 0 : ler0_xor_gt0 x x x 0 0 (- x) false true
  | Gtr0NotGt0 of 0 < x  : ler0_xor_gt0 x 0 0 x x x true false.

Variant comparer0 x : R -> R -> R -> R -> R ->
    bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | ComparerGt0 of 0 < x : comparer0 x 0 0 x x x false false false true false true
  | ComparerLt0 of x < 0 : comparer0 x x x 0 0 (- x) false false true false true false
  | ComparerEq0 of x = 0 : comparer0 x 0 0 0 0 0 true true true true false false.

Lemma real_ge0P x : x \is real -> ger0_xor_lt0 x
   (min 0 x) (min x 0) (max 0 x) (max x 0)
  `|x| (x < 0) (0 <= x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_le0P x : x \is real -> ler0_xor_gt0 x
  (min 0 x) (min x 0) (max 0 x) (max x 0)
  `|x| (0 < x) (x <= 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_ltgt0P x : x \is real ->
  comparer0 x (min 0 x) (min x 0) (max 0 x) (max x 0)
            `|x| (0 == x) (x == 0) (x <= 0) (0 <= x) (x < 0) (x > 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma max_real : {in real &, forall x y, max x y \is real}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma min_real : {in real &, forall x y, min x y \is real}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma bigmax_real I x0 (r : seq I) (P : pred I) (f : I -> R):
  x0 \is real -> {in P, forall i : I, f i \is real} ->
  \big[max/x0]_(i <- r | P i) f i \is real.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma bigmin_real I x0 (r : seq I) (P : pred I) (f : I -> R):
  x0 \is real -> {in P, forall i : I, f i \is real} ->
  \big[min/x0]_(i <- r | P i) f i \is real.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_neqr_lt : {in real &, forall x y, (x != y) = (x < y) || (y < x)}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_sub_real x y : x <= y -> y - x \is real.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ger_sub_real x y : x <= y -> x - y \is real.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_real y x : x <= y -> (x \is real) = (y \is real).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ger_real x y : y <= x -> (x \is real) = (y \is real).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ger1_real x : 1 <= x -> x \is real. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma ler1_real x : x <= 1 -> x \is real. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nreal_leF x y : y \is real -> x \notin real -> (x <= y) = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nreal_geF x y : y \is real -> x \notin real -> (y <= x) = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nreal_ltF x y : y \is real -> x \notin real -> (x < y) = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nreal_gtF x y : y \is real -> x \notin real -> (y < x) = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* real wlog *)

Lemma real_wlog_ler P :
    (forall a b, P b a -> P a b) -> (forall a b, a <= b -> P a b) ->
  forall a b : R, a \is real -> b \is real -> P a b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_wlog_ltr P :
    (forall a, P a a) -> (forall a b, (P b a -> P a b)) ->
    (forall a b, a < b -> P a b) ->
  forall a b : R, a \is real -> b \is real -> P a b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Monotony of addition *)
Lemma ler_add2l x : {mono +%R x : y z / y <= z}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_add2r x : {mono +%R^~ x : y z / y <= z}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_add2l x : {mono +%R x : y z / y < z}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_add2r x : {mono +%R^~ x : y z / y < z}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition ler_add2 := (ler_add2l, ler_add2r).
Definition ltr_add2 := (ltr_add2l, ltr_add2r).
Definition lter_add2 := (ler_add2, ltr_add2).

(* Addition, subtraction and transitivity *)
Lemma ler_add x y z t : x <= y -> z <= t -> x + z <= y + t.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_lt_add x y z t : x <= y -> z < t -> x + z < y + t.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_le_add x y z t : x < y -> z <= t -> x + z < y + t.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_add x y z t : x < y -> z < t -> x + z < y + t.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_sub x y z t : x <= y -> t <= z -> x - z <= y - t.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_lt_sub x y z t : x <= y -> t < z -> x - z < y - t.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_le_sub x y z t : x < y -> t <= z -> x - z < y - t.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_sub x y z t : x < y -> t < z -> x - z < y - t.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_subl_addr x y z : (x - y <= z) = (x <= z + y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_subl_addr x y z : (x - y < z) = (x < z + y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_subr_addr x y z : (x <= y - z) = (x + z <= y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_subr_addr x y z : (x < y - z) = (x + z < y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition ler_sub_addr := (ler_subl_addr, ler_subr_addr).
Definition ltr_sub_addr := (ltr_subl_addr, ltr_subr_addr).
Definition lter_sub_addr := (ler_sub_addr, ltr_sub_addr).

Lemma ler_subl_addl x y z : (x - y <= z) = (x <= y + z).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_subl_addl x y z : (x - y < z) = (x < y + z).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_subr_addl x y z : (x <= y - z) = (z + x <= y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_subr_addl x y z : (x < y - z) = (z + x < y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition ler_sub_addl := (ler_subl_addl, ler_subr_addl).
Definition ltr_sub_addl := (ltr_subl_addl, ltr_subr_addl).
Definition lter_sub_addl := (ler_sub_addl, ltr_sub_addl).

Lemma ler_addl x y : (x <= x + y) = (0 <= y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_addl x y : (x < x + y) = (0 < y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_addr x y : (x <= y + x) = (0 <= y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_addr x y : (x < y + x) = (0 < y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ger_addl x y : (x + y <= x) = (y <= 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gtr_addl x y : (x + y < x) = (y < 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ger_addr x y : (y + x <= x) = (y <= 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gtr_addr x y : (y + x < x) = (y < 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition cpr_add := (ler_addl, ler_addr, ger_addl, ger_addl,
                       ltr_addl, ltr_addr, gtr_addl, gtr_addl).

(* Addition with left member knwon to be positive/negative *)
Lemma ler_paddl y x z : 0 <= x -> y <= z -> y <= x + z.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_paddl y x z : 0 <= x -> y < z -> y < x + z.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_spaddl y x z : 0 < x -> y <= z -> y < x + z.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_spsaddl y x z : 0 < x -> y < z -> y < x + z.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_naddl y x z : x <= 0 -> y <= z -> x + y <= z.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_naddl y x z : x <= 0 -> y < z -> x + y < z.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_snaddl y x z : x < 0 -> y <= z -> x + y < z.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_snsaddl y x z : x < 0 -> y < z -> x + y < z.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Addition with right member we know positive/negative *)
Lemma ler_paddr y x z : 0 <= x -> y <= z -> y <= z + x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_paddr y x z : 0 <= x -> y < z -> y < z + x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_spaddr y x z : 0 < x -> y <= z -> y < z + x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_spsaddr y x z : 0 < x -> y < z -> y < z + x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_naddr y x z : x <= 0 -> y <= z -> y + x <= z.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_naddr y x z : x <= 0 -> y < z -> y + x < z.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_snaddr y x z : x < 0 -> y <= z -> y + x < z.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_snsaddr y x z : x < 0 -> y < z -> y + x < z.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* x and y have the same sign and their sum is null *)
Lemma paddr_eq0 (x y : R) :
  0 <= x -> 0 <= y -> (x + y == 0) = (x == 0) && (y == 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma naddr_eq0 (x y : R) :
  x <= 0 -> y <= 0 -> (x + y == 0) = (x == 0) && (y == 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addr_ss_eq0 (x y : R) :
    (0 <= x) && (0 <= y) || (x <= 0) && (y <= 0) ->
  (x + y == 0) = (x == 0) && (y == 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* big sum and ler *)
Lemma sumr_ge0 I (r : seq I) (P : pred I) (F : I -> R) :
  (forall i, P i -> (0 <= F i)) -> 0 <= \sum_(i <- r | P i) (F i).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_sum I (r : seq I) (P : pred I) (F G : I -> R) :
    (forall i, P i -> F i <= G i) ->
  \sum_(i <- r | P i) F i <= \sum_(i <- r | P i) G i.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_sum_nat (m n : nat) (F G : nat -> R) :
  (forall i, (m <= i < n)%N -> F i <= G i) ->
  \sum_(m <= i < n) F i <= \sum_(m <= i < n) G i.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma psumr_eq0 (I : eqType) (r : seq I) (P : pred I) (F : I -> R) :
    (forall i, P i -> 0 <= F i) ->
  (\sum_(i <- r | P i) (F i) == 0) = (all (fun i => (P i) ==> (F i == 0)) r).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* :TODO: Cyril : See which form to keep *)
Lemma psumr_eq0P (I : finType) (P : pred I) (F : I -> R) :
     (forall i, P i -> 0 <= F i) -> \sum_(i | P i) F i = 0 ->
  (forall i, P i -> F i = 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma psumr_neq0 (I : eqType) (r : seq I) (P : pred I) (F : I -> R) :
    (forall i, P i -> 0 <= F i) ->
  (\sum_(i <- r | P i) (F i) != 0) = (has (fun i => P i && (0 < F i)) r).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma psumr_neq0P (I : finType) (P : pred I) (F : I -> R) :
     (forall i, P i -> 0 <= F i) -> \sum_(i | P i) F i <> 0 ->
  (exists i, P i && (0 < F i)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* mulr and ler/ltr *)

Lemma ler_pmul2l x : 0 < x -> {mono *%R x : x y / x <= y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_pmul2l x : 0 < x -> {mono *%R x : x y / x < y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition lter_pmul2l := (ler_pmul2l, ltr_pmul2l).

Lemma ler_pmul2r x : 0 < x -> {mono *%R^~ x : x y / x <= y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_pmul2r x : 0 < x -> {mono *%R^~ x : x y / x < y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition lter_pmul2r := (ler_pmul2r, ltr_pmul2r).

Lemma ler_nmul2l x : x < 0 -> {mono *%R x : x y /~ x <= y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_nmul2l x : x < 0 -> {mono *%R x : x y /~ x < y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition lter_nmul2l := (ler_nmul2l, ltr_nmul2l).

Lemma ler_nmul2r x : x < 0 -> {mono *%R^~ x : x y /~ x <= y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_nmul2r x : x < 0 -> {mono *%R^~ x : x y /~ x < y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition lter_nmul2r := (ler_nmul2r, ltr_nmul2r).

Lemma ler_wpmul2l x : 0 <= x -> {homo *%R x : y z / y <= z}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_wpmul2r x : 0 <= x -> {homo *%R^~ x : y z / y <= z}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_wnmul2l x : x <= 0 -> {homo *%R x : y z /~ y <= z}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_wnmul2r x : x <= 0 -> {homo *%R^~ x : y z /~ y <= z}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Binary forms, for backchaining. *)

Lemma ler_pmul x1 y1 x2 y2 :
  0 <= x1 -> 0 <= x2 -> x1 <= y1 -> x2 <= y2 -> x1 * x2 <= y1 * y2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_pmul x1 y1 x2 y2 :
  0 <= x1 -> 0 <= x2 -> x1 < y1 -> x2 < y2 -> x1 * x2 < y1 * y2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* complement for x *+ n and <= or < *)

Lemma ler_pmuln2r n : (0 < n)%N -> {mono (@GRing.natmul R)^~ n : x y / x <= y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_pmuln2r n : (0 < n)%N -> {mono (@GRing.natmul R)^~ n : x y / x < y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pmulrnI n : (0 < n)%N -> injective ((@GRing.natmul R)^~ n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma eqr_pmuln2r n : (0 < n)%N -> {mono (@GRing.natmul R)^~ n : x y / x == y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pmulrn_lgt0 x n : (0 < n)%N -> (0 < x *+ n) = (0 < x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pmulrn_llt0 x n : (0 < n)%N -> (x *+ n < 0) = (x < 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pmulrn_lge0 x n : (0 < n)%N -> (0 <= x *+ n) = (0 <= x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pmulrn_lle0 x n : (0 < n)%N -> (x *+ n <= 0) = (x <= 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_wmuln2r x y n : x < y -> (x *+ n < y *+ n) = (0 < n)%N.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_wpmuln2r n : (0 < n)%N -> {homo (@GRing.natmul R)^~ n : x y / x < y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_wmuln2r n : {homo (@GRing.natmul R)^~ n : x y / x <= y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulrn_wge0 x n : 0 <= x -> 0 <= x *+ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulrn_wle0 x n : x <= 0 -> x *+ n <= 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_muln2r n x y : (x *+ n <= y *+ n) = ((n == 0%N) || (x <= y)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_muln2r n x y : (x *+ n < y *+ n) = ((0 < n)%N && (x < y)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma eqr_muln2r n x y : (x *+ n == y *+ n) = (n == 0)%N || (x == y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* More characteristic zero properties. *)

Lemma mulrn_eq0 x n : (x *+ n == 0) = ((n == 0)%N || (x == 0)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma eqNr x : (- x == x) = (x == 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulrIn x : x != 0 -> injective (GRing.natmul x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_wpmuln2l x :
  0 <= x -> {homo (@GRing.natmul R x) : m n / (m <= n)%N >-> m <= n}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_wnmuln2l x :
  x <= 0 -> {homo (@GRing.natmul R x) : m n / (n <= m)%N >-> m <= n}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulrn_wgt0 x n : 0 < x -> 0 < x *+ n = (0 < n)%N.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulrn_wlt0 x n : x < 0 -> x *+ n < 0 = (0 < n)%N.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_pmuln2l x :
  0 < x -> {mono (@GRing.natmul R x) : m n / (m <= n)%N >-> m <= n}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_pmuln2l x :
  0 < x -> {mono (@GRing.natmul R x) : m n / (m < n)%N >-> m < n}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_nmuln2l x :
  x < 0 -> {mono (@GRing.natmul R x) : m n / (n <= m)%N >-> m <= n}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_nmuln2l x :
  x < 0 -> {mono (@GRing.natmul R x) : m n / (n < m)%N >-> m < n}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_nat m n : (m%:R <= n%:R :> R) = (m <= n)%N.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_nat m n : (m%:R < n%:R :> R) = (m < n)%N.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma eqr_nat m n : (m%:R == n%:R :> R) = (m == n)%N.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pnatr_eq1 n : (n%:R == 1 :> R) = (n == 1)%N.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lern0 n : (n%:R <= 0 :> R) = (n == 0%N).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltrn0 n : (n%:R < 0 :> R) = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler1n n : 1 <= n%:R :> R = (1 <= n)%N. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma ltr1n n : 1 < n%:R :> R = (1 < n)%N. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma lern1 n : n%:R <= 1 :> R = (n <= 1)%N. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma ltrn1 n : n%:R < 1 :> R = (n < 1)%N. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltrN10 : -1 < 0 :> R. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma lerN10 : -1 <= 0 :> R. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma ltr10 : 1 < 0 :> R = false. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma ler10 : 1 <= 0 :> R = false. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma ltr0N1 : 0 < -1 :> R = false. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma ler0N1 : 0 <= -1 :> R = false. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pmulrn_rgt0 x n : 0 < x -> 0 < x *+ n = (0 < n)%N.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pmulrn_rlt0 x n : 0 < x -> x *+ n < 0 = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pmulrn_rge0 x n : 0 < x -> 0 <= x *+ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pmulrn_rle0 x n : 0 < x -> x *+ n <= 0 = (n == 0)%N.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nmulrn_rgt0 x n : x < 0 -> 0 < x *+ n = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nmulrn_rge0 x n : x < 0 -> 0 <= x *+ n = (n == 0)%N.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nmulrn_rle0 x n : x < 0 -> x *+ n <= 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* (x * y) compared to 0 *)
(* Remark : pmulr_rgt0 and pmulr_rge0 are defined above *)

(* x positive and y right *)
Lemma pmulr_rlt0 x y : 0 < x -> (x * y < 0) = (y < 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pmulr_rle0 x y : 0 < x -> (x * y <= 0) = (y <= 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* x positive and y left *)
Lemma pmulr_lgt0 x y : 0 < x -> (0 < y * x) = (0 < y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pmulr_lge0 x y : 0 < x -> (0 <= y * x) = (0 <= y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pmulr_llt0 x y : 0 < x -> (y * x < 0) = (y < 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pmulr_lle0 x y : 0 < x -> (y * x <= 0) = (y <= 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* x negative and y right *)
Lemma nmulr_rgt0 x y : x < 0 -> (0 < x * y) = (y < 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nmulr_rge0 x y : x < 0 -> (0 <= x * y) = (y <= 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nmulr_rlt0 x y : x < 0 -> (x * y < 0) = (0 < y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nmulr_rle0 x y : x < 0 -> (x * y <= 0) = (0 <= y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* x negative and y left *)
Lemma nmulr_lgt0 x y : x < 0 -> (0 < y * x) = (y < 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nmulr_lge0 x y : x < 0 -> (0 <= y * x) = (y <= 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nmulr_llt0 x y : x < 0 -> (y * x < 0) = (0 < y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma nmulr_lle0 x y : x < 0 -> (y * x <= 0) = (0 <= y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* weak and symmetric lemmas *)
Lemma mulr_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x * y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulr_le0 x y : x <= 0 -> y <= 0 -> 0 <= x * y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulr_ge0_le0 x y : 0 <= x -> y <= 0 -> x * y <= 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulr_le0_ge0 x y : x <= 0 -> 0 <= y -> x * y <= 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* mulr_gt0 with only one case *)

Lemma mulr_gt0 x y : 0 < x -> 0 < y -> 0 < x * y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* and reverse direction *)

Lemma mulr_ge0_gt0 x y : 0 <= x -> 0 <= y -> (0 < x * y) = (0 < x) && (0 < y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Iterated products *)

Lemma prodr_ge0 I r (P : pred I) (E : I -> R) :
  (forall i, P i -> 0 <= E i) -> 0 <= \prod_(i <- r | P i) E i.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma prodr_gt0 I r (P : pred I) (E : I -> R) :
  (forall i, P i -> 0 < E i) -> 0 < \prod_(i <- r | P i) E i.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_prod I r (P : pred I) (E1 E2 : I -> R) :
    (forall i, P i -> 0 <= E1 i <= E2 i) ->
  \prod_(i <- r | P i) E1 i <= \prod_(i <- r | P i) E2 i.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_prod I r (P : pred I) (E1 E2 : I -> R) :
    has P r -> (forall i, P i -> 0 <= E1 i < E2 i) ->
  \prod_(i <- r | P i) E1 i < \prod_(i <- r | P i) E2 i.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_prod_nat (E1 E2 : nat -> R) (n m : nat) :
   (m < n)%N -> (forall i, (m <= i < n)%N -> 0 <= E1 i < E2 i) ->
  \prod_(m <= i < n) E1 i < \prod_(m <= i < n) E2 i.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* real of mul *)

Lemma realMr x y : x != 0 -> x \is real -> (x * y \is real) = (y \is real).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma realrM x y : y != 0 -> y \is real -> (x * y \is real) = (x \is real).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma realM : {in real &, forall x y, x * y \is real}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma realrMn x n : (n != 0)%N -> (x *+ n \is real) = (x \is real).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* ler/ltr and multiplication between a positive/negative *)

Lemma ger_pmull x y : 0 < y -> (x * y <= y) = (x <= 1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gtr_pmull x y : 0 < y -> (x * y < y) = (x < 1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ger_pmulr x y : 0 < y -> (y * x <= y) = (x <= 1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gtr_pmulr x y : 0 < y -> (y * x < y) = (x < 1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_pmull x y : 0 < y -> (y <= x * y) = (1 <= x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_pmull x y : 0 < y -> (y < x * y) = (1 < x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_pmulr x y : 0 < y -> (y <= y * x) = (1 <= x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_pmulr x y : 0 < y -> (y < y * x) = (1 < x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ger_nmull x y : y < 0 -> (x * y <= y) = (1 <= x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gtr_nmull x y : y < 0 -> (x * y < y) = (1 < x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ger_nmulr x y : y < 0 -> (y * x <= y) = (1 <= x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gtr_nmulr x y : y < 0 -> (y * x < y) = (1 < x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_nmull x y : y < 0 -> (y <= x * y) = (x <= 1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_nmull x y : y < 0 -> (y < x * y) = (x < 1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_nmulr x y : y < 0 -> (y <= y * x) = (x <= 1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_nmulr x y : y < 0 -> (y < y * x) = (x < 1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* ler/ltr and multiplication between a positive/negative
   and a exterior (1 <= _) or interior (0 <= _ <= 1) *)

Lemma ler_pemull x y : 0 <= y -> 1 <= x -> y <= x * y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_nemull x y : y <= 0 -> 1 <= x -> x * y <= y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_pemulr x y : 0 <= y -> 1 <= x -> y <= y * x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_nemulr x y : y <= 0 -> 1 <= x -> y * x <= y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_pimull x y : 0 <= y -> x <= 1 -> x * y <= y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_nimull x y : y <= 0 -> x <= 1 -> y <= x * y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_pimulr x y : 0 <= y -> x <= 1 -> y * x <= y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_nimulr x y : y <= 0 -> x <= 1 -> y <= y * x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulr_ile1 x y : 0 <= x -> 0 <= y -> x <= 1 -> y <= 1 -> x * y <= 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulr_ilt1 x y : 0 <= x -> 0 <= y -> x < 1 -> y < 1 -> x * y < 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition mulr_ilte1 := (mulr_ile1, mulr_ilt1).

Lemma mulr_ege1 x y : 1 <= x -> 1 <= y -> 1 <= x * y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulr_egt1 x y : 1 < x -> 1 < y -> 1 < x * y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Definition mulr_egte1 := (mulr_ege1, mulr_egt1).
Definition mulr_cp1 := (mulr_ilte1, mulr_egte1).

(* ler and ^-1 *)

Lemma invr_gt0 x : (0 < x^-1) = (0 < x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma invr_ge0 x : (0 <= x^-1) = (0 <= x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma invr_lt0 x : (x^-1 < 0) = (x < 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma invr_le0 x : (x^-1 <= 0) = (x <= 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition invr_gte0 := (invr_ge0, invr_gt0).
Definition invr_lte0 := (invr_le0, invr_lt0).

Lemma divr_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x / y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma divr_gt0 x y : 0 < x -> 0 < y -> 0 < x / y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma realV : {mono (@GRing.inv R) : x / x \is real}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* ler and exprn *)
Lemma exprn_ge0 n x : 0 <= x -> 0 <= x ^+ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma realX n : {in real, forall x, x ^+ n \is real}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exprn_gt0 n x : 0 < x -> 0 < x ^+ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition exprn_gte0 := (exprn_ge0, exprn_gt0).

Lemma exprn_ile1 n x : 0 <= x -> x <= 1 -> x ^+ n <= 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exprn_ilt1 n x : 0 <= x -> x < 1 -> x ^+ n < 1 = (n != 0%N).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition exprn_ilte1 := (exprn_ile1, exprn_ilt1).

Lemma exprn_ege1 n x : 1 <= x -> 1 <= x ^+ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exprn_egt1 n x : 1 < x -> 1 < x ^+ n = (n != 0%N).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition exprn_egte1 := (exprn_ege1, exprn_egt1).
Definition exprn_cp1 := (exprn_ilte1, exprn_egte1).

Lemma ler_iexpr x n : (0 < n)%N -> 0 <= x -> x <= 1 -> x ^+ n <= x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_iexpr x n : 0 < x -> x < 1 -> (x ^+ n < x) = (1 < n)%N.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition lter_iexpr := (ler_iexpr, ltr_iexpr).

Lemma ler_eexpr x n : (0 < n)%N -> 1 <= x -> x <= x ^+ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_eexpr x n : 1 < x -> (x < x ^+ n) = (1 < n)%N.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition lter_eexpr := (ler_eexpr, ltr_eexpr).
Definition lter_expr := (lter_iexpr, lter_eexpr).

Lemma ler_wiexpn2l x :
  0 <= x -> x <= 1 -> {homo (GRing.exp x) : m n / (n <= m)%N >-> m <= n}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_weexpn2l x :
  1 <= x -> {homo (GRing.exp x) : m n / (m <= n)%N >-> m <= n}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ieexprn_weq1 x n : 0 <= x -> (x ^+ n == 1) = ((n == 0%N) || (x == 1)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ieexprIn x : 0 < x -> x != 1 -> injective (GRing.exp x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_iexpn2l x :
  0 < x -> x < 1 -> {mono (GRing.exp x) : m n / (n <= m)%N >-> m <= n}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_iexpn2l x :
  0 < x -> x < 1 -> {mono (GRing.exp x) : m n / (n < m)%N >-> m < n}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition lter_iexpn2l := (ler_iexpn2l, ltr_iexpn2l).

Lemma ler_eexpn2l x :
  1 < x -> {mono (GRing.exp x) : m n / (m <= n)%N >-> m <= n}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_eexpn2l x :
  1 < x -> {mono (GRing.exp x) : m n / (m < n)%N >-> m < n}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition lter_eexpn2l := (ler_eexpn2l, ltr_eexpn2l).

Lemma ltr_expn2r n x y : 0 <= x -> x < y ->  x ^+ n < y ^+ n = (n != 0%N).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_expn2r n : {in nneg & , {homo ((@GRing.exp R)^~ n) : x y / x <= y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition lter_expn2r := (ler_expn2r, ltr_expn2r).

Lemma ltr_wpexpn2r n :
  (0 < n)%N -> {in nneg & , {homo ((@GRing.exp R)^~ n) : x y / x < y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_pexpn2r n :
  (0 < n)%N -> {in nneg & , {mono ((@GRing.exp R)^~ n) : x y / x <= y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_pexpn2r n :
  (0 < n)%N -> {in nneg & , {mono ((@GRing.exp R)^~ n) : x y / x < y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition lter_pexpn2r := (ler_pexpn2r, ltr_pexpn2r).

Lemma pexpIrn n : (0 < n)%N -> {in nneg &, injective ((@GRing.exp R)^~ n)}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* expr and ler/ltr *)
Lemma expr_le1 n x : (0 < n)%N -> 0 <= x -> (x ^+ n <= 1) = (x <= 1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma expr_lt1 n x : (0 < n)%N -> 0 <= x -> (x ^+ n < 1) = (x < 1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition expr_lte1 := (expr_le1, expr_lt1).

Lemma expr_ge1 n x : (0 < n)%N -> 0 <= x -> (1 <= x ^+ n) = (1 <= x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma expr_gt1 n x : (0 < n)%N -> 0 <= x -> (1 < x ^+ n) = (1 < x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition expr_gte1 := (expr_ge1, expr_gt1).

Lemma pexpr_eq1 x n : (0 < n)%N -> 0 <= x -> (x ^+ n == 1) = (x == 1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma pexprn_eq1 x n : 0 <= x -> (x ^+ n == 1) = (n == 0%N) || (x == 1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma eqr_expn2 n x y :
  (0 < n)%N -> 0 <= x -> 0 <= y -> (x ^+ n == y ^+ n) = (x == y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrp_eq1 x : 0 <= x -> (x ^+ 2 == 1) = (x == 1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrn_eq1 x : x <= 0 -> (x ^+ 2 == 1) = (x == -1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_sqr : {in nneg &, {mono (fun x => x ^+ 2) : x y / x <= y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_sqr : {in nneg &, {mono (fun x => x ^+ 2) : x y / x < y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_pinv :
  {in [pred x in GRing.unit | 0 < x] &, {mono (@GRing.inv R) : x y /~ x <= y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_ninv :
  {in [pred x in GRing.unit | x < 0] &, {mono (@GRing.inv R) : x y /~ x <= y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_pinv :
  {in [pred x in GRing.unit | 0 < x] &, {mono (@GRing.inv R) : x y /~ x < y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_ninv :
  {in [pred x in GRing.unit | x < 0] &, {mono (@GRing.inv R) : x y /~ x < y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma invr_gt1 x : x \is a GRing.unit -> 0 < x -> (1 < x^-1) = (x < 1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma invr_ge1 x : x \is a GRing.unit -> 0 < x -> (1 <= x^-1) = (x <= 1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition invr_gte1 := (invr_ge1, invr_gt1).

Lemma invr_le1 x (ux : x \is a GRing.unit) (hx : 0 < x) :
  (x^-1 <= 1) = (1 <= x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma invr_lt1 x (ux : x \is a GRing.unit) (hx : 0 < x) : (x^-1 < 1) = (1 < x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition invr_lte1 := (invr_le1, invr_lt1).
Definition invr_cp1 := (invr_gte1, invr_lte1).

(* max and min *)

Lemma addr_min_max x y : min x y + max x y = x + y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addr_max_min x y : max x y + min x y = x + y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma minr_to_max x y : min x y = x + y - max x y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma maxr_to_min x y : max x y = x + y - min x y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_oppr_max : {in real &, {morph -%R : x y / max x y >-> min x y : R}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_oppr_min : {in real &, {morph -%R : x y / min x y >-> max x y : R}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_addr_minl : {in real & real & real, @left_distributive R R +%R min}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_addr_minr : {in real & real & real, @right_distributive R R +%R min}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_addr_maxl : {in real & real & real, @left_distributive R R +%R max}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_addr_maxr : {in real & real & real, @right_distributive R R +%R max}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma minr_pmulr x y z : 0 <= x -> x * min y z = min (x * y) (x * z).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma maxr_pmulr x y z : 0 <= x -> x * max y z = max (x * y) (x * z).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_maxr_nmulr x y z : x <= 0 -> y \is real -> z \is real ->
  x * max y z = min (x * y) (x * z).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_minr_nmulr x y z :  x <= 0 -> y \is real -> z \is real ->
  x * min y z = max (x * y) (x * z).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma minr_pmull x y z : 0 <= x -> min y z * x = min (y * x) (z * x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma maxr_pmull x y z : 0 <= x -> max y z * x = max (y * x) (z * x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_minr_nmull x y z : x <= 0 -> y \is real -> z \is real ->
  min y z * x = max (y * x) (z * x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_maxr_nmull x y z : x <= 0 -> y \is real -> z \is real ->
  max y z * x = min (y * x) (z * x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_maxrN x : x \is real -> max x (- x) = `|x|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_maxNr x : x \is real -> max (- x) x = `|x|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_minrN x : x \is real -> min x (- x) = - `|x|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_minNr x : x \is real ->  min (- x) x = - `|x|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Section RealDomainArgExtremum.

Context {I : finType} (i0 : I).
Context (P : pred I) (F : I -> R) (Pi0 : P i0).
Hypothesis F_real : {in P, forall i, F i \is real}.

Lemma real_arg_minP : extremum_spec <=%R P F [arg min_(i < i0 | P i) F i].
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_arg_maxP : extremum_spec >=%R P F [arg max_(i > i0 | P i) F i].
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End RealDomainArgExtremum.

(* norm *)

Lemma real_ler_norm x : x \is real -> x <= `|x|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* norm + add *)

Section NormedZmoduleTheory.

Variable V : normedZmodType R.
Implicit Types (u v w : V).

Lemma normr_real v : `|v| \is real. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Hint Resolve normr_real : core.

Lemma ler_norm_sum I r (G : I -> V) (P : pred I):
  `|\sum_(i <- r | P i) G i| <= \sum_(i <- r | P i) `|G i|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_norm_sub v w : `|v - w| <= `|v| + `|w|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_dist_add u v w : `|v - w| <= `|v - u| + `|u - w|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_sub_norm_add v w : `|v| - `|w| <= `|v + w|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_sub_dist v w : `|v| - `|w| <= `|v - w|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_dist_dist v w : `| `|v| - `|w| | <= `|v - w|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_dist_norm_add v w : `| `|v| - `|w| | <= `|v + w|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_nnorml v x : x < 0 -> `|v| <= x = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_nnorml v x : x <= 0 -> `|v| < x = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition lter_nnormr := (ler_nnorml, ltr_nnorml).

End NormedZmoduleTheory.

Hint Extern 0 (is_true (norm _ \is real)) => apply: normr_real : core.

Lemma real_ler_norml x y : x \is real -> (`|x| <= y) = (- y <= x <= y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_ler_normlP x y :
  x \is real -> reflect ((-x <= y) * (x <= y)) (`|x| <= y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Arguments real_ler_normlP {x y}.

Lemma real_eqr_norml x y :
  x \is real -> (`|x| == y) = ((x == y) || (x == -y)) && (0 <= y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_eqr_norm2 x y :
  x \is real -> y \is real -> (`|x| == `|y|) = (x == y) || (x == -y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_ltr_norml x y : x \is real -> (`|x| < y) = (- y < x < y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition real_lter_norml := (real_ler_norml, real_ltr_norml).

Lemma real_ltr_normlP x y :
  x \is real -> reflect ((-x < y) * (x < y)) (`|x| < y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Arguments real_ltr_normlP {x y}.

Lemma real_ler_normr x y : y \is real -> (x <= `|y|) = (x <= y) || (x <= - y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_ltr_normr x y : y \is real -> (x < `|y|) = (x < y) || (x < - y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition real_lter_normr := (real_ler_normr, real_ltr_normr).

Lemma real_ltr_normlW x y : x \is real -> `|x| < y -> x < y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_ltrNnormlW x y : x \is real -> `|x| < y -> - y < x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_ler_normlW x y : x \is real -> `|x| <= y -> x <= y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_lerNnormlW x y : x \is real -> `|x| <= y -> - y <= x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_ler_distl x y e :
  x - y \is real -> (`|x - y| <= e) = (y - e <= x <= y + e).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_ltr_distl x y e :
  x - y \is real -> (`|x - y| < e) = (y - e < x < y + e).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition real_lter_distl := (real_ler_distl, real_ltr_distl).

Lemma real_ltr_distl_addr x y e : x - y \is real -> `|x - y| < e -> x < y + e.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_ler_distl_addr x y e : x - y \is real -> `|x - y| <= e -> x <= y + e.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_ltr_distlC_addr x y e : x - y \is real -> `|x - y| < e -> y < x + e.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_ler_distlC_addr x y e : x - y \is real -> `|x - y| <= e -> y <= x + e.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_ltr_distl_subl x y e : x - y \is real -> `|x - y| < e -> x - e < y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_ler_distl_subl x y e : x - y \is real -> `|x - y| <= e -> x - e <= y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_ltr_distlC_subl x y e : x - y \is real -> `|x - y| < e -> y - e < x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_ler_distlC_subl x y e : x - y \is real -> `|x - y| <= e -> y - e <= x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* GG: pointless duplication }-( *)
Lemma eqr_norm_id x : (`|x| == x) = (0 <= x). Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma eqr_normN x : (`|x| == - x) = (x <= 0). Proof. Show. Fail (cvc5_abduct 3). Admitted.
Definition eqr_norm_idVN := =^~ (ger0_def, ler0_def).

Lemma real_exprn_even_ge0 n x : x \is real -> ~~ odd n -> 0 <= x ^+ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_exprn_even_gt0 n x :
  x \is real -> ~~ odd n -> (0 < x ^+ n) = (n == 0)%N || (x != 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_exprn_even_le0 n x :
  x \is real -> ~~ odd n -> (x ^+ n <= 0) = (n != 0%N) && (x == 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_exprn_even_lt0 n x :
  x \is real -> ~~ odd n -> (x ^+ n < 0) = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_exprn_odd_ge0 n x :
  x \is real -> odd n -> (0 <= x ^+ n) = (0 <= x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_exprn_odd_gt0 n x : x \is real -> odd n -> (0 < x ^+ n) = (0 < x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_exprn_odd_le0 n x : x \is real -> odd n -> (x ^+ n <= 0) = (x <= 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_exprn_odd_lt0 n x : x \is real -> odd n -> (x ^+ n < 0) = (x < 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* GG: Could this be a better definition of "real" ? *)
Lemma realEsqr x : (x \is real) = (0 <= x ^+ 2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_normK x : x \is real -> `|x| ^+ 2 = x ^+ 2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Binary sign ((-1) ^+ s). *)

Lemma normr_sign s : `|(-1) ^+ s : R| = 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normrMsign s x : `|(-1) ^+ s * x| = `|x|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma signr_gt0 (b : bool) : (0 < (-1) ^+ b :> R) = ~~ b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma signr_lt0 (b : bool) : ((-1) ^+ b < 0 :> R) = b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma signr_ge0 (b : bool) : (0 <= (-1) ^+ b :> R) = ~~ b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma signr_le0 (b : bool) : ((-1) ^+ b <= 0 :> R) = b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* This actually holds for char R != 2. *)
Lemma signr_inj : injective (fun b : bool => (-1) ^+ b : R).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Ternary sign (sg). *)

Lemma sgr_def x : sg x = (-1) ^+ (x < 0)%R *+ (x != 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma neqr0_sign x : x != 0 -> (-1) ^+ (x < 0)%R = sgr x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gtr0_sg x : 0 < x -> sg x = 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr0_sg x : x < 0 -> sg x = -1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgr0 : sg 0 = 0 :> R. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma sgr1 : sg 1 = 1 :> R. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma sgrN1 : sg (-1) = -1 :> R. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Definition sgrE := (sgr0, sgr1, sgrN1).

Lemma sqr_sg x : sg x ^+ 2 = (x != 0)%:R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulr_sg_eq1 x y : (sg x * y == 1) = (x != 0) && (sg x == y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulr_sg_eqN1 x y : (sg x * sg y == -1) = (x != 0) && (sg x == - sg y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgr_eq0 x : (sg x == 0) = (x == 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgr_odd n x : x != 0 -> (sg x) ^+ n = (sg x) ^+ (odd n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgrMn x n : sg (x *+ n) = (n != 0%N)%:R * sg x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgr_nat n : sg n%:R = (n != 0%N)%:R :> R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgr_id x : sg (sg x) = sg x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgr_lt0 x : (sg x < 0) = (x < 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgr_le0 x : (sgr x <= 0) = (x <= 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* sign and norm *)

Lemma realEsign x : x \is real -> x = (-1) ^+ (x < 0)%R * `|x|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma realNEsign x : x \is real -> - x = (-1) ^+ (0 < x)%R * `|x|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_normrEsign (x : R) (xR : x \is real) : `|x| = (-1) ^+ (x < 0)%R * x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* GG: pointless duplication... *)
Lemma real_mulr_sign_norm x : x \is real -> (-1) ^+ (x < 0)%R * `|x| = x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_mulr_Nsign_norm x : x \is real -> (-1) ^+ (0 < x)%R * `|x| = - x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma realEsg x : x \is real -> x = sgr x * `|x|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normr_sg x : `|sg x| = (x != 0)%:R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgr_norm x : sg `|x| = (x != 0)%:R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* leif *)

Lemma leif_nat_r m n C : (m%:R <= n%:R ?= iff C :> R) = (m <= n ?= iff C)%N.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leif_subLR x y z C : (x - y <= z ?= iff C) = (x <= z + y ?= iff C).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leif_subRL x y z C : (x <= y - z ?= iff C) = (x + z <= y ?= iff C).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leif_add x1 y1 C1 x2 y2 C2 :
    x1 <= y1 ?= iff C1 -> x2 <= y2 ?= iff C2 ->
  x1 + x2 <= y1 + y2 ?= iff C1 && C2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leif_sum (I : finType) (P C : pred I) (E1 E2 : I -> R) :
    (forall i, P i -> E1 i <= E2 i ?= iff C i) ->
  \sum_(i | P i) E1 i <= \sum_(i | P i) E2 i ?= iff [forall (i | P i), C i].
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leif_0_sum (I : finType) (P C : pred I) (E : I -> R) :
    (forall i, P i -> 0 <= E i ?= iff C i) ->
  0 <= \sum_(i | P i) E i ?= iff [forall (i | P i), C i].
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_leif_norm x : x \is real -> x <= `|x| ?= iff (0 <= x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leif_pmul x1 x2 y1 y2 C1 C2 :
    0 <= x1 -> 0 <= x2 -> x1 <= y1 ?= iff C1 -> x2 <= y2 ?= iff C2 ->
  x1 * x2 <= y1 * y2 ?= iff (y1 * y2 == 0) || C1 && C2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leif_nmul x1 x2 y1 y2 C1 C2 :
    y1 <= 0 -> y2 <= 0 -> x1 <= y1 ?= iff C1 -> x2 <= y2 ?= iff C2 ->
  y1 * y2 <= x1 * x2 ?= iff (x1 * x2 == 0) || C1 && C2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leif_pprod (I : finType) (P C : pred I) (E1 E2 : I -> R) :
    (forall i, P i -> 0 <= E1 i) ->
    (forall i, P i -> E1 i <= E2 i ?= iff C i) ->
  let pi E := \prod_(i | P i) E i in
  pi E1 <= pi E2 ?= iff (pi E2 == 0) || [forall (i | P i), C i].
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* lteif *)

Lemma subr_lteifr0 C x y : (y - x < 0 ?<= if C) = (y < x ?<= if C).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma subr_lteif0r C x y : (0 < y - x ?<= if C) = (x < y ?<= if C).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition subr_lteif0 := (subr_lteifr0, subr_lteif0r).

Lemma lteif01 C : 0 < 1 ?<= if C :> R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lteif_oppl C x y : - x < y ?<= if C = (- y < x ?<= if C).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lteif_oppr C x y : x < - y ?<= if C = (y < - x ?<= if C).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lteif_0oppr C x : 0 < - x ?<= if C = (x < 0 ?<= if C).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lteif_oppr0 C x : - x < 0 ?<= if C = (0 < x ?<= if C).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lteif_opp2 C : {mono -%R : x y /~ x < y ?<= if C :> R}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition lteif_oppE := (lteif_0oppr, lteif_oppr0, lteif_opp2).

Lemma lteif_add2l C x : {mono +%R x : y z / y < z ?<= if C}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lteif_add2r C x : {mono +%R^~ x : y z / y < z ?<= if C}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition lteif_add2 := (lteif_add2l, lteif_add2r).

Lemma lteif_subl_addr C x y z : (x - y < z ?<= if C) = (x < z + y ?<= if C).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lteif_subr_addr C x y z : (x < y - z ?<= if C) = (x + z < y ?<= if C).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition lteif_sub_addr := (lteif_subl_addr, lteif_subr_addr).

Lemma lteif_subl_addl C x y z : (x - y < z ?<= if C) = (x < y + z ?<= if C).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lteif_subr_addl C x y z : (x < y - z ?<= if C) = (z + x < y ?<= if C).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition lteif_sub_addl := (lteif_subl_addl, lteif_subr_addl).

Lemma lteif_pmul2l C x : 0 < x -> {mono *%R x : y z / y < z ?<= if C}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lteif_pmul2r C x : 0 < x -> {mono *%R^~ x : y z / y < z ?<= if C}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lteif_nmul2l C x : x < 0 -> {mono *%R x : y z /~ y < z ?<= if C}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lteif_nmul2r C x : x < 0 -> {mono *%R^~ x : y z /~ y < z ?<= if C}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lteif_nnormr C x y : y < 0 ?<= if ~~ C -> (`|x| < y ?<= if C) = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_lteifNE x y C : x \is Num.real -> y \is Num.real ->
  x < y ?<= if ~~ C = ~~ (y < x ?<= if C).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_lteif_norml C x y :
  x \is Num.real ->
  (`|x| < y ?<= if C) = ((- y < x ?<= if C) && (x < y ?<= if C)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_lteif_normr C x y :
  y \is Num.real ->
  (x < `|y| ?<= if C) = ((x < y ?<= if C) || (x < - y ?<= if C)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_lteif_distl C x y e :
  x - y \is real ->
  (`|x - y| < e ?<= if C) = (y - e < x ?<= if C) && (x < y + e ?<= if C).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Mean inequalities. *)

Lemma real_leif_mean_square_scaled x y :
  x \is real -> y \is real -> x * y *+ 2 <= x ^+ 2 + y ^+ 2 ?= iff (x == y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_leif_AGM2_scaled x y :
  x \is real -> y \is real -> x * y *+ 4 <= (x + y) ^+ 2 ?= iff (x == y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leif_AGM_scaled (I : finType) (A : {pred I}) (E : I -> R) (n := #|A|) :
    {in A, forall i, 0 <= E i *+ n} ->
  \prod_(i in A) (E i *+ n) <= (\sum_(i in A) E i) ^+ n
                            ?= iff [forall i in A, forall j in A, E i == E j].
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Polynomial bound. *)

Implicit Type p : {poly R}.

Lemma poly_disk_bound p b : {ub | forall x, `|x| <= b -> `|p.[x]| <= ub}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End NumDomainOperationTheory.

#[global] Hint Resolve ler_opp2 ltr_opp2 real0 real1 normr_real : core.
Arguments ler_sqr {R} [x y].
Arguments ltr_sqr {R} [x y].
Arguments signr_inj {R} [x1 x2].
Arguments real_ler_normlP {R x y}.
Arguments real_ltr_normlP {R x y}.

Section NumDomainMonotonyTheoryForReals.
Local Open Scope order_scope.

Variables (R R' : numDomainType) (D : pred R) (f : R -> R') (f' : R -> nat).
Implicit Types (m n p : nat) (x y z : R) (u v w : R').

Lemma real_mono :
  {homo f : x y / x < y} -> {in real &, {mono f : x y / x <= y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_nmono :
  {homo f : x y /~ x < y} -> {in real &, {mono f : x y /~ x <= y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_mono_in :
    {in D &, {homo f : x y / x < y}} ->
  {in [pred x in D | x \is real] &, {mono f : x y / x <= y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_nmono_in :
    {in D &, {homo f : x y /~ x < y}} ->
  {in [pred x in D | x \is real] &, {mono f : x y /~ x <= y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma realn_mono : {homo f' : x y / x < y >-> (x < y)} ->
  {in real &, {mono f' : x y / x <= y >-> (x <= y)}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma realn_nmono : {homo f' : x y / y < x >-> (x < y)} ->
  {in real &, {mono f' : x y / y <= x >-> (x <= y)}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma realn_mono_in : {in D &, {homo f' : x y / x < y >-> (x < y)}} ->
  {in [pred x in D | x \is real] &, {mono f' : x y / x <= y >-> (x <= y)}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma realn_nmono_in : {in D &, {homo f' : x y / y < x >-> (x < y)}} ->
  {in [pred x in D | x \is real] &, {mono f' : x y / y <= x >-> (x <= y)}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End NumDomainMonotonyTheoryForReals.

Section FinGroup.

Import GroupScope.

Variables (R : numDomainType) (gT : finGroupType).
Implicit Types G : {group gT}.

Lemma natrG_gt0 G : #|G|%:R > 0 :> R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma natrG_neq0 G : #|G|%:R != 0 :> R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma natr_indexg_gt0 G B : #|G : B|%:R > 0 :> R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma natr_indexg_neq0 G B : #|G : B|%:R != 0 :> R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End FinGroup.

Section NumFieldTheory.

Variable F : numFieldType.
Implicit Types x y z t : F.

Lemma unitf_gt0 x : 0 < x -> x \is a GRing.unit.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma unitf_lt0 x : x < 0 -> x \is a GRing.unit.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lef_pinv : {in pos &, {mono (@GRing.inv F) : x y /~ x <= y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lef_ninv : {in neg &, {mono (@GRing.inv F) : x y /~ x <= y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltf_pinv : {in pos &, {mono (@GRing.inv F) : x y /~ x < y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltf_ninv: {in neg &, {mono (@GRing.inv F) : x y /~ x < y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition ltef_pinv := (lef_pinv, ltf_pinv).
Definition ltef_ninv := (lef_ninv, ltf_ninv).

Lemma invf_gt1 x : 0 < x -> (1 < x^-1) = (x < 1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma invf_ge1 x : 0 < x -> (1 <= x^-1) = (x <= 1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition invf_gte1 := (invf_ge1, invf_gt1).

Lemma invf_le1 x : 0 < x -> (x^-1 <= 1) = (1 <= x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma invf_lt1 x : 0 < x -> (x^-1 < 1) = (1 < x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition invf_lte1 := (invf_le1, invf_lt1).
Definition invf_cp1 := (invf_gte1, invf_lte1).

(* These lemma are all combinations of mono(LR|RL) with ler_[pn]mul2[rl]. *)
Lemma ler_pdivl_mulr z x y : 0 < z -> (x <= y / z) = (x * z <= y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_pdivl_mulr z x y : 0 < z -> (x < y / z) = (x * z < y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition lter_pdivl_mulr := (ler_pdivl_mulr, ltr_pdivl_mulr).

Lemma ler_pdivr_mulr z x y : 0 < z -> (y / z <= x) = (y <= x * z).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_pdivr_mulr z x y : 0 < z -> (y / z < x) = (y < x * z).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition lter_pdivr_mulr := (ler_pdivr_mulr, ltr_pdivr_mulr).

Lemma ler_pdivl_mull z x y : 0 < z -> (x <= z^-1 * y) = (z * x <= y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_pdivl_mull z x y : 0 < z -> (x < z^-1 * y) = (z * x < y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition lter_pdivl_mull := (ler_pdivl_mull, ltr_pdivl_mull).

Lemma ler_pdivr_mull z x y : 0 < z -> (z^-1 * y <= x) = (y <= z * x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_pdivr_mull z x y : 0 < z -> (z^-1 * y < x) = (y < z * x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition lter_pdivr_mull := (ler_pdivr_mull, ltr_pdivr_mull).

Lemma ler_ndivl_mulr z x y : z < 0 -> (x <= y / z) = (y <= x * z).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_ndivl_mulr z x y : z < 0 -> (x < y / z) = (y < x * z).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition lter_ndivl_mulr := (ler_ndivl_mulr, ltr_ndivl_mulr).

Lemma ler_ndivr_mulr z x y : z < 0 -> (y / z <= x) = (x * z <= y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_ndivr_mulr z x y : z < 0 -> (y / z < x) = (x * z < y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition lter_ndivr_mulr := (ler_ndivr_mulr, ltr_ndivr_mulr).

Lemma ler_ndivl_mull z x y : z < 0 -> (x <= z^-1 * y) = (y <= z * x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_ndivl_mull z x y : z < 0 -> (x < z^-1 * y) = (y < z * x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition lter_ndivl_mull := (ler_ndivl_mull, ltr_ndivl_mull).

Lemma ler_ndivr_mull z x y : z < 0 -> (z^-1 * y <= x) = (z * x <= y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_ndivr_mull z x y : z < 0 -> (z^-1 * y < x) = (z * x < y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition lter_ndivr_mull := (ler_ndivr_mull, ltr_ndivr_mull).

Lemma natf_div m d : (d %| m)%N -> (m %/ d)%:R = m%:R / d%:R :> F.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normfV : {morph (@norm F F) : x / x ^-1}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normf_div : {morph (@norm F F) : x y / x / y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma invr_sg x : (sg x)^-1 = sgr x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgrV x : sgr x^-1 = sgr x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma splitr x : x = x / 2%:R + x / 2%:R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* lteif *)

Lemma lteif_pdivl_mulr C z x y :
  0 < z -> x < y / z ?<= if C = (x * z < y ?<= if C).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lteif_pdivr_mulr C z x y :
  0 < z -> y / z < x ?<= if C = (y < x * z ?<= if C).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lteif_pdivl_mull C z x y :
  0 < z -> x < z^-1 * y ?<= if C = (z * x < y ?<= if C).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lteif_pdivr_mull C z x y :
  0 < z -> z^-1 * y < x ?<= if C = (y < z * x ?<= if C).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lteif_ndivl_mulr C z x y :
  z < 0 -> x < y / z ?<= if C = (y < x * z ?<= if C).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lteif_ndivr_mulr C z x y :
  z < 0 -> y / z < x ?<= if C = (x * z < y ?<= if C).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lteif_ndivl_mull C z x y :
  z < 0 -> x < z^-1 * y ?<= if C = (y < z * x ?<= if C).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lteif_ndivr_mull C z x y :
  z < 0 -> z^-1 * y < x ?<= if C = (z * x < y ?<= if C).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Interval midpoint. *)

Local Notation mid x y := ((x + y) / 2).

Lemma midf_le x y : x <= y -> (x <= mid x y) * (mid x y <= y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma midf_lt x y : x < y -> (x < mid x y) * (mid x y < y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition midf_lte := (midf_le, midf_lt).

Lemma ler_addgt0Pr x y : reflect (forall e, e > 0 -> x <= y + e) (x <= y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_addgt0Pl x y : reflect (forall e, e > 0 -> x <= e + y) (x <= y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lt_le a b : (forall x, x < a -> x < b) -> a <= b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma gt_ge a b : (forall x, b < x -> a < x) -> a <= b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* The AGM, unscaled but without the nth root. *)

Lemma real_leif_mean_square x y :
  x \is real -> y \is real -> x * y <= mid (x ^+ 2) (y ^+ 2) ?= iff (x == y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma real_leif_AGM2 x y :
  x \is real -> y \is real -> x * y <= mid x y ^+ 2 ?= iff (x == y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leif_AGM (I : finType) (A : {pred I}) (E : I -> F) :
    let n := #|A| in let mu := (\sum_(i in A) E i) / n%:R in
    {in A, forall i, 0 <= E i} ->
  \prod_(i in A) E i <= mu ^+ n
                     ?= iff [forall i in A, forall j in A, E i == E j].
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Implicit Type p : {poly F}.
Lemma Cauchy_root_bound p : p != 0 -> {b | forall x, root p x -> `|x| <= b}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Import GroupScope.

Lemma natf_indexg (gT : finGroupType) (G H : {group gT}) :
  H \subset G -> #|G : H|%:R = (#|G|%:R / #|H|%:R)%R :> F.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End NumFieldTheory.

Section RealDomainTheory.

Variable R : realDomainType.
Implicit Types x y z t : R.

Lemma num_real x : x \is real. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Hint Resolve num_real : core.

Lemma lerP x y : ler_xor_gt x y (min y x) (min x y) (max y x) (max x y)
                                `|x - y| `|y - x| (x <= y) (y < x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltrP x y : ltr_xor_ge x y (min y x) (min x y) (max y x) (max x y)
                                `|x - y| `|y - x| (y <= x) (x < y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltrgtP x y :
   comparer x y  (min y x) (min x y) (max y x) (max x y)
                 `|x - y| `|y - x| (y == x) (x == y)
                 (x >= y) (x <= y) (x > y) (x < y) .
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ger0P x : ger0_xor_lt0 x (min 0 x) (min x 0) (max 0 x) (max x 0)
                                `|x| (x < 0) (0 <= x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler0P x : ler0_xor_gt0 x (min 0 x) (min x 0) (max 0 x) (max x 0)
                                `|x| (0 < x) (x <= 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltrgt0P x : comparer0 x (min 0 x) (min x 0) (max 0 x) (max x 0)
  `|x| (0 == x) (x == 0) (x <= 0) (0 <= x) (x < 0) (x > 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* sign *)

Lemma mulr_lt0 x y :
  (x * y < 0) = [&& x != 0, y != 0 & (x < 0) (+) (y < 0)].
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma neq0_mulr_lt0 x y :
  x != 0 -> y != 0 -> (x * y < 0) = (x < 0) (+) (y < 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulr_sign_lt0 (b : bool) x :
  ((-1) ^+ b * x < 0) = (x != 0) && (b (+) (x < 0)%R).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* sign & norm *)

Lemma mulr_sign_norm x : (-1) ^+ (x < 0)%R * `|x| = x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulr_Nsign_norm x : (-1) ^+ (0 < x)%R * `|x| = - x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma numEsign x : x = (-1) ^+ (x < 0)%R * `|x|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma numNEsign x : -x = (-1) ^+ (0 < x)%R * `|x|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normrEsign x : `|x| = (-1) ^+ (x < 0)%R * x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End RealDomainTheory.

#[global] Hint Resolve num_real : core.

Section RealDomainOperations.

Notation "[ 'arg' 'min_' ( i < i0 | P ) F ]" :=
    (Order.arg_min (disp := ring_display) i0 (fun i => P%B) (fun i => F)) :
   ring_scope.

Notation "[ 'arg' 'min_' ( i < i0 'in' A ) F ]" :=
  [arg min_(i < i0 | i \in A) F] : ring_scope.

Notation "[ 'arg' 'min_' ( i < i0 ) F ]" := [arg min_(i < i0 | true) F] :
  ring_scope.

Notation "[ 'arg' 'max_' ( i > i0 | P ) F ]" :=
   (Order.arg_max (disp := ring_display) i0 (fun i => P%B) (fun i => F)) :
  ring_scope.

Notation "[ 'arg' 'max_' ( i > i0 'in' A ) F ]" :=
    [arg max_(i > i0 | i \in A) F] : ring_scope.

Notation "[ 'arg' 'max_' ( i > i0 ) F ]" := [arg max_(i > i0 | true) F] :
  ring_scope.

(* sgr section *)

Variable R : realDomainType.
Implicit Types x y z t : R.
Let numR_real := @num_real R.
Hint Resolve numR_real : core.

Lemma sgr_cp0 x :
  ((sg x == 1) = (0 < x)) *
  ((sg x == -1) = (x < 0)) *
  ((sg x == 0) = (x == 0)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Variant sgr_val x : R -> bool -> bool -> bool -> bool -> bool -> bool
  -> bool -> bool -> bool -> bool -> bool -> bool -> R -> Set :=
  | SgrNull of x = 0 : sgr_val x 0 true true true true false false
    true false false true false false 0
  | SgrPos of x > 0 : sgr_val x x false false true false false true
    false false true false false true 1
  | SgrNeg of x < 0 : sgr_val x (- x) false true false false true false
    false true false false true false (-1).

Lemma sgrP x :
  sgr_val x `|x| (0 == x) (x <= 0) (0 <= x) (x == 0) (x < 0) (0 < x)
                 (0 == sg x) (-1 == sg x) (1 == sg x)
                 (sg x == 0)  (sg x == -1) (sg x == 1) (sg x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normrEsg x : `|x| = sg x * x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma numEsg x : x = sg x * `|x|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* GG: duplicate! *)
Lemma mulr_sg_norm x : sg x * `|x| = x. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgrM x y : sg (x * y) = sg x * sg y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgrN x : sg (- x) = - sg x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgrX n x : sg (x ^+ n) = (sg x) ^+ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgr_smul x y : sg (sg x * y) = sg x * sg y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgr_gt0 x : (sg x > 0) = (x > 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sgr_ge0 x : (sgr x >= 0) = (x >= 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* norm section *)

Lemma ler_norm x : (x <= `|x|).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_norml x y : (`|x| <= y) = (- y <= x <= y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_normlP x y : reflect ((- x <= y) * (x <= y)) (`|x| <= y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Arguments ler_normlP {x y}.

Lemma eqr_norml x y : (`|x| == y) = ((x == y) || (x == -y)) && (0 <= y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma eqr_norm2 x y : (`|x| == `|y|) = (x == y) || (x == -y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_norml x y : (`|x| < y) = (- y < x < y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition lter_norml := (ler_norml, ltr_norml).

Lemma ltr_normlP x y : reflect ((-x < y) * (x < y)) (`|x| < y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Arguments ltr_normlP {x y}.

Lemma ltr_normlW x y : `|x| < y -> x < y. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltrNnormlW x y : `|x| < y -> - y < x. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_normlW x y : `|x| <= y -> x <= y. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lerNnormlW x y : `|x| <= y -> - y <= x. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_normr x y : (x <= `|y|) = (x <= y) || (x <= - y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_normr x y : (x < `|y|) = (x < y) || (x < - y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition lter_normr := (ler_normr, ltr_normr).

Lemma ler_distl x y e : (`|x - y| <= e) = (y - e <= x <= y + e).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_distl x y e : (`|x - y| < e) = (y - e < x < y + e).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition lter_distl := (ler_distl, ltr_distl).

Lemma ltr_distlC x y e : (`|x - y| < e) = (x - e < y < x + e).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_distlC x y e : (`|x - y| <= e) = (x - e <= y <= x + e).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition lter_distlC := (ler_distlC, ltr_distlC).

Lemma ltr_distl_addr x y e : `|x - y| < e -> x < y + e.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_distl_addr x y e : `|x - y| <= e -> x <= y + e.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_distlC_addr x y e : `|x - y| < e -> y < x + e.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_distlC_addr x y e : `|x - y| <= e -> y <= x + e.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_distl_subl x y e : `|x - y| < e -> x - e < y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_distl_subl x y e : `|x - y| <= e -> x - e <= y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_distlC_subl x y e : `|x - y| < e -> y - e < x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_distlC_subr x y e : `|x - y| <= e -> y - e <= x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exprn_even_ge0 n x : ~~ odd n -> 0 <= x ^+ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exprn_even_gt0 n x : ~~ odd n -> (0 < x ^+ n) = (n == 0)%N || (x != 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exprn_even_le0 n x : ~~ odd n -> (x ^+ n <= 0) = (n != 0%N) && (x == 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exprn_even_lt0 n x : ~~ odd n -> (x ^+ n < 0) = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exprn_odd_ge0 n x : odd n -> (0 <= x ^+ n) = (0 <= x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exprn_odd_gt0 n x : odd n -> (0 < x ^+ n) = (0 < x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exprn_odd_le0 n x : odd n -> (x ^+ n <= 0) = (x <= 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exprn_odd_lt0 n x : odd n -> (x ^+ n < 0) = (x < 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* lteif *)

Lemma lteif_norml C x y :
  (`|x| < y ?<= if C) = (- y < x ?<= if C) && (x < y ?<= if C).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lteif_normr C x y :
  (x < `|y| ?<= if C) = (x < y ?<= if C) || (x < - y ?<= if C).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lteif_distl C x y e :
  (`|x - y| < e ?<= if C) = (y - e < x ?<= if C) && (x < y + e ?<= if C).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Special lemmas for squares. *)

Lemma sqr_ge0 x : 0 <= x ^+ 2. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqr_norm_eq1 x : (x ^+ 2 == 1) = (`|x| == 1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leif_mean_square_scaled x y :
  x * y *+ 2 <= x ^+ 2 + y ^+ 2 ?= iff (x == y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leif_AGM2_scaled x y : x * y *+ 4 <= (x + y) ^+ 2 ?= iff (x == y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Section MinMax.

Lemma oppr_max : {morph -%R : x y / max x y >-> min x y : R}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma oppr_min : {morph -%R : x y / min x y >-> max x y : R}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addr_minl : @left_distributive R R +%R min.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addr_minr : @right_distributive R R +%R min.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addr_maxl : @left_distributive R R +%R max.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addr_maxr : @right_distributive R R +%R max.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma minr_nmulr x y z : x <= 0 -> x * min y z = max (x * y) (x * z).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma maxr_nmulr x y z : x <= 0 -> x * max y z = min (x * y) (x * z).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma minr_nmull x y z : x <= 0 -> min y z * x = max (y * x) (z * x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma maxr_nmull x y z : x <= 0 -> max y z * x = min (y * x) (z * x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma maxrN x : max x (- x) = `|x|.   Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma maxNr x : max (- x) x = `|x|.   Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma minrN x : min x (- x) = - `|x|. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma minNr x : min (- x) x = - `|x|. Proof. Show. Fail (cvc5_abduct 3). Admitted.

End MinMax.

Section PolyBounds.

Variable p : {poly R}.

Lemma poly_itv_bound a b : {ub | forall x, a <= x <= b -> `|p.[x]| <= ub}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma monic_Cauchy_bound : p \is monic -> {b | forall x, x >= b -> p.[x] > 0}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End PolyBounds.

End RealDomainOperations.

Section RealField.

Variables (F : realFieldType) (x y : F).

Lemma leif_mean_square : x * y <= (x ^+ 2 + y ^+ 2) / 2 ?= iff (x == y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leif_AGM2 : x * y <= ((x + y) / 2)^+ 2 ?= iff (x == y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End RealField.

Section ArchimedeanFieldTheory.

Variables (F : archiFieldType) (x : F).

Lemma archi_boundP : 0 <= x -> x < (bound x)%:R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma upper_nthrootP i : (bound x <= i)%N -> x < 2 ^+ i.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End ArchimedeanFieldTheory.

Section RealClosedFieldTheory.

Variable R : rcfType.
Implicit Types a x y : R.

Lemma poly_ivt : real_closed_axiom R. Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Square Root theory *)

Lemma sqrtr_ge0 a : 0 <= sqrt a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Hint Resolve sqrtr_ge0 : core.

Lemma sqr_sqrtr a : 0 <= a -> sqrt a ^+ 2 = a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler0_sqrtr a : a <= 0 -> sqrt a = 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr0_sqrtr a : a < 0 -> sqrt a = 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Variant sqrtr_spec a : R -> bool -> bool -> R -> Type :=
| IsNoSqrtr of a < 0 : sqrtr_spec a a false true 0
| IsSqrtr b of 0 <= b : sqrtr_spec a (b ^+ 2) true false b.

Lemma sqrtrP a : sqrtr_spec a a (0 <= a) (a < 0) (sqrt a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrtr_sqr a : sqrt (a ^+ 2) = `|a|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrtrM a b : 0 <= a -> sqrt (a * b) = sqrt a * sqrt b.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrtr0 : sqrt 0 = 0 :> R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrtr1 : sqrt 1 = 1 :> R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrtr_eq0 a : (sqrt a == 0) = (a <= 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrtr_gt0 a : (0 < sqrt a) = (0 < a).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma eqr_sqrt a b : 0 <= a -> 0 <= b -> (sqrt a == sqrt b) = (a == b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_wsqrtr : {homo @sqrt R : a b / a <= b}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_psqrt : {in @pos R &, {mono sqrt : a b / a <= b}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_sqrt a b : 0 < b -> (sqrt a <= sqrt b) = (a <= b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_sqrt a b : 0 < b -> (sqrt a < sqrt b) = (a < b).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrtrV x : 0 <= x -> sqrt (x^-1) = (sqrt x)^-1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End RealClosedFieldTheory.

Definition conjC {C : numClosedFieldType} : {rmorphism C -> C} :=
 ClosedField.conj_op (ClosedField.conj_mixin (ClosedField.class C)).
Notation "z ^*" := (@conjC _ z) (at level 2, format "z ^*") : ring_scope.

Definition imaginaryC {C : numClosedFieldType} : C :=
 ClosedField.imaginary (ClosedField.conj_mixin (ClosedField.class C)).
Notation "'i" := (@imaginaryC _) (at level 0) : ring_scope.

Section ClosedFieldTheory.

Variable C : numClosedFieldType.
Implicit Types a x y z : C.

Definition normCK x : `|x| ^+ 2 = x * x^*.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrCi : 'i ^+ 2 = -1 :> C. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulCii : 'i * 'i = -1 :> C. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma conjCK : involutive (@conjC C).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Let Re2 z := z + z^*.
Definition nnegIm z := (0 <= imaginaryC * (z^* - z)).
Definition argCle y z := nnegIm z ==> nnegIm y && (Re2 z <= Re2 y).

Variant rootC_spec n (x : C) : Type :=
  RootCspec (y : C) of if (n > 0)%N then y ^+ n = x else y = 0
                        & forall z, (n > 0)%N -> z ^+ n = x -> argCle y z.

Fact rootC_subproof n x : rootC_spec n x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition nthroot n x := let: RootCspec y _ _ := rootC_subproof n x in y.
Notation "n .-root" := (nthroot n) : ring_scope.
Notation sqrtC := 2.-root.

Fact Re_lock : unit. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Fact Im_lock : unit. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Definition Re z := locked_with Re_lock ((z + z^*) / 2%:R).
Definition Im z := locked_with Im_lock ('i * (z^* - z) / 2%:R).
Notation "'Re z" := (Re z) : ring_scope.
Notation "'Im z" := (Im z) : ring_scope.

Lemma ReE z : 'Re z = (z + z^*) / 2%:R. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma ImE z : 'Im z = 'i * (z^* - z) / 2%:R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Let nz2 : 2 != 0 :> C. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normCKC x : `|x| ^+ 2 = x^* * x. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mul_conjC_ge0 x : 0 <= x * x^*.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mul_conjC_gt0 x : (0 < x * x^*) = (x != 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mul_conjC_eq0 x : (x * x^* == 0) = (x == 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma conjC_ge0 x : (0 <= x^*) = (0 <= x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma conjC_nat n : (n%:R)^* = n%:R :> C. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma conjC0 : 0^* = 0 :> C. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma conjC1 : 1^* = 1 :> C. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma conjCN1 : (- 1)^* = - 1 :> C. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma conjC_eq0 x : (x^* == 0) = (x == 0). Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma invC_norm x : x^-1 = `|x| ^- 2 * x^*.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Real number subset. *)

Lemma CrealE x : (x \is real) = (x^* == x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma CrealP {x} : reflect (x^* = x) (x \is real).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma conj_Creal x : x \is real -> x^* = x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma conj_normC z : `|z|^* = `|z|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma CrealJ : {mono (@conjC C) : x / x \is Num.real}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma geC0_conj x : 0 <= x -> x^* = x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma geC0_unit_exp x n : 0 <= x -> (x ^+ n.+1 == 1) = (x == 1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Elementary properties of roots. *)

Ltac case_rootC := rewrite /nthroot; case: (rootC_subproof _ _).

Lemma root0C x : 0.-root x = 0. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rootCK n : (n > 0)%N -> cancel n.-root (fun x => x ^+ n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma root1C x : 1.-root x = x. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rootC0 n : n.-root 0 = 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rootC_inj n : (n > 0)%N -> injective n.-root.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma eqr_rootC n : (n > 0)%N -> {mono n.-root : x y / x == y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rootC_eq0 n x : (n > 0)%N -> (n.-root x == 0) = (x == 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Rectangular coordinates. *)

Lemma nonRealCi : ('i : C) \isn't real.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma neq0Ci : 'i != 0 :> C.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normCi : `|'i| = 1 :> C.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma invCi : 'i^-1 = - 'i :> C.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma conjCi : 'i^* = - 'i :> C.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Crect x : x = 'Re x + 'i * 'Im x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma eqCP x y : x = y <-> ('Re x = 'Re y) /\ ('Im x = 'Im y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma eqC x y : (x == y) = ('Re x == 'Re y) && ('Im x == 'Im y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Creal_Re x : 'Re x \is real.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Creal_Im x : 'Im x \is real.
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Hint Resolve Creal_Re Creal_Im : core.

Fact Re_is_additive : additive Re.
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Canonical Re_additive := Additive Re_is_additive.

Fact Im_is_additive : additive Im.
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Canonical Im_additive := Additive Im_is_additive.

Lemma Creal_ImP z : reflect ('Im z = 0) (z \is real).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Creal_ReP z : reflect ('Re z = z) (z \in real).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ReMl : {in real, forall x, {morph Re : z / x * z}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ReMr : {in real, forall x, {morph Re : z / z * x}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ImMl : {in real, forall x, {morph Im : z / x * z}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ImMr : {in real, forall x, {morph Im : z / z * x}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Re_i : 'Re 'i = 0. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Im_i : 'Im 'i = 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Re_conj z : 'Re z^* = 'Re z.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Im_conj z : 'Im z^* = - 'Im z.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Re_rect : {in real &, forall x y, 'Re (x + 'i * y) = x}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Im_rect : {in real &, forall x y, 'Im (x + 'i * y) = y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma conjC_rect : {in real &, forall x y, (x + 'i * y)^* = x - 'i * y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma addC_rect x1 y1 x2 y2 :
  (x1 + 'i * y1) + (x2 + 'i * y2) = x1 + x2 + 'i * (y1 + y2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma oppC_rect x y : - (x + 'i * y)  = - x + 'i * (- y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma subC_rect x1 y1 x2 y2 :
  (x1 + 'i * y1) - (x2 + 'i * y2) = x1 - x2 + 'i * (y1 - y2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma mulC_rect x1 y1 x2 y2 : (x1 + 'i * y1) * (x2 + 'i * y2) =
                              x1 * x2 - y1 * y2 + 'i * (x1 * y2 + x2 * y1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ImM x y : 'Im (x * y) = 'Re x * 'Im y + 'Re y * 'Im x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ImMil x : 'Im ('i * x) = 'Re x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ReMil x : 'Re ('i * x) = - 'Im x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ReMir x : 'Re (x * 'i) = - 'Im x. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ImMir x : 'Im (x * 'i) = 'Re x. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ReM x y : 'Re (x * y) = 'Re x * 'Re y - 'Im x * 'Im y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normC2_rect :
  {in real &, forall x y, `|x + 'i * y| ^+ 2 = x ^+ 2 + y ^+ 2}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normC2_Re_Im z : `|z| ^+ 2 = 'Re z ^+ 2 + 'Im z ^+ 2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma invC_Crect x y : (x + 'i * y)^-1  = (x^* - 'i * y^*) / `|x + 'i * y| ^+ 2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma invC_rect :
  {in real &, forall x y, (x + 'i * y)^-1  = (x - 'i * y) / (x ^+ 2 + y ^+ 2)}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ImV x : 'Im x^-1 = - 'Im x / `|x| ^+ 2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ReV x : 'Re x^-1 = 'Re x / `|x| ^+ 2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rectC_mulr x y z : (x + 'i * y) * z = x * z + 'i * (y * z).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rectC_mull x y z : z * (x + 'i * y) = z * x + 'i * (z * y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma divC_Crect x1 y1 x2 y2 :
  (x1 + 'i * y1) / (x2 + 'i * y2) =
  (x1 * x2^* + y1 * y2^* + 'i * (x2^* * y1 - x1 * y2^*)) /
    `|x2 + 'i * y2| ^+ 2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma divC_rect x1 y1 x2 y2 :
     x1 \is real -> y1 \is real -> x2 \is real -> y2 \is real ->
  (x1 + 'i * y1) / (x2 + 'i * y2) =
  (x1 * x2 + y1 * y2 + 'i * (x2 * y1 - x1 * y2)) /
    (x2 ^+ 2 + y2 ^+ 2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Im_div x y : 'Im (x / y) = ('Re y * 'Im x - 'Re x * 'Im y) / `|y| ^+ 2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Re_div x y : 'Re (x / y) = ('Re x * 'Re y + 'Im x * 'Im y) / `|y| ^+ 2.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leif_normC_Re_Creal z : `|'Re z| <= `|z| ?= iff (z \is real).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma leif_Re_Creal z : 'Re z <= `|z| ?= iff (0 <= z).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Equality from polar coordinates, for the upper plane. *)
Lemma eqC_semipolar x y :
  `|x| = `|y| -> 'Re x = 'Re y -> 0 <= 'Im x * 'Im y -> x = y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Nth roots. *)

Let argCleP y z :
  reflect (0 <= 'Im z -> 0 <= 'Im y /\ 'Re z <= 'Re y) (argCle y z).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rootC_Re_max n x y :
  (n > 0)%N -> y ^+ n = x -> 0 <= 'Im y -> 'Re y <= 'Re (n.-root x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Let neg_unity_root n : (n > 1)%N -> exists2 w : C, w ^+ n = 1 & 'Re w < 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Im_rootC_ge0 n x : (n > 1)%N -> 0 <= 'Im (n.-root x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rootC_lt0 n x : (1 < n)%N -> (n.-root x < 0) = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rootC_ge0 n x : (n > 0)%N -> (0 <= n.-root x) = (0 <= x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rootC_gt0 n x : (n > 0)%N -> (n.-root x > 0) = (x > 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rootC_le0 n x : (1 < n)%N -> (n.-root x <= 0) = (x == 0).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_rootCl n : (n > 0)%N -> {in Num.nneg, {mono n.-root : x y / x <= y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_rootC n : (n > 0)%N -> {in Num.nneg &, {mono n.-root : x y / x <= y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_rootCl n : (n > 0)%N -> {in Num.nneg, {mono n.-root : x y / x < y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltr_rootC n : (n > 0)%N -> {in Num.nneg &, {mono n.-root : x y / x < y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma exprCK n x : (0 < n)%N -> 0 <= x -> n.-root (x ^+ n) = x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma norm_rootC n x : `|n.-root x| = n.-root `|x|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rootCX n x k : (n > 0)%N -> 0 <= x -> n.-root (x ^+ k) = n.-root x ^+ k.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rootC1 n : (n > 0)%N -> n.-root 1 = 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rootCpX n x k : (k > 0)%N -> 0 <= x -> n.-root (x ^+ k) = n.-root x ^+ k.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rootCV n x : 0 <= x -> n.-root x^-1 = (n.-root x)^-1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rootC_eq1 n x : (n > 0)%N -> (n.-root x == 1) = (x == 1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rootC_ge1 n x : (n > 0)%N -> (n.-root x >= 1) = (x >= 1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rootC_gt1 n x : (n > 0)%N -> (n.-root x > 1) = (x > 1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rootC_le1 n x : (n > 0)%N -> 0 <= x -> (n.-root x <= 1) = (x <= 1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rootC_lt1 n x : (n > 0)%N -> 0 <= x -> (n.-root x < 1) = (x < 1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rootCMl n x z : 0 <= x -> n.-root (x * z) = n.-root x * n.-root z.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma rootCMr n x z : 0 <= x -> n.-root (z * x) = n.-root z * n.-root x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma imaginaryCE : 'i = sqrtC (-1).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* More properties of n.-root will be established in cyclotomic.v. *)

(* The proper form of the Arithmetic - Geometric Mean inequality. *)

Lemma leif_rootC_AGM (I : finType) (A : {pred I}) (n := #|A|) E :
    {in A, forall i, 0 <= E i} ->
  n.-root (\prod_(i in A) E i) <= (\sum_(i in A) E i) / n%:R
                             ?= iff [forall i in A, forall j in A, E i == E j].
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Square root. *)

Lemma sqrtC0 : sqrtC 0 = 0. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma sqrtC1 : sqrtC 1 = 1. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma sqrtCK x : sqrtC x ^+ 2 = x. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma sqrCK x : 0 <= x -> sqrtC (x ^+ 2) = x. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrtC_ge0 x : (0 <= sqrtC x) = (0 <= x). Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma sqrtC_eq0 x : (sqrtC x == 0) = (x == 0). Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma sqrtC_gt0 x : (sqrtC x > 0) = (x > 0). Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma sqrtC_lt0 x : (sqrtC x < 0) = false. Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma sqrtC_le0 x : (sqrtC x <= 0) = (x == 0). Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ler_sqrtC : {in Num.nneg &, {mono sqrtC : x y / x <= y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma ltr_sqrtC : {in Num.nneg &, {mono sqrtC : x y / x < y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma eqr_sqrtC : {mono sqrtC : x y / x == y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma sqrtC_inj : injective sqrtC.
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Lemma sqrtCM : {in Num.nneg &, {morph sqrtC : x y / x * y}}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma sqrCK_P x : reflect (sqrtC (x ^+ 2) = x) ((0 <= 'Im x) && ~~ (x < 0)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normC_def x : `|x| = sqrtC (x * x^*).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma norm_conjC x : `|x^*| = `|x|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normC_rect :
  {in real &, forall x y, `|x + 'i * y| = sqrtC (x ^+ 2 + y ^+ 2)}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normC_Re_Im z : `|z| = sqrtC ('Re z ^+ 2 + 'Im z ^+ 2).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(* Norm sum (in)equalities. *)

Lemma normC_add_eq x y :
    `|x + y| = `|x| + `|y| ->
  {t : C | `|t| == 1 & (x, y) = (`|x| * t, `|y| * t)}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normC_sum_eq (I : finType) (P : pred I) (F : I -> C) :
     `|\sum_(i | P i) F i| = \sum_(i | P i) `|F i| ->
   {t : C | `|t| == 1 & forall i, P i -> F i = `|F i| * t}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normC_sum_eq1 (I : finType) (P : pred I) (F : I -> C) :
    `|\sum_(i | P i) F i| = (\sum_(i | P i) `|F i|) ->
     (forall i, P i -> `|F i| = 1) ->
   {t : C | `|t| == 1 & forall i, P i -> F i = t}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normC_sum_upper (I : finType) (P : pred I) (F G : I -> C) :
     (forall i, P i -> `|F i| <= G i) ->
     \sum_(i | P i) F i = \sum_(i | P i) G i ->
   forall i, P i -> F i = G i.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normC_sub_eq x y :
  `|x - y| = `|x| - `|y| -> {t | `|t| == 1 & (x, y) = (`|x| * t, `|y| * t)}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End ClosedFieldTheory.

Notation "n .-root" := (@nthroot _ n).
Notation sqrtC := 2.-root.
Notation "'i" := (@imaginaryC _) : ring_scope.
Notation "'Re z" := (Re z) : ring_scope.
Notation "'Im z" := (Im z) : ring_scope.

Arguments conjCK {C} x.
Arguments sqrCK {C} [x] le0x.
Arguments sqrCK_P {C x}.

#[global] Hint Extern 0 (is_true (in_mem ('Re _) _)) =>
  solve [apply: Creal_Re] : core.
#[global] Hint Extern 0 (is_true (in_mem ('Im _) _)) =>
  solve [apply: Creal_Im] : core.

End Theory.

(*************)
(* FACTORIES *)
(*************)

Module NumMixin.
Section NumMixin.
Variable (R : idomainType).

Record of_ := Mixin {
  le : rel R;
  lt : rel R;
  norm : R -> R;
  normD     : forall x y, le (norm (x + y)) (norm x + norm y);
  addr_gt0  : forall x y, lt 0 x -> lt 0 y -> lt 0 (x + y);
  norm_eq0  : forall x, norm x = 0 -> x = 0;
  ger_total : forall x y, le 0 x -> le 0 y -> le x y || le y x;
  normM     : {morph norm : x y / x * y};
  le_def    : forall x y, (le x y) = (norm (y - x) == y - x);
  lt_def    : forall x y, (lt x y) = (y != x) && (le x y)
}.

Variable (m : of_).

Local Notation "x <= y" := (le m x y) : ring_scope.
Local Notation "x < y" := (lt m x y) : ring_scope.
Local Notation "`| x |" := (norm m x) : ring_scope.

Lemma ltrr x : x < x = false. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ge0_def x : (0 <= x) = (`|x| == x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma subr_ge0 x y : (0 <= x - y) = (y <= x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma subr_gt0 x y : (0 < y - x) = (x < y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lt_trans : transitive (lt m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma le01 : 0 <= 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lt01 : 0 < 1.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma ltW x y : x < y -> x <= y. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma lerr x : x <= x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma le_def' x y : (x <= y) = (x == y) || (x < y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma le_trans : transitive (le m).
by move=> y x z; rewrite !le_def' => /predU1P [->|hxy] // /predU1P [<-|hyz];
  rewrite ?hxy ?(lt_trans hxy hyz) orbT.
Qed.

Lemma normrMn x n : `|x *+ n| = `|x| *+ n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normrN1 : `|-1| = 1 :> R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma normrN x : `|- x| = `|x|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition ltPOrderMixin : ltPOrderMixin R :=
  LtPOrderMixin le_def' ltrr lt_trans.

Definition normedZmodMixin :
  @normed_mixin_of R R ltPOrderMixin :=
  @Num.NormedMixin _ _ ltPOrderMixin (norm m)
                   (normD m) (@norm_eq0 m) normrMn normrN.

Definition numDomainMixin :
  @mixin_of R ltPOrderMixin normedZmodMixin :=
  @Num.Mixin _ ltPOrderMixin normedZmodMixin (@addr_gt0 m)
             (@ger_total m) (@normM m) (@le_def m).

End NumMixin.

Module Exports.
Notation numMixin := of_.
Notation NumMixin := Mixin.
Coercion ltPOrderMixin : numMixin >-> Order.LtPOrderMixin.of_.
Coercion normedZmodMixin : numMixin >-> normed_mixin_of.
Coercion numDomainMixin : numMixin >-> mixin_of.
Definition NumDomainOfIdomain (T : idomainType) (m : of_ T) :=
  NumDomainType (POrderType ring_display T m) m.
End Exports.

End NumMixin.
Import NumMixin.Exports.

Module RealMixin.
Section RealMixin.
Variables (R : numDomainType).

Variable (real : real_axiom R).

Lemma le_total : totalPOrderMixin R.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

End RealMixin.

Module Exports.
Coercion le_total : real_axiom >-> totalPOrderMixin.
Definition RealDomainOfNumDomain (T : numDomainType) (m : real_axiom T) :=
  [realDomainType of OrderOfPOrder m].
End Exports.

End RealMixin.
Import RealMixin.Exports.

Module RealLeMixin.
Section RealLeMixin.
Variables (R : idomainType).

Record of_ := Mixin {
  le : rel R;
  lt : rel R;
  norm : R -> R;
  le0_add   : forall x y, le 0 x -> le 0 y -> le 0 (x + y);
  le0_mul   : forall x y, le 0 x -> le 0 y -> le 0 (x * y);
  le0_anti  : forall x, le 0 x -> le x 0 -> x = 0;
  sub_ge0   : forall x y, le 0 (y - x) = le x y;
  le0_total : forall x, le 0 x || le x 0;
  normN     : forall x, norm (- x) = norm x;
  ge0_norm  : forall x, le 0 x -> norm x = x;
  lt_def    : forall x y, lt x y = (y != x) && le x y;
}.

Variable (m : of_).

Local Notation "x <= y" := (le m x y) : ring_scope.
Local Notation "x < y" := (lt m x y) : ring_scope.
Local Notation "`| x |" := (norm m x) : ring_scope.

Let le0N x : (0 <= - x) = (x <= 0). Proof. Show. Fail (cvc5_abduct 3). Admitted.
Let leN_total x : 0 <= x \/ 0 <= - x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Let le00 : 0 <= 0. Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact lt0_add x y : 0 < x -> 0 < y -> 0 < x + y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact eq0_norm x : `|x| = 0 -> x = 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact le_def x y : (x <= y) = (`|y - x| == y - x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact normM : {morph norm m : x y / x * y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact le_normD x y : `|x + y| <= `|x| + `|y|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact le_total : total (le m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition numMixin : numMixin R :=
  NumMixin le_normD lt0_add eq0_norm (in2W le_total) normM le_def (lt_def m).

Definition orderMixin :
  totalPOrderMixin (POrderType ring_display R numMixin) :=
  le_total.

End RealLeMixin.

Module Exports.
Notation realLeMixin := of_.
Notation RealLeMixin := Mixin.
Coercion numMixin : realLeMixin >-> NumMixin.of_.
Coercion orderMixin : realLeMixin >-> totalPOrderMixin.
Definition LeRealDomainOfIdomain (R : idomainType) (m : of_ R) :=
  [realDomainType of @OrderOfPOrder _ (NumDomainOfIdomain m) m].
Definition LeRealFieldOfField (R : fieldType) (m : of_ R) :=
  [realFieldType of [numFieldType of LeRealDomainOfIdomain m]].
End Exports.

End RealLeMixin.
Import RealLeMixin.Exports.

Module RealLtMixin.
Section RealLtMixin.
Variables (R : idomainType).

Record of_ := Mixin {
  lt : rel R;
  le : rel R;
  norm : R -> R;
  lt0_add   : forall x y, lt 0 x -> lt 0 y -> lt 0 (x + y);
  lt0_mul   : forall x y, lt 0 x -> lt 0 y -> lt 0 (x * y);
  lt0_ngt0  : forall x,  lt 0 x -> ~~ (lt x 0);
  sub_gt0   : forall x y, lt 0 (y - x) = lt x y;
  lt0_total : forall x, x != 0 -> lt 0 x || lt x 0;
  normN     : forall x, norm (- x) = norm x;
  ge0_norm  : forall x, le 0 x -> norm x = x;
  le_def    : forall x y, le x y = (x == y) || lt x y;
}.

Variable (m : of_).

Local Notation "x < y" := (lt m x y) : ring_scope.
Local Notation "x <= y" := (le m x y) : ring_scope.
Local Notation "`| x |" := (norm m x) : ring_scope.

Fact lt0N x : (- x < 0) = (0 < x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.
Let leN_total x : 0 <= x \/ 0 <= - x.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Let le00 : (0 <= 0). Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact sub_ge0 x y : (0 <= y - x) = (x <= y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact le0_add x y : 0 <= x -> 0 <= y -> 0 <= x + y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact le0_mul x y : 0 <= x -> 0 <= y -> 0 <= x * y.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact normM : {morph norm m : x y / x * y}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact le_normD x y : `|x + y| <= `|x| + `|y|.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact eq0_norm x : `|x| = 0 -> x = 0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact le_def' x y : (x <= y) = (`|y - x| == y - x).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact lt_def x y : (x < y) = (y != x) && (x <= y).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Fact le_total : total (le m).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Definition numMixin : numMixin R :=
  NumMixin le_normD (@lt0_add m) eq0_norm (in2W le_total) normM le_def' lt_def.

Definition orderMixin :
  totalPOrderMixin (POrderType ring_display R numMixin) :=
  le_total.

End RealLtMixin.

Module Exports.
Notation realLtMixin := of_.
Notation RealLtMixin := Mixin.
Coercion numMixin : realLtMixin >-> NumMixin.of_.
Coercion orderMixin : realLtMixin >-> totalPOrderMixin.
Definition LtRealDomainOfIdomain (R : idomainType) (m : of_ R) :=
  [realDomainType of @OrderOfPOrder _ (NumDomainOfIdomain m) m].
Definition LtRealFieldOfField (R : fieldType) (m : of_ R) :=
  [realFieldType of [numFieldType of LtRealDomainOfIdomain m]].
End Exports.

End RealLtMixin.
Import RealLtMixin.Exports.

End Num.

Export Num.NumDomain.Exports Num.NormedZmodule.Exports.
Export Num.NumDomain_joins.Exports.
Export Num.NumField.Exports Num.ClosedField.Exports.
Export Num.RealDomain.Exports Num.RealField.Exports.
Export Num.ArchimedeanField.Exports Num.RealClosedField.Exports.
Export Num.Syntax Num.PredInstances.
Export Num.NumMixin.Exports Num.RealMixin.Exports.
Export Num.RealLeMixin.Exports Num.RealLtMixin.Exports.

Notation ImaginaryMixin := Num.ClosedField.ImaginaryMixin.

