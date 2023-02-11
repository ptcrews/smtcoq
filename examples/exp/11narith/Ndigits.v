(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Bool Morphisms Setoid Bvector BinPos BinNat PeanoNat Pnat Nnat
        Basics ByteVector.

Local Open Scope N_scope.
Local Open Scope program_scope.
Add Rec LoadPath "/home/arjun/Desktop/smtcoq/abduction-arjunvish-smtcoq/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
(** This file is mostly obsolete, see directly [BinNat] now. *)

(** Compatibility names for some bitwise operations *)

Notation Pxor := Pos.lxor (only parsing).
Notation Nxor := N.lxor (only parsing).
Notation Pbit := Pos.testbit_nat (only parsing).
Notation Nbit := N.testbit_nat (only parsing).

Notation Nxor_eq := N.lxor_eq (only parsing).
Notation Nxor_comm := N.lxor_comm (only parsing).
Notation Nxor_assoc := N.lxor_assoc (only parsing).
Notation Nxor_neutral_left := N.lxor_0_l (only parsing).
Notation Nxor_neutral_right := N.lxor_0_r (only parsing).
Notation Nxor_nilpotent := N.lxor_nilpotent (only parsing).

(** Equivalence of bit-testing functions,
    either with index in [N] or in [nat]. *)

Lemma Ptestbit_Pbit :
 forall p n, Pos.testbit p (N.of_nat n) = Pos.testbit_nat p n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Ntestbit_Nbit : forall a n, N.testbit a (N.of_nat n) = N.testbit_nat a n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Pbit_Ptestbit :
 forall p n, Pos.testbit_nat p (N.to_nat n) = Pos.testbit p n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nbit_Ntestbit :
 forall a n, N.testbit_nat a (N.to_nat n) = N.testbit a n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Equivalence of shifts, index in [N] or [nat] *)

Lemma Nshiftr_nat_S : forall a n,
 N.shiftr_nat a (S n) = N.div2 (N.shiftr_nat a n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nshiftl_nat_S : forall a n,
 N.shiftl_nat a (S n) = N.double (N.shiftl_nat a n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nshiftr_nat_equiv :
 forall a n, N.shiftr_nat a (N.to_nat n) = N.shiftr a n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nshiftr_equiv_nat :
 forall a n, N.shiftr a (N.of_nat n) = N.shiftr_nat a n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nshiftl_nat_equiv :
 forall a n, N.shiftl_nat a (N.to_nat n) = N.shiftl a n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nshiftl_equiv_nat :
 forall a n, N.shiftl a (N.of_nat n) = N.shiftl_nat a n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Correctness proofs for shifts, nat version *)

Lemma Nshiftr_nat_spec : forall a n m,
  N.testbit_nat (N.shiftr_nat a n) m = N.testbit_nat a (m+n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nshiftl_nat_spec_high : forall a n m, (n<=m)%nat ->
  N.testbit_nat (N.shiftl_nat a n) m = N.testbit_nat a (m-n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nshiftl_nat_spec_low : forall a n m, (m<n)%nat ->
 N.testbit_nat (N.shiftl_nat a n) m = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** A left shift for positive numbers (used in BigN) *)

Lemma Pshiftl_nat_0 : forall p, Pos.shiftl_nat p 0 = p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Pshiftl_nat_S :
 forall p n, Pos.shiftl_nat p (S n) = xO (Pos.shiftl_nat p n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Pshiftl_nat_N :
 forall p n, Npos (Pos.shiftl_nat p n) = N.shiftl_nat (Npos p) n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Pshiftl_nat_plus : forall n m p,
  Pos.shiftl_nat p (m + n) = Pos.shiftl_nat (Pos.shiftl_nat p n) m.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Semantics of bitwise operations with respect to [N.testbit_nat] *)

Lemma Pxor_semantics p p' n :
 N.testbit_nat (Pos.lxor p p') n = xorb (Pos.testbit_nat p n) (Pos.testbit_nat p' n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nxor_semantics a a' n :
 N.testbit_nat (N.lxor a a') n = xorb (N.testbit_nat a n) (N.testbit_nat a' n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Por_semantics p p' n :
 Pos.testbit_nat (Pos.lor p p') n = (Pos.testbit_nat p n) || (Pos.testbit_nat p' n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nor_semantics a a' n :
 N.testbit_nat (N.lor a a') n = (N.testbit_nat a n) || (N.testbit_nat a' n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Pand_semantics p p' n :
 N.testbit_nat (Pos.land p p') n = (Pos.testbit_nat p n) && (Pos.testbit_nat p' n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nand_semantics a a' n :
 N.testbit_nat (N.land a a') n = (N.testbit_nat a n) && (N.testbit_nat a' n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Pdiff_semantics p p' n :
 N.testbit_nat (Pos.ldiff p p') n = (Pos.testbit_nat p n) && negb (Pos.testbit_nat p' n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Ndiff_semantics a a' n :
 N.testbit_nat (N.ldiff a a') n = (N.testbit_nat a n) && negb (N.testbit_nat a' n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Equality over functional streams of bits *)

Definition eqf (f g:nat -> bool) := forall n:nat, f n = g n.

Program Instance eqf_equiv : Equivalence eqf.

Local Infix "==" := eqf (at level 70, no associativity).

(** If two numbers produce the same stream of bits, they are equal. *)

Local Notation Step H := (fun n => H (S n)).

Lemma Pbit_faithful_0 : forall p, ~(Pos.testbit_nat p == (fun _ => false)).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Pbit_faithful : forall p p', Pos.testbit_nat p == Pos.testbit_nat p' -> p = p'.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nbit_faithful : forall n n', N.testbit_nat n == N.testbit_nat n' -> n = n'.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nbit_faithful_iff : forall n n', N.testbit_nat n == N.testbit_nat n' <-> n = n'.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Local Close Scope N_scope.

(** Checking whether a number is odd, i.e.
   if its lower bit is set. *)

Notation Nbit0 := N.odd (only parsing).

Definition Nodd (n:N) := N.odd n = true.
Definition Neven (n:N) := N.odd n = false.

Lemma Nbit0_correct : forall n:N, N.testbit_nat n 0 = N.odd n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Ndouble_bit0 : forall n:N, N.odd (N.double n) = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Ndouble_plus_one_bit0 :
 forall n:N, N.odd (N.succ_double n) = true.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Ndiv2_double :
 forall n:N, Neven n -> N.double (N.div2 n) = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Ndiv2_double_plus_one :
 forall n:N, Nodd n -> N.succ_double (N.div2 n) = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Ndiv2_correct :
 forall (a:N) (n:nat), N.testbit_nat (N.div2 a) n = N.testbit_nat a (S n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nxor_bit0 :
 forall a a':N, N.odd (N.lxor a a') = xorb (N.odd a) (N.odd a').
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nxor_div2 :
 forall a a':N, N.div2 (N.lxor a a') = N.lxor (N.div2 a) (N.div2 a').
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nneg_bit0 :
 forall a a':N,
   N.odd (N.lxor a a') = true -> N.odd a = negb (N.odd a').
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nneg_bit0_1 :
 forall a a':N, N.lxor a a' = Npos 1 -> N.odd a = negb (N.odd a').
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nneg_bit0_2 :
 forall (a a':N) (p:positive),
   N.lxor a a' = Npos (xI p) -> N.odd a = negb (N.odd a').
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nsame_bit0 :
 forall (a a':N) (p:positive),
   N.lxor a a' = Npos (xO p) -> N.odd a = N.odd a'.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** a lexicographic order on bits, starting from the lowest bit *)

Fixpoint Nless_aux (a a':N) (p:positive) : bool :=
  match p with
  | xO p' => Nless_aux (N.div2 a) (N.div2 a') p'
  | _ => andb (negb (N.odd a)) (N.odd a')
  end.

Definition Nless (a a':N) :=
  match N.lxor a a' with
  | N0 => false
  | Npos p => Nless_aux a a' p
  end.

Lemma Nbit0_less :
 forall a a',
   N.odd a = false -> N.odd a' = true -> Nless a a' = true.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nbit0_gt :
 forall a a',
   N.odd a = true -> N.odd a' = false -> Nless a a' = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nless_not_refl : forall a, Nless a a = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nless_def_1 :
 forall a a', Nless (N.double a) (N.double a') = Nless a a'.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nless_def_2 :
 forall a a',
   Nless (N.succ_double a) (N.succ_double a') = Nless a a'.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nless_def_3 :
 forall a a', Nless (N.double a) (N.succ_double a') = true.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nless_def_4 :
 forall a a', Nless (N.succ_double a) (N.double a') = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nless_z : forall a, Nless a N0 = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma N0_less_1 :
 forall a, Nless N0 a = true -> {p : positive | a = Npos p}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma N0_less_2 : forall a, Nless N0 a = false -> a = N0.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nless_trans :
 forall a a' a'',
   Nless a a' = true -> Nless a' a'' = true -> Nless a a'' = true.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nless_total :
 forall a a', {Nless a a' = true} + {Nless a' a = true} + {a = a'}.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Number of digits in a number *)

Notation Nsize := N.size_nat (only parsing).

(** conversions between N and bit vectors. *)

Fixpoint P2Bv (p:positive) : Bvector (Pos.size_nat p) :=
 match p return Bvector (Pos.size_nat p) with
   | xH => Bvect_true 1%nat
   | xO p => Bcons false (Pos.size_nat p) (P2Bv p)
   | xI p => Bcons true (Pos.size_nat p) (P2Bv p)
 end.

Definition N2Bv (n:N) : Bvector (N.size_nat n) :=
  match n as n0 return Bvector (N.size_nat n0) with
    | N0 => Bnil
    | Npos p => P2Bv p
  end.

Fixpoint P2Bv_sized (m : nat) (p : positive) : Bvector m :=
  match m with
  | O => []
  | S m =>
    match p with
    | xI p => true  :: P2Bv_sized  m p
    | xO p => false :: P2Bv_sized  m p
    | xH   => true  :: Bvect_false m
    end
  end.

Definition N2Bv_sized (m : nat) (n : N) : Bvector m :=
  match n with
  | N0     => Bvect_false m
  | Npos p => P2Bv_sized  m p
  end.

Definition N2ByteV_sized (m : nat) : N -> ByteVector m :=
  of_Bvector ∘ N2Bv_sized (m * 8).

Fixpoint Bv2N (n:nat)(bv:Bvector n) : N :=
  match bv with
    | Vector.nil _ => N0
    | Vector.cons _ false n bv => N.double (Bv2N n bv)
    | Vector.cons _ true n bv => N.succ_double (Bv2N n bv)
  end.

Arguments Bv2N {n} bv, n bv.

Definition ByteV2N {n : nat} : ByteVector n -> N :=
  Bv2N ∘ to_Bvector.

Lemma Bv2N_N2Bv : forall n, Bv2N _ (N2Bv n) = n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** The opposite composition is not so simple: if the considered
  bit vector has some zeros on its right, they will disappear during
  the return [Bv2N] translation: *)

Lemma Bv2N_Nsize : forall n (bv:Bvector n), N.size_nat (Bv2N n bv) <= n.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** In the previous lemma, we can only replace the inequality by
  an equality whenever the highest bit is non-null. *)

Lemma Bv2N_Nsize_1 : forall n (bv:Bvector (S n)),
  Bsign _ bv = true <->
  N.size_nat (Bv2N _ bv) = (S n).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Bv2N_upper_bound (n : nat) (bv : Bvector n) :
    (Bv2N bv < N.shiftl_nat 1 n)%N.
Proof with simpl; auto.
  induction bv as [|h]...
  - constructor.
  - destruct h.
    + apply N.succ_double_lt...
    + apply N.double_lt_mono...
Qed.

Corollary ByteV2N_upper_bound (n : nat) (v : ByteVector n) :
  (ByteV2N v < N.shiftl_nat 1 (n * 8))%N.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** To state nonetheless a second result about composition of
 conversions, we define a conversion on a given number of bits : *)

#[deprecated(since = "8.9.0", note = "Use N2Bv_sized instead.")]
Fixpoint N2Bv_gen (n:nat)(a:N) : Bvector n :=
 match n return Bvector n with
   | 0 => Bnil
   | S n => match a with
       | N0 => Bvect_false (S n)
       | Npos xH => Bcons true _ (Bvect_false n)
       | Npos (xO p) => Bcons false _ (N2Bv_gen n (Npos p))
       | Npos (xI p) => Bcons true _ (N2Bv_gen n (Npos p))
      end
  end.

(** The first [N2Bv] is then a special case of [N2Bv_gen] *)

Lemma N2Bv_N2Bv_gen : forall (a:N), N2Bv a = N2Bv_gen (N.size_nat a) a.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** In fact, if [k] is large enough, [N2Bv_gen k a] contains all digits of
   [a] plus some zeros. *)

Lemma N2Bv_N2Bv_gen_above : forall (a:N)(k:nat),
 N2Bv_gen (N.size_nat a + k) a = Vector.append (N2Bv a) (Bvect_false k).
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Here comes now the second composition result. *)

Lemma N2Bv_Bv2N : forall n (bv:Bvector n),
   N2Bv_gen n (Bv2N n bv) = bv.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** accessing some precise bits. *)

Lemma Nbit0_Blow : forall n, forall (bv:Bvector (S n)),
  N.odd (Bv2N _ bv) = Blow _ bv.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Notation Bnth := (@Vector.nth_order bool).

Lemma Bnth_Nbit : forall n (bv:Bvector n) p (H:p<n),
  Bnth bv H = N.testbit_nat (Bv2N _ bv) p.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nbit_Nsize : forall n p, N.size_nat n <= p -> N.testbit_nat n p = false.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nbit_Bth: forall n p (H:p < N.size_nat n),
  N.testbit_nat n p = Bnth (N2Bv n) H.
Proof. Show. Fail (cvc5_abduct 3). Admitted.

(** Binary bitwise operations are the same in the two worlds. *)

Lemma Nxor_BVxor : forall n (bv bv' : Bvector n),
  Bv2N _ (BVxor _ bv bv') = N.lxor (Bv2N _ bv) (Bv2N _ bv').
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma Nand_BVand : forall n (bv bv' : Bvector n),
  Bv2N _ (BVand _ bv bv') = N.land (Bv2N _ bv) (Bv2N _ bv').
Proof. Show. Fail (cvc5_abduct 3). Admitted.

Lemma N2Bv_sized_Nsize (n : N) :
  N2Bv_sized (N.size_nat n) n = N2Bv n.
Proof with simpl; auto.
  destruct n as [|p]...
  induction p as [p IHp|p IHp|]...
  all: rewrite IHp...
Qed.

Lemma N2Bv_sized_Bv2N (n : nat) (v : Bvector n) :
  N2Bv_sized n (Bv2N n v) = v.
Proof with simpl; auto.
  induction v as [|h n v IHv]...
  destruct h;
  unfold N2Bv_sized;
  destruct (Bv2N n v) as [|[]];
  rewrite <- IHv...
Qed.

Lemma N2Bv_N2Bv_sized_above (a : N) (k : nat) :
  N2Bv_sized (N.size_nat a + k) a = N2Bv a ++ Bvect_false k.
Proof with auto.
  destruct a as [|p]...
  induction p; simpl; f_equal...
Qed.
