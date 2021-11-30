(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2021                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import PArray List Bool ZArith Psatz.
Require Import Misc State SMT_terms BVList.

Import Form.

Local Open Scope array_scope.
Local Open Scope int63_scope.

Set Implicit Arguments.
Unset Strict Implicit.

Definition or_of_imp args :=
  let last := PArray.length args - 1 in
  PArray.mapi (fun i l => if i == last then l else Lit.neg l) args.
(* Register or_of_imp as PrimInline. *)

Lemma length_or_of_imp : forall args,
  PArray.length (or_of_imp args) = PArray.length args.
Proof. intro; unfold or_of_imp; apply length_mapi. Qed.

Lemma get_or_of_imp : forall args i,
  i < (PArray.length args) - 1 -> (or_of_imp args).[i] = Lit.neg (args.[i]).
Proof.
  unfold or_of_imp; intros args i H; case_eq (0 < PArray.length args).
  intro Heq; rewrite get_mapi.
  replace (i == PArray.length args - 1) with false; auto; symmetry; rewrite eqb_false_spec; intro; subst i; unfold is_true in H; rewrite ltb_spec, (to_Z_sub_1 _ _ Heq) in H; omega.
  rewrite ltb_spec; unfold is_true in H; rewrite ltb_spec, (to_Z_sub_1 _ _ Heq) in H; omega.
  rewrite ltb_negb_geb; case_eq (PArray.length args <= 0); try discriminate; intros Heq _; assert (H1: PArray.length args = 0).
  apply to_Z_inj; rewrite leb_spec in Heq; destruct (to_Z_bounded (PArray.length args)) as [H1 _]; change [|0|] with 0%Z in *; omega.
  rewrite !get_outofbound.
  rewrite default_mapi, H1; auto.
  rewrite H1; case_eq (i < 0); auto; intro H2; eelim ltb_0; eassumption.
  rewrite length_mapi, H1; case_eq (i < 0); auto; intro H2; eelim ltb_0; eassumption.
Qed.

Lemma get_or_of_imp2 : forall args i, 0 < PArray.length args ->
  i = (PArray.length args) - 1 -> (or_of_imp args).[i] = args.[i].
Proof.
  unfold or_of_imp; intros args i Heq Hi; rewrite get_mapi; subst i.
  rewrite Int63Axioms.eqb_refl; auto.
  rewrite ltb_spec, (to_Z_sub_1 _ _ Heq); omega.
Qed.

Lemma afold_right_impb p a :
  (forall x, p (Lit.neg x) = negb (p x)) ->
  (PArray.length a == 0) = false ->
  (afold_right bool int true implb p a) =
  List.existsb p (to_list (or_of_imp a)).
Proof.
  intros Hp Hl.
  case_eq (afold_right bool int true implb p a); intro Heq; symmetry.
  - apply afold_right_implb_true_inv in Heq.
    destruct Heq as [Heq|[[i [Hi Heq]]|Heq]].
    + rewrite Heq in Hl. discriminate.
    + rewrite existsb_exists. exists (Lit.neg (a .[ i])). split.
      * {
          apply (to_list_In_eq _ i).
          - rewrite length_or_of_imp. apply (ltb_trans _ (PArray.length a - 1)); auto.
            now apply minus_1_lt.
          - now rewrite get_or_of_imp.
        }
      * now rewrite Hp, Heq.
    + rewrite existsb_exists. exists (a.[(PArray.length a) - 1]). split.
      * {
          apply (to_list_In_eq _ (PArray.length a - 1)).
          - rewrite length_or_of_imp.
            now apply minus_1_lt.
          - symmetry. apply get_or_of_imp2; auto.
            unfold is_true. rewrite ltb_spec. rewrite eqb_false_spec in Hl.
            assert (0%Z <> [|PArray.length a|])
              by (change 0%Z with [|0|]; intro H; apply to_Z_inj in H; auto).
            destruct (to_Z_bounded (PArray.length a)) as [H1 _].
            clear -H H1. change [|0|] with 0%Z. lia.
        }
      * {
          apply Heq. now apply minus_1_lt.
        }
  - apply afold_right_implb_false_inv in Heq.
    destruct Heq as [H1 [H2 H3]].
    case_eq (existsb p (to_list (or_of_imp a))); auto.
    rewrite existsb_exists. intros [x [H4 H5]].
    apply In_to_list in H4. destruct H4 as [i [H4 ->]].
    case_eq (i < PArray.length a - 1); intro Heq.
    + assert (H6 := H2 _ Heq). now rewrite (get_or_of_imp Heq), Hp, H6 in H5.
    + assert (H6:i = PArray.length a - 1).
      {
        clear -H4 Heq H1.
        rewrite length_or_of_imp in H4.
        apply to_Z_inj. rewrite (to_Z_sub_1 _ 0); auto.
        rewrite ltb_spec in H4; auto.
        rewrite ltb_negb_geb in Heq.
        case_eq (PArray.length a - 1 <= i); intro H2; rewrite H2 in Heq; try discriminate.
        clear Heq. rewrite leb_spec in H2. rewrite (to_Z_sub_1 _ 0) in H2; auto.
        lia.
      }
      rewrite get_or_of_imp2 in H5; auto.
      rewrite H6, H3 in H5. discriminate.
Qed.


Section CHECKER.

  Variable t_form : PArray.array form.
  Local Notation get_hash := (PArray.get t_form) (only parsing).
  Variable s : S.t.


  (*  * true             : {true}  *)

  Definition check_True := C._true.


  (* * false             : {(not false)} *)

  Definition check_False  := Lit.neg (Lit._false)::nil.


  (* * notnot           : {(not (not not x)) x} *)
  Definition check_NotNot l :=
    if Lit.is_pos l then C._true
    else
      l :: Lit.neg l :: nil.
    (*match get_hash (Lit.blit l) with
      | Fnot2 i x => (*if (i == 1) then*) l :: x :: nil
                     (*else (Lit.neg l) :: (Fnot2 (i-1) x) :: nil*)
      | _ => C._true
      end.*)

  
  (*  * tautology        : {(x_1 ... x_i ... (not x_i) ... x_n) --> true)}
     *)
  Definition check_Tautology pos l :=
    match S.get s pos, get_hash (Lit.blit l) with
    | xs, Ttrue => if (existsb (fun x => Lit.is_pos x && 
               (existsb (fun y => negb (Lit.is_pos y) && (x == y)) xs)) 
               xs) then
      l::nil else C._true
    end.

  (*  * Contractionction      : {(x_1 ... x_n) --> (x_k1 ... x_kn)}, 
          where duplicates are removed and order is preserved 
     *)
  Definition check_Contraction pos ys :=
    match S.get s pos with
    | xs => (* Check whether each element in xs only occurs once in ys *)
        if (List.forallb (fun x => Nat.eqb (List.length (List.filter (fun y => y == x) ys)) 1) xs) then
        ys else C._true
    end.


  (* * and_neg          : {(and a_1 ... a_n) (not a_1) ... (not a_n)}
     * or_pos           : {(not (or a_1 ... a_n)) a_1 ... a_n} 
     * implies_pos      : {(not (implies a b)) (not a) b}
     * xor_pos1         : {(not (xor a b)) a b}
     * xor_neg1         : {(xor a b) a (not b)}
     * equiv_pos1       : {(not (iff a b)) a (not b)}
     * equiv_neg1       : {(iff a b) (not a) (not b)}
     * ite_pos1         : {(not (if_then_else a b c)) a c}
     * ite_neg1         : {(if_then_else a b c) a (not c)} *)

  Definition check_BuildDef l :=
    match get_hash (Lit.blit l) with
    | Fand args => 
      if Lit.is_pos l then l :: List.map Lit.neg (PArray.to_list args) 
      else C._true
    | For args =>
      if Lit.is_pos l then C._true
      else l :: PArray.to_list args
    | Fimp args =>
      if Lit.is_pos l then C._true
      else if PArray.length args == 0 then C._true
      else
        let args := or_of_imp args in
        l :: PArray.to_list args
    | Fxor a b =>
      if Lit.is_pos l then l::a::Lit.neg b::nil 
      else l::a::b::nil
    | Fiff a b =>
      if Lit.is_pos l then l::Lit.neg a::Lit.neg b::nil
      else l::a::Lit.neg b::nil
    | Fite a b c =>
      if Lit.is_pos l then l::a::Lit.neg c::nil
      else l::a::c::nil
    | _ => C._true
    end.


  (* * not_and           : {(not (and a_1 ... a_n))} --> {(not a_1) ... (not a_n)}
     * or                : {(or a_1 ... a_n)} --> {a_1 ... a_n}
     * implies           : {(implies a b)} --> {(not a) b}
     * xor1              : {(xor a b)} --> {a b}
     * not_xor1          : {(not (xor a b))} --> {a (not b)}
     * equiv2            : {(iff a b)} --> {a (not b)}
     * not_equiv2        : {(not (iff a b))} --> {(not a) (not b)}
     * ite1              : {(if_then_else a b c)} --> {a c}
     * not_ite1          : {(not (if_then_else a b c))} --> {a (not c)} *)

  Definition check_ImmBuildDef pos :=
    match S.get s pos with
    | l::nil =>
      match get_hash (Lit.blit l) with
      | Fand args => 
        if Lit.is_pos l then C._true
        else List.map Lit.neg (PArray.to_list args) 
      | For args =>
        if Lit.is_pos l then PArray.to_list args
        else C._true
      | Fimp args =>
        if PArray.length args == 0 then C._true else
        if Lit.is_pos l then 
          let args := or_of_imp args in
          PArray.to_list args
        else C._true
      | Fxor a b =>
        if Lit.is_pos l then a::b::nil
        else a::Lit.neg b::nil 
      | Fiff a b =>
        if Lit.is_pos l then a::Lit.neg b::nil
        else Lit.neg a::Lit.neg b::nil
      | Fite a b c =>
        if Lit.is_pos l then a::c::nil
        else a::Lit.neg c::nil
      | _ => C._true
      end
    | _ => C._true
    end.


  (* * xor_pos2          : {(not (xor a b)) (not a) (not b)}
     * xor_neg2          : {(xor a b) (not a) b}
     * equiv_pos2        : {(not (iff a b)) (not a) b}
     * equiv_neg2        : {(iff a b) a b}
     * ite_pos2          : {(not (if_then_else a b c)) (not a) b}
     * ite_neg2          : {(if_then_else a b c) (not a) (not b)} *)

  Definition check_BuildDef2 l :=
    match get_hash (Lit.blit l) with
    | Fxor a b =>
      if Lit.is_pos l then l::Lit.neg a::b::nil
      else l::Lit.neg a::Lit.neg b::nil
    | Fiff a b =>
      if Lit.is_pos l then l::a::b::nil
      else l::Lit.neg a::b::nil
    | Fite a b c =>
      if Lit.is_pos l then l::Lit.neg a::Lit.neg b::nil
      else l::Lit.neg a::b::nil
    | _ => C._true
    end.


  (* * xor2              : {(xor a b)} --> {(not a) (not b)}
     * not_xor2          : {(not (xor a b))} --> {(not a) b}
     * equiv1            : {(iff a b)} --> {(not a) b}
     * not_equiv1        : {(not (iff a b))} --> {a b}
     * ite2              : {(if_then_else a b c)} --> {(not a) b}
     * not_ite2          : {(not (if_then_else a b c))} --> {(not a) (not b)}
     *)

  Definition check_ImmBuildDef2 pos :=
    match S.get s pos with
    | l::nil =>
      match get_hash (Lit.blit l) with
      | Fxor a b =>
        if Lit.is_pos l then Lit.neg a::Lit.neg b::nil
        else Lit.neg a::b::nil
      | Fiff a b =>
        if Lit.is_pos l then Lit.neg a::b::nil
        else a::b::nil
      | Fite a b c =>
        if Lit.is_pos l then Lit.neg a::b::nil
        else Lit.neg a::Lit.neg b::nil
      | _ => C._true
      end
    | _ => C._true
    end.

 
  (* * or_neg           : {(or a_1 ... a_n) (not a_i)}
     * and_pos          : {(not (and a_1 ... a_n)) a_i} 
     * implies_neg1     : {(implies a b) a}
     * implies_neg2     : {(implies a b) (not b)} *)

  Definition check_BuildProj l i :=
    let x := Lit.blit l in
    match get_hash x with
    | For args =>
      if i < PArray.length args then Lit.lit x::Lit.neg (args.[i])::nil
      else C._true
    | Fand args =>
      if i < PArray.length args then Lit.nlit x::(args.[i])::nil
      else C._true
    | Fimp args =>
      let len := PArray.length args in
      if i < len then
        if i == len - 1 then Lit.lit x::Lit.neg (args.[i])::nil
        else Lit.lit x::(args.[i])::nil
      else C._true
    | _ => C._true
    end.


  (* * and               : {(and a_1 ... a_n)} --> {a_i} 
     * not_or            : {(not (or a_1 ... a_n))} --> {(not a_i)}
     * not_implies1      : {(not (implies a b))} --> {a}
     * not_implies2      : {(not (implies a b))} --> {(not b)} *)

  Definition check_ImmBuildProj pos i := 
    match S.get s pos with
    | l::nil =>
      let x := Lit.blit l in
      match get_hash x with
      | For args =>
        if (i < PArray.length args) && negb (Lit.is_pos l) then Lit.neg (args.[i])::nil
        else C._true
      | Fand args =>
        if (i < PArray.length args) && (Lit.is_pos l) then (args.[i])::nil
        else C._true
      | Fimp args =>
        let len := PArray.length args in
        if (i < len) && negb (Lit.is_pos l) then
          if i == len - 1 then Lit.neg (args.[i])::nil
          else (args.[i])::nil
        else C._true
      | _ => C._true
      end
    | _ => C._true
    end.


  (* * not_simplify     : {iff (not (not x)) x}
                          {iff (not false) true}
                          {iff (not true) false}
  *)
  Definition check_NotSimplify l := 
    match get_hash (Lit.blit l) with
    | Fiff a b => 
        match get_hash (Lit.blit a), get_hash (Lit.blit b) with
        | Fnot2 1 x, _ => if x == b then (l::nil) else C._true
        | Ffalse, Ftrue => if (negb (Lit.is_pos a) && (Lit.is_pos b)) then (l::nil) else C._true
        | Ftrue, Ffalse => if (negb (Lit.is_pos a) && (Lit.is_pos b)) then (l::nil) else C._true
        | _, _ => C._true
        end
    | _ => C._true
    end.


  (* * and_simplify     : {iff (and true ... true) true}
                          {iff (and x_1 ... x_n) (and x_1 ... x_n'), removing all true from x_1,...,x_n}
                          {iff (and x_1 ... x_n) (and x_1 ... x_n'), removing all repeated literals from x_1,...,x_n}
                          {iff (and x_1 ... false ... x_n) false}
                          {iff (and x_1 ... x_i ... x_j ... x_n) false, if x_i = not x_j}
  *)
  Definition check_AndSimplify l :=
    match get_hash (Lit.blit l) with
    | Fiff x y => 
      if (Lit.is_pos x) && (Lit.is_pos y) then
        match get_hash (Lit.blit x), get_hash (Lit.blit y) with
        (* and true ... true <-> true *)
        | Fand xs, Ftrue =>
          if PArray.forallb (fun x => eqb x true) 
                            (PArray.map (fun x => Lit.is_pos x && match get_hash (Lit.blit x) with
                                                  | Ftrue => true
                                                  | _ => false
                                                  end) xs) then
          l::nil else C._true
        (* and x_1 ... x_n <-> and x_1 ... x_n', where all true in x_i are removed *)
        | Fand xs, Fand ys => if ((PArray.existsb (fun x => Lit.is_pos x && match get_hash (Lit.blit x) with
                                                            | Ftrue => true
                                                            | _ => false
                                                            end) xs) &&
                                 negb (PArray.existsb (fun x => Lit.is_pos x && match get_hash (Lit.blit x) with
                                                            | Ftrue => true
                                                            | _ => false
                                                            end) ys)) ||
        (* and x_1 ... x_n <-> and x_1 ... x_n', where all duplicates are removed *)
                                 ((PArray.existsbi (fun i x => (PArray.existsbi (fun j y => (negb (i == j)) && (x == y)) xs)) xs) && 
                                 negb (PArray.existsbi (fun i x => (PArray.existsbi (fun j y => (negb (i == j)) && (x == y)) ys)) ys)) then
                                    l::nil else C._true
        (* and x_1 ... false ... x_n <-> false *)
        | Fand xs, Ffalse => if (PArray.existsb (fun x => Lit.is_pos x && match get_hash (Lit.blit x) with
                                                          | Ffalse => true
                                                          | _ => false
                                                          end) 
                                        xs) ||
        (* and x_1 ... x_i ... (not x_i) ... x_n <-> false *)
                                (PArray.existsb (fun x => Lit.is_pos x && 
                                  (PArray.existsb (fun y => negb (Lit.is_pos y) && (Lit.blit x == Lit.blit y)) xs)) xs) then
                             l::nil else C._true
        | _, _ => C._true
        end
      else C._true
    | _ => C._true
    end.


    (* * or_simplify     :  {iff (or false ... false) false}
                            {iff (or x_1 ... x_n) (or x_1 ... x_n'), removing all false from x_1,...,x_n}
                            {iff (or x_1 ... x_n) (or x_1 ... x_n'), removing all repeated literals from x_1,...,x_n}
                            {iff (or x_1 ... true ... x_n) true}
                            {iff (or x_1 ... x_i ... x_j ... x_n) true, if x_i = not x_j}
    *)
    Definition check_OrSimplify l :=
      match get_hash (Lit.blit l) with
      | Fiff x y => 
        if (Lit.is_pos x) && (Lit.is_pos y) then
          match get_hash (Lit.blit x), get_hash (Lit.blit y) with
          (* or false ... false <-> false *)
          | For xs, Ffalse =>
            if PArray.forallb (fun x => eqb x true) 
                              (PArray.map (fun x => Lit.is_pos x && match get_hash (Lit.blit x) with
                                                    | Ffalse => true
                                                    | _ => false
                                                    end) xs) then
            l::nil else C._true
          (* or x_1 ... x_n <-> or x_1 ... x_n', where all false in x_i are removed *)
          | For xs, For ys => if ((PArray.existsb (fun x => Lit.is_pos x && match get_hash (Lit.blit x) with
                                                              | Ffalse => true
                                                              | _ => false
                                                              end) xs) &&
                                   negb (PArray.existsb (fun x => Lit.is_pos x && match get_hash (Lit.blit x) with
                                                              | Ffalse => true
                                                              | _ => false
                                                              end) ys)) ||
          (* or x_1 ... x_n <-> or x_1 ... x_n', where all duplicates are removed *)
                                   ((PArray.existsbi (fun i x => (PArray.existsbi (fun j y => (negb (i == j)) && (x == y)) xs)) xs) && 
                                   negb (PArray.existsbi (fun i x => (PArray.existsbi (fun j y => (negb (i == j)) && (x == y)) ys)) ys)) then
                                      l::nil else C._true
          (* or x_1 ... true ... x_n <-> true *)
          | For xs, Ftrue => if (PArray.existsb (fun x => Lit.is_pos x && match get_hash (Lit.blit x) with
                                                            | Ftrue => true
                                                            | _ => false
                                                            end)
                                          xs) ||
          (* or x_1 ... x_i ... (not x_i) ... x_n <-> true *)
                                  (PArray.existsb (fun x => Lit.is_pos x && 
                                    (PArray.existsb (fun y => negb (Lit.is_pos y) && (Lit.blit x == Lit.blit y)) xs)) xs) then
                               l::nil else C._true
          | _, _ => C._true
          end
        else C._true
      | _ => C._true
      end.

Fixpoint list_eqb l1 l2 : bool :=
  if Nat.eqb (List.length l1) (List.length l2) then
    match l1, l2 with
    | h1 :: t1, h2 :: t2 => (h1 == h2) && list_eqb t1 t2
    | _, _ => false
    end
  else false.

  Definition form_eqb (x y : form) : bool := 
    match x, y with
    | Fatom x, Fatom y => x == y
    | Ftrue, Ftrue | Ffalse, Ffalse => true
    | Fnot2 m x, Fnot2 n y => (x == y) && 
                             (((is_even m) && (is_even n)) || 
                             (negb (is_even m) && negb (is_even n)))
    | Fand xs, Fand ys => PArray.eqb (Int63Native.eqb) xs ys
    | For xs, For ys => PArray.eqb (Int63Native.eqb) xs ys
    | Fimp xs, Fimp ys => PArray.eqb (Int63Native.eqb) xs ys
    | Fxor x1 x2, Fxor y1 y2 => (x1 == y1) && (x2 == y2)
    | Fiff x1 x2, Fiff y1 y2 => (x1 == y1) && (x2 == y2)
    | Fite x1 x2 x3, Fite y1 y2 y3 => (x1 == y1) && (x2 == y2) && (x3 == y3)
    | FbbT x1 x2, FbbT y1 y2 => (x1 == y1) && (list_eqb x2 y2)
    | _, _ => false
    end.

    (* implies_simplify     : {iff (not x -> not y) (y -> x)}
                              {iff (false -> x) true}
                              {iff (x -> true) true}
                              {iff (true -> x) x}
                              {iff (x -> false) (not x)}
                              {iff (x -> x) true}
                              {iff (not x -> x) x}
                              {iff (x -> not x) (not x)}
                              {iff ((x -> y) -> y) (or x y)}
    *)
    Definition check_ImpliesSimplify l :=
      match get_hash (Lit.blit l) with
      | Fiff x y => 
          match get_hash (Lit.blit x) with
          | Fimp xs => 
            if PArray.length xs == 2 then
              let x0 := xs.[0] in
              let x1 := xs.[1] in
              let x0h := get_hash (Lit.blit x0) in
              let x1h := get_hash (Lit.blit x1) in
              let yh := get_hash (Lit.blit y) in
              (* More general cases first *)
              (* iff (x -> x) true *)
              if (x0 == x1) && (form_eqb yh Ftrue) then l::nil 
              (* iff (true -> x) x *)
              else if (x1 == y) && (form_eqb x0h Ftrue) then l::nil
              (* iff (x -> false) (not x) *)
              else if (y == Lit.neg x0) && (form_eqb x1h Ffalse) then l::nil
              (* iff (x -> not x) (not x) *)
              else if (x1 == Lit.neg x0) && (x1 == y) then l::nil
              (* iff (not x -> x) x *)
              else if (x0 == Lit.neg x1) && (x1 == y) then l::nil
              (* More specific cases next *)
              else 
                match x0h, x1h, yh with
                (* iff (false -> x) true *)
                | Ffalse, _, Ftrue => l::nil
                (* iff (x -> true) true *)
                | _, Ftrue, Ftrue => l::nil
                (* iff (not x -> not y) (y -> x) *)
                | x0h, x1h, Fimp ys => 
                  if PArray.length ys == 2 then
                    let y0 := ys.[0] in
                    let y1 := ys.[1] in
                    if (x0 == Lit.neg y1) && (x1 == Lit.neg y0) then l::nil else C._true
                  else C._true
                (*iff ((x -> y) -> y) (or x y)*)
                | Fimp x0s, x1h, For ys =>
                  if (PArray.length x0s == 2) && (PArray.length ys == 2) then
                    let x00 := x0s.[0] in
                    let x01 := x0s.[1] in
                    let y0 := ys.[0] in
                    let y1 := ys.[1] in
                    if (x00 == y0) && (x01 == x1) && (x1 == y1) then l::nil else C._true
                  else C._true
                | _, _, _ => C._true
                end
            else C._true
          | _ => C._true
          end
      | _ => C._true
      end.

      
    (* equiv_simplify     :   {iff (iff (not x) (not y)) (iff x y)}
                              {iff (iff x x) true}
                              {iff (iff x (not x)) false}
                              {iff (iff (not x) x) false}
                              {iff (iff true x) x}
                              {iff (iff x true) x}
                              {iff (iff false x) (not x)}
                              {iff (iff x false) (not x)}
    *)
    Definition check_EquivSimplify l :=
      match get_hash (Lit.blit l) with
      | Fiff x y => 
          match get_hash (Lit.blit x) with
          | Fiff x1 x2 => 
            let x1h := get_hash (Lit.blit x1) in
            let x2h := get_hash (Lit.blit x2) in
            let yh := get_hash (Lit.blit y) in
            (* More general cases first *)
            (* iff (iff true x) x *)
            if (x2 == y) && (form_eqb x1h Ftrue) then l::nil 
            (* iff (iff x true) x *)
            else if (x1 == y) && (form_eqb x2h Ftrue) then l::nil
            (* iff (iff false x) (not x) *)
            else if (y == Lit.neg x2) && (form_eqb x1h Ffalse) then l::nil
            (* iff (iff x false) (not x) *)
            else if (y == Lit.neg x1) && (form_eqb x2h Ffalse) then l::nil
            (* More specific cases next *)
            else 
              match x1h, x2h, yh with
              (* iff (iff x x) true *)
              | _, _, Ftrue => if (x1 == x2) then l::nil else C._true
              (* iff (iff x (not x)) false *)
              | _, _, Ffalse => if (x2 == Lit.neg x1) then l::nil else
                                if (x1 == Lit.neg x2) then l::nil else C._true
              | _, _, Fiff y1 y2 => if (x1 == Lit.neg y1) && (x2 == Lit.neg y2) then l::nil 
                                    else C._true
              | _, _, _ => C._true
              end
          | _ => C._true
          end
      | _ => C._true
      end.

    
    (* bool_simplify     :    {iff (not (x -> y)) (and x (not y))}
                              {iff (not (or x y)) (and (not x) (not y))}
                              {iff (not (and x y)) (or (not x) (not y))}
                              {iff (x -> (y -> z)) ((and x y) -> z)}
                              {iff ((x -> y) -> y) (or x y)}
                              {iff (and x (x -> y)) (and x y)}
                              {iff (and (x -> y) x) (and x y)}
    *)    
    Definition check_BoolSimplify l :=
      match get_hash (Lit.blit l) with
      | Fiff x y => 
          match get_hash (Lit.blit x), get_hash (Lit.blit y) with
          (* iff (not (x -> y)) (and x (not y)) *)
          | Fimp xs, Fand ys => 
              if (PArray.length xs == 2) && (PArray.length ys == 2) 
              && negb (Lit.is_pos x) && (Lit.is_pos y) then
                let x0 := xs.[0] in
                let x1 := xs.[1] in
                let y0 := ys.[0] in
                let y1 := ys.[1] in
                if (x0 == y0) && (y1 == Lit.neg x1) then l::nil else C._true 
              else C._true
          (* iff (not (or x y)) (and (not x) (not y)) *)
          | For xs, Fand ys =>
              if (PArray.length xs == 2) && (PArray.length ys == 2) 
              && negb (Lit.is_pos x) && (Lit.is_pos y) then
                let x0 := xs.[0] in
                let x1 := xs.[1] in
                let y0 := ys.[0] in
                let y1 := ys.[1] in
                if (y0 == Lit.neg x0) && (y1 == Lit.neg x1) then l::nil else C._true 
              else C._true
          (* iff (not (and x y)) (or (not x) (not y)) *)
          | Fand xs, For ys =>
              if (PArray.length xs == 2) && (PArray.length ys == 2) 
              && negb (Lit.is_pos x) && (Lit.is_pos y) then
                let x0 := xs.[0] in
                let x1 := xs.[1] in
                let y0 := ys.[0] in
                let y1 := ys.[1] in
                if (y0 == Lit.neg x0) && (y1 == Lit.neg x1) then l::nil else C._true 
              else C._true
          (* iff (x -> (y -> z)) ((and x y) -> z) *)
          | Fimp xs, Fimp ys =>
              if (PArray.length xs == 2) && (PArray.length ys == 2) 
              && (Lit.is_pos x) && (Lit.is_pos y) then
                let x0 := xs.[0] in
                let x1 := xs.[1] in
                let y0 := ys.[0] in
                let y1 := ys.[1] in
                match get_hash (Lit.blit x1), get_hash (Lit.blit y0) with
                | Fimp x1s, Fand y0s => 
                    if (PArray.length x1s == 2) && (PArray.length y0s == 2) 
                    && (Lit.is_pos x1) && (Lit.is_pos y0) then
                      let x10 := xs.[0] in
                      let x11 := xs.[1] in
                      let y00 := ys.[0] in
                      let y01 := ys.[1] in
                      if (x0 == y00) && (x10 == y00) && (x11 == y1) then l::nil 
                      else C._true
                    else C._true
                | _, _ => C._true
                end
              else C._true
          (* iff ((x -> y) -> y) (or x y) *)
          | Fimp xs, For ys => 
              if (PArray.length xs == 2) && (PArray.length ys == 2) 
              && (Lit.is_pos x) && (Lit.is_pos y) then
                let x0 := xs.[0] in
                let x1 := xs.[1] in
                let y0 := ys.[0] in
                let y1 := ys.[1] in
                match get_hash (Lit.blit x0) with
                | Fimp x0s => 
                    if (PArray.length x0s == 2) && (Lit.is_pos x0) then
                      let x00 := xs.[0] in
                      let x01 := xs.[1] in
                      if (x00 == y0) && (x01 == x1) && (x1 == y1) then l::nil 
                      else C._true 
                    else C._true
                | _ => C._true
                end
              else C._true
          (* iff (and (x -> y) x) (and x y) *)
          (* iff (and x (x -> y)) (and x y) *)
          | Fand xs, Fand ys => 
              if (PArray.length xs == 2) && (PArray.length ys == 2) 
              && (Lit.is_pos x) && (Lit.is_pos y) then
                let x0 := xs.[0] in
                let x1 := xs.[1] in
                let y0 := ys.[0] in
                let y1 := ys.[1] in
                match get_hash (Lit.blit x0), get_hash (Lit.blit x1) with
                | Fimp x0s, _ =>
                    if (PArray.length x0s == 2) && (Lit.is_pos x0) then
                      let x00 := xs.[0] in
                      let x01 := xs.[1] in
                      if (x00 == y0) && (x01 == y1) && (x1 == y0) then l::nil 
                      else C._true 
                    else C._true
                | _, Fimp x1s =>
                    if (PArray.length x1s == 2) && (Lit.is_pos x1) then
                      let x10 := xs.[0] in
                      let x11 := xs.[1] in
                      if (x0 == x10) && (x10 == y0) && (x11 == y1) then l::nil 
                      else C._true 
                    else C._true
                | _, _ => C._true
                end
              else C._true
          | _, _ => C._true
          end
      | _ => C._true
      end.


    (* connective_def     : {iff (xor x y) (or (and (not x) y) (and x (not y)))}
                            {iff (iff x y) (and (x -> y) (y -> x)))}
                            {iff (ite f x y) (and (f -> x) ((not f) -> (not y))))}
    *)
    Definition check_ConnDef l :=
      match get_hash (Lit.blit l) with
      | Fiff x y => 
          if (Lit.is_pos x) && (Lit.is_pos y) then
            match get_hash (Lit.blit x), get_hash (Lit.blit y) with
            (* iff (xor x y) (or (and (not x) y) (and x (not y))) *)
            | Fxor x0 x1, For ys =>
                if (PArray.length ys == 2)then
                  let y0 := ys.[0] in
                  let y1 := ys.[1] in
                  match get_hash (Lit.blit y0), get_hash (Lit.blit y1) with
                    | Fand y0s, Fand y1s => 
                        if (PArray.length y0s == 2) && (Lit.is_pos y0) && 
                           (PArray.length y1s == 2) && (Lit.is_pos y1) then
                          let y00 := y0s.[0] in
                          let y01 := y0s.[1] in
                          let y10 := y1s.[0] in
                          let y11 := y1s.[1] in
                          if (x0 == y10) && (y00 == Lit.neg x0) && (x1 == y01) && (y11 == Lit.neg x1) then
                          l::nil else C._true
                        else C._true
                    | _, _ => C._true
                  end
                else C._true
            (* iff (iff x y) (and (x -> y) (y -> x))) *)
            | Fiff x0 x1, Fand ys =>
                if (PArray.length ys == 2)then
                  let y0 := ys.[0] in
                  let y1 := ys.[1] in
                  match get_hash (Lit.blit y0), get_hash (Lit.blit y1) with
                    | Fimp y0s, Fimp y1s => 
                        if (PArray.length y0s == 2) && (Lit.is_pos y0) && 
                           (PArray.length y1s == 2) && (Lit.is_pos y1) then
                          let y00 := y0s.[0] in
                          let y01 := y0s.[1] in
                          let y10 := y1s.[0] in
                          let y11 := y1s.[1] in
                          if (x0 == y00) && (x0 == y11) && (x1 == y01) && (x1 == y10) then
                          l::nil else C._true
                        else C._true
                    | _, _ => C._true
                  end
                else C._true
            (* iff (ite f x y) (and (f -> x) ((not f) -> (not y)))) *)
            | Fite f x0 x1, Fand ys =>
                if (PArray.length ys == 2)then
                  let y0 := ys.[0] in
                  let y1 := ys.[1] in
                  match get_hash (Lit.blit y0), get_hash (Lit.blit y1) with
                    | Fimp y0s, Fimp y1s => 
                        if (PArray.length y0s == 2) && (Lit.is_pos y0) && 
                           (PArray.length y1s == 2) && (Lit.is_pos y1) then
                          let y00 := y0s.[0] in
                          let y01 := y0s.[1] in
                          let y10 := y1s.[0] in
                          let y11 := y1s.[1] in
                          if (f == y00) && (y10 == Lit.neg f) && (x0 == y01) && (y11 == Lit.neg x1) then
                          l::nil else C._true
                        else C._true
                    | _, _ => C._true
                  end
                else C._true
            | _, _ => C._true
            end
          else C._true
      | _ => C._true
      end.


    (* ite_simplify       :   {iff (ite true x y) x}
                              {iff (ite false x y) y)}
                              {iff (ite f x x) x}
                              {iff (ite (not f) x y) (ite f y x)}
                              {iff (ite f (ite f x y) z) (ite f x z)}
                              {iff (ite f x (ite f y z)) (ite f x z)}
                              {iff (ite f true false) f}
                              {iff (ite f false true) (not f)}
                              {iff (ite f true x) (or f x)}
                              {iff (ite f x false) (and f x)}
                              {iff (ite f false x) (and (not f) x)}
                              {iff (ite f x true) (or (not f) x)}
    *)
    Definition check_IteSimplify l :=
      match get_hash (Lit.blit l) with
      | Fiff x y => 
        if (Lit.is_pos x) then
          match get_hash (Lit.blit x) with
          | Fite xf x1 x2 => 
            (* iff (ite f x x) x *)
            if (x1 == x2) && (x1 == y) then l::nil else
            match get_hash (Lit.blit xf), get_hash (Lit.blit x1), get_hash (Lit.blit x2), get_hash (Lit.blit y) with
              (* iff (ite f (ite f x y) z) (ite f x z) *)
              | _, Fite x1f x11 x12, _, Fite yf y1 y2 => 
                if (Lit.is_pos x1) && (Lit.is_pos y) && (xf == x1f) && (xf == yf) && (x11 == y1) && (x2 == y2) then 
                l::nil else C._true
              (* iff (ite f x (ite f y z)) (ite f x z) *)
              | _, _, Fite x2f x21 x22, Fite yf y1 y2 =>
                if (Lit.is_pos x2) && (Lit.is_pos y) && (xf == x2f) && (xf == yf) && (x1 == y1) && (x22 == y2) then 
                l::nil else C._true
              (* iff (ite (not f) x y) (ite f y x) *)
              | _, _, _, Fite yf y1 y2 =>
                if (Lit.is_pos y) && (xf == Lit.neg yf) && (x1 == y2) && (x2 == y1) then l::nil else C._true
              (* iff (ite f true x) (or f x) *)
              | _, Ftrue, _, For ys =>
                if (Lit.is_pos y) && (PArray.length ys == 2)then
                  let y0 := ys.[0] in
                  let y1 := ys.[1] in
                  if (xf == y0) && (x2 == y1) then l::nil else C._true
                else C._true
              (* iff (ite f x false) (and f x) *)
              | _, _, Ffalse, Fand ys =>
                if (Lit.is_pos y) && (PArray.length ys == 2)then
                  let y0 := ys.[0] in
                  let y1 := ys.[1] in
                  if (xf == y0) && (x1 == y1) then l::nil else C._true
                else C._true
              (* iff (ite f false x) (and (not f) x) *)
              | _, Ffalse, _, Fand ys =>
                if (Lit.is_pos y) && (PArray.length ys == 2)then
                  let y0 := ys.[0] in
                  let y1 := ys.[1] in
                  if (y0 == Lit.neg xf) && (x2 == y1) then l::nil else C._true
                else C._true
              (* iff (ite f x true) (or (not f) x) *)
              | _, _, Ftrue, For ys =>
                if (Lit.is_pos y) && (PArray.length ys == 2)then
                  let y0 := ys.[0] in
                  let y1 := ys.[1] in
                  if (y0 == Lit.neg xf) && (x1 == y1) then l::nil else C._true
                else C._true
              (* iff (ite true x y) x *)
              | Ftrue, _, _, _ =>
                if (x1 == y) then l::nil else C._true
              (* iff (ite false x y) y) *)
              | Ffalse, _, _, _ =>
                if (x2 == y) then l::nil else C._true
              (* iff (ite f true false) f *)
              | _, Ftrue, Ffalse, _ => 
                if (xf == y) then l::nil else C._true
              (* iff (ite f false true) (not f) *)
              | _, Ffalse, Ftrue, _ => 
                if (y == Lit.neg xf) then l::nil else C._true
              | _, _, _, _ => C._true
            end
          | _ => C._true
          end
        else C._true
      | _ => C._true
      end.


    (* ac_simp        :       {iff x (y_1 o y_2 o ... o y_n), where o is and/or and
                                - all chains with and/or are flattened
                                - repeated literals in each and/or application are removed}
    *)

    (* Array append *)
    (*Definition array_append {A:Type} x1 x2 :=
      let len1 := @PArray.length A x1 in
      let len2 := @PArray.length A x2 in
      let def := PArray.default x1 in
      let res := PArray.make (len1 + len2) def in
      PArray.mapi (fun i x => if negb (i < 0) && (i < len1) then
                                PArray.get x1 i
                              else
                                PArray.get x2 (i-len1)) res.

    Fixpoint array_of_list_aux l ar i :=
      match l with
      | nil => ar
      | h :: t => array_of_list_aux t (@PArray.set int ar i h) (i+1)
      end.

    Definition array_of_list l :=
      match l with
      | nil => PArray.make 0 0
      | l => let ar := PArray.make (Int31.phi_inv (Z.of_nat (List.length l))) 0 in
              array_of_list_aux l ar 0
      end.

    Definition arrAppend x y :=
      array_of_list (List.app (PArray.to_list x) (PArray.to_list y)).

    Fixpoint acSimp l :=
      match get_hash (Lit.blit l) with
      | Fand xs => 
        let xs' := PArray.map (fun x => match get_hash (Lit.blit x) with
        (* for each literal, if literal is Fand, recursive call, and then flatten *)
                                       | Fand xs2 => match (acSimp x) with
                                                     | Fand xs2' => Fand (array_append xs xs2')
                                                     | y => y
                                                     end
        (* for each literal, if literal is For, recursive call *)
                                       | For xs2 => acSimp x 
                                       | y => y
                                       end) xs in
        (* remove repetitions *)
        Fand xs' (* this is ill-typed since xs' is unhashed, we need to hash it again *)
      | For xs => 
        let xs' := PArray.map (fun x => match get_hash (Lit.blit x) with
        (* for each literal, if literal is For, recursive call, and then flatten *)
                                       | For xs2 => match (acSimp x) with
                                                     | For xs2' => For (array_append xs xs2')
                                                     | y => y
                                                    end
        (* for each literal, if literal is Fand, recursive call *)
                                       | Fand xs2 => acSimp x 
                                       | y => y
                                       end) xs in
        (* remove repetitions *)
        For xs' (* this is ill-typed since xs' is unhashed, we need to hash it again *)
      | y => y
      end.

    Definition check_AcSimp l :=
      match get_hash (Lit.blit l) with
      | Fiff x y => 
        if (Lit.is_pos x) && (Lit.is_pos y) then
          if (acSimp x) == y then l else C._true
        else C._true
      | _ => C._true
      end.*)


  (** The correctness proofs *)

  Variable interp_atom : atom -> bool.
  Variable interp_bvatom : atom -> forall s, BITVECTOR_LIST.bitvector s.

  Hypothesis Hch_f : check_form t_form.

  Local Notation rho := (Form.interp_state_var interp_atom interp_bvatom t_form).

  Let Hwfrho : Valuation.wf rho.
  Proof.
    destruct (check_form_correct interp_atom interp_bvatom _ Hch_f) as (_, H);exact H. 
  Qed.

  Lemma valid_check_True : C.valid rho check_True.
  Proof. 
    apply C.interp_true;trivial.
  Qed.

  Lemma valid_check_False : C.valid rho check_False.
  Proof.
    unfold check_False, C.valid. change (Lit.interp rho (Lit.neg Lit._false) || false = true).
    rewrite Lit.interp_neg.
    assert (W:= Lit.interp_false _ Hwfrho).
    destruct (Lit.interp rho Lit._false);trivial;elim W;red;trivial.
  Qed.

  Let rho_interp : forall x : int,
    rho x = interp interp_atom interp_bvatom t_form (t_form.[ x]).
  Proof.
    destruct (check_form_correct interp_atom interp_bvatom _ Hch_f) as ((H,H0), _).
    intros x;apply wf_interp_form;trivial.
  Qed.

  Ltac tauto_check :=
   try (rewrite !Lit.interp_neg);
   repeat 
     match goal with |- context [Lit.interp rho ?x] => 
     destruct (Lit.interp rho x);trivial end.

  Lemma valid_check_NotNot : forall l, C.valid rho (check_NotNot l).
  Proof.
    admit.
  Admitted.

  Lemma valid_check_Tautology : forall pos l, C.valid rho (check_Tautology pos l).
  Proof.
    admit.
  Admitted.

  Lemma valid_check_Contraction : forall pos1 pos2, C.valid rho (check_Contraction pos1 pos2).
  Proof.
    admit.
  Admitted.
  
  Lemma valid_check_BuildDef : forall l, C.valid rho (check_BuildDef l).
  Proof.
   unfold check_BuildDef,C.valid;intros l.
   case_eq (t_form.[Lit.blit l]);intros;auto using C.interp_true;
     case_eq (Lit.is_pos l);intros Heq;auto using C.interp_true;simpl;
       try (unfold Lit.interp at 1;rewrite Heq;unfold Var.interp; rewrite rho_interp, H;simpl;
            tauto_check).
   - rewrite afold_left_and, C.Cinterp_neg;apply orb_negb_r.
   - rewrite afold_left_or, orb_comm;apply orb_negb_r.
   - case_eq (PArray.length a == 0); auto using C.interp_true.
     intro Hl; simpl.
     unfold Lit.interp at 1;rewrite Heq;unfold Var.interp; rewrite rho_interp, H;simpl.
     rewrite (afold_right_impb (Lit.interp_neg _) Hl), orb_comm;try apply orb_negb_r.
  Qed.

  Lemma valid_check_BuildDef2 : forall l, C.valid rho (check_BuildDef2 l).
  Proof.
   unfold check_BuildDef2,C.valid;intros l.
   case_eq (t_form.[Lit.blit l]);intros;auto using C.interp_true;
   case_eq (Lit.is_pos l);intros Heq;auto using C.interp_true;simpl;
   unfold Lit.interp at 1;rewrite Heq;unfold Var.interp; rewrite rho_interp, H;simpl;
   tauto_check.
  Qed.

  Lemma valid_check_BuildProj : forall l i, C.valid rho (check_BuildProj l i).
  Proof.
   unfold check_BuildProj,C.valid;intros l i.
   case_eq (t_form.[Lit.blit l]);intros;auto using C.interp_true;
   case_eq (i < PArray.length a);intros Hlt;auto using C.interp_true;simpl.
   - rewrite Lit.interp_nlit;unfold Var.interp;rewrite rho_interp, orb_false_r, H.
     simpl;rewrite afold_left_and.
     case_eq (forallb (Lit.interp rho) (to_list a));trivial.
     rewrite forallb_forall;intros Heq;rewrite Heq;trivial.
     apply to_list_In; auto.
   - rewrite Lit.interp_lit;unfold Var.interp;rewrite rho_interp, orb_false_r, H.
     simpl;rewrite afold_left_or.
     unfold C.interp;case_eq (existsb (Lit.interp rho) (to_list a));trivial.
     rewrite <-not_true_iff_false, existsb_exists, Lit.interp_neg.
     case_eq (Lit.interp rho (a .[ i]));trivial.
     intros Heq Hex;elim Hex;exists (a.[i]);split;trivial.
     apply to_list_In; auto.
   - assert (Hl : (PArray.length a == 0) = false)
       by (rewrite eqb_false_spec; intro H1; rewrite H1 in Hlt; now elim (ltb_0 i)).
     case_eq (i == PArray.length a - 1);intros Heq;simpl;
       rewrite Lit.interp_lit;unfold Var.interp;rewrite rho_interp, H;simpl.
     + rewrite Lit.interp_neg, orb_false_r.
       rewrite (afold_right_impb (Lit.interp_neg _) Hl).
       case_eq (Lit.interp rho (a .[ i])); intro Hi.
       * rewrite orb_false_r, existsb_exists.
         exists (a .[ i]). split; auto.
         {
           apply (to_list_In_eq _ i).
           - now rewrite length_or_of_imp.
           - symmetry. apply get_or_of_imp2.
             + clear -Hl. rewrite eqb_false_spec in Hl.
               unfold is_true. rewrite ltb_spec. change [|0|] with 0%Z.
               assert (H:[|PArray.length a|] <> 0%Z)
                 by (intro H; apply Hl; now apply to_Z_inj).
               destruct (to_Z_bounded (PArray.length a)) as [H1 _].
               lia.
             + now rewrite Int63Properties.eqb_spec in Heq.
         }
       * now rewrite orb_true_r.
     + rewrite orb_false_r.
       case_eq (Lit.interp rho (a .[ i])); intro Hi.
       * now rewrite orb_true_r.
       * rewrite (afold_right_impb (Lit.interp_neg _) Hl).
         rewrite orb_false_r, existsb_exists.
         exists (Lit.neg (a .[ i])).
         {
           split.
           - apply (to_list_In_eq _ i).
             + now rewrite length_or_of_imp.
             + symmetry. apply get_or_of_imp.
               clear -Hlt Heq.
               unfold is_true. rewrite ltb_spec. rewrite (to_Z_sub_1 _ i); auto.
               rewrite eqb_false_spec in Heq.
               assert (H:[|i|] <> ([|PArray.length a|] - 1)%Z)
                 by (intro H; apply Heq, to_Z_inj; rewrite (to_Z_sub_1 _ i); auto).
               clear Heq.
               rewrite ltb_spec in Hlt. lia.
           - now rewrite Lit.interp_neg, Hi.
         }
  Qed.
  
  Lemma valid_check_NotSimplify : forall l, C.valid rho (check_NotSimplify l).
  Proof.
    admit.
  Admitted.

  Lemma valid_check_AndSimplify : forall l, C.valid rho (check_AndSimplify l).
  Proof.
    admit.
  Admitted.

  Lemma valid_check_OrSimplify : forall l, C.valid rho (check_OrSimplify l).
  Proof.
    admit.
  Admitted.

  Lemma valid_check_ImpliesSimplify : forall l, C.valid rho (check_ImpliesSimplify l).
  Proof.
    admit.
  Admitted.

  Lemma valid_check_EquivSimplify : forall l, C.valid rho (check_EquivSimplify l).
  Proof.
    admit.
  Admitted.

  Lemma valid_check_BoolSimplify : forall l, C.valid rho (check_BoolSimplify l).
  Proof.
    admit.
  Admitted.

  Lemma valid_check_ConnDef : forall l, C.valid rho (check_ConnDef l).
  Proof.
    admit.
  Admitted.

  Lemma valid_check_IteSimplify : forall l, C.valid rho (check_IteSimplify l).
  Proof.
    admit.
  Admitted.

  Hypothesis Hs : S.valid rho s.

  Lemma valid_check_ImmBuildDef : forall cid,
     C.valid rho (check_ImmBuildDef cid).
  Proof.
   unfold check_ImmBuildDef,C.valid;intros cid.
   generalize (Hs cid);unfold C.valid.
   destruct (S.get s cid) as [ | l [ | _l _c]];auto using C.interp_true.
   simpl;unfold Lit.interp, Var.interp; rewrite !rho_interp;
   destruct (t_form.[Lit.blit l]);auto using C.interp_true;
   case_eq (Lit.is_pos l);intros Heq;auto using C.interp_true;simpl;
   tauto_check.
   - rewrite afold_left_and, C.Cinterp_neg, orb_false_r;trivial.
   - rewrite afold_left_or, orb_false_r;trivial.
   - case_eq (PArray.length a == 0); auto using C.interp_true.
     intro Hl. now rewrite orb_false_r, (afold_right_impb (Lit.interp_neg _) Hl).
   - case_eq (PArray.length a == 0); auto using C.interp_true.
  Qed.

  Lemma valid_check_ImmBuildDef2 : forall cid, C.valid rho (check_ImmBuildDef2 cid).
  Proof.
    unfold check_ImmBuildDef2,C.valid;intros cid.
    generalize (Hs cid);unfold C.valid.
    destruct (S.get s cid) as [ | l [ | _l _c]];auto using C.interp_true.
    simpl;unfold Lit.interp, Var.interp; rewrite !rho_interp;
    destruct (t_form.[Lit.blit l]);auto using C.interp_true;
    case_eq (Lit.is_pos l);intros Heq;auto using C.interp_true;simpl;
    tauto_check.
  Qed.

  Lemma valid_check_ImmBuildProj : forall cid i, C.valid rho (check_ImmBuildProj cid i).
  Proof.
   unfold check_ImmBuildProj,C.valid;intros cid i.
   generalize (Hs cid);unfold C.valid.
   destruct (S.get s cid) as [ | l [ | _l _c]];auto using C.interp_true.
   simpl;unfold Lit.interp, Var.interp; rewrite !rho_interp;
     destruct (t_form.[Lit.blit l]);auto using C.interp_true;
       case_eq (i < PArray.length a); intros Hlt;auto using C.interp_true;
       case_eq (Lit.is_pos l);intros Heq;auto using C.interp_true;simpl;
       rewrite !orb_false_r.  
   - rewrite afold_left_and.
     rewrite forallb_forall;intros H;apply H;auto.
     apply to_list_In; auto.
   - rewrite negb_true_iff, <-not_true_iff_false, afold_left_or.
     unfold C.interp;rewrite existsb_exists, Lit.interp_neg.
     case_eq (Lit.interp rho (a .[ i]));trivial.
     intros Heq' Hex;elim Hex;exists (a.[i]);split;trivial.
     apply to_list_In; auto.
   - rewrite negb_true_iff, <-not_true_iff_false.
     assert (Hl:(PArray.length a == 0) = false)
       by (rewrite eqb_false_spec; intro H; rewrite H in Hlt; now apply (ltb_0 i)).
     rewrite (afold_right_impb (Lit.interp_neg _) Hl).
     case_eq (i == PArray.length a - 1);intros Heq';simpl;
       unfold C.interp;simpl;try rewrite Lit.interp_neg;rewrite orb_false_r,
                                                        existsb_exists;case_eq (Lit.interp rho (a .[ i]));trivial;
         intros Heq2 Hex;elim Hex.
     exists (a.[i]);split;trivial.
     assert (H1: 0 < PArray.length a) by (apply (leb_ltb_trans _ i _); auto; apply leb_0); rewrite Int63Properties.eqb_spec in Heq'; rewrite <- (get_or_of_imp2 H1 Heq'); apply to_list_In; rewrite length_or_of_imp; auto.
     exists (Lit.neg (a.[i]));rewrite Lit.interp_neg, Heq2;split;trivial.
     assert (H1: i < PArray.length a - 1 = true) by (rewrite ltb_spec, (to_Z_sub_1 _ _ Hlt); rewrite eqb_false_spec in Heq'; assert (H1: [|i|] <> ([|PArray.length a|] - 1)%Z) by (intro H1; apply Heq', to_Z_inj; rewrite (to_Z_sub_1 _ _ Hlt); auto); rewrite ltb_spec in Hlt; omega); rewrite <- (get_or_of_imp H1); apply to_list_In; rewrite length_or_of_imp; auto.
  Qed.

End CHECKER.
  
Unset Implicit Arguments.
