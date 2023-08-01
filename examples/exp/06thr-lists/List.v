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


(* [Require Import SMTCoq.SMTCoq.] loads the SMTCoq library.
   If you are using native-coq instead of Coq 8.9, replace it with:
     Require Import SMTCoq.
   *)
   Add Rec LoadPath "/home/arjun/Desktop/smtcoq/abduction-arjunvish-smtcoq/smtcoq/src" as SMTCoq.
   Require Import SMTCoq.SMTCoq.
   
   Require Setoid.
   Require Import PeanoNat Le Gt Minus Bool Lt.
   
   Set Implicit Arguments.
   (* Set Universe Polymorphism. *)
   
   (******************************************************************)
   (** * Basics: definition of polymorphic lists and some operations *)
   (******************************************************************)
   
   (** The definition of [list] is now in [Init/Datatypes],
       as well as the definitions of [length] and [app] *)
   
   Open Scope list_scope.
   
   (** Standard notations for lists.
   In a special module to avoid conflicts. *)
   Module ListNotations.
   Notation "[ ]" := nil (format "[ ]") : list_scope.
   Notation "[ x ]" := (cons x nil) : list_scope.
   Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)) : list_scope.
   End ListNotations.
   
   Import ListNotations.
   
   Section Lists.
   
     Variable A : Type.
   
     (** Head and tail *)
   
     Definition hd (default:A) (l:list A) :=
       match l with
         | [] => default
         | x :: _ => x
       end.
   
     Definition hd_error (l:list A) :=
       match l with
         | [] => None
         | x :: _ => Some x
       end.
   
     Definition tl (l:list A) :=
       match l with
         | [] => nil
         | a :: m => m
       end.
   
     (** The [In] predicate *)
     Fixpoint In (a:A) (l:list A) : Prop :=
       match l with
         | [] => False
         | b :: m => b = a \/ In a m
       end.
   
   End Lists.
   
   Section Facts.
   
     Variable A : Type.
   
   
     (** *** Generic facts *)
   
     (** Discrimination *)
     Theorem nil_cons (x:A) (l:list A) : [] <> x :: l.
     Proof. Show. Fail (abduce 3). Admitted.
   
   
     (** Destruction *)
   
     Theorem destruct_list (l : list A) : {x:A & {tl:list A | l = x::tl}}+{l = []}.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma hd_error_tl_repr l (a:A) r :
       hd_error l = Some a /\ tl l = r <-> l = a :: r.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma hd_error_some_nil l (a:A) : hd_error l = Some a -> l <> nil.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Theorem length_zero_iff_nil (l : list A):
       length l = 0 <-> l=[].
     Proof. Show. Fail (abduce 3). Admitted.
   
     (** *** Head and tail *)
   
     Theorem hd_error_nil : hd_error (@nil A) = None.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Theorem hd_error_cons (l : list A) (x : A) : hd_error (x::l) = Some x.
     Proof. Show. Fail (abduce 3). Admitted.
   
   
     (**************************)
     (** *** Facts about [app] *)
     (**************************)
   
     (** Discrimination *)
     Theorem app_cons_not_nil (x y:list A) (a:A) : [] <> x ++ a :: y.
     Proof. Show. Fail (abduce 3). Admitted.
   
   
     (** Concat with [nil] *)
     Theorem app_nil_l (l:list A) : [] ++ l = l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Theorem app_nil_r (l:list A) : l ++ [] = l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     (* begin hide *)
     (* Deprecated *)
     Theorem app_nil_end (l:list A) : l = l ++ [].
     Proof. Show. Fail (abduce 3). Admitted.
     (* end hide *)
   
     (** [app] is associative *)
     Theorem app_assoc (l m n:list A) : l ++ m ++ n = (l ++ m) ++ n.
     Proof. Show. Fail (abduce 3). Admitted.
   
     (* begin hide *)
     (* Deprecated *)
     Theorem app_assoc_reverse (l m n:list A) : (l ++ m) ++ n = l ++ m ++ n.
     Proof. Show. Fail (abduce 3). Admitted.
     #[local]
     Hint Resolve app_assoc_reverse : core.
     (* end hide *)
   
     (** [app] commutes with [cons] *)
     Theorem app_comm_cons (x y:list A) (a:A) : a :: (x ++ y) = (a :: x) ++ y.
     Proof. Show. Fail (abduce 3). Admitted.
   
     (** Facts deduced from the result of a concatenation *)
   
     Theorem app_eq_nil (l l':list A) : l ++ l' = [] -> l = [] /\ l' = [].
     Proof. Show. Fail (abduce 3). Admitted.
   
     Theorem app_eq_unit (x y:list A) (a:A) :
         x ++ y = [a] -> x = [] /\ y = [a] \/ x = [a] /\ y = [].
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma elt_eq_unit l1 l2 (a b : A) :
       l1 ++ a :: l2 = [b] -> a = b /\ l1 = [] /\ l2 = [].
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma app_inj_tail_iff :
       forall (x y:list A) (a b:A), x ++ [a] = y ++ [b] <-> x = y /\ a = b.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma app_inj_tail :
       forall (x y:list A) (a b:A), x ++ [a] = y ++ [b] -> x = y /\ a = b.
     Proof. Show. Fail (abduce 3). Admitted.
   
     (** Compatibility with other operations *)
   
     Lemma app_length : forall l l' : list A, length (l++l') = length l + length l'.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma last_length : forall (l : list A) a, length (l ++ a :: nil) = S (length l).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma app_inv_head_iff:
      forall l l1 l2 : list A, l ++ l1 = l ++ l2 <-> l1 = l2.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma app_inv_head:
      forall l l1 l2 : list A, l ++ l1 = l ++ l2 -> l1 = l2.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma app_inv_tail:
       forall l l1 l2 : list A, l1 ++ l = l2 ++ l -> l1 = l2.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma app_inv_tail_iff:
       forall l l1 l2 : list A, l1 ++ l = l2 ++ l <-> l1 = l2.
     Proof. Show. Fail (abduce 3). Admitted.
   
     (************************)
     (** *** Facts about [In] *)
     (************************)
   
   
     (** Characterization of [In] *)
   
     Theorem in_eq : forall (a:A) (l:list A), In a (a :: l).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Theorem in_cons : forall (a b:A) (l:list A), In b l -> In b (a :: l).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Theorem not_in_cons (x a : A) (l : list A):
       ~ In x (a::l) <-> x<>a /\ ~ In x l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Theorem in_nil : forall a:A, ~ In a [].
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma in_app_or : forall (l m:list A) (a:A), In a (l ++ m) -> In a l \/ In a m.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma in_or_app : forall (l m:list A) (a:A), In a l \/ In a m -> In a (l ++ m).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma in_app_iff : forall l l' (a:A), In a (l++l') <-> In a l \/ In a l'.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Theorem in_split : forall x (l:list A), In x l -> exists l1 l2, l = l1++x::l2.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma in_elt : forall (x:A) l1 l2, In x (l1 ++ x :: l2).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma in_elt_inv : forall (x y : A) l1 l2,
       In x (l1 ++ y :: l2) -> x = y \/ In x (l1 ++ l2).
     Proof. Show. Fail (abduce 3). Admitted.
   
     (** Inversion *)
     Lemma in_inv : forall (a b:A) (l:list A), In b (a :: l) -> a = b \/ In b l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     (** Decidability of [In] *)
     Theorem in_dec :
       (forall x y:A, {x = y} + {x <> y}) ->
       forall (a:A) (l:list A), {In a l} + {~ In a l}.
     Proof. Show. Fail (abduce 3). Admitted.
   
   
   
   End Facts.
   
   #[global]
   Hint Resolve app_assoc app_assoc_reverse: datatypes.
   #[global]
   Hint Resolve app_comm_cons app_cons_not_nil: datatypes.
   #[global]
   Hint Immediate app_eq_nil: datatypes.
   #[global]
   Hint Resolve app_eq_unit app_inj_tail: datatypes.
   #[global]
   Hint Resolve in_eq in_cons in_inv in_nil in_app_or in_or_app: datatypes.
   
   
   
   (*******************************************)
   (** * Operations on the elements of a list *)
   (*******************************************)
   
   Section Elts.
   
     Variable A : Type.
   
     (*****************************)
     (** ** Nth element of a list *)
     (*****************************)
   
     Fixpoint nth (n:nat) (l:list A) (default:A) {struct l} : A :=
       match n, l with
         | O, x :: l' => x
         | O, other => default
         | S m, [] => default
         | S m, x :: t => nth m t default
       end.
   
     Fixpoint nth_ok (n:nat) (l:list A) (default:A) {struct l} : bool :=
       match n, l with
         | O, x :: l' => true
         | O, other => false
         | S m, [] => false
         | S m, x :: t => nth_ok m t default
       end.
   
     Lemma nth_in_or_default :
       forall (n:nat) (l:list A) (d:A), {In (nth n l d) l} + {nth n l d = d}.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma nth_S_cons :
       forall (n:nat) (l:list A) (d a:A),
         In (nth n l d) l -> In (nth (S n) (a :: l) d) (a :: l).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Fixpoint nth_error (l:list A) (n:nat) {struct n} : option A :=
       match n, l with
         | O, x :: _ => Some x
         | S n, _ :: l => nth_error l n
         | _, _ => None
       end.
   
     Definition nth_default (default:A) (l:list A) (n:nat) : A :=
       match nth_error l n with
         | Some x => x
         | None => default
       end.
   
     Lemma nth_default_eq :
       forall n l (d:A), nth_default d l n = nth n l d.
     Proof. Show. Fail (abduce 3). Admitted.
   
     (** Results about [nth] *)
   
     Lemma nth_In :
       forall (n:nat) (l:list A) (d:A), n < length l -> In (nth n l d) l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma In_nth l x d : In x l ->
       exists n, n < length l /\ nth n l d = x.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma nth_overflow : forall l n d, length l <= n -> nth n l d = d.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma nth_indep :
       forall l n d d', n < length l -> nth n l d = nth n l d'.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma app_nth1 :
       forall l l' d n, n < length l -> nth n (l++l') d = nth n l d.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma app_nth2 :
       forall l l' d n, n >= length l -> nth n (l++l') d = nth (n-length l) l' d.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma app_nth2_plus : forall l l' d n,
       nth (length l + n) (l ++ l') d = nth n l' d.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma nth_middle : forall l l' a d,
       nth (length l) (l ++ a :: l') d = a.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma nth_split n l d : n < length l ->
       exists l1, exists l2, l = l1 ++ nth n l d :: l2 /\ length l1 = n.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma nth_ext : forall l l' d d', length l = length l' ->
       (forall n, n < length l -> nth n l d = nth n l' d') -> l = l'.
     Proof. Show. Fail (abduce 3). Admitted.
   
     (** Results about [nth_error] *)
   
     Lemma nth_error_In l n x : nth_error l n = Some x -> In x l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma In_nth_error l x : In x l -> exists n, nth_error l n = Some x.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma nth_error_None l n : nth_error l n = None <-> length l <= n.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma nth_error_Some l n : nth_error l n <> None <-> n < length l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma nth_error_split l n a : nth_error l n = Some a ->
       exists l1, exists l2, l = l1 ++ a :: l2 /\ length l1 = n.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma nth_error_app1 l l' n : n < length l ->
       nth_error (l++l') n = nth_error l n.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma nth_error_app2 l l' n : length l <= n ->
       nth_error (l++l') n = nth_error l' (n-length l).
     Proof. Show. Fail (abduce 3). Admitted.
   
     (** Results directly relating [nth] and [nth_error] *)
   
     Lemma nth_error_nth : forall (l : list A) (n : nat) (x d : A),
       nth_error l n = Some x -> nth n l d = x.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma nth_error_nth' : forall (l : list A) (n : nat) (d : A),
       n < length l -> nth_error l n = Some (nth n l d).
     Proof. Show. Fail (abduce 3). Admitted.
   
     (******************************)
     (** ** Last element of a list *)
     (******************************)
   
     (** [last l d] returns the last element of the list [l],
       or the default value [d] if [l] is empty. *)
   
     Fixpoint last (l:list A) (d:A) : A :=
     match l with
       | [] => d
       | [a] => a
       | a :: l => last l d
     end.
   
     Lemma last_last : forall l a d, last (l ++ [a]) d = a.
     Proof. Show. Fail (abduce 3). Admitted.
   
     (** [removelast l] remove the last element of [l] *)
   
     Fixpoint removelast (l:list A) : list A :=
       match l with
         | [] =>  []
         | [a] => []
         | a :: l => a :: removelast l
       end.
   
     Lemma app_removelast_last :
       forall l d, l <> [] -> l = removelast l ++ [last l d].
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma exists_last :
       forall l, l <> [] -> { l' : (list A) & { a : A | l = l' ++ [a]}}.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma removelast_app :
       forall l l', l' <> [] -> removelast (l++l') = l ++ removelast l'.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma removelast_last : forall l a, removelast (l ++ [a]) = l.
     Proof. Show. Fail (abduce 3). Admitted.
   
   
     (*****************)
     (** ** Remove    *)
     (*****************)
   
     Hypothesis eq_dec : forall x y : A, {x = y}+{x <> y}.
   
     Fixpoint remove (x : A) (l : list A) : list A :=
       match l with
         | [] => []
         | y::tl => if (eq_dec x y) then remove x tl else y::(remove x tl)
       end.
   
     Lemma remove_cons : forall x l, remove x (x :: l) = remove x l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma remove_app : forall x l1 l2,
       remove x (l1 ++ l2) = remove x l1 ++ remove x l2.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Theorem remove_In : forall (l : list A) (x : A), ~ In x (remove x l).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma notin_remove: forall l x, ~ In x l -> remove x l = l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma in_remove: forall l x y, In x (remove y l) -> In x l /\ x <> y.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma in_in_remove : forall l x y, x <> y -> In x l -> In x (remove y l).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma remove_remove_comm : forall l x y,
       remove x (remove y l) = remove y (remove x l).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma remove_remove_eq : forall l x, remove x (remove x l) = remove x l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma remove_length_le : forall l x, length (remove x l) <= length l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma remove_length_lt : forall l x, In x l -> length (remove x l) < length l.
     Proof. Show. Fail (abduce 3). Admitted.
   
   
     (******************************************)
     (** ** Counting occurrences of an element *)
     (******************************************)
   
     Fixpoint count_occ (l : list A) (x : A) : nat :=
       match l with
         | [] => 0
         | y :: tl =>
           let n := count_occ tl x in
           if eq_dec y x then S n else n
       end.
   
     (** Compatibility of count_occ with operations on list *)
     Theorem count_occ_In l x : In x l <-> count_occ l x > 0.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Theorem count_occ_not_In l x : ~ In x l <-> count_occ l x = 0.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma count_occ_nil x : count_occ [] x = 0.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Theorem count_occ_inv_nil l :
       (forall x:A, count_occ l x = 0) <-> l = [].
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma count_occ_cons_eq l x y :
       x = y -> count_occ (x::l) y = S (count_occ l y).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma count_occ_cons_neq l x y :
       x <> y -> count_occ (x::l) y = count_occ l y.
     Proof. Show. Fail (abduce 3). Admitted.
   
   End Elts.
   
   (*******************************)
   (** * Manipulating whole lists *)
   (*******************************)
   
   Section ListOps.
   
     Variable A : Type.
   
     (*************************)
     (** ** Reverse           *)
     (*************************)
   
     Fixpoint rev (l:list A) : list A :=
       match l with
         | [] => []
         | x :: l' => rev l' ++ [x]
       end.
   
     Lemma rev_app_distr : forall x y:list A, rev (x ++ y) = rev y ++ rev x.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Remark rev_unit : forall (l:list A) (a:A), rev (l ++ [a]) = a :: rev l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma rev_involutive : forall l:list A, rev (rev l) = l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma rev_eq_app : forall l l1 l2, rev l = l1 ++ l2 -> l = rev l2 ++ rev l1.
     Proof. Show. Fail (abduce 3). Admitted.
   
     (** Compatibility with other operations *)
   
     Lemma in_rev : forall l x, In x l <-> In x (rev l).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma rev_length : forall l, length (rev l) = length l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma rev_nth : forall l d n,  n < length l ->
       nth n (rev l) d = nth (length l - S n) l d.
     Proof. Show. Fail (abduce 3). Admitted.
   
   
     (**  An alternative tail-recursive definition for reverse *)
   
     Fixpoint rev_append (l l': list A) : list A :=
       match l with
         | [] => l'
         | a::l => rev_append l (a::l')
       end.
   
     Definition rev' l : list A := rev_append l [].
   
     Lemma rev_append_rev : forall l l', rev_append l l' = rev l ++ l'.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma rev_alt : forall l, rev l = rev_append l [].
     Proof. Show. Fail (abduce 3). Admitted.
   
   
   (*********************************************)
   (** Reverse Induction Principle on Lists  *)
   (*********************************************)
   
     Section Reverse_Induction.
   
       Lemma rev_list_ind : forall P:list A-> Prop,
         P [] ->
         (forall (a:A) (l:list A), P (rev l) -> P (rev (a :: l))) ->
         forall l:list A, P (rev l).
       Proof. Show. Fail (abduce 3). Admitted.
   
       Theorem rev_ind : forall P:list A -> Prop,
         P [] ->
         (forall (x:A) (l:list A), P l -> P (l ++ [x])) -> forall l:list A, P l.
       Proof. Show. Fail (abduce 3). Admitted.
   
     End Reverse_Induction.
   
     (*************************)
     (** ** Concatenation     *)
     (*************************)
   
     Fixpoint concat (l : list (list A)) : list A :=
     match l with
     | nil => nil
     | cons x l => x ++ concat l
     end.
   
     Lemma concat_nil : concat nil = nil.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma concat_cons : forall x l, concat (cons x l) = x ++ concat l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma concat_app : forall l1 l2, concat (l1 ++ l2) = concat l1 ++ concat l2.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma in_concat : forall l y,
       In y (concat l) <-> exists x, In x l /\ In y x.
     Proof. Show. Fail (abduce 3). Admitted.
   
   
     (***********************************)
     (** ** Decidable equality on lists *)
     (***********************************)
   
     Hypothesis eq_dec : forall (x y : A), {x = y}+{x <> y}.
   
     Lemma list_eq_dec : forall l l':list A, {l = l'} + {l <> l'}.
     Proof. Show. Fail (abduce 3). Admitted.
   
   End ListOps.
   
   (***************************************************)
   (** * Applying functions to the elements of a list *)
   (***************************************************)
   
   (************)
   (** ** Map  *)
   (************)
   
   Section Map.
     Variables (A : Type) (B : Type).
     Variable f : A -> B.
   
     Fixpoint map (l:list A) : list B :=
       match l with
         | [] => []
         | a :: t => (f a) :: (map t)
       end.
   
     Lemma map_cons (x:A)(l:list A) : map (x::l) = (f x) :: (map l).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma in_map :
       forall (l:list A) (x:A), In x l -> In (f x) (map l).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma in_map_iff : forall l y, In y (map l) <-> exists x, f x = y /\ In x l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma map_length : forall l, length (map l) = length l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma map_nth : forall l d n,
       nth n (map l) (f d) = f (nth n l d).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma map_nth_error : forall n l d,
       nth_error l n = Some d -> nth_error (map l) n = Some (f d).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma map_app : forall l l',
       map (l++l') = (map l)++(map l').
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma map_last : forall l a,
       map (l ++ [a]) = (map l) ++ [f a].
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma map_rev : forall l, map (rev l) = rev (map l).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma map_eq_nil : forall l, map l = [] -> l = [].
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma map_eq_cons : forall l l' b,
       map l = b :: l' -> exists a tl, l = a :: tl /\ f a = b /\ map tl = l'.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma map_eq_app  : forall l l1 l2,
       map l = l1 ++ l2 -> exists l1' l2', l = l1' ++ l2' /\ map l1' = l1 /\ map l2' = l2.
     Proof. Show. Fail (abduce 3). Admitted.
   
     (** [map] and count of occurrences *)
   
     Hypothesis decA: forall x1 x2 : A, {x1 = x2} + {x1 <> x2}.
     Hypothesis decB: forall y1 y2 : B, {y1 = y2} + {y1 <> y2}.
     Hypothesis Hfinjective: forall x1 x2: A, (f x1) = (f x2) -> x1 = x2.
   
     Theorem count_occ_map x l:
       count_occ decA l x = count_occ decB (map l) (f x).
     Proof. Show. Fail (abduce 3). Admitted.
   
     (** [flat_map] *)
   
     Definition flat_map (f:A -> list B) :=
       fix flat_map (l:list A) : list B :=
       match l with
         | nil => nil
         | cons x t => (f x)++(flat_map t)
       end.
   
     Lemma flat_map_app : forall f l1 l2,
       flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma in_flat_map : forall (f:A->list B)(l:list A)(y:B),
       In y (flat_map f l) <-> exists x, In x l /\ In y (f x).
     Proof. Show. Fail (abduce 3). Admitted.
   
   End Map.
   
   Lemma flat_map_concat_map : forall A B (f : A -> list B) l,
     flat_map f l = concat (map f l).
   Proof. Show. Fail (abduce 3). Admitted.
   
   Lemma concat_map : forall A B (f : A -> B) l, map f (concat l) = concat (map (map f) l).
   Proof. Show. Fail (abduce 3). Admitted.
   
   Lemma remove_concat A (eq_dec : forall x y : A, {x = y}+{x <> y}) : forall l x,
     remove eq_dec x (concat l) = flat_map (remove eq_dec x) l.
   Proof. Show. Fail (abduce 3). Admitted.
   
   Lemma map_id : forall (A :Type) (l : list A),
     map (fun x => x) l = l.
   Proof. Show. Fail (abduce 3). Admitted.
   
   Lemma map_map : forall (A B C:Type)(f:A->B)(g:B->C) l,
     map g (map f l) = map (fun x => g (f x)) l.
   Proof. Show. Fail (abduce 3). Admitted.
   
   Lemma map_ext_in :
     forall (A B : Type)(f g:A->B) l, (forall a, In a l -> f a = g a) -> map f l = map g l.
   Proof. Show. Fail (abduce 3). Admitted.
   
   Lemma ext_in_map :
     forall (A B : Type)(f g:A->B) l, map f l = map g l -> forall a, In a l -> f a = g a.
   Proof. Show. Fail (abduce 3). Admitted.
   
   Arguments ext_in_map [A B f g l].
   
   Lemma map_ext_in_iff :
      forall (A B : Type)(f g:A->B) l, map f l = map g l <-> forall a, In a l -> f a = g a.
   Proof. Show. Fail (abduce 3). Admitted.
   
   Arguments map_ext_in_iff {A B f g l}.
   
   Lemma map_ext :
     forall (A B : Type)(f g:A->B), (forall a, f a = g a) -> forall l, map f l = map g l.
   Proof. Show. Fail (abduce 3). Admitted.
   
   Lemma flat_map_ext : forall (A B : Type)(f g : A -> list B),
     (forall a, f a = g a) -> forall l, flat_map f l = flat_map g l.
   Proof. Show. Fail (abduce 3). Admitted.
   
   Lemma nth_nth_nth_map A : forall (l : list A) n d ln dn, n < length ln \/ length l <= dn ->
     nth (nth n ln dn) l d = nth n (map (fun x => nth x l d) ln) d.
   Proof. Show. Fail (abduce 3). Admitted.
   
   
   (************************************)
   (** Left-to-right iterator on lists *)
   (************************************)
   
   Section Fold_Left_Recursor.
     Variables (A : Type) (B : Type).
     Variable f : A -> B -> A.
   
     Fixpoint fold_left (l:list B) (a0:A) : A :=
       match l with
         | nil => a0
         | cons b t => fold_left t (f a0 b)
       end.
   
     Lemma fold_left_app : forall (l l':list B)(i:A),
       fold_left (l++l') i = fold_left l' (fold_left l i).
     Proof. Show. Fail (abduce 3). Admitted.
   
   End Fold_Left_Recursor.
   
   Lemma fold_left_length :
     forall (A:Type)(l:list A), fold_left (fun x _ => S x) l 0 = length l.
   Proof. Show. Fail (abduce 3). Admitted.
   
   (************************************)
   (** Right-to-left iterator on lists *)
   (************************************)
   
   Section Fold_Right_Recursor.
     Variables (A : Type) (B : Type).
     Variable f : B -> A -> A.
     Variable a0 : A.
   
     Fixpoint fold_right (l:list B) : A :=
       match l with
         | nil => a0
         | cons b t => f b (fold_right t)
       end.
   
   End Fold_Right_Recursor.
   
     Lemma fold_right_app : forall (A B:Type)(f:A->B->B) l l' i,
       fold_right f i (l++l') = fold_right f (fold_right f i l') l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma fold_left_rev_right : forall (A B:Type)(f:A->B->B) l i,
       fold_right f i (rev l) = fold_left (fun x y => f y x) l i.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Theorem fold_symmetric :
       forall (A : Type) (f : A -> A -> A),
       (forall x y z : A, f x (f y z) = f (f x y) z) ->
       forall (a0 : A), (forall y : A, f a0 y = f y a0) ->
       forall (l : list A), fold_left f l a0 = fold_right f a0 l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     (** [(list_power x y)] is [y^x], or the set of sequences of elts of [y]
         indexed by elts of [x], sorted in lexicographic order. *)
   
     Fixpoint list_power (A B:Type)(l:list A) (l':list B) :
       list (list (A * B)) :=
       match l with
         | nil => cons nil nil
         | cons x t =>
     flat_map (fun f:list (A * B) => map (fun y:B => cons (x, y) f) l')
           (list_power t l')
       end.
   
   
     (*************************************)
     (** ** Boolean operations over lists *)
     (*************************************)
   
     Section Bool.
       Variable A : Type.
       Variable f : A -> bool.
   
     (** find whether a boolean function can be satisfied by an
          elements of the list. *)
   
       Fixpoint existsb (l:list A) : bool :=
         match l with
         | nil => false
         | a::l => f a || existsb l
         end.
   
       Lemma existsb_exists :
         forall l, existsb l = true <-> exists x, In x l /\ f x = true.
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma existsb_nth : forall l n d, n < length l ->
         existsb l = false -> f (nth n l d) = false.
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma existsb_app : forall l1 l2,
         existsb (l1++l2) = existsb l1 || existsb l2.
       Proof. Show. Fail (abduce 3). Admitted.
   
     (** find whether a boolean function is satisfied by
       all the elements of a list. *)
   
       Fixpoint forallb (l:list A) : bool :=
         match l with
         | nil => true
         | a::l => f a && forallb l
         end.
   
       Lemma forallb_forall :
         forall l, forallb l = true <-> (forall x, In x l -> f x = true).
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma forallb_app :
         forall l1 l2, forallb (l1++l2) = forallb l1 && forallb l2.
       Proof. Show. Fail (abduce 3). Admitted.
   
     (** [filter] *)
   
       Fixpoint filter (l:list A) : list A :=
         match l with
         | nil => nil
         | x :: l => if f x then x::(filter l) else filter l
         end.
   
       Lemma filter_In : forall x l, In x (filter l) <-> In x l /\ f x = true.
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma filter_app (l l':list A) :
         filter (l ++ l') = filter l ++ filter l'.
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma concat_filter_map : forall (l : list (list A)),
         concat (map filter l) = filter (concat l).
       Proof. Show. Fail (abduce 3). Admitted.
   
     (** [find] *)
   
       Fixpoint find (l:list A) : option A :=
         match l with
         | nil => None
         | x :: tl => if f x then Some x else find tl
         end.
   
       Lemma find_some l x : find l = Some x -> In x l /\ f x = true.
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma find_none l : find l = None -> forall x, In x l -> f x = false.
       Proof. Show. Fail (abduce 3). Admitted.
   
     (** [partition] *)
   
       Fixpoint partition (l:list A) : list A * list A :=
         match l with
         | nil => (nil, nil)
         | x :: tl => let (g,d) := partition tl in
                      if f x then (x::g,d) else (g,x::d)
         end.
   
     Theorem partition_cons1 a l l1 l2:
       partition l = (l1, l2) ->
       f a = true ->
       partition (a::l) = (a::l1, l2).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Theorem partition_cons2 a l l1 l2:
       partition l = (l1, l2) ->
       f a=false ->
       partition (a::l) = (l1, a::l2).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Theorem partition_length l l1 l2:
       partition l = (l1, l2) ->
       length l = length l1 + length l2.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Theorem partition_inv_nil (l : list A):
       partition l = ([], []) <-> l = [].
     Proof. Show. Fail (abduce 3). Admitted.
   
     Theorem elements_in_partition l l1 l2:
       partition l = (l1, l2) ->
       forall x:A, In x l <-> In x l1 \/ In x l2.
     Proof. Show. Fail (abduce 3). Admitted.
   
     End Bool.
   
   
     (*******************************)
     (** ** Further filtering facts *)
     (*******************************)
   
     Section Filtering.
       Variables (A : Type).
   
       Lemma filter_map : forall (f g : A -> bool) (l : list A),
         filter f l = filter g l <-> map f l = map g l.
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma filter_ext_in : forall (f g : A -> bool) (l : list A),
         (forall a, In a l -> f a = g a) -> filter f l = filter g l.
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma ext_in_filter : forall (f g : A -> bool) (l : list A),
         filter f l = filter g l -> (forall a, In a l -> f a = g a).
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma filter_ext_in_iff : forall (f g : A -> bool) (l : list A),
         filter f l = filter g l <-> (forall a, In a l -> f a = g a).
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma filter_ext : forall (f g : A -> bool),
         (forall a, f a = g a) -> forall l, filter f l = filter g l.
       Proof. Show. Fail (abduce 3). Admitted.
   
       (** Remove by filtering *)
   
       Hypothesis eq_dec : forall x y : A, {x = y}+{x <> y}.
   
       Definition remove' (x : A) : list A -> list A :=
         filter (fun y => if eq_dec x y then false else true).
   
       Lemma remove_alt (x : A) (l : list A) : remove' x l = remove eq_dec x l.
       Proof. Show. Fail (abduce 3). Admitted.
   
       (** Counting occurrences by filtering *)
   
       Definition count_occ' (l : list A) (x : A) : nat :=
         length (filter (fun y => if eq_dec y x then true else false) l).
   
       Lemma count_occ_alt (l : list A) (x : A) :
         count_occ' l x = count_occ eq_dec l x.
       Proof. Show. Fail (abduce 3). Admitted.
   
     End Filtering.
   
   
     (******************************************************)
     (** ** Operations on lists of pairs or lists of lists *)
     (******************************************************)
   
     Section ListPairs.
       Variables (A : Type) (B : Type).
   
     (** [split] derives two lists from a list of pairs *)
   
       Fixpoint split (l:list (A*B)) : list A * list B :=
         match l with
         | [] => ([], [])
         | (x,y) :: tl => let (left,right) := split tl in (x::left, y::right)
         end.
   
       Lemma in_split_l : forall (l:list (A*B))(p:A*B),
         In p l -> In (fst p) (fst (split l)).
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma in_split_r : forall (l:list (A*B))(p:A*B),
         In p l -> In (snd p) (snd (split l)).
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma split_nth : forall (l:list (A*B))(n:nat)(d:A*B),
         nth n l d = (nth n (fst (split l)) (fst d), nth n (snd (split l)) (snd d)).
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma split_length_l : forall (l:list (A*B)),
         length (fst (split l)) = length l.
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma split_length_r : forall (l:list (A*B)),
         length (snd (split l)) = length l.
       Proof. Show. Fail (abduce 3). Admitted.
   
     (** [combine] is the opposite of [split].
         Lists given to [combine] are meant to be of same length.
         If not, [combine] stops on the shorter list *)
   
       Fixpoint combine (l : list A) (l' : list B) : list (A*B) :=
         match l,l' with
         | x::tl, y::tl' => (x,y)::(combine tl tl')
         | _, _ => nil
         end.
   
       Lemma split_combine : forall (l: list (A*B)),
         let (l1,l2) := split l in combine l1 l2 = l.
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma combine_split : forall (l:list A)(l':list B), length l = length l' ->
         split (combine l l') = (l,l').
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma in_combine_l : forall (l:list A)(l':list B)(x:A)(y:B),
         In (x,y) (combine l l') -> In x l.
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma in_combine_r : forall (l:list A)(l':list B)(x:A)(y:B),
         In (x,y) (combine l l') -> In y l'.
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma combine_length : forall (l:list A)(l':list B),
         length (combine l l') = min (length l) (length l').
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma combine_nth : forall (l:list A)(l':list B)(n:nat)(x:A)(y:B),
         length l = length l' ->
         nth n (combine l l') (x,y) = (nth n l x, nth n l' y).
       Proof. Show. Fail (abduce 3). Admitted.
   
     (** [list_prod] has the same signature as [combine], but unlike
        [combine], it adds every possible pairs, not only those at the
        same position. *)
   
       Fixpoint list_prod (l:list A) (l':list B) :
         list (A * B) :=
         match l with
         | nil => nil
         | cons x t => (map (fun y:B => (x, y)) l')++(list_prod t l')
         end.
   
       Lemma in_prod_aux :
         forall (x:A) (y:B) (l:list B),
     In y l -> In (x, y) (map (fun y0:B => (x, y0)) l).
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma in_prod :
         forall (l:list A) (l':list B) (x:A) (y:B),
           In x l -> In y l' -> In (x, y) (list_prod l l').
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma in_prod_iff :
         forall (l:list A)(l':list B)(x:A)(y:B),
           In (x,y) (list_prod l l') <-> In x l /\ In y l'.
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma prod_length : forall (l:list A)(l':list B),
         length (list_prod l l') = (length l) * (length l').
       Proof. Show. Fail (abduce 3). Admitted.
   
     End ListPairs.
   
   
   
   
   (*****************************************)
   (** * Miscellaneous operations on lists  *)
   (*****************************************)
   
   
   
   (******************************)
   (** ** Length order of lists  *)
   (******************************)
   
   Section length_order.
     Variable A : Type.
   
     Definition lel (l m:list A) := length l <= length m.
   
     Variables a b : A.
     Variables l m n : list A.
   
     Lemma lel_refl : lel l l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma lel_trans : lel l m -> lel m n -> lel l n.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma lel_cons_cons : lel l m -> lel (a :: l) (b :: m).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma lel_cons : lel l m -> lel l (b :: m).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma lel_tail : lel (a :: l) (b :: m) -> lel l m.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma lel_nil : forall l':list A, lel l' nil -> nil = l'.
     Proof. Show. Fail (abduce 3). Admitted.
   End length_order.
   
   #[global]
   Hint Resolve lel_refl lel_cons_cons lel_cons lel_nil lel_nil nil_cons:
     datatypes.
   
   
   (******************************)
   (** ** Set inclusion on list  *)
   (******************************)
   
   Section SetIncl.
   
     Variable A : Type.
   
     Definition incl (l m:list A) := forall a:A, In a l -> In a m.
     #[local]
     Hint Unfold incl : core.
   
     Lemma incl_nil_l : forall l, incl nil l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma incl_l_nil : forall l, incl l nil -> l = nil.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma incl_refl : forall l:list A, incl l l.
     Proof. Show. Fail (abduce 3). Admitted.
     #[local]
     Hint Resolve incl_refl : core.
   
     Lemma incl_tl : forall (a:A) (l m:list A), incl l m -> incl l (a :: m).
     Proof. Show. Fail (abduce 3). Admitted.
     #[local]
     Hint Immediate incl_tl : core.
   
     Lemma incl_tran : forall l m n:list A, incl l m -> incl m n -> incl l n.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma incl_appl : forall l m n:list A, incl l n -> incl l (n ++ m).
     Proof. Show. Fail (abduce 3). Admitted.
     #[local]
     Hint Immediate incl_appl : core.
   
     Lemma incl_appr : forall l m n:list A, incl l n -> incl l (m ++ n).
     Proof. Show. Fail (abduce 3). Admitted.
     #[local]
     Hint Immediate incl_appr : core.
   
     Lemma incl_cons :
       forall (a:A) (l m:list A), In a m -> incl l m -> incl (a :: l) m.
     Proof. Show. Fail (abduce 3). Admitted.
     #[local]
     Hint Resolve incl_cons : core.
   
     Lemma incl_cons_inv : forall (a:A) (l m:list A),
       incl (a :: l) m -> In a m /\ incl l m.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma incl_app : forall l m n:list A, incl l n -> incl m n -> incl (l ++ m) n.
     Proof. Show. Fail (abduce 3). Admitted.
     #[local]
     Hint Resolve incl_app : core.
   
     Lemma incl_app_app : forall l1 l2 m1 m2:list A,
       incl l1 m1 -> incl l2 m2 -> incl (l1 ++ l2) (m1 ++ m2).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma incl_app_inv : forall l1 l2 m : list A,
       incl (l1 ++ l2) m -> incl l1 m /\ incl l2 m.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma incl_filter f l : incl (filter f l) l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma remove_incl (eq_dec : forall x y : A, {x = y} + {x <> y}) : forall l1 l2 x,
       incl l1 l2 -> incl (remove eq_dec x l1) (remove eq_dec x l2).
     Proof. Show. Fail (abduce 3). Admitted.
   
   End SetIncl.
   
   Lemma incl_map A B (f : A -> B) l1 l2 : incl l1 l2 -> incl (map f l1) (map f l2).
   Proof. Show. Fail (abduce 3). Admitted.
   
   #[global]
   Hint Resolve incl_refl incl_tl incl_tran incl_appl incl_appr incl_cons
     incl_app incl_map: datatypes.
   
   
   (**************************************)
   (** * Cutting a list at some position *)
   (**************************************)
   
   Section Cutting.
   
     Variable A : Type.
   
     Fixpoint firstn (n:nat)(l:list A) : list A :=
       match n with
         | 0 => nil
         | S n => match l with
        | nil => nil
        | a::l => a::(firstn n l)
            end
       end.
   
     Lemma firstn_nil n: firstn n [] = [].
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma firstn_cons n a l: firstn (S n) (a::l) = a :: (firstn n l).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma firstn_all l: firstn (length l) l = l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma firstn_all2 n: forall (l:list A), (length l) <= n -> firstn n l = l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma firstn_O l: firstn 0 l = [].
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma firstn_le_length n: forall l:list A, length (firstn n l) <= n.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma firstn_length_le: forall l:list A, forall n:nat,
       n <= length l -> length (firstn n l) = n.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma firstn_app n:
       forall l1 l2,
       firstn n (l1 ++ l2) = (firstn n l1) ++ (firstn (n - length l1) l2).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma firstn_app_2 n:
       forall l1 l2,
       firstn ((length l1) + n) (l1 ++ l2) = l1 ++ firstn n l2.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma firstn_firstn:
       forall l:list A,
       forall i j : nat,
       firstn i (firstn j l) = firstn (min i j) l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Fixpoint skipn (n:nat)(l:list A) : list A :=
       match n with
         | 0 => l
         | S n => match l with
        | nil => nil
        | a::l => skipn n l
            end
       end.
   
     Lemma firstn_skipn_comm : forall m n l,
     firstn m (skipn n l) = skipn n (firstn (n + m) l).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma skipn_firstn_comm : forall m n l,
     skipn m (firstn n l) = firstn (n - m) (skipn m l).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma skipn_O : forall l, skipn 0 l = l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma skipn_nil : forall n, skipn n ([] : list A) = [].
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma skipn_cons n a l: skipn (S n) (a::l) = skipn n l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma skipn_all : forall l, skipn (length l) l = nil.
     Proof. Show. Fail (abduce 3). Admitted.
   
   #[deprecated(since="8.12",note="Use skipn_all instead.")] Notation skipn_none := skipn_all.
   
     Lemma skipn_all2 n: forall l, length l <= n -> skipn n l = [].
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma firstn_skipn : forall n l, firstn n l ++ skipn n l = l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma firstn_length : forall n l, length (firstn n l) = min n (length l).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma skipn_length n :
       forall l, length (skipn n l) = length l - n.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma skipn_app n : forall l1 l2,
       skipn n (l1 ++ l2) = (skipn n l1) ++ (skipn (n - length l1) l2).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma firstn_skipn_rev: forall x l,
         firstn x l = rev (skipn (length l - x) (rev l)).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma firstn_rev: forall x l,
       firstn x (rev l) = rev (skipn (length l - x) l).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma skipn_rev: forall x l,
         skipn x (rev l) = rev (firstn (length l - x) l).
     Proof. Show. Fail (abduce 3). Admitted.
   
      Lemma removelast_firstn : forall n l, n < length l ->
        removelast (firstn (S n) l) = firstn n l.
      Proof. Show. Fail (abduce 3). Admitted.
   
      Lemma removelast_firstn_len : forall l,
        removelast l = firstn (pred (length l)) l.
      Proof. Show. Fail (abduce 3). Admitted.
   
      Lemma firstn_removelast : forall n l, n < length l ->
        firstn n (removelast l) = firstn n l.
      Proof. Show. Fail (abduce 3). Admitted.
   
   End Cutting.
   
   (**************************************************************)
   (** ** Combining pairs of lists of possibly-different lengths *)
   (**************************************************************)
   
   Section Combining.
       Variables (A B : Type).
   
       Lemma combine_nil : forall (l : list A),
         combine l (@nil B) = @nil (A*B).
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma combine_firstn_l : forall (l : list A) (l' : list B),
         combine l l' = combine l (firstn (length l) l').
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma combine_firstn_r : forall (l : list A) (l' : list B),
         combine l l' = combine (firstn (length l') l) l'.
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma combine_firstn : forall (l : list A) (l' : list B) (n : nat),
         firstn n (combine l l') = combine (firstn n l) (firstn n l').
       Proof. Show. Fail (abduce 3). Admitted.
   
   End Combining.
   
   (**********************************************************************)
   (** ** Predicate for List addition/removal (no need for decidability) *)
   (**********************************************************************)
   
   Section Add.
   
     Variable A : Type.
   
     (* [Add a l l'] means that [l'] is exactly [l], with [a] added
        once somewhere *)
     Inductive Add (a:A) : list A -> list A -> Prop :=
       | Add_head l : Add a l (a::l)
       | Add_cons x l l' : Add a l l' -> Add a (x::l) (x::l').
   
     Lemma Add_app a l1 l2 : Add a (l1++l2) (l1++a::l2).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma Add_split a l l' :
       Add a l l' -> exists l1 l2, l = l1++l2 /\ l' = l1++a::l2.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma Add_in a l l' : Add a l l' ->
      forall x, In x l' <-> In x (a::l).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma Add_length a l l' : Add a l l' -> length l' = S (length l).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma Add_inv a l : In a l -> exists l', Add a l' l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma incl_Add_inv a l u v :
       ~In a l -> incl (a::l) v -> Add a u v -> incl l u.
     Proof. Show. Fail (abduce 3). Admitted.
   
   End Add.
   
   (********************************)
   (** ** Lists without redundancy *)
   (********************************)
   
   Section ReDun.
   
     Variable A : Type.
   
     Inductive NoDup : list A -> Prop :=
       | NoDup_nil : NoDup nil
       | NoDup_cons : forall x l, ~ In x l -> NoDup l -> NoDup (x::l).
   
     Lemma NoDup_Add a l l' : Add a l l' -> (NoDup l' <-> NoDup l /\ ~In a l).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma NoDup_remove l l' a :
       NoDup (l++a::l') -> NoDup (l++l') /\ ~In a (l++l').
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma NoDup_remove_1 l l' a : NoDup (l++a::l') -> NoDup (l++l').
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma NoDup_remove_2 l l' a : NoDup (l++a::l') -> ~In a (l++l').
     Proof. Show. Fail (abduce 3). Admitted.
   
     Theorem NoDup_cons_iff a l:
       NoDup (a::l) <-> ~ In a l /\ NoDup l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma NoDup_rev l : NoDup l -> NoDup (rev l).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma NoDup_filter f l : NoDup l -> NoDup (filter f l).
     Proof. Show. Fail (abduce 3). Admitted.
   
     (** Effective computation of a list without duplicates *)
   
     Hypothesis decA: forall x y : A, {x = y} + {x <> y}.
   
     Fixpoint nodup (l : list A) : list A :=
       match l with
         | [] => []
         | x::xs => if in_dec decA x xs then nodup xs else x::(nodup xs)
       end.
   
     Lemma nodup_fixed_point (l : list A) :
       NoDup l -> nodup l = l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma nodup_In l x : In x (nodup l) <-> In x l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma nodup_incl l1 l2 : incl l1 (nodup l2) <-> incl l1 l2.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma NoDup_nodup l: NoDup (nodup l).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma nodup_inv k l a : nodup k = a :: l -> ~ In a l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Theorem NoDup_count_occ l:
       NoDup l <-> (forall x:A, count_occ decA l x <= 1).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Theorem NoDup_count_occ' l:
       NoDup l <-> (forall x:A, In x l -> count_occ decA l x = 1).
     Proof. Show. Fail (abduce 3). Admitted.
   
     (** Alternative characterisations of being without duplicates,
         thanks to [nth_error] and [nth] *)
   
     Lemma NoDup_nth_error l :
       NoDup l <->
       (forall i j, i<length l -> nth_error l i = nth_error l j -> i = j).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma NoDup_nth l d :
       NoDup l <->
       (forall i j, i<length l -> j<length l ->
          nth i l d = nth j l d -> i = j).
     Proof. Show. Fail (abduce 3). Admitted.
   
     (** Having [NoDup] hypotheses bring more precise facts about [incl]. *)
   
     Lemma NoDup_incl_length l l' :
       NoDup l -> incl l l' -> length l <= length l'.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma NoDup_length_incl l l' :
       NoDup l -> length l' <= length l -> incl l l' -> incl l' l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma NoDup_incl_NoDup (l l' : list A) : NoDup l ->
       length l' <= length l -> incl l l' -> NoDup l'.
     Proof. Show. Fail (abduce 3). Admitted.
   
   End ReDun.
   
   (** NoDup and map *)
   
   (** NB: the reciprocal result holds only for injective functions,
       see FinFun.v *)
   
   Lemma NoDup_map_inv A B (f:A->B) l : NoDup (map f l) -> NoDup l.
   Proof. Show. Fail (abduce 3). Admitted.
   
   (***********************************)
   (** ** Sequence of natural numbers *)
   (***********************************)
   
   Section NatSeq.
   
     (** [seq] computes the sequence of [len] contiguous integers
         that starts at [start]. For instance, [seq 2 3] is [2::3::4::nil]. *)
   
     Fixpoint seq (start len:nat) : list nat :=
       match len with
         | 0 => nil
         | S len => start :: seq (S start) len
       end.
   
     Lemma cons_seq : forall len start, start :: seq (S start) len = seq start (S len).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma seq_length : forall len start, length (seq start len) = len.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma seq_nth : forall len start n d,
       n < len -> nth n (seq start len) d = start+n.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma seq_shift : forall len start,
       map S (seq start len) = seq (S start) len.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma in_seq len start n :
       In n (seq start len) <-> start <= n < start+len.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma seq_NoDup len start : NoDup (seq start len).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma seq_app : forall len1 len2 start,
       seq start (len1 + len2) = seq start len1 ++ seq (start + len1) len2.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma seq_S : forall len start, seq start (S len) = seq start len ++ [start + len].
     Proof. Show. Fail (abduce 3). Admitted.
   
   End NatSeq.
   
   Section Exists_Forall.
   
     (** * Existential and universal predicates over lists *)
   
     Variable A:Type.
   
     Section One_predicate.
   
       Variable P:A->Prop.
   
       Inductive Exists : list A -> Prop :=
         | Exists_cons_hd : forall x l, P x -> Exists (x::l)
         | Exists_cons_tl : forall x l, Exists l -> Exists (x::l).
   
       #[local]
       Hint Constructors Exists : core.
   
       Lemma Exists_exists (l:list A) :
         Exists l <-> (exists x, In x l /\ P x).
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma Exists_nth l :
         Exists l <-> exists i d, i < length l /\ P (nth i l d).
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma Exists_nil : Exists nil <-> False.
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma Exists_cons x l:
         Exists (x::l) <-> P x \/ Exists l.
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma Exists_app l1 l2 :
         Exists (l1 ++ l2) <-> Exists l1 \/ Exists l2.
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma Exists_rev l : Exists l -> Exists (rev l).
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma Exists_dec l:
         (forall x:A, {P x} + { ~ P x }) ->
         {Exists l} + {~ Exists l}.
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma Exists_fold_right l :
         Exists l <-> fold_right (fun x => or (P x)) False l.
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma incl_Exists l1 l2 : incl l1 l2 -> Exists l1 -> Exists l2.
       Proof. Show. Fail (abduce 3). Admitted.
   
       Inductive Forall : list A -> Prop :=
         | Forall_nil : Forall nil
         | Forall_cons : forall x l, P x -> Forall l -> Forall (x::l).
   
       #[local]
       Hint Constructors Forall : core.
   
       Lemma Forall_forall (l:list A):
         Forall l <-> (forall x, In x l -> P x).
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma Forall_nth l :
         Forall l <-> forall i d, i < length l -> P (nth i l d).
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma Forall_inv : forall (a:A) l, Forall (a :: l) -> P a.
       Proof. Show. Fail (abduce 3). Admitted.
   
       Theorem Forall_inv_tail : forall (a:A) l, Forall (a :: l) -> Forall l.
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma Forall_app l1 l2 :
         Forall (l1 ++ l2) <-> Forall l1 /\ Forall l2.
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma Forall_elt a l1 l2 : Forall (l1 ++ a :: l2) -> P a.
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma Forall_rev l : Forall l -> Forall (rev l).
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma Forall_rect : forall (Q : list A -> Type),
         Q [] -> (forall b l, P b -> Q (b :: l)) -> forall l, Forall l -> Q l.
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma Forall_dec :
         (forall x:A, {P x} + { ~ P x }) ->
         forall l:list A, {Forall l} + {~ Forall l}.
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma Forall_fold_right l :
         Forall l <-> fold_right (fun x => and (P x)) True l.
       Proof. Show. Fail (abduce 3). Admitted.
   
       Lemma incl_Forall l1 l2 : incl l2 l1 -> Forall l1 -> Forall l2.
       Proof. Show. Fail (abduce 3). Admitted.
   
     End One_predicate.
   
     Lemma map_ext_Forall B : forall (f g : A -> B) l,
       Forall (fun x => f x = g x) l -> map f l = map g l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Theorem Exists_impl : forall (P Q : A -> Prop), (forall a : A, P a -> Q a) ->
       forall l, Exists P l -> Exists Q l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma Exists_or : forall (P Q : A -> Prop) l,
       Exists P l \/ Exists Q l -> Exists (fun x => P x \/ Q x) l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma Exists_or_inv : forall (P Q : A -> Prop) l,
       Exists (fun x => P x \/ Q x) l -> Exists P l \/ Exists Q l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma Forall_impl : forall (P Q : A -> Prop), (forall a, P a -> Q a) ->
       forall l, Forall P l -> Forall Q l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma Forall_and : forall (P Q : A -> Prop) l,
       Forall P l -> Forall Q l -> Forall (fun x => P x /\ Q x) l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma Forall_and_inv : forall (P Q : A -> Prop) l,
       Forall (fun x => P x /\ Q x) l -> Forall P l /\ Forall Q l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma Forall_Exists_neg (P:A->Prop)(l:list A) :
       Forall (fun x => ~ P x) l <-> ~(Exists P l).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma Exists_Forall_neg (P:A->Prop)(l:list A) :
       (forall x, P x \/ ~P x) ->
       Exists (fun x => ~ P x) l <-> ~(Forall P l).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma neg_Forall_Exists_neg (P:A->Prop) (l:list A) :
       (forall x:A, {P x} + { ~ P x }) ->
       ~ Forall P l ->
       Exists (fun x => ~ P x) l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma Forall_Exists_dec (P:A->Prop) :
       (forall x:A, {P x} + { ~ P x }) ->
       forall l:list A,
       {Forall P l} + {Exists (fun x => ~ P x) l}.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma incl_Forall_in_iff l l' :
       incl l l' <-> Forall (fun x => In x l') l.
     Proof. Show. Fail (abduce 3). Admitted.
   
   End Exists_Forall.
   
   #[global]
   Hint Constructors Exists : core.
   #[global]
   Hint Constructors Forall : core.
   
   Lemma exists_Forall A B : forall (P : A -> B -> Prop) l,
     (exists k, Forall (P k) l) -> Forall (fun x => exists k, P k x) l.
   Proof. Show. Fail (abduce 3). Admitted.
   
   Lemma Forall_image A B : forall (f : A -> B) l,
     Forall (fun y => exists x, y = f x) l <-> exists l', l = map f l'.
   Proof. Show. Fail (abduce 3). Admitted.
   
   Lemma concat_nil_Forall A : forall (l : list (list A)),
     concat l = nil <-> Forall (fun x => x = nil) l.
   Proof. Show. Fail (abduce 3). Admitted.
   
   Lemma in_flat_map_Exists A B : forall (f : A -> list B) x l,
     In x (flat_map f l) <-> Exists (fun y => In x (f y)) l.
   Proof. Show. Fail (abduce 3). Admitted.
   
   Lemma notin_flat_map_Forall A B : forall (f : A -> list B) x l,
     ~ In x (flat_map f l) <-> Forall (fun y => ~ In x (f y)) l.
   Proof. Show. Fail (abduce 3). Admitted.
   
   
   Section Forall2.
   
     (** [Forall2]: stating that elements of two lists are pairwise related. *)
   
     Variables A B : Type.
     Variable R : A -> B -> Prop.
   
     Inductive Forall2 : list A -> list B -> Prop :=
       | Forall2_nil : Forall2 [] []
       | Forall2_cons : forall x y l l',
         R x y -> Forall2 l l' -> Forall2 (x::l) (y::l').
   
     #[local]
     Hint Constructors Forall2 : core.
   
     Theorem Forall2_refl : Forall2 [] [].
     Proof. Show. Fail (abduce 3). Admitted.
   
     Theorem Forall2_app_inv_l : forall l1 l2 l',
       Forall2 (l1 ++ l2) l' ->
       exists l1' l2', Forall2 l1 l1' /\ Forall2 l2 l2' /\ l' = l1' ++ l2'.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Theorem Forall2_app_inv_r : forall l1' l2' l,
       Forall2 l (l1' ++ l2') ->
       exists l1 l2, Forall2 l1 l1' /\ Forall2 l2 l2' /\ l = l1 ++ l2.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Theorem Forall2_app : forall l1 l2 l1' l2',
       Forall2 l1 l1' -> Forall2 l2 l2' -> Forall2 (l1 ++ l2) (l1' ++ l2').
     Proof. Show. Fail (abduce 3). Admitted.
   End Forall2.
   
   #[global]
   Hint Constructors Forall2 : core.
   
   Section ForallPairs.
   
     (** [ForallPairs] : specifies that a certain relation should
       always hold when inspecting all possible pairs of elements of a list. *)
   
     Variable A : Type.
     Variable R : A -> A -> Prop.
   
     Definition ForallPairs l :=
       forall a b, In a l -> In b l -> R a b.
   
     (** [ForallOrdPairs] : we still check a relation over all pairs
        of elements of a list, but now the order of elements matters. *)
   
     Inductive ForallOrdPairs : list A -> Prop :=
       | FOP_nil : ForallOrdPairs nil
       | FOP_cons : forall a l,
         Forall (R a) l -> ForallOrdPairs l -> ForallOrdPairs (a::l).
   
     #[local]
     Hint Constructors ForallOrdPairs : core.
   
     Lemma ForallOrdPairs_In : forall l,
       ForallOrdPairs l ->
       forall x y, In x l -> In y l -> x=y \/ R x y \/ R y x.
     Proof. Show. Fail (abduce 3). Admitted.
   
     (** [ForallPairs] implies [ForallOrdPairs]. The reverse implication is true
       only when [R] is symmetric and reflexive. *)
   
     Lemma ForallPairs_ForallOrdPairs l: ForallPairs l -> ForallOrdPairs l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma ForallOrdPairs_ForallPairs :
       (forall x, R x x) ->
       (forall x y, R x y -> R y x) ->
       forall l, ForallOrdPairs l -> ForallPairs l.
     Proof. Show. Fail (abduce 3). Admitted.
   End ForallPairs.
   
   Section Repeat.
   
     Variable A : Type.
     Fixpoint repeat (x : A) (n: nat ) :=
       match n with
         | O => []
         | S k => x::(repeat x k)
       end.
   
     Theorem repeat_length x n:
       length (repeat x n) = n.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Theorem repeat_spec n x y:
       In y (repeat x n) -> y=x.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma repeat_cons n a :
       a :: repeat a n = repeat a n ++ (a :: nil).
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma repeat_app x n m :
       repeat x (n + m) = repeat x n ++ repeat x m.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma repeat_eq_app x n l1 l2 :
       repeat x n = l1 ++ l2 -> repeat x (length l1) = l1 /\ repeat x (length l2) = l2.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma repeat_eq_cons x y n l :
       repeat x n = y :: l -> x = y /\ repeat x (pred n) = l.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma repeat_eq_elt x y n l1 l2 :
       repeat x n = l1 ++ y :: l2 -> x = y /\ repeat x (length l1) = l1 /\ repeat x (length l2) = l2.
     Proof. Show. Fail (abduce 3). Admitted.
   
     Lemma Forall_eq_repeat x l :
       Forall (eq x) l -> l = repeat x (length l).
     Proof. Show. Fail (abduce 3). Admitted.
   
   End Repeat.
   
   Lemma repeat_to_concat A n (a:A) :
     repeat a n = concat (repeat [a] n).
   Proof. Show. Fail (abduce 3). Admitted.
   
   
   (** Sum of elements of a list of [nat]: [list_sum] *)
   
   Definition list_sum l := fold_right plus 0 l.
   
   Lemma list_sum_app : forall l1 l2,
      list_sum (l1 ++ l2) = list_sum l1 + list_sum l2.
   Proof. Show. Fail (abduce 3). Admitted.
   
   (** Max of elements of a list of [nat]: [list_max] *)
   
   Definition list_max l := fold_right max 0 l.
   
   Lemma list_max_app : forall l1 l2,
      list_max (l1 ++ l2) = max (list_max l1) (list_max l2).
   Proof. Show. Fail (abduce 3). Admitted.
   
   Lemma list_max_le : forall l n,
     list_max l <= n <-> Forall (fun k => k <= n) l.
   Proof. Show. Fail (abduce 3). Admitted.
   
   Lemma list_max_lt : forall l n, l <> nil ->
     list_max l < n <-> Forall (fun k => k < n) l.
   Proof. Show. Fail (abduce 3). Admitted.
   
   