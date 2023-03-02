Require Import SMTCoq.SMTCoq.
Require Import Bool.

Require Import ZArith.

Local Open Scope Z_scope.

Section F.
  Variable f : Z -> Z -> Z.
  (* Properties *)
  Parameter i : Z -> Z.
  Parameter inv : forall (x : Z), f x (i x) = 0.
  Parameter ident : forall (x : Z), f x 0 = x.

  Goal forall (x y z: Z),
    x = y + 1 -> f y z = f (x - 1) z.
  Proof.
    intros. rewrite H. 
    assert (y + 1 - 1 = y).
    { apply Z.add_simpl_r. }
    rewrite H0. reflexivity.
  Qed.

  Goal forall (x y z: Z),
    x = y + 1 -> f y z = f (x - 1) z.
  Proof.
    smt.
  Qed.
  
  Parameter comm : forall (x y : Z), f x y = f y x.
  Goal forall (x y : Z), (f x y) >= 0 -> (f y x) >= 0.
  Proof. smt comm. Qed.

End F.