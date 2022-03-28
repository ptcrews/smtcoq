Add Rec LoadPath "/home/arjun/Desktop/smtcoq/abduction-arjunvish-smtcoq/smtcoq/src" as SMTCoq.

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
    smt.
  Qed.
  
  Goal forall (x y : Z), (f x y) >= 0 -> (f y x) >= 0.
  Proof. cvc5_abduct. Qed.
End F.