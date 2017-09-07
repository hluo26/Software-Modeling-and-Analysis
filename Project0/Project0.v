Module Project0.

Require Import Omega.

Inductive myBool : Type :=
| ttrue : myBool
| ffalse : myBool.

Definition myOr(x y:myBool):myBool :=
  match x with
  | ttrue => ttrue
  | ffalse => y
  end.

(** Replace [Admitted] with definitions for the following functions *)

Definition myAnd(x y:myBool):myBool:=
match x with
|ttrue => y
|ffalse => ffalse
end.


Definition myNot(x:myBool):myBool:=
match x with
|ttrue => ffalse
|fflase => ttrue
end.


Definition myImplies(x y:myBool):myBool:=
match x with
|ffalse => ttrue
|ttrue => y
end.

  
(** Replace [Admitted] with proofs of the following examples and theorems. *)

Example e1: (myAnd ttrue ttrue) = ttrue.
Proof. simpl. reflexivity. Qed.

Example e2: (myAnd ttrue ffalse) = ffalse.
Proof. simpl. reflexivity. Qed.

Example e3: (myOr ttrue ttrue) = ttrue.
Proof. simpl. reflexivity. Qed.

Example e4: (myOr ttrue ffalse) = ttrue.
Proof. simpl. reflexivity. Qed.

Theorem symmetric_myOr: forall x y, myOr x y = myOr y x.
intros x y. destruct x.
destruct y.
reflexivity.
reflexivity.
destruct y.
reflexivity.
reflexivity.
Qed.

Theorem symmetric_myAnd : forall x y, myAnd x y = myAnd y x.
intros x y. destruct x.
destruct y.
reflexivity.
reflexivity.
destruct y.
reflexivity.
reflexivity.
Qed.

Theorem left_identity_or : forall x, myOr ffalse x = x.
intros x. destruct x.
reflexivity.
reflexivity.
Qed.

Theorem left_idnetity_and : forall x, myAnd ttrue x = x.
intros x. destruct x.
reflexivity.
reflexivity.
Qed.
  
Theorem not_not: forall x, myNot (myNot x) = x.
intros x. destruct x.
reflexivity.
reflexivity.
Qed.
  
Theorem demorgan: forall x y, myNot (myAnd x y) = myOr (myNot x) (myNot y).
intros x y. destruct x.
destruct y.
reflexivity.
reflexivity.
destruct y.
reflexivity.
reflexivity.
Qed.

Theorem contrapostive: forall x y, 
  (myImplies x y) = (myImplies (myNot y) (myNot x)).
intros x y. destruct x.
destruct y.
reflexivity.
reflexivity.
destruct y.
reflexivity.
reflexivity.
Qed.

Theorem and_assoc: forall x y z, myAnd x (myAnd y z) = (myAnd (myAnd x y) z).
intros x y z. destruct x.
destruct y.
destruct z.
reflexivity.
reflexivity.
destruct z.
reflexivity.
reflexivity.
destruct y.
destruct z.
reflexivity.
reflexivity.
destruct z.
reflexivity.
reflexivity.
Qed.


Theorem and_distr: forall x y z, myAnd x (myOr y z) = (myOr (myAnd x y) (myAnd x z)).
intros x y z. destruct x.
destruct y.
destruct z.
reflexivity.
reflexivity.
destruct z.
reflexivity.
reflexivity.
destruct y.
destruct z.
reflexivity.
reflexivity.
destruct z.
reflexivity.
reflexivity.
Qed.

End Project0.