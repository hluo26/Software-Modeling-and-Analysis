(*Add LoadPath "/Users/hluo/Dropbox/EECS755/lf" as <>.
Print LoadPath.*)

Require Import Omega.
Module Lists.
Import Poly.

  Inductive boollist : Type :=
  | bool_nil : boollist
  | bool_cons : bool -> boollist -> boollist.

  Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

  Inductive prod (X Y : Type) : Type :=
  | pair : X -> Y -> prod X Y.
Arguments pair {X} {Y} _ _.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Arguments nil {X}.
Arguments cons {X} _ _.
  Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

  Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Theorem beq_nat_0_l : forall n,
   beq_nat 0 n = true -> n = 0.
Proof.
  intros n.
  induction n as[|n'].
  intros H.
  reflexivity.
  simpl. intros H. inversion H.
Qed.

Theorem rev_involutive : 
  forall (X : Type), forall (l : list X),
      rev (rev l) = l.
  intros.
  induction l as [|n l'].
  reflexivity.
  simpl. 

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros l l' H.
  rewrite ->H. symmetry.
  
Example inversion_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  