Require Import Omega.

Module NatList.

  Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

  Notation "x :: l" := (cons x l) (at level 60, right associativity).
  Notation "[ ]" := nil.
  Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

  Fixpoint repeat (n count : nat) : natlist :=
    match count with
    |O => nil
    |S count' => n :: (repeat n count')
    end.

  Fixpoint app(l1 l2 : natlist): natlist :=
  match l1 with
  |nil => l2
  |h :: l1' => h::(app l1' l2)
  end.

  Fixpoint length(l : natlist) : nat :=
  match l with
  |nil => O
  |h :: l' => 1 + (length l')
  end.

  Fixpoint snoc(l : natlist)(s : nat) : natlist :=
  match l with
  |nil => s::[]
  |h :: l' => h::(snoc l' s)
  end.

  Fixpoint rev(l: natlist) : natlist :=
  match l with
  |nil => []
  |h :: l' => snoc (rev l') h
  end.
  
  Notation "x ++ y" := (app x y) 
                         (right associativity, at level 60).


  Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
  Proof.
  induction l.
  simpl. reflexivity.
  simpl. rewrite ->IHl. reflexivity.
  Qed.

  Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
  Proof.
  intros.
  induction l as [|n l'].
  reflexivity.

  

  Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4 )) = ((l1 ++ l2 ) ++ l3 ) ++ l4.
  Proof.
  Admitted.

  Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2 ) = (nonzeros l1 ) ++ (nonzeros l2 ).
  Proof.
  Admitted.

  Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  admit.
  
  
  

End NatList.