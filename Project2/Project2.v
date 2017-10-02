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

  Theorem snoc_cons: forall l n, rev(snoc l n) = n :: (rev l).
  Proof.
    intros. induction l.
    reflexivity.
    simpl. rewrite IHl. reflexivity.
  Qed.

  Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
  Proof.
  intros.
  induction l as [|n l'].
  reflexivity.
  simpl. rewrite -> snoc_cons.
  rewrite ->IHl'. reflexivity.
  Qed.

  Theorem app_assoc : forall l1 l2 l3 : natlist, 
      (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof.
    intros l1 l2 l3. induction l1 as [| n l1'].
    (*  Case "l1 = nil". *)
    simpl. reflexivity.
    (*  Case "l1 = cons n l1'". *)
    simpl. rewrite IHl1'. reflexivity. Qed.

  Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4 )) = ((l1 ++ l2 ) ++ l3 ) ++ l4.
  Proof.
  intros l1 l2 l3 l4.
  rewrite ->app_assoc.
  rewrite ->app_assoc.
  reflexivity.
  Qed.

  Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  |nil => nil
  |h::l' => if beq_nat h 0 then nonzeros l' else h::nonzeros l'
  end.

  Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2 ) = (nonzeros l1 ) ++ (nonzeros l2 ).
  Proof.
  intros l1 l2.
  induction l1.
  simpl. reflexivity.
  destruct n.
  simpl. rewrite -> IHl1. reflexivity.
  simpl. rewrite -> IHl1. reflexivity.
  Qed.

  Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1 with
  |nil => match l2 with
          | nil => true
          | h2::l2' => false
          end
  |h1::l1' => match l2 with
              | nil => false
              | h2::l2' => if beq_nat h1 h2 then beq_natlist l1' l2' else false
              end
  end.

  Example test_beq_natlist1 :
  (beq_natlist nil nil = true).
  Proof.
  simpl. reflexivity.
  Qed.

  Example test_beq_natlist2 :
  beq_natlist [1;2;3] [1;2;3] = true.
  Proof.
  simpl. reflexivity.
  Qed.

  Example test_beq_natlist3 :
  beq_natlist [1;2;3] [1;2;4] = false.
  Proof.
  simpl. reflexivity.
  Qed.

  Lemma beq_nat_refl : forall n, true = beq_nat n n.
  Proof.
  intros n.
  induction n.
  simpl. reflexivity.
  simpl. apply IHn.
  Qed.

  Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
  Proof.
  intros l.
  induction l as [|n l'].
  simpl. reflexivity.
  rewrite -> IHl'. 
  simpl. rewrite <-beq_nat_refl. reflexivity.
  Qed.

  Theorem ble_n_Sn : forall n,
  leb n (S n) = true.
  Proof.
  intros n. induction n.
  -
  simpl. reflexivity.
  -
  simpl. rewrite IHn. reflexivity. Qed.

  Definition bag := natlist.

  Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  |nil => 0
  |h :: s' => match beq_nat v h with
              |true => 1 + (count v s')  
              |false => (count v s')
              end
  end.

  Theorem count_member_nonzero : forall (s : bag),
  leb 1 (count 1 (1 :: s)) = true.
  Proof.
  intros.
  simpl. reflexivity.
  Qed.

  Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
  |nil => nil
  |h :: s' => if beq_nat v h then s' else h :: (remove_one v s')
  end.


  Theorem remove_decreases_count: forall (s : bag),
  leb (count 0 (remove_one 0 s)) (count 0 s) = true.
  Proof.
  intros s.
  induction s as [|l s'].
  simpl. reflexivity.
  destruct l.
  simpl. rewrite -> ble_n_Sn. reflexivity.
  simpl. rewrite -> IHs'. reflexivity.
  Qed.

  Definition sum := app.

  Theorem bag_count_sum: forall (n : nat)(s1 s2 : bag),
  count n s1 + count n s2 = count n (sum s1 s2).
  Proof.
  intros n s1 s2. induction s1 as [| l s1'].
    reflexivity.
    simpl. 
    remember (beq_nat n l) as equal.
    destruct equal.
    rewrite <- IHs1'. reflexivity.
    rewrite <- IHs1'. reflexivity.
    Qed.
    

  Theorem rev_injective: forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.
  Proof.
  intros l1 l2.
  intros H.
  destruct l1.
  destruct l2.
  reflexivity.
  rewrite <- rev_involutive.
  rewrite <- H.
  simpl. reflexivity.
  destruct l2.
  rewrite <- rev_involutive.
  rewrite <- H.
  simpl. rewrite -> snoc_cons.
  rewrite -> rev_involutive.
  reflexivity.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite -> rev_involutive.
  reflexivity.
  Qed.

End NatList.