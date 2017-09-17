Require Import Omega.

(** Stack of natural numbers *)

Module Natstack.

  Inductive natstack : Type :=
  | empty : natstack
  | push : nat -> natstack -> natstack.
  
  Definition pop(s:natstack):natstack :=
    match s with
    | empty => empty
    | push n' s' => s'
    end.
  
  Definition top(s:natstack):nat :=
    match s with
    | empty => 0
    | push n' s' => n'
    end.
  
  Fixpoint size(s:natstack):nat :=
    match s with
    | empty => 0
    | push _ s' => 1+(size s')
    end.
  
  (** Some sanity check examples.  Proofs should be very simple. *)

  Example ex1: pop (push 0 (push 1 empty)) = push 1 empty.
Proof.
  simpl.
  reflexivity.
Qed.
    
  Example ex2: top (push 0 (push 1 empty)) = 0.
Proof.
  simpl.
  reflexivity.
Qed.

  Example ex3: size (push 0 (push 1 empty)) = 2.
Proof.
  simpl.
  reflexivity.
Qed.

  (** Proofs of actual properties. *)
  
  Theorem pop_push: forall x s, pop (push x s) = s.
  Proof.
  simpl. reflexivity.
Qed.
  Theorem top_push: forall x s, top (push x s) = x.
  Proof.
  simpl. reflexivity.
Qed.

  Theorem push_ne_empty: forall x s, push x s <> empty.
  Proof.
  intros.
  discriminate.
Qed.

    
  Theorem stack_extensionality: forall x x' s s',
      x=x' -> s=s' -> (push x s) = (push x' s').
  Proof.
  intros.
  destruct s.
  rewrite -> H.
  rewrite -> H0.
  reflexivity.
  rewrite -> H.
  rewrite -> H0.
  reflexivity.
Qed.

  
    
  Theorem stack_duck: forall s s',
      s<>empty -> s'<>empty -> top s = top s' -> pop s = pop s' -> s=s'.
  Proof.
  intros s.
  intros H H0 H1 H2.
  destruct s.
  

  
    
  Theorem stack_ext: forall s, s<>empty -> (push (top s) (pop s))=s.
  Proof.
  intros s.
  intros H.
  destruct s.
  destruct H.
  simpl. reflexivity.
  simpl. reflexivity.
Qed.

    
  Theorem sixe_push_gt: forall x s, size (push x s) > size s.
  Proof.
  intros [] [].
  simpl. omega.
  simpl. omega.
  simpl. omega.
  simpl. omega.
Qed.

  

  (** A couple of practice proofs from Pierce *)
  
  Theorem mult_S_1 : forall n m : nat,
      m = S n ->
      m * (1 + n) = m * m.
  Admitted.
  
  Theorem andb_true_elim2 : forall b c : bool,
      andb b c = true -> c = true.
  Admitted.

End Natstack.