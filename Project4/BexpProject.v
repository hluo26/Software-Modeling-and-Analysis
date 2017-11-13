(** In this project we will extend the definition for IMP arithmetic
  expressions to include Boolean expressions.  We will define a second
  abstract data type, [bexp], that references [aexp] to include numbers in
  boolean relations like less than and equals. We will then define [beval]
  and [bevalR] to capture evaluation semantics.  Finally, we'll do a few
  correctness proofs and examples. *) 
Require Import Omega.

Module Bexp.

(** [aexp] definition does not change *)
  
Inductive aexp : Type :=
| ANum : nat -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.

(** [bexp] defines Boolean operations and references [aexp] to include
  numbers. *)

Inductive bexp : Type :=
| BTrue : bexp
| BFalse : bexp
| BEq : aexp -> aexp -> bexp
| BLe : aexp -> aexp -> bexp
| BNot : bexp -> bexp
| BAnd : bexp -> bexp -> bexp.

(** [aeval] does not change *)

Fixpoint aeval(a:aexp):nat :=
  match a with
  | ANum x => x
  | APlus l r => (aeval l) + (aeval r)
  | AMinus l r => (aeval l) - (aeval r)
  | AMult l r => (aeval l) * (aeval r)
  end.

(** Exercise 1: Dedfine [beval] by replacing [true] with a [match] expression
  as is done  for [aexp] above. *)

Fixpoint ble_nat n m  :=
  match n, m  with
    | O, _ => true
    | S n', O => false
    | S n', S m' => ble_nat n' m'
  end.

Fixpoint beval(b:bexp):bool := 
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval a1)(aeval a2)
  | BLe a1 a2 => ble_nat (aeval a1)(aeval a2)
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.
  

(** Exercise 2: Verify these examples.   Proofs should be trivial.  The last
  one that uses [<>] will take a bit more work, but not too much.  Remember
  [intros]. *)

Example ex1: beval BTrue = true.
Proof.
simpl. reflexivity.
Qed.
                          
Example ex2: beval (BLe (ANum 3) (ANum 5)) = true.
Proof.
simpl. reflexivity.
Qed.

Example ex3: beval (BNot (BEq (ANum 5) (ANum 3))) = true.
Proof.
simpl. reflexivity.
Qed.

Example ex4: beval (BLe (ANum 5) (ANum 3)) <> true.
Proof.
intros.
discriminate.
Qed.

(** Optimiation over arithmetic expressions does not change *)

Fixpoint opt_0plus(a:aexp):aexp :=
  match a with
  | ANum x => ANum x
  | APlus (ANum 0) r => (opt_0plus r)
  | APlus l r => APlus (opt_0plus l) (opt_0plus r)
  | AMinus l r => AMinus (opt_0plus l) (opt_0plus r)
  | AMult l r => AMult (opt_0plus l) (opt_0plus r)
  end.

(** Exercise 3.  Define the 0 plus optimization over Booleans.  Think carefully
  about this. It is not hard at all.  Remember that boolean expressions
  are not optimized, but arithmetic expressions must be. *)

Fixpoint opt_0plus_b (b : bexp) : bexp := 
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq (opt_0plus a1)(opt_0plus a2)
  | BLe a1 a2 => BLe (opt_0plus a1)(opt_0plus a2)
  | BNot a1 => BNot (opt_0plus_b a1) 
  | BAnd b1 b2 => BAnd (opt_0plus_b b1) (opt_0plus_b b2)
  end.

(** Including the proof that optimization is sound over artimetic expressions
  for your reference.  You may also want to use this theorem later on.  Yes,
  that is a hint. *)

Theorem opt_0plus_sound: forall a, aeval (opt_0plus a) = aeval a.
Proof.
  intros a.
  induction a.
  (* ANum *)
  reflexivity.
  (* APlus *)
  induction a1.
  (* APLus ANum *)
  destruct n. simpl. assumption. simpl. rewrite <- IHa2. reflexivity.
  simpl. simpl in IHa1. rewrite IHa1. rewrite IHa2. reflexivity.
  simpl. simpl in IHa1. rewrite IHa1. rewrite IHa2. reflexivity.
  simpl. simpl in IHa1. rewrite IHa1. rewrite IHa2. reflexivity.
  simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  simpl. rewrite IHa1. rewrite IHa2. reflexivity.
Qed.

(** Exercise 4: Prove the optimization function over Boolean expressions
  is sound. *)

Theorem opt_0plus_b_sound: forall b, beval (opt_0plus_b b) = beval b.
Proof.
intros b.
induction b.
simpl. reflexivity.
simpl. reflexivity.
simpl. rewrite opt_0plus_sound. rewrite opt_0plus_sound. reflexivity.
simpl. rewrite opt_0plus_sound. rewrite opt_0plus_sound. reflexivity.
simpl. rewrite IHb. reflexivity.
simpl. rewrite IHb1. rewrite IHb2. reflexivity.
Qed.


        
(** The evaluation relation for arithmetic expressions does not change. *)

Inductive aevalR : aexp -> nat -> Prop := 
| E_ANum: forall n, aevalR (ANum n) n
| E_APlus: forall l r m n o,
    aevalR l m -> aevalR r n -> o=(m+n) -> aevalR (APlus l r) o
| E_AMinus: forall l r m n o,
    aevalR l m -> aevalR r n -> o=(m-n) -> aevalR (AMinus l r) o
| E_AMult: forall l r m n o,
    aevalR l m -> aevalR r n -> o=(m*n) -> aevalR (AMult l r) o.

Hint Constructors aevalR.

(** Exercise 5: Define the evaluation relation for Booleans.  Works the
  same way. *)

Inductive bevalR : bexp -> bool -> Prop :=
  | E_BTrue: bevalR (BTrue) true
  | E_BFalse: bevalR (BFalse) false
  | E_BEq: forall (l r:aexp)(m n:nat) , aevalR l m -> aevalR r n -> bevalR(BEq l r)(beq_nat m n)
  | E_BLe: forall (l r:aexp)(m n:nat) , aevalR l m -> aevalR r n -> bevalR(BLe l r)(ble_nat m n)
  | E_BNot: forall (l:bexp)(m:bool), bevalR l m -> bevalR(BNot l)(negb m)
  | E_BAnd: forall (l r:bexp)(m n:bool), bevalR l m -> bevalR r n -> bevalR(BAnd l r)(andb m n).
  

Hint Constructors bevalR.

Theorem aeval_correct: forall a, aevalR a (aeval a).
Proof.
  intros a.
  induction a.
  simpl. apply E_ANum.
  simpl. eapply E_APlus. apply IHa1. apply IHa2. reflexivity.
  simpl. eapply E_AMinus. apply IHa1. apply IHa2. reflexivity.
  simpl. eapply E_AMult. apply IHa1. apply IHa2. reflexivity.
Qed.

(** Exercise 6: Prove your evaluator is correct with respect to the relational
  defition.  The proof above will give you an idea of how to proceed.  *)

Theorem beval_correct: forall b, bevalR b (beval b).
Proof.
intros.
induction b.
simpl. eapply E_BTrue.
simpl. eapply E_BFalse.
simpl. eapply E_BEq. eapply aeval_correct. eapply aeval_correct.
simpl. eapply E_BLe. eapply aeval_correct. eapply aeval_correct.
simpl. eapply E_BNot. apply IHb.
simpl. eapply E_BAnd. apply IHb1. apply IHb2.
Qed.

(** Exercise 7: Prove the optimization is correct with respect to the
  relational definition.  This proof is not trivial, but still doable.  *)

Theorem opt_0plus_correct: forall a, bevalR a (beval (opt_0plus_b a)).
Proof.
intros.
induction a.
simpl. eapply E_BTrue.
simpl. eapply E_BFalse.
simpl. eapply E_BEq. rewrite opt_0plus_sound. eapply aeval_correct. rewrite opt_0plus_sound. eapply aeval_correct.
simpl. eapply E_BLe. rewrite opt_0plus_sound. eapply aeval_correct. rewrite opt_0plus_sound. eapply aeval_correct.
simpl. eapply E_BNot. rewrite opt_0plus_b_sound. eapply beval_correct.
simpl. eapply E_BAnd. apply IHa1. apply IHa2.
Qed.

End Bexp.
