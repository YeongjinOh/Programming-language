Require Export D.

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday (d:day) : day :=
match d with
| monday => tuesday
| tuesday => wednesday
| wednesday => thursday
| thursday => friday
| friday => monday
| saturday => monday
| sunday => monday
end.

Inductive bool: Type :=
| true : bool
| false : bool.

Definition negb (b:bool) : bool :=
match b with
| true => false
| false => true
end.

Definition andb (b1 b2:bool) : bool :=
match b1 with
| true => b2
| false => false
end.

Definition orb (b1 b2:bool) : bool :=
match b1 with
| true => true
| false => b2
end.

Definition nandb (b1 b2:bool) : bool :=
negb (andb b1 b2).

Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

(*
Inductive nat : Type :=
| O : nat
| S : nat -> nat
.
*)

Inductive permut : Type :=
| a : permut
| b : permut
| c : permut.

Definition np (p:permut) : permut :=
match p with
| a => b
| b => c
| c => a
end.

Theorem three_cycle : forall p, np (np (np p)) = p.
Proof.  intros. induction p.
  Case "a". reflexivity.
  Case "b". reflexivity.
  Case "c". reflexivity. Qed.

Definition pred (n:nat) : nat :=
match n with
| O => O
| S n' => n'
end.

Example pred_exception : exists n, ~(pred (S n) = S (pred n)).
Proof. exists O. intros contra. simpl in contra. inversion contra. Qed.

Definition minus_two (n:nat) : nat :=
pred (pred n).

Fixpoint evenb (n:nat) : bool :=
match n with
| O => true
| S O => false
| S (S m) => (evenb m)
end.

Definition oddb (n:nat) : bool :=
negb (evenb n).

Example test_oddb1: (oddb (S O)) = true.
Proof. reflexivity. Qed.
Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof. reflexivity. Qed.

Fixpoint plus (n m:nat) : nat :=
match n with
| O => m
| S n' => S (plus n' m)
end.

Fixpoint mult (n m:nat) : nat :=
match n with
| O => O
| S n' => plus m (mult n' m)
end.

Example test_mult1: (mult 3 3) = 9.
Proof. reflexivity. Qed.

Fixpoint minus (n m:nat) : nat :=
match n with
| O => O
| S n' => match m with
         | O => S n'
         | S m' => minus n' m'
        end
end.

Fixpoint exp (n m:nat) : nat :=
match m with
| O => S O
| S m' => mult n (exp n m')
end.


Fixpoint factorial (n:nat) : nat := 
match n with
| O => S O
| S n' => mult n (factorial n')
end.

Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.

Fixpoint beq_nat (n m:nat) : bool :=
match n,m with
| O, O => true
| _, O => false
| O, _ => false
| S n', S m' => beq_nat n' m'
end.

Fixpoint ble_nat (n m:nat) : bool :=
match n,m with
| O, _ => true
| _, O => false
| S n', S m' => ble_nat n' m'
end.

Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. reflexivity. Qed.

Definition blt_nat (n m:nat) : bool :=
  andb (negb (beq_nat n m)) (ble_nat n m).

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. reflexivity. Qed.

Theorem plus_O_n : forall n:nat, O + n = n.
Proof. reflexivity. Qed.

Theorem plus_n_O : forall n:nat, n + O = n.
Proof. intro n. induction n. reflexivity. simpl. rewrite IHn. reflexivity. Qed.

Theorem plus_1_n : forall n, 1 + n = S n.
Proof. intros n. reflexivity. Qed.

Theorem plus_id_example : forall n m, 
  n = m -> n + n = m + m.
Proof. intros. rewrite H. reflexivity. Qed.

Theorem plus_id_exercise : forall n m o,
  n = m -> m = o -> n + m = m + o.
Proof. 
  intros n m o Hnm Hmo. rewrite->Hnm. rewrite<-Hmo. reflexivity. Qed.

Theorem mult_0_plus : forall n m,
  (O + n) * m = n * m.
Proof. intros. rewrite plus_O_n.  reflexivity. Qed.

Theorem mult_S_l : forall n m, 
  m = S n -> m * (1 + n ) = m * m.
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Theorem plus_1_neq_0_firsttry : forall n,
  beq_nat (n + 1) 0 = false.
Proof. intros. destruct n as [|n'].
  Case "O". reflexivity.
  Case "S n'". reflexivity.
Qed.

Theorem negb_involutive : forall b,
  negb (negb b) = b.
Proof.
  intro b. destruct b. reflexivity. reflexivity. Qed.

Theorem zero_nbeq_plus_l :forall n,
  beq_nat 0 (n + 1) = false.
Proof. intro n. destruct n. reflexivity. reflexivity. Qed.

Theorem identity_fn_applied_twice : forall (f:bool->bool),
  (forall x, f x = x) -> forall b, f (f b) = b.
Proof. intros. rewrite H. apply H. Qed.

Theorem andb_eq_orb : forall (b c:bool),
  (andb b c = orb b c) -> b = c.
Proof. intros b c H. destruct b. destruct c.
  reflexivity. inversion H. destruct c. inversion H. reflexivity. Qed.
