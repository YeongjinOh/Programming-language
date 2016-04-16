Require Import Arith NPeano.

(** Important: 
    - You are NOT allowed to use the [admit] tactic
      because [admit] simply admits any goal 
      regardless of whether it is provable or not.

      But, you can leave [admit] for problems that you cannot prove.
      Then you will get zero points for those problems.

    - You are NOT allowed to use the following tactics.

      [tauto], [intuition], [firstorder], [omega].

    - Here is the list of tactics and tacticals you have learned.

      [intros]
      [revert]
      [reflexivity]
      [simpl]
      [rewrite]
      [induction]
      [assert]
      [unfold]
      [apply] ... [with] ... [in] ...
      [destruct] ... [as] ... [eqn:] ...
      [inversion]
      [symmetry]
      [generalize dependent]
      [split]
      [exists]
      [clear]
      [subst]
      [rename] ... [into] ...
      [contradiction]
      [constructor]
      [auto]
      [repeat]
      [try]
      [;]
**)

Definition admit {T: Type} : T.  Admitted.

(**
  Definition of [list] 
 **)

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Fixpoint app (X : Type) (l1 l2 : list X)
                : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons X h (app X t l2)
  end.

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments app {X} l1 l2.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Check (3 :: ([0; 1] ++ [])).

(**
  You may want to use the following lemmas.
 **)

Check mult_comm.
Check mult_1_r.
Check mult_assoc.
Check plus_comm.
Check plus_0_r.
Check plus_assoc.
Check plus_minus.
Check mult_plus_distr_l.
Check mult_plus_distr_r.
Check mult_minus_distr_l.
Check mult_minus_distr_r.

Check le_not_lt.
Check lt_le_trans.
Check lt_irrefl.

(*=========== 3141592 ===========*)

(** Easy:
    Prove the following theorem.
 **)

Lemma forall_not_ex_not: forall (X: Type) (P: X -> Prop)
    (ALL: forall x, P x),
  ~ exists x, ~ P x.
Proof.
  intros. unfold not. intro contra. destruct contra. apply H in ALL. inversion ALL.
Qed.

(*=========== 3141592 ===========*)

(** Easy:
    Define a function [square_sum] satisfying:

      square_sum n = 1^2 + 2^2 + ... +n^2

 **)

Fixpoint square_sum (n: nat) : nat :=
match n with
| O => O
| S n' => square_sum n' + n*n 
end.

Example square_sum_example1: square_sum 5 = 55.
Proof. reflexivity.  Qed.

Example square_sum_example2: square_sum 10 = 385.
Proof. reflexivity.  Qed.

(*=========== 3141592 ===========*)

(** Medium:
    Define a function [fibonacci] satisfying:

      fibonacci 0 = 0
      fibonacci 1 = 1
      fibonacci (n+2) = fibonacci (n+1) + fibonacci n

 **)

Fixpoint fibonacci (n: nat) : nat :=
match n with
| O => O
| S m => match m with
        | O => S O
        | S k => fibonacci m + fibonacci k
        end
end.

Example fibonacci_example1: fibonacci 5 = 5.
Proof. reflexivity.  Qed.

Example fibonacci_example2: fibonacci 10 = 55.
Proof. reflexivity.  Qed.

(*=========== 3141592 ===========*)

(** Medium:
    Prove the following theorem.
 **)

Fixpoint odd_sum (n: nat) : nat :=
  match n with
  | 0 => 0
  | S m => 1 + 2*m + odd_sum m
  end.

 Lemma n_sum : forall n m, n + n * m = n * S m.
  Proof. intros. induction n. reflexivity. simpl. rewrite<-IHn.
  replace (n + (m + n * m)) with (m + (n + n * m)).
  reflexivity. rewrite->plus_assoc. rewrite plus_comm with (n:=m) (m:=n). rewrite<-plus_assoc.
 reflexivity. Qed.
  
Theorem odd_sum__square: forall n,
  odd_sum n = n * n.
Proof.
  intros. induction n.
  (* O *) reflexivity.
  (* S n *) simpl.  apply f_equal. rewrite IHn. rewrite plus_0_r.
  assert (n + n * n = n * S n). apply n_sum. rewrite<-H. rewrite plus_assoc. reflexivity. Qed.

(*=========== 3141592 ===========*)

(** Medium:
    Prove the following theorem.
 **)

Lemma app_tail_cancel: forall X (l1 l2: list X) a
    (EQ: l1 ++ [a] = l2 ++ [a]),
  l1 = l2.
Proof.
  intros. generalize dependent l2. induction l1. intros. induction l2.
  reflexivity. inversion EQ. destruct l2. inversion H1. inversion H1.
  intros. induction l2. inversion EQ. destruct l1. inversion H1. inversion H1.
  inversion EQ. apply IHl1 in H1. rewrite H1. reflexivity. Qed.

(*=========== 3141592 ===========*)

(** Medium:
    Prove the following theorem.
 **)

Lemma odd_or_even: forall n,
  exists k, n = 2*k \/ n = 1 + 2*k.
Proof.
  intros. induction n. exists 0. left. reflexivity.
  destruct IHn. destruct H.
  exists x. right. rewrite H. simpl. reflexivity.
  exists (S x).  left. rewrite H. simpl. apply f_equal.
  Lemma S_an_a_Sb : forall a b,
    S(a + b) = a + S b.
  Proof. intros. induction a. reflexivity. simpl. rewrite IHa. reflexivity. Qed.
  apply S_an_a_Sb.
Qed.

(*=========== 3141592 ===========*)

(** Hard:
    Prove the following theorem.
 **)

Definition excluded_middle := forall (P:Prop), P \/ ~P. 

Lemma six_div : forall n,
  exists k, n=6*k \/ n=6*k+1 \/ n=6*k+2 \/ n=6*k+3 \/ n=6*k+4 \/ n=6*k+5.
Proof. intros. induction n.
  exists 0. left. reflexivity. 
  destruct IHn. destruct H. exists x. right. left. rewrite H. rewrite plus_comm . reflexivity.
  destruct H. exists x. right. right. left. rewrite H. rewrite<-plus_comm . replace (6*x+2) with (2+6*x). reflexivity. rewrite<-plus_comm. reflexivity.
  destruct H. exists x. right. right. right. left. rewrite H. rewrite<-plus_comm . replace (6*x+3) with (3+6*x). reflexivity. rewrite<-plus_comm. reflexivity.
  destruct H. exists x. right. right. right. right. left. rewrite H. rewrite<-plus_comm . replace (6*x+4) with (4+6*x). reflexivity. rewrite<-plus_comm. reflexivity.
  destruct H. exists x. right. right. right. right. right. rewrite H. rewrite<-plus_comm . replace (6*x+5) with (5+6*x). reflexivity. rewrite<-plus_comm. reflexivity.
  exists (x+1). left. rewrite H. replace (S (6*x+5)) with (6*x+ S 5). rewrite->mult_plus_distr_l. reflexivity. rewrite S_an_a_Sb. reflexivity. Qed.
(*
Lemma div : forall a n m,
  (a<>0) -> 
    a * n = a * m ->
      n = m.
Proof. intros. induction n. induction m. reflexivity.
  unfold not in H.

Lemma a0_am : forall a m, 
  a<>0 -> a*0 = a*m -> m=0.
Proof. intros. induction m. reflexivity. rewrite->mult_comm in H0.  simpl in H0.

Lemma O_ab : forall a b,
  a<>0 -> 0=a*b -> b=0.
Proof. intros. induction b. reflexivity.
  rewrite mult_comm in H0. simpl in H0.

Lemma O_a_plus_b: forall a b,
  0 = a + b -> a=0.
Proof. intros. induction b. rewrite H. rewrite plus_0_r. reflexivity.
  rewrite IHb. reflexivity. 
*)
Lemma two_three_rel_prime: forall n m
    (EQ: 2 * n = 3 * m),
  exists k, m = 2 * k.
Proof.
  intros. destruct (six_div (3*m)).
  (* 6x *)
  destruct H. exists x. inversion H. 
Admitted.

(*=========== 3141592 [30] ===========*)

(** Easy:
    Define a predicate [sorted_min: nat -> list nat -> Prop], where
    [sorted_min n l] holds iff the elements in the list [l] is greater
    than or equal to [n] and sorted in the increasing order.
 **)

Fixpoint ble_nat (n x:nat) : bool :=
match n,x with
| O, _ => true
| _, O => false
| S n', S x' => ble_nat n' x'
end.

Inductive sorted_min: nat -> list nat -> Prop :=
|sm_nil : forall n, sorted_min n []
|sm_cons: forall n x tl, sorted_min x tl -> (ble_nat n x = true) -> sorted_min n (x::tl)
.

Example sorted_min_example1: sorted_min 0 [1; 3; 4; 4; 5].
Proof. apply sm_cons. apply sm_cons. apply sm_cons. apply sm_cons. apply sm_cons. apply sm_nil. reflexivity.  reflexivity.  reflexivity.  reflexivity.  reflexivity.  Qed.

Example sorted_min_example2: sorted_min 2 [2; 2; 3; 6].
Proof. apply sm_cons. apply sm_cons. apply sm_cons. apply sm_cons. apply sm_nil.
   reflexivity.  reflexivity.  reflexivity.  reflexivity.
Qed.

Example sorted_min_non_example1: sorted_min 1 [0; 1] -> False.
Proof. intros. inversion H. inversion H4. Qed.





(** Medium:
    Prove the following theorem. 
 **)

Inductive appears_in (n : nat) : list nat -> Prop :=
| ai_here : forall l, appears_in n (n::l)
| ai_later : forall m l, appears_in n l -> appears_in n (m::l).

Lemma le_trans : forall n m o,
    n <= m -> m <= o -> n <= o.
Proof. intros n m o Hnm Hmo. induction Hmo. assumption.
 apply le_S. assumption.
Qed.

Lemma le_O_n : forall n, O <= n.
Proof. intros. induction n. reflexivity.
  apply (le_trans 0 n (S n)). assumption. apply le_S. apply le_n. Qed.

Lemma Sn_le_Sm__n_le_m : forall n m,
  n <= m -> S n <= S m.
Proof. intros. induction H. apply le_n. apply le_S. assumption.
Qed. 
  

Lemma ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof.
  intros. generalize dependent n. induction m.
    intros. destruct n. reflexivity. inversion H.
    intros. induction n. apply le_O_n.
    inversion H. apply IHm in H1. apply Sn_le_Sm__n_le_m. assumption. Qed.
    

Lemma sorted_not_in: forall n m l
    (SORTED: sorted_min m l)
    (LT: n < m),
  ~ appears_in n l.
Proof.
  intros. unfold not. intros contra.
  induction SORTED. 
  (* nil *)
    inversion contra.
  (* cons *)
    apply ble_nat_true in H. 
    assert (n<x). apply lt_le_trans with (m:=n0) (p:=x). assumption. assumption. apply IHSORTED in H0. inversion H0. 
    inversion contra. rewrite H2 in H0. apply lt_irrefl in H0. inversion H0.
    assumption.

Qed.









(** Hard:
    Prove the following theorem.
 **)

(* [beq_nat n m] returns [true]  if [n = m] holds; 
                 returns [false] otherwise. *)
Check beq_nat.
Check beq_nat_false.
Check beq_nat_true.
Check beq_nat_refl.

(* [ltb n m] returns [true]  if [n < m] holds; 
             returns [false] otherwise.
   Note that [ltb n m] is displayed as [n <? m]. *)
Check ltb.
Check ltb_lt.

Fixpoint appears_inb (n: nat) (l: list nat) : bool :=
  match l with
  | nil => false
  | m :: l' => 
    if ltb n m
    then false
    else (if beq_nat n m
          then true
          else appears_inb n l')
  end.

Theorem appears_inb_correct: forall n l
    (SORTED: sorted_min 0 l)
    (NOTAPPEAR: appears_inb n l = false),
  ~ appears_in n l.
Proof.
  intros. 

  Qed.

