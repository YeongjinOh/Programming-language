Require Export D.

Theorem double_injective : forall n m,
  double n = double m -> n = m.

Proof. 
  intros n m. generalize dependent n. induction m as [|m' IH].
  Case "m = 0". intros n H. destruct n. reflexivity. inversion H.
  Case "n = S n'". intros n H. destruct n. inversion H.
  inversion H. apply IH in H1. rewrite H1. reflexivity.
Qed.

Theorem double_injective2 : forall n m,
  double n = double m -> n = m.
  Proof.
  intros n. induction n as [|n' IH].
  Case "n = 0". intros m H. induction m as [|m' IHm].
    SCase "m = 0". reflexivity.
    SCase "m = S m'". inversion H.
  Case "n = S n'". intros m H. induction m as [|m'].
    SCase "m = 0". inversion H.
    SCase "m = S m'". inversion H. apply f_equal. apply IH. apply H1.
  Qed.

  Theorem beq_nat_true : forall n m, beq_nat n m = true -> n = m.
  Proof.
    intro n. induction n as [|n'].
    Case "n = 0". intros m H. destruct m. reflexivity. inversion H.
    Case "n = S n'". intros m H. destruct m. inversion H.
    inversion H. apply f_equal. apply IHn' in H1. assumption. Qed.

Theorem length_snoc : forall (X:Type) (v:X) (l:list X) (n:nat),
  length l = n -> length (snoc l v) = S n.
Proof.
intros. generalize dependent l. induction n.
  Case "0". intros. destruct l. 
    SCase "[]". reflexivity.
    SCase "x::l". inversion H.
  Case "S n". intros. destruct l.
    SCase "[]". inversion H.
    SCase "x::ln". simpl. apply f_equal. apply IHn. inversion H. reflexivity. Qed.

Theorem idx: forall (n:nat) (X:Type) (l:list X),
  length l = n -> index n l = None.
Proof.
  intros. generalize dependent n. induction l as [|h t].
  Case "[]". intros. simpl. reflexivity.
  Case "h::t".  intros. destruct n. inversion H.
  simpl. apply IHt. inversion H. reflexivity. Qed.

Theorem length_snoc''' : forall (n:nat) (X:Type) (v:X) (l:list X),
length l = n -> length (snoc l v) = S n.
Proof.
  intros. generalize dependent n. induction l as [|hd tl].
  Case "[]". intros. destruct n. reflexivity. inversion H.
  Case "hd::tl". intros. destruct n as [|n']. inversion H.
    SCase "n = S n'". simpl. apply f_equal. apply IHtl. inversion H. reflexivity. Qed.

Theorem app_length_cons : forall (X:Type) (l1 l2:list X) (x:X) (n:nat),
length (l1 ++ (x :: l2)) = n -> S (length (l1 ++ l2)) = n.

Proof. intros. generalize dependent n. induction l1 as [|hd tl].
  Case "[]". intros. simpl. simpl in H. assumption.
  Case "hd::tl". intros. simpl. destruct n. inversion H.
    apply f_equal.  apply IHtl.  inversion H. reflexivity. Qed.

Theorem app_length_twice : forall (X:Type) (n:nat) (l:list X),
  length l = n -> length (l++l) = n+n.
Proof. intros. generalize dependent n. induction l. 
  Case "[]". intros. destruct n. reflexivity. inversion H.
  Case "x::l". intros. destruct n. inversion H.
  simpl. replace (S (n + S n)) with (S (S (n + n))).
  apply f_equal.
  Lemma length_one_more : forall (X:Type) (x:X) (l1 l2:list X),
  length (l1 ++ x::l2) = S (length (l1++l2)). 
    Proof. intros. induction l1. reflexivity. 
    simpl. rewrite IHl1. reflexivity. Qed.
  rewrite length_one_more. apply f_equal. apply IHl. inversion H. reflexivity.
  Lemma simple_plus_lem : forall n m, S (n + m)= n + S m.
  Proof. intros. induction n. reflexivity.  simpl. rewrite IHn. reflexivity. Qed.
  rewrite simple_plus_lem. reflexivity.  Qed.

Theorem double_induction: forall (P : nat -> nat -> Prop),
  P 0 0 ->
  (forall m, P m 0 -> P (S m) 0) ->
  (forall n, P 0 n -> P 0 (S n)) ->
  (forall m n, P m n -> P (S m) (S n)) ->
  forall m n, P m n.
Proof.
  intros P H1 H2 H3 H4 m. induction m as [ | m' ].
  Case "m = O".
     intros n. induction  n as [ | n' ].
     SCase "n = O".
       apply H1. apply H3. apply IHn'.
  Case "m = S m'".
     intros n.  induction n as [ | n'].
     SCase "n = O".
       apply H2. apply IHm'. apply H4. apply IHm'.
Qed.


Theorem double_induction2: forall (P :nat->nat->Prop),
  P 0 0 ->
   (forall m, P m 0 -> P (S m) 0) ->
    (forall n, P 0 n -> P 0 (S n)) ->
      (forall n m, P m n -> P (S m) (S n)) ->
        forall m n, P m n.

Proof. intros. generalize dependent m. induction n as [|n'].
  Case "n = 0". induction m. 
    SCase "m = 0".  apply H.
    SCase "m = S m". apply H0. apply IHm.
  Case "n = S n". intro m. induction m.
    SCase "m = 0". apply H1. apply IHn'. 
    SCase "m = S m". apply H2. apply IHn'. Qed.

Definition sillyfun (n:nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall n,
  sillyfun n = false.
Proof. 
  intros. unfold sillyfun. destruct (beq_nat n 3). reflexivity.
  destruct (beq_nat n 5). reflexivity. reflexivity. Qed.

Theorem override_shadow : forall (X:Type) x1 x2 k1 k2 (f:nat->X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
 intros. unfold override. destruct (beq_nat k1 k2). reflexivity.
  reflexivity. Qed.


(********************************************************)


Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros. generalize dependent l2. induction l1.
  Case "[]". intros. destruct l2. simpl. Abort.

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

(********************************************************)

Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros. unfold sillyfun1 in H. destruct (beq_nat n 3) eqn:H3.
  apply beq_nat_true in H3. rewrite H3. reflexivity.
  destruct (beq_nat n 5) eqn:H5. apply beq_nat_true in H5. rewrite H5. reflexivity. inversion H. Qed.


Theorem bool_fn_applied_thrice :
  forall (f:bool->bool) (b:bool),  f (f (f b)) = f b.
Proof.
 intros. destruct b. destruct (f true) eqn:ft. rewrite ft. apply ft.
  destruct (f false) eqn:ff. apply ft. apply ff.
  destruct (f false) eqn:ff.  destruct (f true) eqn:ft.
  apply ft. apply ff. rewrite ff. apply ff. Qed.

Theorem override_same : forall (X:Type) x1 k1 k2 (f:nat->X),
  f k1 = x1 -> (override f k1 x1) k2 = f k2.
Proof. 
  intros. unfold override. destruct (beq_nat k1 k2) eqn:eq.
  apply beq_nat_true in eq. rewrite<-eq. rewrite H. reflexivity.
  reflexivity. Qed. 

Theorem beq_nat_sym : forall n m, beq_nat n m = beq_nat m n.
Proof.
  intro n. induction n.
  Case "n = 0". intros. destruct m. reflexivity. reflexivity.
  Case "n = S n". intros. destruct m. reflexivity.
    SCase "m = S m". simpl. apply IHn. Qed.

Lemma beq_nat_same : forall n, beq_nat n n = true.
Proof.
  intros. induction n. reflexivity. simpl. apply IHn.
Qed.

Theorem beq_nat_trans : forall n m p,
  beq_nat n m = true ->
    beq_nat m p = true ->
      beq_nat n p = true.
Proof.
  intros n m p Hnm Hmp. apply beq_nat_true in Hnm. apply beq_nat_true in Hmp. rewrite<-Hnm in Hmp. rewrite Hmp.
  induction p. reflexivity. simpl. apply beq_nat_same. Qed.

Theorem override_permute : forall (X:Type) x1 x2 k1 k2 k3 (f:nat->X), 
beq_nat k2 k1 = false ->
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
  intros. unfold override. destruct (beq_nat k1 k3) eqn:K13.
  Case "k1=k3". destruct (beq_nat k2 k3) eqn:K23.
    SCase "k2=k3". apply beq_nat_true in K13. apply beq_nat_true in K23. rewrite<-K13 in K23. rewrite K23 in H. rewrite beq_nat_same in H. inversion H.
    SCase "k2!=k3". reflexivity.
  Case "k1!=k3". destruct (beq_nat k2 k3) eqn:K23.
    SCase "k2=k3". reflexivity.
    SCase "k2!=k3". reflexivity.
Qed.

Theorem filter_exercise: forall (X:Type) (test:X->bool) (x:X) (l lf:list X),
  filter test l = x::lf -> test x = true.
Proof. intros. induction l.
  Case "[]". inversion H.
  Case "x0::l". inversion H. destruct (test x0) eqn:Ht.
    SCase "true". inversion H1. rewrite H2 in Ht. apply Ht.
    SCase "false". apply IHl. apply H1. Qed.

Fixpoint forallb {X:Type} (test:X->bool) (l:list X) : bool :=
match l with
| [] => true
| hd::tl => if test hd then forallb test tl
            else false
end.

Fixpoint existsb {X:Type} (test:X->bool) (l:list X) : bool :=
match l with
| [] => false
| hd::tl => if test hd then true
            else existsb test tl
end.

Eval compute in forallb oddb [1;3;5;7;9].
Eval compute in forallb negb [false;false].
Eval compute in forallb evenb [0;2;4;5].
Eval compute in forallb (beq_nat 5) [] = true.
Eval compute in      existsb (beq_nat 5) [0;2;3;6] = false.
Eval compute in      existsb (andb true) [true;true;false] = true.
Eval compute in      existsb oddb [1;0;0;0;0;3] = true.
Eval compute in      (existsb evenb [] = false).


