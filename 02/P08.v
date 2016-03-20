Require Export D.



Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.  
  intros. induction n. simpl. reflexivity.
  simpl.
  
  Lemma plus_assoc : forall a b c : nat,
   a + (b + c) = (a + b) + c.
   Proof. 
     intros. induction a. reflexivity.
     simpl. rewrite <- IHa. reflexivity. Qed.
  
  Lemma mult_dist : forall a b c : nat,
    a * c + b * c = (a + b) * c.
    Proof.
      intros. induction a. simpl.  reflexivity.
      simpl. rewrite <- plus_assoc. rewrite <- IHa. reflexivity. Qed.
  
  rewrite <- mult_dist. rewrite -> IHn. reflexivity. Qed.
