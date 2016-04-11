Require Export D.




(** **** Problem #24 : 2 stars (override_same)  
    Hint: use the lemma [beq_nat_true]. *)
Theorem override_same : forall (X:Type) x1 k1 k2 (f : nat->X),
  f k1 = x1 -> 
  (override f k1 x1) k2 = f k2.
Proof.
 intros. unfold override. destruct (beq_nat k1 k2) eqn:a. rewrite <- H. 
  Lemma beq_nat_eq_true : forall (k1 k2:nat), 
    beq_nat k1 k2 = true -> k1 = k2.
  Proof. intros k1.  induction k1. destruct k2. reflexivity. 
    intros H. inversion H.
    destruct k2. intros H. inversion H.
    intros H. inversion H. apply f_equal. apply IHk1. apply H1. Qed.
    apply f_equal. apply beq_nat_eq_true. apply a.
    reflexivity.
  
Qed.
