Require Export D.



(** **** Problem #19 : 2 stars (beq_nat_true)  *)
Theorem beq_nat_true : forall n m,
    beq_nat n m = true -> n = m.
Proof.
  intros n. induction n. intros. destruct m. reflexivity.
  inversion H.
  intros. 
  destruct m. inversion H. 
  Lemma nm_SnSm_eq : forall (n m:nat),
    n=m -> S n=S m.
  Proof. intros.  rewrite ->H. reflexivity. Qed.
  apply nm_SnSm_eq. apply IHn. inversion H. reflexivity.
Qed.

