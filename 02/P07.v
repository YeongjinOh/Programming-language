Require Export D.



(** **** Problem : 3 stars (mult_comm) *)

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.  
  intros. induction n. simpl. reflexivity.
  simpl. rewrite -> IHn.
  Lemma plus_assoc : forall a b c : nat, a + (b + c) = (a + b) + c.
  Proof. 
      intros. induction a. reflexivity.
      simpl. rewrite -> IHa. reflexivity. Qed.
  rewrite -> plus_assoc. reflexivity.
Qed.

