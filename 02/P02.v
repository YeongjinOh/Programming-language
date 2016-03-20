Require Export D.



Theorem plus_n_Sm : forall n m : nat, 
  S (n + m) = n + (S m).
Proof. 
  intros. induction n. reflexivity.
  simpl. rewrite <- IHn. reflexivity.
Qed.

