Require Export D.



Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof. intros n m. unfold "<". intro H. apply le_S. apply H. Qed.
