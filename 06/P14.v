Require Export D.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof. intros. induction H. apply le_n. apply le_S. assumption.
Qed.
