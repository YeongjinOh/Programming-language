Require Export D.


Theorem O_le_n : forall n, 0<=n.
Proof. intros. induction n as [|n']. apply le_n. apply le_S. assumption. Qed.


Theorem Sn_le_Sm__n_le_m: forall n m, n <= m -> S n <= S m.
Proof. intros. induction H. apply le_n. apply le_S. apply IHle. Qed.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof. intros. generalize dependent n. induction m.
  Case "O". induction n.
    SCase "O". intros. apply le_n.
    SCase "S n". intros. inversion H. 
  Case "S m". intros. induction n.
    SCase "O". apply O_le_n.
    SCase "S n". inversion H. apply IHm in H1. apply Sn_le_Sm__n_le_m. assumption. Qed.
