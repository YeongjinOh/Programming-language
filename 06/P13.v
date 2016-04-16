Require Export D.



Theorem O_le_n : forall n,
  0 <= n.
 Proof. intros. induction n as [|n']. apply le_n. apply le_S. assumption. Qed.

