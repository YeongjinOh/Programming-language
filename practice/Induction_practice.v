Require Export D.

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  intros. induction n.
  Case "O". reflexivity.
  Case "S n". simpl. rewrite IHn. reflexivity. Qed.

Theorem mult_0_plus : forall n m:nat,
  (0 + n) * m = n * m.
Proof. intros.
  assert (H:0+n = n). reflexivity. rewrite H. reflexivity. Qed. 

Print plus_comm.

Theorem plus_swap : forall n m p,
    n + (m + p) = m + (n + p).
Proof. 
  intros. rewrite plus_assoc. rewrite plus_assoc.
  assert (n+m = m+n). apply plus_comm. rewrite H. reflexivity. Qed.


