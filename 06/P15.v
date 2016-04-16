Require Export D.

Lemma le_trans : forall m n o,
  m <= n -> n <= o -> m <= o.
Proof. intros m n o Hmn Hno. induction Hno as [|n o]. 
  Case "le_n". apply Hmn.
  Case "le_S". apply le_S. apply IHHno. assumption. Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof. intros. inversion H. apply le_n. apply le_trans with (m:=n) (n:=S n) (o:=m). apply le_S. apply le_n. apply H2.  
Qed.

