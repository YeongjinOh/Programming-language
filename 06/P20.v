Require Export D.


Lemma le_trans : forall m n o,
  m <= n -> n <= o -> m <= o.
Proof. intros m n o Hmn Hno. induction Hno as [|n o]. 
  Case "le_n". apply Hmn.
  Case "le_S". apply le_S. apply IHHno. assumption. Qed.

Theorem n_le_m__Sn_le_Sm: forall n m, S n <= S m -> n <= m.
Proof. intros. inversion H. apply le_n. apply le_trans with (m:=n) (n:=S n) (o:=m). apply le_S. apply le_n. apply H2.  
Qed.



Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
intro n. induction n.
  Case "O". intros. induction m.
    SCase "O". reflexivity. 
    SCase "S m". reflexivity.
  Case "S n". intros. induction m.
    SCase "O". inversion H.
    SCase "S m". simpl. apply IHn. apply n_le_m__Sn_le_Sm.
assumption. Qed.
  
