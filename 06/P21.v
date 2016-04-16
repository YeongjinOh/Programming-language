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

Lemma le_trans : forall m n o,
  m <= n -> n <= o -> m <= o.
Proof. intros m n o Hmn Hno. induction Hno as [|n o]. 
  Case "le_n". apply Hmn.
  Case "le_S". apply le_S. apply IHHno. assumption. Qed.

Theorem n_le_m__Sn_le_Sm: forall n m, S n <= S m -> n <= m.
Proof. intros. inversion H. apply le_n. apply le_trans with (m:=n) (n:=S n) (o:=m). apply le_S. apply le_n. apply H2.  
Qed.


Theorem le_ble_nat: forall n m,
  n <= m -> ble_nat n m = true.
Proof. intro n. induction n.
  Case "O". intros. induction m.
    SCase "O". reflexivity. 
    SCase "S m". reflexivity.
  Case "S n". intros. induction m.
    SCase "O". inversion H.
    SCase "S m". simpl. apply IHn. apply n_le_m__Sn_le_Sm.
    assumption. Qed.

Theorem ble_nat_true_trans : forall n m o,
  ble_nat n m = true -> ble_nat m o = true -> ble_nat n o = true.                               
Proof. intros. apply ble_nat_true in H. apply ble_nat_true in H0.
  apply le_ble_nat. apply le_trans with (m:=n) (n:=m). assumption. assumption. Qed.

Theorem ble_nat_false: forall n m,
  ble_nat n m = false -> ~(n<=m).
Proof. intros. unfold not. intro Hnm. apply le_ble_nat in Hnm. rewrite H in Hnm. inversion Hnm. Qed.
