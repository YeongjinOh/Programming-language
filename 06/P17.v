Require Export D.

Lemma n_plus_O__n: forall n, n+0=n.
Proof. intros. induction n. reflexivity. simpl. rewrite->IHn. reflexivity. Qed.


Lemma O_le_n : forall n, 0<=n.
Proof. intros. induction n as [|n']. apply le_n. apply le_S. assumption. Qed.



Lemma a_Sb__S_a_b : forall a b, a + S b= S (a+b).
Proof. intros. induction a. reflexivity. simpl. rewrite IHa. reflexivity. Qed.

Lemma plus_comm: forall a b, a + b = b + a.
Proof. intros. induction a.
  Case "a". simpl. symmetry. apply n_plus_O__n.
  Case "S a". simpl. rewrite a_Sb__S_a_b. rewrite IHa. reflexivity. Qed.

Theorem le_plus_l: forall a b, a <= a + b.
Proof. intro a. induction a.
  Case "O". simpl. apply O_le_n.
  Case "S a". simpl. induction b.
    SCase "O". rewrite n_plus_O__n. apply le_n.
    SCase "S b". replace (a + S b) with (S (a + b)). apply le_S. apply IHb. symmetry. apply a_Sb__S_a_b. Qed. 



Lemma le_trans : forall m n o,
  m <= n -> n <= o -> m <= o.
Proof. intros m n o Hmn Hno. induction Hno as [|n o]. 
  Case "le_n". apply Hmn.
  Case "le_S". apply le_S. apply IHHno. assumption. Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof. intros n1 n2 m. unfold "<". split.
  Case "n1". apply le_trans with (m:=S n1) (n:= S(n1+n2)) (o:=m).
    replace (S (n1 + n2)) with (S n1 + n2). apply le_plus_l.
    simpl. reflexivity. apply H.
  Case "n2". apply le_trans with (m:=S n2) (n:=S (n1 + n2)) (o:= m). replace (S (n1 + n2)) with (S n2 + n1). apply le_plus_l. simpl. rewrite plus_comm.  reflexivity. apply H. Qed.

