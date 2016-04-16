Require Export D.

Lemma O_le_n : forall n, 0<=n.
Proof. intros. induction n as [|n']. apply le_n. apply le_S. assumption. Qed.

Lemma n_plus_O__n: forall n, n+0=n.
Proof. intros. induction n. reflexivity. simpl. rewrite->IHn. reflexivity. Qed.

Lemma a_Sb__S_a_b : forall a b, a + S b= S (a+b).
Proof. intros. induction a. reflexivity. simpl. rewrite IHa. reflexivity. Qed.


Theorem le_plus_l : forall a b,
  a <= a + b.
Proof. intro a. induction a.
  Case "O". simpl. apply O_le_n.
  Case "S a". simpl. induction b.
    SCase "O". rewrite n_plus_O__n. apply le_n.
    SCase "S b". replace (a + S b) with (S (a + b)). apply le_S. apply IHb. symmetry. apply a_Sb__S_a_b. Qed. 
