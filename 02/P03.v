Require Export D.



Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof. 
  intros. induction n. simpl. induction m. reflexivity. simpl. rewrite <- IHm. reflexivity.
  simpl. rewrite -> IHn. 
  Lemma plus_Smn_mSn : forall n m:nat, S (m + n) = m + S n.
  Proof.
   intros.  induction m. reflexivity. simpl. rewrite -> IHm. reflexivity.
Qed.
  apply plus_Smn_mSn. Qed.
