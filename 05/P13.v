Require Export D.



(** 2 stars, optional (beq_nat_false)  *)
Theorem beq_nat_false : forall n m,
  beq_nat n m = false -> n <> m.
Proof.
  Lemma ex_falso : forall P:Prop, 
    False -> P.
  Proof. intros P contra. inversion contra. Qed.
  unfold not. intros n m.  generalize dependent m. induction n.
  Case "n = 0". induction m.
    SCase "m = 0". intro H. inversion H. 
    SCase "m = S m". simpl. intro H. intro Hcontra. inversion Hcontra.
  Case "n = S n". induction m.
    SCase "m = 0". simpl. intro H. intro Hcontra. inversion Hcontra.
    SCase "m = S m". simpl. intro H. intro Heq. apply IHn with (m:=m). apply H. inversion Heq. reflexivity.

  Qed.

