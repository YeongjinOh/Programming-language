Require Export D.


(** 2 stars (false_beq_nat)  *)
Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof.
  unfold not. intros n m. generalize dependent m. induction n.
  Case "n = 0". induction m. intro H.
    SCase "m = 0". simpl. 
     Lemma ex_falso : forall P:Prop, False -> P.
      Proof. intros P Hcontra. inversion Hcontra. Qed.
     apply ex_falso. apply H. reflexivity.
    SCase "m = S m". intro H. reflexivity.
  Case "n = S n". induction m.
    SCase "m = 0". intro H. reflexivity.
    SCase "m = S m".  intro H. simpl. apply IHn. intro Heq.
      apply H. rewrite -> Heq. reflexivity.
Qed.

