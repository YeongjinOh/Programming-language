Require Export D.



(** 1 star, optional (or_distributes_over_and)  *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. split.
  Case "only if". intros H. destruct H as [HP|[HQ HR]].
    SCase "left". apply conj. left. apply HP. left. apply HP.
    SCase "right". apply conj. right. apply HQ. right. apply HR.
  Case "if". intros H. destruct H as [HPQ HPR]. 
    destruct HPQ as [HP|HQ]. left. apply HP.
    destruct HPR as [HP|HR]. left. apply HP.
    right. apply conj. apply HQ. apply HR.
Qed.

