Require Export D.



(** **** Exercise: 2 stars (dist_exists_or)  *)
(** Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros. split.
  Case "->". intros. destruct H as [x H]. inversion H.
    SCase "P x". left. exists x. assumption.     
    SCase "Q x". right. exists x. assumption.
  Case "<-". intros. destruct H.
    SCase "P x". destruct H as [x]. exists x. left. assumption.
    SCase "Q x". destruct H as [x]. exists x. right. assumption.
Qed.
