Require Export D.

(** 2 stars (contrapositive)  *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H. intros HNQ. unfold not. intros HQ.
  apply H in HQ. unfold not in HNQ. apply HNQ in HQ. inversion HQ.
Qed.

