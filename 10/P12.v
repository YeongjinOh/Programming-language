Require Export P11.



(** **** Exercise: 2 stars, advanced (hoare_asgn_weakest)  *)
(** Show that the precondition in the rule [hoare_asgn] is in fact the
    weakest precondition. *)

Theorem hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) (X ::= a) Q.
Proof.
  unfold is_wp. intros. split.
  Case "correctness".
    apply hoare_asgn.
  Case "weakestness".
    unfold assert_implies, assn_sub. intros.
    unfold update. unfold hoare_triple in H.
    pose proof H st. apply H1.
    constructor. reflexivity. assumption.
Qed.

