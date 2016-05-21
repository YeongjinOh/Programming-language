Require Export P10.



(** **** Exercise: 3 stars, advanced, optional (is_wp_formal)  *)
(** Prove formally using the definition of [hoare_triple] that [Y <= 4]
   is indeed the weakest precondition of [X ::= Y + 1] with respect to
   postcondition [X <= 5]. *)

Theorem is_wp_example :
  is_wp (fun st => st Y <= 4)
    (X ::= APlus (AId Y) (ANum 1)) (fun st => st X <= 5).
Proof.
  unfold is_wp. split. 
  Case "correct precondition".
    unfold hoare_triple. intros.
    inversion H; subst. unfold update; simpl. omega.
  Case "weakestness".  
    unfold assert_implies. intros.
    unfold hoare_triple in H.
    pose proof H st (update st X (aeval st (APlus (AId Y) (ANum 1)))). simpl in H1.
    assert ((X ::= (APlus (AId Y) (ANum 1))) /  st || update st X (st Y + 1)). constructor. simpl. reflexivity.
    apply H1 in H2. unfold update in H2. simpl in H2. omega.
    assumption.
Qed.

