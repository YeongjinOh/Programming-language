Require Export P06.



(** **** Exercise: 3 stars, optional (add_slowly_decoration)  *)
(** The following program adds the variable X into the variable Z
    by repeatedly decrementing X and incrementing Z.
  WHILE X <> 0 DO
     Z ::= Z + 1;;
     X ::= X - 1
  END

    Following the pattern of the [subtract_slowly] example above, pick
    a precondition and postcondition that give an appropriate
    specification of [add_slowly]; then (informally) decorate the
    program accordingly. *)

Theorem slow_addition_dec_correct : forall n m,
  {{fun st => st X = n /\ st Y = m }}
  WHILE BNot (BEq (AId X) (ANum 0)) DO
     Y ::= APlus (AId Y) (ANum 1);;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{fun st => st Y = n + m}}.
Proof. intros n m.
  apply hoare_consequence_pre with (P':= (fun st => st X + st Y = n + m )).
  Case "{{P'}} while {{Q}}".
    eapply hoare_consequence_post.
    SCase "{{P'} while {{P'/\~b}}".
      apply hoare_while.  (* now P'/\b c1;;c2 P' *)
      eapply hoare_seq.
      SSCase "{{P''}} c2 {{P'}}". apply hoare_asgn.
      SSCase "{{P'/\b}} c1 {{P''}}".
        eapply hoare_consequence_pre. apply hoare_asgn.
        unfold assert_implies, assn_sub. intros.
        unfold update; simpl. destruct H. simpl in H0.
        apply negb_true_iff in H0. apply beq_nat_false_iff in H0.
        omega.
    SCase "P'/\~b ->> Q".
      unfold assert_implies. intros.
      destruct H. simpl in H0. apply negb_false_iff in H0. apply beq_nat_true_iff in H0. omega.
  Case "P' ->> P".
    unfold assert_implies. intros. omega.
Qed.

