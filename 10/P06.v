Require Export P05.



(** **** Exercise: 2 stars (slow_assignment)  *)
(** A roundabout way of assigning a number currently stored in [X] to
    the variable [Y] is to start [Y] at [0], then decrement [X] until
    it hits [0], incrementing [Y] at each step. Here is a program that
    implements this idea:
      {{ X = m }}
    Y ::= 0;;
    WHILE X <> 0 DO
      X ::= X - 1;;
      Y ::= Y + 1
    END
      {{ Y = m }} 
    Write an informal decorated program showing that this is correct. *)

Theorem slow_assignment : forall m,
    {{ fun st => st X = m }}
    Y ::= ANum 0;;
    WHILE BNot (BEq (AId X) (ANum 0)) DO
      X ::= AMinus (AId X) (ANum 1);;
      Y ::= APlus (AId Y) (ANum 1)
    END
    {{ fun st => st Y = m }}.
Proof. intros.
  (* {{P}} c;;while {{R}} *)
  eapply hoare_seq with (Q:= (fun st => st X + st Y= m)). (* Q = P /\ Y=0 *)
  Case "{{Q}} while {{R}} ". eapply hoare_consequence_post. 
    SCase "{{Q}} while {{R'}}". apply hoare_while. (* R' = Q/\~b *)
    (* now need to show that {{Q/\b}} c1;;c2 {{Q}} *)
    simpl. eapply hoare_seq.
      SSCase "{{Q'}} c2 {{R'}}".
        apply hoare_asgn.
      SSCase "{{Q/\b}} c1 {{Q'}}".
        eapply hoare_consequence_pre. 
        (* {{Q''}} c1 {{Q'}} *) apply hoare_asgn.
        (* Q/\b ->> Q'' *) unfold assert_implies, assn_sub. intros; simpl.
        unfold update. simpl. destruct H. rewrite<-H. 
        apply negb_true_iff in H0. apply beq_nat_false_iff in H0.
        (* We need the condition that xt X > 0 to use omega here *) omega.
    SCase "R' ->> R".
  unfold hoare_triple, assert_implies. intros.
  destruct H. simpl in H0. apply negb_false in H0. apply beq_nat_true_iff in H0. omega.

  Case "{{P}} c {{Q}}".
    unfold hoare_triple. intros. inversion H; subst. simpl.
    unfold update. simpl. omega.
Qed.
