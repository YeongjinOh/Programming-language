Require Export P08.



(** **** Exercise: 4 stars (factorial)  *)
(** Recall that [n!] denotes the factorial of [n] (i.e. [n! =
    1*2*...*n]).  Here is an Imp program that calculates the factorial
    of the number initially stored in the variable [X] and puts it in
    the variable [Y]:
    {{ X = m }} 
  Y ::= 1 ;;
  WHILE X <> 0
  DO
     Y ::= Y * X ;;
     X ::= X - 1
  END
    {{ Y = m! }}

    Fill in the blanks in following decorated program:
    {{ X = m }} ->>
    {{ (st X)! * Y = m! [Y|->1]}}
  Y ::= 1;;
    {{ (st X)! * Y = m! }} : I
  WHILE X <> 0
  DO   {{  I  /\ X <> 0         }} ->>
       {{    I [Y |-> Y*X] [X |-> X-1]         }}
     Y ::= Y * X;;
       {{    I [X |-> X-1]                     }}
     X ::= X - 1
       {{    I                                 }}
  END
    {{ (st X)! * Y = m!  /\  st X = 0 }} ->>
    {{ Y = m! }}
*)

Print fact.

Lemma mult_dist_l : forall a b c,
  a * (b + c) = a * b + a * c.
Proof. intros. induction a. reflexivity.
  simpl. rewrite IHa. omega. Qed.
Lemma mult_dist_r : forall a b c,
(a + b) * c = a * c + b * c.
Proof. intros. rewrite mult_comm. rewrite mult_dist_l. 
  rewrite mult_comm. replace (c*b) with (b*c). omega. apply mult_comm. Qed.

Lemma fact_mult : forall m,
  m <> 0 -> fact (m - 1) * m = fact m.
Proof. intros. induction m. contradiction H. reflexivity.
  simpl. replace (m-0) with m. replace (S m) with (1 + m).
  rewrite mult_dist_l. rewrite mult_comm. simpl. rewrite mult_comm. omega. omega. omega. Qed.

Theorem factorial_dec_correct: forall m,
  {{ fun st => st X = m }} 
  Y ::= ANum 1 ;;
  WHILE BNot (BEq (AId X) (ANum 0))
  DO
     Y ::= AMult (AId Y) (AId X) ;;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{ fun st => st Y = fact m }}.
Proof.
  intros m. eapply hoare_consequence with (P':= (fun st=> fact (st X) * st Y = fact m)[Y|->ANum 1]) (Q':= (fun st => fact (st X) * st Y = fact m /\ st X = 0)).
  Case "{{P'}} c;;while {{Q'}}".
    apply hoare_seq with (Q:= (fun st=> fact (st X) * st Y = fact m )). (* Q = I *)
    SCase "{{I}} while {{Q'}}".
      eapply hoare_consequence_post. apply hoare_while.
      SSCase "{{I/\b}} c1;;c2 {{I}}".
        eapply hoare_seq. (* {{I'}} c2 {{I}} *) apply hoare_asgn.
        (* {{I/\b}} c1 {{I'}} *)
        eapply hoare_consequence_pre. apply hoare_asgn.
        unfold assert_implies, assn_sub. simpl. intros.
        unfold update. simpl.
        destruct H. destruct H.
        apply negb_true_iff in H0. apply beq_nat_false_iff in H0.
        replace (st Y * st X) with (st X * st Y).
        rewrite mult_assoc. rewrite fact_mult. omega. assumption.
        apply mult_comm.
      SSCase "I ->> Q'".
        unfold hoare_triple, assert_implies. intros.
        destruct H. simpl in H0. apply negb_false_iff in H0. apply beq_nat_true_iff in H0. split; assumption.
    SCase "{{P'}} c {{I}}".
      apply hoare_asgn. 
  Case "P ->> P'".
    unfold assert_implies, assn_sub.  intros.
    unfold update. simpl. rewrite H. omega.
  Case "Q' ->> Q".
    unfold assert_implies. intros.
    destruct H.  rewrite H0 in H. rewrite<-H. simpl. omega.
Qed.

