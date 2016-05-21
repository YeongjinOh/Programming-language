Require Export P09.



(** **** Exercise: 3 stars (two_loops)  *)
(** Here is a very inefficient way of adding 3 numbers:
  X ::= 0;;
  Y ::= 0;;
  Z ::= c;;
  WHILE X <> a DO
    X ::= X + 1;;
    Z ::= Z + 1
  END;;
  WHILE Y <> b DO
    Y ::= Y + 1;;
    Z ::= Z + 1
  END

    Show that it does what it should by filling in the blanks in the
    following decorated program.

    {{ True }} ->>
    {{  c = c + 0 + 0  }}
  X ::= 0;;
    {{  c = c + X + 0  }}
  Y ::= 0;;
    {{  c = c + X + Y  }}
  Z ::= c;;
    {{  Z = c + X + Y  }}
  WHILE X <> a DO
      {{  Z = c + X + Y  /\  X <> a }} ->>
      {{  Z = c + X + Y [Z |-> Z + ] [X |-> X + 1] }}
    X ::= X + 1;;
      {{  Z = c + X + Y [Z |-> Z + 1]   }}
    Z ::= Z + 1
      {{  Z = c + X + Y  }}
  END;;
    {{ Z = c + X + Y /\  X = a }} ->>
    {{ Z = c + a + Y  }}
  WHILE Y <> b DO
      {{ Z = c + a + Y  /\  Y <> b  }} ->>
      {{ Z = c + a + Y [Z |-> Z + 1] [Y |-> Y + 1] }}
    Y ::= Y + 1;;
      {{ Z = c + a + Y [Z |-> Z + 1] }}
    Z ::= Z + 1
      {{ Z = c + a + Y }}
  END
    {{ Z = c + a + Y  /\ Y = b  }} ->>
    {{ Z = c + a + b }}
*)
  Lemma aeval_ANum_same : forall st n m, aeval st (ANum n) = m -> n = m.
  Proof. intros st n. induction n; intros. inversion H. reflexivity.
  inversion H. simpl. reflexivity. Qed.
 
Theorem add_three_numbers_correct: forall a b c,
  {{ fun st => True }}                                   
  X ::= ANum 0;;
  Y ::= ANum 0;;
  Z ::= ANum c;;
  WHILE BNot (BEq (AId X) (ANum a)) DO
    X ::= APlus (AId X) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END;;
  WHILE BNot (BEq (AId Y) (ANum b)) DO
    Y ::= APlus (AId Y) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END
  {{ fun st => st Z = a + b + c }}.
Proof.
  intros.
    apply hoare_consequence_pre with (P':= (fun st => c = 0 + 0 + c)).
    Case "{{P'}} c1;;c2;;c3;;while1;;while2 {{R}}".
      apply hoare_seq with (Q:= (fun st => c = st X + 0 + c)).
      (* {{P1}} c2;;c3;;while {{R}} *)
      apply hoare_seq with (Q:= (fun st => c = st X + st Y + c)).
      (* {{P2}} c3;;while {{R}} *)
      apply hoare_seq with (Q:= (fun st => st Z = st X + st Y + c)).
      (* {{P3}} while1;;while2 {{R}} *)
      apply hoare_seq with (Q:= (fun st => st Z = st X + st Y + c /\ st X = a)).
      SCase "{{Q}} while2 {{R}}".
        apply hoare_consequence with (P':= (fun st => st Z = c + a + st Y)) (Q':= (fun st => st Z = c + a + st Y /\ st Y = b)).
        SSCase "{{Q'}} while2 {{R'}}".
          eapply hoare_consequence_post. apply hoare_while.
          eapply hoare_seq. apply hoare_asgn.
          eapply hoare_consequence_pre. apply hoare_asgn.
          unfold assert_implies, assn_sub. intros.
          unfold update; simpl. destruct H; rewrite H. omega.
          unfold assert_implies. intros.
          destruct H. simpl in H0. apply negb_false_iff in H0.
          apply beq_nat_true_iff in H0. split; assumption.
        SSCase "Q ->> Q'".
          unfold assert_implies, assn_sub, update. intros. omega.
        SSCase "R' ->> R".
          unfold assert_implies, assn_sub, update. intros. omega.
      SCase "{{P3}} while1 {{Q}}".
        eapply hoare_consequence_post. apply hoare_while.
        eapply hoare_seq. apply hoare_asgn.
        eapply hoare_consequence_pre. apply hoare_asgn.
        unfold assert_implies, assn_sub, update. intros. simpl. omega.
        unfold assert_implies, assn_sub, update. intros.
        destruct H. simpl in H0. apply negb_false_iff in H0.
        apply beq_nat_true_iff in H0. split; assumption.
      SCase "{{P2}} c3 {{P3}}".
        unfold hoare_triple. intros. inversion H.
        unfold update. simpl. rewrite<-H0.
        symmetry. apply (aeval_ANum_same st). assumption.
      SCase "{{P1}} c2 {{P2}}".
        unfold hoare_triple.  intros. inversion H.
        unfold update. simpl. rewrite H0. apply aeval_ANum_same in H5. rewrite H5. omega.
      SCase "{{P'}} c1 {{P1}}".
        unfold hoare_triple. intros. inversion H.
        apply aeval_ANum_same in H5. unfold update. simpl. omega.
  Case "P =>> P'".
    unfold assert_implies. intros.  omega.
Qed.

