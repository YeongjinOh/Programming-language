Require Export D.


Theorem ceval_deterministic: forall c st st1 st2,
     c / st || st1 ->
     c / st || st2 ->
     st1 = st2.

Proof.
  intros c st st1 st2 E1 E2.

  generalize dependent st2.
  ceval_cases (induction E1) Case; intros st2 E2.
(*; inversion E2; subst; try reflexivity *)
  inversion E2. reflexivity.
  inversion E2.  subst. reflexivity.
  inversion E2. subst. rewrite IHE1_2 with st2. reflexivity. apply IHE1_1 in H1. rewrite H1. apply H4.
  inversion E2; subst. 
    SCase "true". apply IHE1. apply H6. 
    SCase "false". rewrite H in H5. inversion H5.
  inversion E2; subst.
    SCase "true". rewrite H in H5. inversion H5.
    SCase "false". apply IHE1. apply H6.
  inversion E2. 
    SCase "false". reflexivity.
    SCase "true". rewrite H in H2. inversion H2.
  inversion E2. subst. rewrite H in H4. inversion H4.
  subst. apply IHE1_2. apply IHE1_1 in H3. rewrite<-H3 in H6. apply H6.
Qed.



(** **** Exercise: 3 stars (loop_never_stops)  *)
Theorem loop_never_stops : forall st st',
  ~(loop / st || st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef eqn:Heqloopdef.
    (* Proceed by induction on the assumed derivation showing that
     [loopdef] terminates.  Most of the cases are immediately
     contradictory (and so can be solved in one step with
     [inversion]). *)
  induction contra; inversion Heqloopdef; subst.
(*  induction loopdef; inversion Heqloopdef. *)
  Case "E_WhileEnd". inversion H.
  Case "E_WhileLoop". apply IHcontra2. reflexivity.
Qed.

