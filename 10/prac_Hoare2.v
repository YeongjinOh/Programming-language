Require Export D.

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Definition reduce_to_zero' : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    X ::= AMinus (AId X) (ANum 1)
  END.

Lemma not_true_iff_flase : forall b, 
  negb b = false -> b = true.
Proof. intros. destruct b. reflexivity.  inversion H. Qed.

Theorem reduce_to_zero_correct' :
  {{fun st => True}}
  reduce_to_zero'
  {{fun st => st X = 0}}.
Proof.
  unfold reduce_to_zero'.
  (* First we need to transform the postcondition so
     that hoare_while will apply. *)
  eapply hoare_consequence_post.
  apply hoare_while.
  Case "Loop body preserves invariant".
    (* Need to massage precondition before hoare_asgn applies *)
    eapply hoare_consequence_pre. apply hoare_asgn.
    (* Proving trivial implication (2) ->> (3) *)
    intros st [HT Hbp]. unfold assn_sub. apply I.
  Case "Invariant and negated guard imply postcondition".
    intros st [Inv GuardFalse].
    unfold bassn in GuardFalse. simpl in GuardFalse.
    (* SearchAbout helps to find the right lemmas *)
    SearchAbout [not true].
(*    rewrite not_true_iff_false in GuardFalse.*)
    SearchAbout [negb false].
    rewrite negb_false_iff in GuardFalse.
    SearchAbout [beq_nat true].
    apply beq_nat_true in GuardFalse.
    apply GuardFalse. Qed.

(*
  unfold hoare_triple. intros.
  unfold reduce_to_zero' in H.  inversion H; subst.
  Case "While Loop".
    inversion H5. destruct (beq_nat (st' X) 0) eqn:Heq. 
    apply beq_nat_eq. symmetry. assumption.
    inversion H2.
  Case "While End".
    inversion H3. destruct (beq_nat (st X) 0) eqn:Heq.
    inversion H2.  *)



Lemma le_sum : forall n m, n <= m -> S n <= S m.
  Proof. intros. omega. Qed.


Example while_example :
    {{fun st => st X <= 3}}
  WHILE (BLe (AId X) (ANum 2))
  DO X ::= APlus (AId X) (ANum 1) END
    {{fun st => st X = 3}}.
Proof. intros.
  eapply hoare_consequence_post. apply hoare_while.
  Case "True".
  unfold hoare_triple. intros.
  destruct H0. inversion H; subst.
  simpl. unfold update. rewrite eq_id. replace (st X + 1) with (S (st X)). apply le_sum. inversion H1. apply ble_nat_true. assumption. omega.
 Case "False". 
  unfold hoare_triple.  unfold assert_implies. intros.
  destruct H. inversion H. reflexivity.
  inversion H0. apply ble_nat_false in H4. apply H4 in H2. inversion H2. Qed.

Lemma hoare_while : forall P b c,
{{fun st => P st /\ bassn b st }} c {{P}} ->
{{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  unfold hoare_triple.
  intros P b c Hhoare st st' He HP.
  (* Like we've seen before, we need to reason by induction 
     on He, because, in the "keep looping" case, its hypotheses 
     talk about the whole loop instead of just c. *)
  remember (WHILE b DO c END) as wcom eqn:Heqwcom.
  ceval_cases (induction He) Case;
    (* While 이외의 command는 inversion으로 없어짐 *)
    try (inversion Heqwcom); subst; clear Heqwcom.
  Case "E_WhileEnd".
    split; try assumption. unfold not, bassn. rewrite H. intros Hcontra. inversion Hcontra.
  Case "E_WhileLoop".
  apply IHHe2. reflexivity.
  eapply Hhoare. apply He1. split; assumption. Qed.


(* command에 induction inversion 차이 *)
Lemma hoar : forall b' c c' st st', WHILE b' DO c' END = c -> c / st||st'-> True.
Proof. intros. induction H0; subst; inversion H; subst.
  (* E_WhilEnd *) reflexivity.
  (* E_WhileLoop *) reflexivity.
Qed.

Example while_example2 :
    {{fun st => st X <= 3}}
  WHILE (BLe (AId X) (ANum 2))
  DO X ::= APlus (AId X) (ANum 1) END
    {{fun st => st X = 3}}.
Proof. 
  eapply hoare_consequence_post.
  Case "{{P}} c {{Q'}}".
    apply hoare_while.
    unfold hoare_triple; intros.
    destruct H0. inversion H1. apply ble_nat_true in H3. inversion H; subst. unfold update. rewrite eq_id. simpl. replace (st X + 1) with (S (st X)). apply le_sum. assumption. omega.
  Case "Q' ->> Q". 
    unfold hoare_triple, assert_implies. intros.
    destruct H. inversion H. reflexivity.
    unfold not, bassn in H0. simpl in H0. 
    destruct (ble_nat (st X) 2) eqn:Hb. contradiction H0. reflexivity. 
    apply ble_nat_false in Hb. apply Hb in H2. inversion H2.
Qed.

Theorem always_loop_hoare : forall P Q,
  {{P}} WHILE BTrue DO SKIP END {{Q}}.
Proof. 
  intros. eapply hoare_consequence_post. apply hoare_while.
  unfold bassn, hoare_triple. intros. inversion H; subst. apply H0.
  unfold bassn, hoare_triple, assert_implies. intros. destruct H.
  simpl in H0. contradiction H0. reflexivity. Qed.


Theorem reduce_to_zero_correct'_one_more :
  {{fun st => True}}
  reduce_to_zero'
  {{fun st => st X = 0}}.
Proof. 
  unfold reduce_to_zero'.
  eapply hoare_consequence_post.
  Case "{{P}} c {{Q'}}".
    apply hoare_while. (* Q' = P/\~b 이 되고, P/\b c P 임을 보이자 *)
    unfold bassn, hoare_triple. intros. reflexivity.
  Case "Q' ->> Q".
   (* P/\~b ->> Q 임을 보이면 된다. *)
    unfold hoare_triple, bassn, assert_implies. intros.
    destruct H. simpl in H0. apply eq_true_negb_classical in H0.
    symmetry in H0. apply beq_nat_eq in H0. assumption.
Qed.


