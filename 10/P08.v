Require Export P07.



(** The postcondition does not hold at the beginning of the loop,
    since [m = parity m] does not hold for an arbitrary [m], so we
    cannot use that as an invariant.  To find an invariant that works,
    let's think a bit about what this loop does.  On each iteration it
    decrements [X] by [2], which preserves the parity of [X].  So the
    parity of [X] does not change, i.e. it is invariant.  The initial
    value of [X] is [m], so the parity of [X] is always equal to the
    parity of [m]. Using [parity X = parity m] as an invariant we
    obtain the following decorated program:
    {{ X = m }} ->>                              (a - OK)
    {{ parity X = parity m }}
  WHILE 2 <= X DO
      {{ parity X = parity m /\ 2 <= X }}  ->>    (c - OK)
      {{ parity (X-2) = parity m }}
    X ::= X - 2
      {{ parity X = parity m }}
  END
    {{ parity X = parity m /\ X < 2 }}  ->>       (b - OK)
    {{ X = parity m }}

    With this invariant, conditions (a), (b), and (c) are all
    satisfied. For verifying (b), we observe that, when [X < 2], we
    have [parity X = X] (we can easily see this in the definition of
    [parity]).  For verifying (c), we observe that, when [2 <= X], we
    have [parity X = parity (X-2)]. *)


(** **** Exercise: 3 stars, optional (parity_formal)  *)
(** Translate this proof to Coq. Refer to the reduce-to-zero example
    for ideas. You may find the following two lemmas useful: *)

Lemma parity_ge_2 : forall x,
  2 <= x ->
  parity (x - 2) = parity x.
Proof.
  induction x; intro. reflexivity.
  destruct x. inversion H. inversion H1.
  simpl. rewrite <- minus_n_O. reflexivity.
Qed.

Lemma parity_ge_2_big : forall x,
  parity x = parity (x + 2).
intros. 
  destruct x. reflexivity.
  destruct x. reflexivity.
  replace (S (S x)) with (S (S x) + 2 - 2).
  replace (S (S x) + 2 - 2 + 2) with (S (S x) + 2).
  apply parity_ge_2. omega. omega. omega. Qed.

Lemma parity_lt_2 : forall x,
  ~ 2 <= x ->
  parity (x) = x.
Proof.
  intros. induction x. reflexivity. destruct x. reflexivity.
    apply ex_falso_quodlibet. apply H. omega.
Qed.

Theorem parity_correct : forall m,
    {{ fun st => st X = m }}
  WHILE BLe (ANum 2) (AId X) DO
    X ::= AMinus (AId X) (ANum 2)
  END
    {{ fun st => st X = parity m }}.
Proof.
  intros m.
  apply hoare_consequence_pre with (P':= (fun st => (parity (st X) = parity m))).
  Case "{{I}} while {{Q}}".
    eapply hoare_consequence_post. apply hoare_while.
    SCase "{{I /\ b}} c {{I}}".
      unfold hoare_triple. intros.
      assert (Hle : 2 <= st X).
        destruct H0. 
        simpl in H1. destruct (st X) eqn:Hx. inversion H1.
        destruct n eqn:Hn. inversion H1. omega.
      inversion H; subst. simpl. unfold update. 
      rewrite eq_id. rewrite parity_ge_2. apply H0. assumption.
      
    SCase "I/\~b ->> Q".
      unfold hoare_triple, assert_implies. intros.
      destruct H. rewrite<-H. symmetry.
      apply parity_lt_2.
      unfold not. intros.
      simpl in H0. destruct (st X). inversion H1.
      destruct n. inversion H1. inversion H3.
      inversion H0.
  Case "P ->> I".
    unfold assert_implies. intros. rewrite H. omega.
Qed.

