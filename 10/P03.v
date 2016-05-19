Require Export P02.



(** **** Exercise: 4 stars (hoare_asgn_wrong)  *)
(** The assignment rule looks backward to almost everyone the first
    time they see it.  If it still seems backward to you, it may help
    to think a little about alternative "forward" rules.  Here is a
    seemingly natural one:
      ------------------------------ (hoare_asgn_wrong)
      {{ True }} X ::= a {{ X = a }}
    Give a counterexample showing that this rule is incorrect
    (informally). Hint: The rule universally quantifies over the
    arithmetic expression [a], and your counterexample needs to
    exhibit an [a] for which the rule doesn't work. *)

Theorem hoare_asgn_wrong:
  exists a, ~ {{ fun st => True }} X ::= a {{ fun st => st X = aeval st a}}.
Proof.
  remember (update empty_state X 1) as st.
  remember (APlus (AId X) (ANum 1)) as Xnext.
  remember (update st X (aeval st Xnext)) as st'.
  exists  Xnext.
  unfold not. intros.
  unfold hoare_triple in H.
  pose proof H st st'; clear H.
  assert (st' X = aeval st' Xnext -> False).
   rewrite Heqst'; rewrite Heqst; rewrite HeqXnext. simpl. unfold update. rewrite eq_id. intro. inversion H.
  apply H. apply H0. rewrite Heqst'. apply E_Ass. reflexivity.
  reflexivity. Qed.

