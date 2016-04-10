Require Export D.



(** **** Problem #13 : 3 stars (apply_exercise1)  *)
(** Hint: you can use [apply] with previously defined lemmas, not
    just hypotheses in the context.  Remember that [SearchAbout] is
    your friend. *)

Lemma rev_involutive : forall l : list nat,
  rev (rev l) = l.
Proof.
  intros. induction l. reflexivity.
  Lemma rev_snoc_lemma : forall n:nat, forall l:list nat,
    rev (n :: l) = snoc (rev l) n.
  Proof. intros. reflexivity. Qed.
  rewrite -> rev_snoc_lemma. simpl.
  Lemma rev_snoc_lemma2 : forall n:nat, forall l:list nat,
    rev (snoc l n) = n :: rev l.
  Proof. intros. induction l. reflexivity.
  simpl. rewrite -> IHl. simpl. reflexivity. Qed.
  rewrite -> rev_snoc_lemma2. rewrite -> IHl. reflexivity.
  
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     rev l = l'.
Proof.
 intros.
   rewrite -> H.  apply rev_involutive.
Qed.

