Require Export D.



(** Hint: You may need to first state and prove some lemma about snoc and rev. *)
Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros. induction l. reflexivity.
  Lemma rev_snoc_lemma : forall n:nat, forall l:natlist,
    rev (n :: l) = snoc (rev l) n.
  Proof. intros. reflexivity. Qed.
  rewrite -> rev_snoc_lemma. simpl.
  Lemma rev_snoc_lemma2 : forall n:nat, forall l:natlist,
    rev (snoc l n) = n :: rev l.
  Proof. intros. induction l. reflexivity.
  simpl. rewrite -> IHl. simpl. reflexivity. Qed.
  rewrite -> rev_snoc_lemma2. rewrite -> IHl. reflexivity.
  
Qed.

