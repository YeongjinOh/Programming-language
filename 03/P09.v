Require Export D.



(** **** Problem #5  : 4 stars, advanced (rev_injective) *)

(** Hint: You can use the lemma [rev_involutive]. *)
Theorem rev_injective: forall l1 l2 : natlist, 
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros.
  Lemma rev_involutive : forall l:natlist,
    rev (rev l) = l.
  Proof. intros. induction l. reflexivity.
    simpl.
    Lemma rev_snoc_lemma : forall l:natlist, forall n:nat,
       rev (snoc l n) = n:: rev l.
       Proof. intros. induction l. reflexivity. simpl. rewrite -> IHl. reflexivity. Qed.
       rewrite -> rev_snoc_lemma. rewrite -> IHl. reflexivity. Qed.
  (* End of proof of Lemma rev_involutive *)
  
  Lemma rev_injective_inverse : forall l1 l2 : natlist,
    l1 = l2 -> rev l1 = rev l2.
  Proof.
    intros. induction l1. induction l2. reflexivity.
    rewrite <- H. reflexivity.
    induction l2. rewrite -> H. reflexivity.
    rewrite -> H.  reflexivity.
  Qed.
  assert (H2 : l1 = rev (rev l1)).
  rewrite rev_involutive. reflexivity.
  assert (H3 : l2 = rev (rev l2)).
  rewrite rev_involutive. reflexivity.
  rewrite -> H2. rewrite -> H3.
  apply rev_injective_inverse. apply H.
  
  Qed.

