Require Export D.



Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  intros. induction l1. 
  induction l2. reflexivity.
  simpl. 
  Lemma any_app_nul : forall l:natlist,
    l = l ++ [].
  Proof. intros. induction l. reflexivity. simpl. rewrite <- IHl. reflexivity. Qed.
  rewrite <- any_app_nul. reflexivity.
  simpl. rewrite -> IHl1. simpl.
  Lemma snoc_app_input : forall n:nat, forall l1 l2:natlist,
    snoc (l1 ++ l2) n = l1 ++ snoc l2 n.
  Proof.
    intros. induction l1. reflexivity.
    simpl. rewrite -> IHl1. reflexivity. Qed.
    rewrite -> snoc_app_input. reflexivity.

Qed.

