Require Export D.



Theorem snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
 intros. induction l. reflexivity.
 simpl. rewrite -> IHl. reflexivity.
Qed.

