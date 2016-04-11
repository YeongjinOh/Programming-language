Require Export D.



(** 1 star (not_both_true_and_false)  *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof. 
  intros P. unfold not. intros contra.
  destruct contra as [HP HNP]. apply HNP in HP. inversion HP.
Qed.

