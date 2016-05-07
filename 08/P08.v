Require Export D.



(** **** Exercise: 3 stars (swap_if_branches)  *)
(** Show that we can swap the branches of an IF by negating its
    condition *)

Lemma bool_negb : forall b1 b2,
  negb b1 = b2 -> b1 = negb b2.
Proof. intros. destruct b1; destruct b2; try inversion H; try reflexivity. Qed.


Theorem swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  split; intros.
  Case "->". inversion H; subst. 
    SCase "True". apply E_IfFalse. simpl. rewrite H5. reflexivity. assumption.
    SCase "False". apply E_IfTrue. simpl. rewrite H5. reflexivity.  assumption.
  Case "<-".  inversion H; subst. inversion H5. 
    SCase "False". apply E_IfFalse. simpl. apply bool_negb in H1;simpl in H1. assumption. assumption.
    SCase "True". apply E_IfTrue. simpl in H5. apply bool_negb in H5. simpl in H5. assumption. assumption.
  Qed.

