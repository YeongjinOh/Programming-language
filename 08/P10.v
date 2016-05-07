Require Export D.



(** **** Exercise: 2 stars, optional (seq_assoc)  *)
Theorem seq_assoc : forall c1 c2 c3,
  cequiv ((c1;;c2);;c3) (c1;;(c2;;c3)).
Proof.
  intros. split; intros.
  Case "->". inversion H; subst. inversion H2; subst.
  apply E_Seq with st'1. assumption. apply E_Seq with st'0; assumption.
  Case "<-". inversion H; subst. inversion H5; subst. apply E_Seq with st'1. apply E_Seq with st'0; assumption. assumption.
  Qed.

