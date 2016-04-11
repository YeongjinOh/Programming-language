Require Export D.



(** 2 stars, advanced (double_neg_inf)  *)
Theorem double_neg_inf: forall (P: Prop),
  P -> ~~P.
Proof.
  intros P H. unfold not. intros HPF. apply HPF in H. inversion H. 
Qed.

