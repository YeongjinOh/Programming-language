Require Export D.



(** **** Exercise: 2 stars (skip_right)  *)
(** Prove that adding a SKIP after a command results in an equivalent
    program *)

Theorem skip_right: forall c,
  cequiv 
    (c;; SKIP) 
    c.
Proof. 
  split; intros. inversion H; subst. inversion H5; subst. assumption.
  apply E_Seq with st'. assumption. apply E_Skip.
Qed.

