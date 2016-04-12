Require Export D.



(** 1 star (inversion_practice)  *)
Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros. inversion H. inversion pf_evn. apply pf_evn0. 
  Qed.
