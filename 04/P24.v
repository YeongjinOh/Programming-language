Require Export D.



(** **** Problem #23 : 2 stars (destruct_eqn_practice)  *)
Theorem bool_fn_applied_thrice : 
  forall (f : bool -> bool) (b : bool), 
  f (f (f b)) = f b.
Proof.
  intros. destruct b. destruct (f true) eqn:a. rewrite -> a. apply a.
  destruct (f false) eqn:af. apply a. apply af.
  destruct (f false) eqn:af.  destruct (f true) eqn:atr. apply atr. apply af. rewrite -> af. apply af.
  Qed.

