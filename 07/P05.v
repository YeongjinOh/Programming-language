Require Export D.



(** **** Exercise: 1 star (update_eq)  *)
Theorem update_eq : forall n x st,
  (update st x n) x = n.
Proof.
  intros. unfold update. apply eq_id.
Qed.

