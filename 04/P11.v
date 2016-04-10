Require Export D.



(** **** Problem #10 : 2 stars (fold_length) *)
(** Many common functions on lists can be implemented in terms of
   [fold].  For example, here is an alternative definition of [length]: *)

Print fold_length.

(** Prove the correctness of [fold_length]. *)

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  exact GIVEUP.
Qed.

