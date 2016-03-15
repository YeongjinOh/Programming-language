Require Export D.



(** **** Problem #3 : 2 stars (boolean functions) *)
(** Use the tactics you have learned so far to prove the following 
    theorem about boolean functions. *)

Theorem negation_fn_applied_twice : 
  forall (f : bool -> bool), 
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  exact GIVEUP.
Qed.

