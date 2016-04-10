Require Export D.



(** **** Problem #14 : 3 stars, optional (apply_with_exercise)  
    Hint: Use the [apply ... with ...] tactic. *)

Check trans_lt.

Example trans_eq_exercise : forall (n m o p : nat),
     (minustwo o) < m ->
     (n + p) < (minustwo o) ->
     (n + p) < m. 
Proof.
  exact GIVEUP.
Qed.

