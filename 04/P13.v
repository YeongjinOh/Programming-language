Require Export D.



(** **** Problem #12 : 2 stars, optional (silly_ex)  *)
(** Complete the following proof without using [simpl]. 
    Hint: Use the [apply] tactic. *)

Theorem silly_ex : 
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  exact GIVEUP.
Qed.

