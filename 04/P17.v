Require Export D.



(** **** Problem #16 : 1 star (sillyex2)  
    Hint: use the [inversion] tactic. *)
Example sillyex2 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = [] ->
     y :: l = z :: j ->
     x = z.
Proof.
  exact GIVEUP.
Qed.

