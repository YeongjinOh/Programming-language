Require Export D.



(** **** Problem #15 : 1 star (sillyex1) 
    Hint: Use the [inversion] tactic. *) 
Example sillyex1 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = z :: j ->
     y :: l = x :: j ->
     x = y.
Proof.
  exact GIVEUP.
Qed.

