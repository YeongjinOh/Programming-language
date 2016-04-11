Require Export D.



(** 2 stars, optional (orb_false_elim)  *)
Theorem orb_false_elim : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof. 
  intros b c H. destruct b.
  Case "b=true". inversion H.
  Case "b=false". destruct c.
    SCase "c=true". inversion H.
    SCase "c=false". apply conj. reflexivity. reflexivity.
Qed.

