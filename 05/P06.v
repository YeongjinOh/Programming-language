Require Export D.



(** 2 stars, optional (orb_false)  *)
Theorem orb_prop : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  intros b c H. destruct b.
  Case "b=true". left. reflexivity. 
  Case "b=false". destruct c.
    SCase "c=true". right. reflexivity.
    SCase "c=false". inversion H.
  Qed.

