Require Export D.



(** 1 star (gorgeous_plus13)  *)
Theorem gorgeous_plus13: forall n, 
  gorgeous n -> gorgeous (13+n).
Proof.
  intros. apply g_plus3. apply g_plus5. apply g_plus5. apply H.
  Qed.
