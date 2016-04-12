Require Export D.



(** 3 stars, advanced (beautiful__gorgeous)  *)


Lemma plus_assoc: forall a b c, 
  (a + b) + c = a + (b + c).
Proof. intros. induction a.
  Case "a = 0". reflexivity.
  Case "a = S a". simpl. rewrite -> IHa. reflexivity. Qed.

Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
  intros n m Hn Hm. induction Hn.
  Case "n = 0". simpl. apply Hm.
  Case "n = 3 + n0". rewrite -> plus_assoc. apply g_plus3. apply IHHn.
  Case "n = 5 + n0". rewrite -> plus_assoc. apply g_plus5. apply IHHn.  
  Qed.

Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
  intros n Hb. induction Hb.
  Case "n = 0". apply g_0.
  Case "n = 3". apply g_plus3. apply g_0.
  Case "n = 5". apply g_plus5. apply g_0.
  Case "n = n + m". apply gorgeous_sum.  apply IHHb1. apply IHHb2.
  Qed.
