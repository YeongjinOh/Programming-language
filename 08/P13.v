Require Export D.



(** **** Exercise: 3 stars (CIf_congruence)  *)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).
Proof.
  unfold bequiv; unfold cequiv; split; intros.
  Case "->". inversion H2; subst.
    apply E_IfTrue.  rewrite<-H;  apply H8. apply H0; assumption.
    apply E_IfFalse.  rewrite<-H;  apply H8. apply H1; assumption.
  Case "<-". inversion H2; subst. 
    apply E_IfTrue.  rewrite->H;  apply H8. apply H0; assumption.
    apply E_IfFalse.  rewrite->H;  apply H8. apply H1; assumption.
 
  Qed.

