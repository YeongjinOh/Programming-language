Require Export P04.

Lemma optimize_0plus_com_sound:
  ctrans_sound optimize_0plus_com.
Proof.
  unfold ctrans_sound. intros. unfold cequiv.
  com_cases (induction c) Case; intros.
  (* SKIP *)
  reflexivity.
  (* Ass *)
  simpl. split; intros. 
  SCase "->". inversion H; subst. apply E_Ass. symmetry. apply optimize_0plus_aexp_sound.
  SCase "<-". inversion H; subst. rewrite<-optimize_0plus_aexp_sound. apply E_Ass. reflexivity.
  (* ;; *)
  simpl.
  split; intros; inversion H; subst;
  assert (c1 / st || st'0 <-> optimize_0plus_com c1 / st || st'0); try apply IHc1;
  assert (c2 / st'0 || st' <-> optimize_0plus_com c2 / st'0 || st'); try apply IHc2;
  destruct H0 as [Hc1 Hoc1]; destruct H1 as [Hc2 Hoc2]. 
  SCase "->";
  apply E_Seq with st'0; try apply Hc1; try apply Hc2; assumption.
  SCase "<-";
  apply E_Seq with st'0; try apply Hoc1; try apply Hoc2; assumption.
  (* IFB *)
  destruct (beval st b) eqn:Hb. 
  SCase "True". split; intros; apply E_IfTrue.
    (* -> *)rewrite<-optimize_0plus_bexp_sound; assumption. inversion H; subst. apply IHc1; assumption. rewrite H5 in Hb. inversion Hb. assumption.
    (* <- *) inversion H; subst. apply IHc1; assumption. rewrite<-optimize_0plus_bexp_sound in H5. rewrite H5 in Hb. inversion Hb. 
  SCase "False". split; intros.
    SSCase "->". 
    inversion H; subst. rewrite H5 in Hb; inversion Hb.
    apply E_IfFalse. rewrite<-optimize_0plus_bexp_sound; assumption. apply IHc2; assumption.
    SSCase "<-". 
    inversion H; subst. rewrite<-optimize_0plus_bexp_sound in H5. rewrite H5 in Hb; inversion Hb.
    apply E_IfFalse; try assumption. apply IHc2; try assumption.
  (* WHILE *)
  split; intros.
  SCase "->".  inversion H; subst. 
  SSCase "E_WhileEnd".
    apply E_WhileEnd. rewrite<-optimize_0plus_bexp_sound; assumption.
  SSCase "E_WhileLoop".
simpl.
Print cequiv.
  assert (HWhile : cequiv (WHILE b DO c END) (WHILE optimize_0plus_bexp b DO optimize_0plus_com c END)).
  apply CWhile_congruence.
  apply optimize_0plus_bexp_sound.
  unfold cequiv. apply IHc.
  unfold cequiv in HWhile. apply HWhile. assumption.
  
  SCase "<-". inversion H; subst.
  SSCase "E_WhileEnd".
    apply E_WhileEnd. rewrite<-optimize_0plus_bexp_sound in H4; assumption.
  assert (HWhile : cequiv (WHILE b DO c END) (WHILE optimize_0plus_bexp b DO optimize_0plus_com c END)).
 apply CWhile_congruence.
  apply optimize_0plus_bexp_sound.
  unfold cequiv. apply IHc.
  unfold cequiv in HWhile. apply HWhile. assumption.
Qed.

