Require Export P02.

Lemma aeval_lem : forall st a2 a, 
  (aeval st match a2 with |ANum 0 => a | _ => APlus a (optimize_0plus_aexp a2) end = aeval st (APlus a (optimize_0plus_aexp a2))).
Proof. intros. destruct a2; try reflexivity. destruct n. simpl. omega. reflexivity. Qed.

Lemma opt_APlus_helper : forall a1 a2 st,
  aeval st a1 = aeval st (optimize_0plus_aexp a1) ->
  aeval st a2 = aeval st (optimize_0plus_aexp a2) ->
  aeval st a1 + aeval st a2= aeval st (APlus (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)). 
Proof. intros. aexp_cases (induction a1) Case;
  (* a1 = ANum, Aid *)
  try (simpl; rewrite H0; reflexivity);   simpl; rewrite<-H0;
  (* a1 = AMinus AMult *)
  try (inversion H; reflexivity).
Qed.

Lemma opt_APlus_helper2 : forall a1 a2 st,
  aeval st (APlus (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)) = aeval st (optimize_0plus_aexp (APlus a1 a2)).
Proof. intros. simpl. aexp_cases (induction a1) Case; try (simpl; rewrite aeval_lem; reflexivity).
  destruct n. reflexivity. 
  simpl. rewrite aeval_lem. reflexivity. 
Qed.

Lemma optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.
Proof.
  unfold atrans_sound; intros; unfold aequiv; intros.
  aexp_cases (induction a) Case; try reflexivity; try (simpl; rewrite IHa1; rewrite IHa2; reflexivity). 
 rewrite<-opt_APlus_helper2. replace (aeval st (APlus a1 a2)) with (aeval st a1 + aeval st a2); try reflexivity.
 apply opt_APlus_helper; assumption.
Qed.

