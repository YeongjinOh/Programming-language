Require Export P05.



Lemma constfold_0plus_sound:
  ctrans_sound constfold_0plus.
Proof.
  unfold ctrans_sound. intros. 
  unfold cequiv. intros.
  unfold constfold_0plus.
  assert (c / st || st' <-> (fold_constants_com c) / st || st').
  apply fold_constants_com_sound.
  rewrite H.
  apply optimize_0plus_com_sound.
  Qed.

