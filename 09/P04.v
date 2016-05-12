Require Export P03.



Lemma optimize_0plus_bexp_sound:
  btrans_sound optimize_0plus_bexp.
Proof.
  unfold btrans_sound. intros. unfold bequiv. intros.
  bexp_cases (induction b) Case;
  (* BTrue BFalse *)
  try reflexivity;
  (* BEq BLe *)
  try (simpl; rewrite<-optimize_0plus_aexp_sound; rewrite<-optimize_0plus_aexp_sound; reflexivity).
  (* BNot *)
  simpl. rewrite IHb. reflexivity. 
  (* BAnd *)
  simpl. rewrite IHb1. rewrite IHb2. reflexivity. 
  Qed.

