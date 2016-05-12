Require Export D.

Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.

Proof.
  unfold atrans_sound. intro a. unfold aequiv.  intros st.
  aexp_cases (induction a) Case; try reflexivity.
(* 여기서 simpl을 해줘야함. simpl을 하고 나서 destruct 해야, 전개된 fold_constatns_aexp a1 들까지 다 destruct 된다 !! *)

simpl.
destruct (fold_constants_aexp a1); destruct (fold_constants_aexp a2); rewrite IHa1; rewrite IHa2; reflexivity.

simpl.
destruct (fold_constants_aexp a1); destruct (fold_constants_aexp a2); rewrite IHa1; rewrite IHa2; reflexivity.

simpl.
destruct (fold_constants_aexp a1); destruct (fold_constants_aexp a2); rewrite IHa1; rewrite IHa2; reflexivity.
Qed.



Lemma optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.
Proof.
  unfold atrans_sound.
  intros a.
  induction a;
    try (simpl; apply refl_aequiv).
    destruct a1.
      destruct n.
        unfold aequiv. simpl. apply IHa2.
        unfold aequiv. unfold aequiv in IHa2. 
        simpl. intros st. rewrite IHa2.
Qed.



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
(* 이거 다시 한번 증명해봐... a1 = APlus 일 때 inversion 잘 쓰면 된다는거 이해하기!! *)









Lemma optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.
Proof.
  unfold atrans_sound; intros; unfold aequiv; intros.
  aexp_cases (induction a) Case; try reflexivity; try (simpl; rewrite IHa1; rewrite IHa2; reflexivity). 
  simpl. aexp_cases (destruct (optimize_0plus_aexp a1) eqn:Ha) SCase.
(*  aexp_cases (induction a1) SCase. *)
  simpl. destruct a1.
  destruct n0. simpl. assumption. rewrite aeval_lem. simpl. rewrite IHa2. inversion Ha. reflexivity.
  simpl. rewrite aeval_lem. simpl. rewrite IHa2. inversion Ha. 
  rewrite aeval_lem. simpl. rewrite IHa2. simpl in IHa1. rewrite IHa1. reflexivity.
  rewrite aeval_lem. simpl. rewrite IHa2. simpl in IHa1. rewrite IHa1. reflexivity.
  rewrite aeval_lem. simpl. rewrite IHa2. simpl in IHa1. rewrite IHa1. reflexivity.
  destruct a1. 
  destruct n. simpl. assumption.
  rewrite aeval_lem. simpl. rewrite IHa2. inversion Ha. 
  rewrite aeval_lem. simpl. rewrite IHa2. simpl in IHa1. rewrite IHa1. reflexivity.
  rewrite aeval_lem. simpl. rewrite IHa2. simpl in IHa1. rewrite IHa1. reflexivity.
  rewrite aeval_lem. simpl. rewrite IHa2. simpl in IHa1. rewrite IHa1. reflexivity.
  rewrite aeval_lem. simpl. rewrite IHa2. simpl in IHa1. rewrite IHa1. reflexivity.
 
  destruct a1.
  destruct n. simpl. assumption.
  rewrite aeval_lem. simpl. rewrite IHa2. inversion Ha. 
  rewrite aeval_lem. simpl. rewrite IHa2. inversion Ha. 
  rewrite aeval_lem. simpl. rewrite IHa2. inversion Ha. 
  simpl in IHa1. rewrite IHa1. reflexivity.
   rewrite aeval_lem. simpl. rewrite IHa2. inversion Ha. 
  rewrite aeval_lem. simpl. rewrite IHa2. inversion Ha. 
 
  destruct a1.
  destruct n. simpl. assumption.
  rewrite aeval_lem. simpl. rewrite IHa2. inversion Ha. 
  rewrite aeval_lem. simpl. rewrite IHa2. inversion Ha. 
  rewrite aeval_lem. simpl. rewrite IHa2. inversion Ha. 
  simpl in IHa1. rewrite IHa1. reflexivity.
   rewrite aeval_lem. simpl. rewrite IHa2. inversion Ha. 
  simpl in IHa1.  rewrite IHa1. rewrite H0. rewrite H1. reflexivity.
  simpl. rewrite aeval_lem. simpl. rewrite IHa2. simpl in IHa1. rewrite IHa1. reflexivity.

  destruct a1.
  destruct n. simpl. assumption.
  rewrite aeval_lem. simpl. rewrite IHa2. inversion Ha. 
  rewrite aeval_lem. simpl. rewrite IHa2. inversion Ha. 
  rewrite aeval_lem. simpl. rewrite IHa2. inversion Ha. 



