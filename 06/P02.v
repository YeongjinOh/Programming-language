Require Export D.



(** 2 stars (b_times2)  *)
Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
Proof.
  intros n H. 
  Lemma n_plus_0_is_n : forall n:nat,
    n = n+0.
  Proof. intros. induction n. reflexivity.
        simpl. rewrite <- IHn. reflexivity. Qed.
  Lemma n_plus_n_is_2n : forall n:nat,
    n+n = 2*n.
  Proof. intros. induction n. reflexivity. 
    simpl. rewrite <- n_plus_0_is_n. reflexivity. Qed.
  rewrite <- n_plus_n_is_2n. apply b_sum with (n:=n) (m:=n).
    apply H. apply H.
Qed.
