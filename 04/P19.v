Require Export D.



(** **** Problem #18 : 3 stars (plus_n_n_injective)  *)
(** Practice using "in" variants in this exercise. *)

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  { (* Hint: use the [destruct] and [inversion] tactics. *)
    intros. destruct m. reflexivity.
    inversion H.
  }
  { (* Hint: use the plus_n_Sm lemma *) 
    intros. destruct m. inversion H. inversion H.
    Lemma plus_n_Sm : forall (n m:nat),
      n + S m = S (n + m).
    Proof. intros. induction n. reflexivity.
      simpl. rewrite -> IHn. reflexivity. Qed.
    rewrite->plus_n_Sm in H1. symmetry in H1. rewrite -> plus_n_Sm in H1. inversion H1.
    Lemma nm_SnSm_eq : forall (n m:nat),
      n=m -> S n=S m.
    Proof. intros. rewrite -> H. reflexivity. Qed.
    apply nm_SnSm_eq. apply IHn'. symmetry. apply H2.
  }
Qed.

