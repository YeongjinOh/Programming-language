Require Export D.



(** **** Problem : 2 stars (double_plus) *)

(* See [D.v] for the definition of [double] *)

(** Use induction to prove this simple fact about [double]: *)

Lemma double_plus : forall n, double n = n + n .
Proof.  
  intros. induction n. simpl. reflexivity.
  simpl. rewrite -> IHn.
  Lemma plus_Smn_mSn : forall m n:nat, S (m + n) = m + S n.
  Proof.
      intros. induction m. reflexivity.
      simpl. rewrite -> IHm. reflexivity. Qed.
  rewrite -> plus_Smn_mSn. reflexivity.
Qed.

