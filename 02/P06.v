Require Export D.



(** **** Problem  : 4 stars (plus_swap) *)
(** Use [assert] to help prove this theorem if necessary.  
    You shouldn't need to use induction. *)

Theorem plus_swap : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.  
  Lemma plus_assoc : forall a b c:nat, a + (b + c) = (a + b) + c.
  Proof.
    intros. induction a. reflexivity. simpl. rewrite -> IHa. reflexivity. Qed.
    intros. rewrite -> plus_assoc. symmetry. rewrite -> plus_assoc.  assert (H : m + n = n + m).
    induction n. simpl. induction m. reflexivity. simpl. rewrite -> IHm. reflexivity. simpl. rewrite <- IHn.
    Lemma plus_mSn_Smn : forall n m : nat, m + S n = S (m + n). 
      intros. induction m. reflexivity. simpl. rewrite -> IHm. reflexivity. 
    Qed.
    apply plus_mSn_Smn.
    rewrite -> H. reflexivity.
    
    Qed.

