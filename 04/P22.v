Require Export D.



(** **** Problem #21 : 3 stars, optional (double_induction)  *)
(** Prove the following principle of induction over two naturals. *)

Theorem double_induction: forall (P : nat -> nat -> Prop), 
  P 0 0 ->
  (forall m, P m 0 -> P (S m) 0) ->
  (forall n, P 0 n -> P 0 (S n)) ->
  (forall m n, P m n -> P (S m) (S n)) ->
  forall m n, P m n.
Proof.
  intros. generalize dependent n. induction m. induction n. apply H. apply H1. apply IHn.
  induction n. apply H0. apply IHm.
  apply H2. apply IHm.

Qed.

