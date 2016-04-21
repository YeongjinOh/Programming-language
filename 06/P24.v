Require Export D.



(** **** Exercise: 3 stars, optional (not_exists_dist)  *)
(** (The other direction of this theorem requires the classical "law
    of the excluded middle".) *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  unfold excluded_middle. unfold not.
  intros H X P H2 x. destruct H with (P:=P x).
  Case "P". apply H0.
  Case "~P". apply ex_falso_quodlibet. apply H2. exists x. assumption.
Qed.
