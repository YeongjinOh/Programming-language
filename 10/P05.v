Require Export P04.



(** **** Exercise: 2 stars (if_minus_plus)  *)
(** Prove the following hoare triple using [hoare_if]: *)

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Theorem hoare_if_simpl : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
  {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof. intros. unfold hoare_triple in *. intros.
  destruct (beval st b) eqn:Hb.  
  Case "True".
  inversion H1; subst. 
  apply (H st); try split; try assumption.
  rewrite Hb in H8. inversion H8.
  Case "False".
  inversion H1; subst.
  rewrite Hb in H8. inversion H8.
  apply (H0 st); try split; try assumption.
  unfold bassn. rewrite Hb. unfold not; intros; inversion H3.
Qed.

Lemma minus_plus_same : forall m n,
  n <= m -> m = m - n + n.
Proof. intros. omega. Qed. 

Theorem if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}. 
Proof.
  apply hoare_if_simpl; unfold hoare_triple; intros.
  Case "True".
  destruct H0. inversion H; subst. simpl. unfold update.
  rewrite eq_id. simpl. rewrite plus_comm. apply minus_plus_same.
  unfold bassn in H1. inversion H1. apply ble_nat_true. assumption.
  Case "False".
  destruct H0. inversion H; subst. simpl. unfold update.
  rewrite eq_id. simpl. reflexivity.
Qed.

