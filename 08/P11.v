Require Export D.

Lemma update_same : forall st X x,
  update st X (st X) x = st x.
Proof. intros. unfold update.
  destruct (eq_id_dec X x). rewrite e. reflexivity. reflexivity. Qed.

(** **** Exercise: 2 stars (assign_aequiv)  *)
Theorem assign_aequiv : forall X e,
  aequiv (AId X) e -> 
  cequiv SKIP (X ::= e).
Proof.
  split; intros. 
  Case "->".
    inversion H0; subst; unfold aequiv in H.
    assert (aeval st' (AId X) = aeval st' e). apply H.
    inversion H1. assert (update st' X (st' X) = st').
    apply functional_extensionality; intros. rewrite update_same. reflexivity. rewrite<-H2 at 2. constructor. symmetry. assumption.
  Case "<-".
  inversion H0; subst. unfold aequiv in H. assert (aeval st (AId X) = aeval st e). apply H. inversion H1. assert (update st X (st X) = st). apply functional_extensionality; intros; rewrite update_same. reflexivity. rewrite H2. constructor.
  
Qed.

