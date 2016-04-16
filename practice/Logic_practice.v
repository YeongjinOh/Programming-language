Require Export D.

Inductive and (P Q:Prop): Prop :=
|conj : P -> Q -> and P Q
.

Inductive or (P Q:Prop): Prop :=
|left : P -> or P Q
|right : Q -> or P Q
.

Theorem proj1 : forall (P Q:Prop),
  P/\Q -> P.
Proof.
  intros. destruct H. assumption. Qed.

Theorem or_commut : forall (P Q:Prop),
  P \/ Q -> Q \/ P.
Proof. 
  intros. destruct H. right. assumption. left. assumption. Qed.

