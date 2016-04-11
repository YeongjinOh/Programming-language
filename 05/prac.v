Require Export D.


Definition peirce := forall P Q: Prop,
  ((P -> Q) -> P) -> P.

Definition classic := forall P:Prop,
  ~~P -> P.

Definition excluded_middle := forall P:Prop,
  P \/ ~P.

Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P \/ Q.

Definition implies_to_or := forall P Q:Prop,
  (P -> Q)  ->  (~P \/ Q).

Theorem double_neg : forall P:Prop,
P -> ~~P.
Proof.
  intros P. intros HP. unfold not. intros HNP.  apply HNP in HP. inversion HP. Qed.

Theorem classic_double_net : forall P:Prop,
  ~~P -> P.
Proof.
  intros P H. unfold not in H. intros H.  
  Lemma p_false : forall P:Prop,
  (P -> False) <-> ~P.
  Proof. intros P. split.
<F2>
 unfold not in H.

