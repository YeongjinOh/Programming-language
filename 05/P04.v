Require Export D.



Theorem iff_trans : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R H1 H2.
  destruct H1 as [HPQ HQP]. destruct H2 as [HQR HRQ].
  split. intros HP. apply HQR. apply HPQ. apply HP.
  intros HR. apply HQP. apply HRQ. apply HR.
Qed.

