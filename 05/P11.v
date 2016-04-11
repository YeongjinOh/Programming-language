Require Export D.


(** 3 stars (excluded_middle_irrefutable)  *)
(** This theorem implies that it is always safe to add a decidability
axiom (i.e. an instance of excluded middle) for any _particular_ Prop [P].
Why? Because we cannot prove the negation of such an axiom; if we could,
we would have both [~ (P \/ ~P)] and [~ ~ (P \/ ~P)], a contradiction. *)

Theorem excluded_middle_irrefutable:  forall (P:Prop), ~ ~ (P \/ ~ P).  
Proof.
  intros P H. 
    assert (Hcontra: ~P /\ ~~P).
    Proof. unfold not. apply conj.
    Case "~P". unfold not in H. intro HP. apply H. left. apply HP. 
    Case "~~P". intro HNP. unfold not in H. apply H. right. apply HNP. (* end of assertion *)
  unfold not in Hcontra. unfold not in H. 
  inversion Hcontra as [HNP HNNP].  apply H. right. apply HNP.
Qed.

