Require Export D.



(** 2 star (ev__even)  *)
  
 Theorem ev__even: forall n : nat,
  ev n -> even n.
  
Proof.
  intros n H. induction H as [|n0].
  Case "n = 0". reflexivity.
  Case "n = S S n0". unfold even. unfold even in IHev. simpl. apply IHev. Qed. 
