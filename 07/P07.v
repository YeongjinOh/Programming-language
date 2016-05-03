Require Export D.



(** **** Exercise: 1 star (update_example)  *)
(** Before starting to play with tactics, make sure you understand
    exactly what the theorem is saying! *)

Theorem update_neq : forall x2 x1 n st,
  x2 <> x1 ->                        
  (update st x2 n) x1 = (st x1).
Proof.
  intros. unfold update. apply neq_id. assumption.  
Qed.

Theorem update_example : forall (n:nat),
  (update empty_state (Id 2) n) (Id 3) = 0.
Proof.
  intros. apply (update_neq (Id 3) (Id 2) n empty_state).
  unfold not. intros. inversion H.
  Qed.

