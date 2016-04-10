Require Export D.



(** **** Problem #11 : 3 stars (fold_map) *)
(** We can also define [map] in terms of [fold].  Finish [fold_map]
    below. *)

Print fold_map.

(** Prove the correctness of [fold_map]. *)

Theorem fold_map_correct : forall (X Y:Type) (f : X -> Y) (l : list X),
  fold_map f l = map f l.
Proof.
  intros. unfold fold_map. induction l. reflexivity.
  simpl. rewrite -> IHl. reflexivity.
Qed.

