Require Export D.



(** There is a short solution to the next exercise.  If you find
    yourself getting tangled up, step back and try to look for a
    simpler way. *)
Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros. assert (H1 : l1 ++ (l2 ++ (l3 ++ l4)) = (l1 ++ l2) ++ (l3 ++ l4)).
  rewrite -> app_assoc. reflexivity.
  assert (H2 : ((l1 ++ l2) ++ l3) ++ l4 = (l1 ++ l2) ++ (l3 ++ l4)). rewrite -> app_assoc. reflexivity.
  rewrite -> H1. rewrite -> H2. reflexivity.

Qed.

