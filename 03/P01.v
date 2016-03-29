Require Export D.



(** **** Problem #1 : 2 stars (list_funs) *)
(** Complete the definitions of [nonzeros], [oddmembers] and
    [countoddmembers] below. Have a look at the tests to understand
    what these functions should do. *)

Fixpoint nonzeros (l:natlist) : natlist :=
  GIVEUP.

Example test_nonzeros:            nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. exact GIVEUP. Qed.

(** An exercise about your implementation of [nonzeros]: *)
Theorem nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  exact GIVEUP.
Qed.

