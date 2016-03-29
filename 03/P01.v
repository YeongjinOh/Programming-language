Require Export D.



(** **** Problem #1 : 2 stars (list_funs) *)
(** Complete the definitions of [nonzeros], [oddmembers] and
    [countoddmembers] below. Have a look at the tests to understand
    what these functions should do. *)

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | [] => []
  | hd::tl => match hd with
            | 0 => nonzeros tl
            | _ => hd :: (nonzeros tl)
            end
  end.


Example test_nonzeros:            nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

(** An exercise about your implementation of [nonzeros]: *)
Theorem nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
 intros. induction l1. reflexivity. 
 induction n. simpl. apply IHl1.
 simpl. rewrite -> IHl1. reflexivity.
  
Qed.

