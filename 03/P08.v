Require Export D.



(** **** Problem #4 : 2 stars (beq_natlist) *)
(** Fill in the definition of [beq_natlist], which compares
    lists of numbers for equality.  Prove that [beq_natlist l l]
    yields [true] for every list [l]. 

    You can use [beq_nat] from Basics.v
*)

Check beq_nat.

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  GIVEUP.

Example test_beq_natlist1 :   beq_natlist nil nil = true.
Proof. exact GIVEUP. Qed.
Example test_beq_natlist2 :   beq_natlist [1;2;3] [1;2;3] = true.
Proof. exact GIVEUP. Qed.
Example test_beq_natlist3 :   beq_natlist [1;2;3] [1;2;4] = false.
Proof. exact GIVEUP. Qed.

(** Hint: You may need to first prove a lemma about reflexivity of beq_nat. *)
Theorem beq_natlist_refl : forall l:natlist,
  beq_natlist l l = true.
Proof.
  exact GIVEUP.
Qed.
  
(** [] *)

