Require Export D.



(** **** Problem #18 : 3 stars (plus_n_n_injective)  *)
(** Practice using "in" variants in this exercise. *)

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  { (* Hint: use the [destruct] and [inversion] tactics. *)
    exact GIVEUP. 
  }
  { (* Hint: use the plus_n_Sm lemma *) 
    exact GIVEUP. 
  } 
Qed.

