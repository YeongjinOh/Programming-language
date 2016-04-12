Require Export D.



(** The [inversion] tactic can also be used to derive goals by showing
    the absurdity of a hypothesis. *)

(** 1 star (inversion_practice)  *)
Theorem even5_nonsense : 
  ev 5 -> 2 + 2 = 9.
Proof.
  intro H. inversion H as [|n Hcontra]. inversion Hcontra as [|n' Hcontra'].  inversion Hcontra'.
  Qed.
