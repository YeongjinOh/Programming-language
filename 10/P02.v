Require Export P01.



Theorem assn_sub_ex2:
  {{ (fun st => 0 <= st X /\ st X <= 5) [X |-> ANum 3] }}
     X ::= ANum 3
  {{ fun st => 0 <= st X /\ st X <= 5 }}.
Proof.
  unfold hoare_triple. unfold assn_sub.
  intros. inversion H; subst. assumption.
  
  Qed.

