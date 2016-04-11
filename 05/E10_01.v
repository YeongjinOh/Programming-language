Require Import P10.



Check not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).

