Require Import P07.



Check orb_false_elim : forall b c,
  orb b c = false -> b = false /\ c = false.

