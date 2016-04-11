Require Import P06.



Check orb_prop : forall b c,
  orb b c = true -> b = true \/ c = true.

