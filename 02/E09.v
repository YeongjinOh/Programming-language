Require Import P09.



Check snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.

