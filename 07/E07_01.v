Require Import P07.



Check update_example : forall (n:nat),
  (update empty_state (Id 2) n) (Id 3) = 0.

