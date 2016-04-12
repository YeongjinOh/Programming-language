Require Import P10.



Check even__ev_strong: forall n : nat, 
  (even (pred n) -> ev (pred n)) /\ (even n -> ev n).

Check even__ev: forall n : nat,
  even n -> ev n.

