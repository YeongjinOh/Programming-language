Require Import P04.



Check mult_S_1 : forall n m : nat,
  m = S n -> 
  m * (1 + n) = m * m.

