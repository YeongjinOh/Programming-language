Require Import P09.



Check override_example : forall (b:bool),
  (override (constfun b) 3 true) 2 = b.

