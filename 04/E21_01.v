Require Import P21.



Check index_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     index n l = None.

