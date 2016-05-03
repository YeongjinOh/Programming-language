Require Import P05.



Check update_eq : forall n x st,
  (update st x n) x = n.

