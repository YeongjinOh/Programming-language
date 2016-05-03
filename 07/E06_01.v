Require Import P06.



Check update_neq : forall x2 x1 n st,
  x2 <> x1 ->                        
  (update st x2 n) x1 = (st x1).

