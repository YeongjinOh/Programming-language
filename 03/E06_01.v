Require Import P06.



Check snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].

