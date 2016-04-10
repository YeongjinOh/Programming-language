Require Import P12.



Check fold_map_correct : forall (X Y:Type) (f : X -> Y) (l : list X),
  fold_map f l = map f l.

