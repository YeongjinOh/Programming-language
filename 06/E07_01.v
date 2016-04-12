Require Import P07.


Check SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.

