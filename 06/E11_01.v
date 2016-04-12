Require Import P11.



Check test_pal_1: pal [0; 1; 0].

Check pal_app_rev: forall (X: Type) (l: list X),
  pal (l ++ rev l).

Check pal_rev: forall (X: Type) (l: list X),
  pal l -> l = rev l.

