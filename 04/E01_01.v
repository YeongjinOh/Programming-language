Require Import P01.



Check test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).

Check split_map: forall X Y (l: list (X*Y)),
   fst (split l) = map fst l.

