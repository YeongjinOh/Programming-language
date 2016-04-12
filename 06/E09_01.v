Require Import P09.



Check double_even : forall n,
  ev (double n).

Check ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).


Check ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.

Check ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).

