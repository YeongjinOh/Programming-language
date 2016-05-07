Require Import P03.


Check loop_never_stops : forall st st',
  ~(loop / st || st').

