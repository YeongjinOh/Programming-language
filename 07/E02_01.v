Require Import P02.



Check optimize_1mult_sound: forall a,
  aeval (optimize_1mult a) = aeval a.

