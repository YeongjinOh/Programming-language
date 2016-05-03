Require Import P01.



Check optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.

