Require Import P03.



Check beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.

