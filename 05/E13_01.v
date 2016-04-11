Require Import P13.



Check beq_nat_false : forall n m,
  beq_nat n m = false -> n <> m.

