Require Import P12.



Check false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.

