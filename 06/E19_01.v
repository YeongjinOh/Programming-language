Require Import P19.


Check ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.

