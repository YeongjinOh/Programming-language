Require Import P22.


Check ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).

