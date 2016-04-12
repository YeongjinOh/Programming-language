Require Import P20.


Check le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.

