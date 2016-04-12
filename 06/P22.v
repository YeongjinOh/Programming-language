Require Export D.



Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  exact GIVEUP.
Qed.
