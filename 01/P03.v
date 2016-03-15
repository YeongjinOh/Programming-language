Require Export D.



(** **** Problem #3: 2 stars (blt_nat) *)
(** The [blt_nat] function tests [nat]ural numbers for [l]ess-[t]han,
    yielding a [b]oolean.  Use [Fixpoint] to define it. *)

Definition blt_nat (n m : nat) : bool :=
  GIVEUP.

Example test_blt_nat1:             (blt_nat 2 2) = false.
Proof. exact GIVEUP. Qed.
Example test_blt_nat2:             (blt_nat 2 4) = true.
Proof. exact GIVEUP. Qed.
Example test_blt_nat3:             (blt_nat 4 2) = false.
Proof. exact GIVEUP. Qed.

