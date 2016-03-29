Require Export D.



(** **** Problem #6 : 2 stars (hd_opt) *)
(** Using the same idea, fix the [hd] function from earlier so we don't
   have to pass a default element for the [nil] case.  *)

Definition hd_opt (l : natlist) : natoption :=
  GIVEUP.

Example test_hd_opt1 : hd_opt [] = None.
Proof. exact GIVEUP. Qed.
Example test_hd_opt2 : hd_opt [1] = Some 1.
Proof. exact GIVEUP. Qed.
Example test_hd_opt3 : hd_opt [5;6] = Some 5.
Proof. exact GIVEUP. Qed.


(** This exercise relates your new [hd_opt] to the old [hd]. *)
Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_opt l).
Proof.
  exact GIVEUP.
Qed.

