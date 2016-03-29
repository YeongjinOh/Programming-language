Require Import P10.



Check option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_opt l).
