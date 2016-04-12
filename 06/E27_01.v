Require Import P27.



Check test_all_1: all (fun x => x = 1) [1; 1].

Check forallb_correct: forall X (P: X -> bool) l,
  forallb P l = true <-> all (fun x => P x = true) l.

