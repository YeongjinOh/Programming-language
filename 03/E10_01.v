Require Import P10.



Check
(conj test_hd_opt1
(conj test_hd_opt2
(test_hd_opt3)))
:
hd_opt [] = None /\
hd_opt [1] = Some 1 /\
hd_opt [5;6] = Some 5.

