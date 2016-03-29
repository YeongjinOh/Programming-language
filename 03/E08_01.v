Require Import P08.



Check
(conj test_beq_natlist1
(conj test_beq_natlist2
(test_beq_natlist3)))
:   
beq_natlist nil nil = true /\
beq_natlist [1;2;3] [1;2;3] = true /\
beq_natlist [1;2;3] [1;2;4] = false.

