Require Import P29.



Check
(conj _ _ test_nostutter_1
(conj _ _ test_nostutter_2
(conj _ _ test_nostutter_3
          test_nostutter_4)))
:
nostutter [3;1;4;1;5;6] /\
nostutter [] /\
nostutter [5] /\
not (nostutter [3;1;1;4]).

