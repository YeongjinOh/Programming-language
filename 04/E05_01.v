Require Import P05.



Check 
(conj test_filter_even_gt7_1
(test_filter_even_gt7_2))
:
filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8] /\
filter_even_gt7 [5;2;6;19;129] = [].

