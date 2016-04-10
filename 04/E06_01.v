Require Import P06.



Check
(conj test_partition1
(test_partition2))
: 
partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]) /\
partition (fun x => false) [5;9;0] = ([], [5;9;0]).

