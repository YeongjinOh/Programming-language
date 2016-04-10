Require Export D.



(** **** Problem #4 : 2 stars (filter_even_gt7) *)

(** Use [filter] (instead of [Fixpoint]) to write a Coq function
    [filter_even_gt7] that takes a list of natural numbers as input
    and returns a list of just those that are even and greater than
    7. *)

Fixpoint greater_than (a b:nat) : bool :=
match a with
| O => false
| S n => match b with
        | O => true
        | S m => greater_than n m
        end
end.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => andb (evenb n) (greater_than n 7)) l
.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

