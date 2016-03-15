(** **** SNU 4190.310, 2016 Spring *)

(** Assignment 01 *)
(** Due: 2015/03/20 23:59 *)

(* Important: 
   - You are NOT allowed to use the [admit] tactic.

   - You are NOT allowed to use the following tactics.
     [tauto], [intuition], [firstorder], [omega].

   - Just leave [exact GIVEUP] for those problems that you fail to prove.
*)

Definition GIVEUP {T: Type} : T.  Admitted.


Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

