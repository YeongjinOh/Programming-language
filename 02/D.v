(** **** SNU 4190.310, 2016 Spring *)

(** Assignment 02 *)
(** Due: 2016/03/27 23:59 *)

(* Important: 
   - You are NOT allowed to use the [admit] tactic.

   - You are NOT allowed to use the following tactics.
     [tauto], [intuition], [firstorder], [omega].

   - Just leave [exact GIVEUP] for those problems that you fail to prove.
*)

Definition GIVEUP {T: Type} : T.  Admitted.


(** The following function doubles its argument: *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.

Notation "( x , y )" := (pair x y).

Definition fst := 
  fun (p : natprod) =>
  match p with
  | (x, y) => x
  end.

Definition snd (p : natprod) : nat := 
  match p with
  | (x, y) => y
  end.

Definition swap_pair (p : natprod) : natprod := 
  match p with
  | (x,y) => (y,x)
  end.

