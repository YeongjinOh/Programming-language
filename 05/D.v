(** **** SNU 4190.310, 2016 Spring *)

(** Assignment 05 *)
(** Due: 2016/04/17 23:59 *)

(* Important: 
   - Do NOT import other files.

   - You are NOT allowed to use the [admit] tactic.

   - You are NOT allowed to use the following tactics.
     [tauto], [intuition], [firstorder], [omega].

   - Just leave [exact GIVEUP] for those problems that you fail to prove.
*)


Definition GIVEUP {T: Type} : T.  Admitted.

Require Export MoreCoq.

(* Important: 
   - You are NOT allowed to use the [admit] tactic
     because [admit] simply admits any goal 
     regardless of whether it is provable or not.

     But, you can leave [admit] for problems that you cannot prove.
     Then you will get zero points for those problems.

   - You are NOT allowed to use the following tactics.

     [tauto], [intuition], [firstorder], [omega].
*)

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q). 

Notation "P /\ Q" := (and P Q) : type_scope.

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q. 

Notation "P \/ Q" := (or P Q) : type_scope.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q) 
                      (at level 95, no associativity) 
                      : type_scope.

Inductive False : Prop := . 

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Notation "x <> y" := (~ (x = y)) : type_scope.


