Require Export D.



Check optimize_1mult.
(*
[optimize_1mult] is defined as follows:

Fixpoint optimize_1mult (a:aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | APlus e1 e2 =>
      APlus (optimize_1mult e1) (optimize_1mult e2)
  | AMinus e1 e2 =>
      AMinus (optimize_1mult e1) (optimize_1mult e2)
  | AMult (ANum 1) e2 =>
      optimize_1mult e2
  | AMult e1 (ANum 1) =>
      optimize_1mult e1
  | AMult e1 e2 =>
      AMult (optimize_1mult e1) (optimize_1mult e2)
  end.
*)

(** Hint:
    If you use the tacticals [;], [try] and [omega] well,
    you can prove the following theorem in 5 lines.
 **)

 Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "APlus"
  | Case_aux c "AMinus"  | Case_aux c "AMult" ].

 Tactic Notation "inductive_cases" tactic(first) ident(c) :=
   first;
   [ Case_aux c "O" | Case_aux c "S n"].

Theorem optimize_1mult_sound: forall a,
  aeval (optimize_1mult a) = aeval a.
Proof.
  intros. aexp_cases (induction a) Case; try reflexivity; try (simpl; omega).
   aexp_cases (destruct a1) SCase. 
  (* SCase = "ANum" *)
  destruct n.
  SSCase "n = 0".
      aexp_cases (destruct a2) SSSCase; try reflexivity. destruct n. reflexivity. destruct n; try reflexivity.
  SSCase "n = S n".
    aexp_cases (destruct a2) SSSCase. destruct n. destruct n0; try reflexivity. simpl in *. omega. simpl in *. destruct n0; try reflexivity. simpl. destruct n0; try reflexivity. simpl. omega.
  destruct n; simpl in *; rewrite IHa2; [try omega|reflexivity]. 
  destruct n; simpl in *; rewrite IHa2; [try omega|reflexivity]. 
  destruct n; simpl in *; rewrite IHa2; [try omega|reflexivity]. 
 
  (* SCase = "APlus" *)
   aexp_cases (destruct a2) SSSCase.  destruct n. simpl in *. rewrite IHa1. omega. destruct n.  simpl in *. rewrite IHa1. omega. simpl in *. rewrite IHa1. omega.
  simpl in *. rewrite IHa1. rewrite IHa2. omega.
  simpl in *. rewrite IHa1. rewrite IHa2. omega.
  simpl in *. rewrite IHa1. rewrite IHa2. omega.

  (* SCase = "AMinus" *)
   aexp_cases (destruct a2) SSSCase.  destruct n. simpl in *. rewrite IHa1. omega. destruct n.  simpl in *. rewrite IHa1. omega. simpl in *. rewrite IHa1. omega.
  simpl in *. rewrite IHa1. rewrite IHa2. omega.
  simpl in *. rewrite IHa1. rewrite IHa2. omega.
  simpl in *. rewrite IHa1. rewrite IHa2. omega.

  (* SCase = "AMult" *)
   aexp_cases (destruct a2) SSSCase.  destruct n. simpl in *. rewrite IHa1. omega. destruct n.  simpl in *. rewrite IHa1. omega. simpl in *. rewrite IHa1. omega.
  simpl in *. rewrite IHa1. rewrite IHa2. omega.
  simpl in *. rewrite IHa1. rewrite IHa2. omega.
  simpl in *. rewrite IHa1. rewrite IHa2. omega.

Qed.



