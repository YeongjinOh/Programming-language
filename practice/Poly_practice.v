Require Export D.


Theorem rev_snoc : forall (X:Type) (v:X) (s:list X), 
  rev (snoc s v) = v :: (rev s).
Proof.
  intros. induction s. simpl.  reflexivity.
  simpl. rewrite IHs. simpl. reflexivity. Qed.


Theorem rev_involutive : forall (X : Type) (l : list X),
  rev (rev l) = l.
Proof.
  intros. induction l.  reflexivity.
  simpl. rewrite rev_snoc. rewrite IHl. reflexivity. Qed.

Theorem snoc_with_append : forall (X:Type) (l1 l2:list X) (v:X),
  snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  intros. induction l1. simpl. reflexivity.
  simpl. rewrite IHl1. reflexivity. Qed. 

Inductive list (X:Type) : Type :=
| nil : list X
| cons : X -> list X -> list X
.

Check nil.
Check cons.

Fixpoint length (X:Type) (l:list X) : nat :=
match l with
|nil => 0
|cons hd tl => S(length X tl)
end.


Example test_length1 :
      length nat (cons nat 1 (cons nat 2 (nil nat))) = 2.
Proof. reflexivity. Qed.
Example test_length2 :
      length bool (cons bool true (nil bool)) = 1.
Proof. reflexivity. Qed.



Arguments nil {X}.
Arguments cons {X} _ _. (* use underscore for argument position that has no name *)
  Arguments length {X} l.
  Arguments app {X} l1 l2.
  Arguments rev {X} l.
  Arguments snoc {X} l v.

  (* note: no _ arguments required... *)
  Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
  Check (length list123'').


Fixpoint repeati {X : Type} (n : X) (count : nat) : list X :=
match count with
|O => nil
|S n' => cons n (repeati n n')
end.

Example test_repeat1:
  repeati true 2 = cons true (cons true nil).

Proof. reflexivity. Qed. 

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).


Definition list123''' := [1; 2; 3].

Theorem rev_involutive : ∀X : Type, ∀l : list X,
  rev (rev l) = l.
Proof.
(* FILL IN HERE *) Admitted.

Theorem snoc_with_append : ∀X : Type,
                         ∀l1 l2 : list X,
                         ∀v : X,
  snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  (* FILL IN HERE *) Admitted.
