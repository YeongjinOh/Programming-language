Require Export D.



(** **** Exercise: 3 stars (all_forallb)  *)
(** Inductively define a property [all] of lists, parameterized by a
    type [X] and a property [P : X -> Prop], such that [all X P l]
    asserts that [P] is true for every element of the list [l]. *)

Inductive all {X : Type} (P : X -> Prop) : list X -> Prop :=
|all_nil : all P []
|all_cons :  forall hd tl, P hd -> all P tl -> all P (hd::tl)
.

(** Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Poly]: *)

Print forallb.

(** Using the property [all], write down a specification for [forallb],
    and prove that it satisfies the specification. Try to make your 
    specification as precise as possible.

    Are there any important properties of the function [forallb] which
    are not captured by your specification? *)

Example test_all_1: all (fun x => x = 1) [1; 1].
Proof. apply all_cons. reflexivity. apply all_cons. reflexivity. apply all_nil.  Qed.

Theorem forallb_correct: forall X (P: X -> bool) l,
  forallb P l = true <-> all (fun x => P x = true) l.
Proof.
  intros. split.
  Case "->". induction l. 
    SCase "[]". intros. apply all_nil.
    SCase "x::l". intros. apply all_cons. inversion H.
    destruct (P x) eqn:Hb. simpl. simpl in H1. symmetry. assumption.
      simpl. reflexivity.
      apply IHl. inversion H. destruct (forallb P l) eqn :Hb.
      symmetry. assumption. destruct (P x). simpl. reflexivity. simpl. reflexivity.
  Case "<-". induction l.
    SCase "[]". intros. simpl. reflexivity.
    SCase "x::l". intros. inversion H. simpl. rewrite H2. simpl.
      apply IHl. assumption.
Qed.

