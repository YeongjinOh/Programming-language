Require Export D.



(** 4 stars (palindromes)  *)
(** A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor
        c : forall l, l = rev l -> pal l
      may seem obvious, but will not work very well.)
 
    - Prove [pal_app_rev] that 
       forall l, pal (l ++ rev l).
    - Prove [pal_rev] that 
       forall l, pal l -> l = rev l.
*)

Inductive pal {X: Type} : list X -> Prop :=
| pal_nil: pal []
| pal_sgl: forall (x:X), pal [x]
| pal_rcs: forall (x:X) (l:list X), pal l -> pal (x::(snoc l x)).

Example test_pal_1: pal [0; 1; 0].
Proof. apply pal_rcs with (x:=0) (l:=[1]). apply pal_sgl. Qed.

Theorem pal_app_rev: forall (X: Type) (l: list X),
  pal (l ++ rev l).
Proof.
  intros. induction l.
  Case "[]". simpl. apply pal_nil.
  Case "x::l". simpl. replace (x :: l ++ snoc (rev l) x) with (x :: snoc (l ++ rev l) x). apply pal_rcs. apply IHl.
    Lemma snoc_app_lem : forall (X:Type) (x:X) l1 l2, snoc (l1 ++ l2) x = l1 ++ snoc l2 x.
    Proof. intros. induction l1. reflexivity.
    simpl. rewrite IHl1. reflexivity. Qed.
  rewrite snoc_app_lem with (l2:=(rev l)). reflexivity.
Qed.

Theorem pal_rev: forall (X: Type) (l: list X),
  pal l -> l = rev l.
 Proof. intros. induction H.
  Case "[]". reflexivity.
  Case "[x]". reflexivity.
  Case "x::l". simpl.
    Lemma x_snoc_lem : forall (X:Type) (x y:X) l,
      x :: snoc l y = snoc (x::l) y.
    Proof. intros. simpl. reflexivity. Qed.
    rewrite x_snoc_lem.
    Lemma snoc_rev_lem : forall (X:Type) (x:X) l,
       x :: (rev l)  = rev (snoc l x).
    Proof. intros.  induction l.
      Case "[]". simpl. reflexivity.
      Case "x0::l". simpl. rewrite<-IHl. simpl. reflexivity. Qed.
    assert (Hrev : x::l = x::(rev l)).
    Proof.  rewrite<-IHpal. reflexivity.
    rewrite -> Hrev. rewrite->snoc_rev_lem. reflexivity.
Qed.

