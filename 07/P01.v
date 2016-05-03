Require Export D.



(** **** Exercise: 3 stars (optimize_0plus_b)  *)
(** Since the [optimize_0plus] tranformation doesn't change the value
    of [aexp]s, we should be able to apply it to all the [aexp]s that
    appear in a [bexp] without changing the [bexp]'s value.  Write a
    function which performs that transformation on [bexp]s, and prove
    it is sound.  Use the tacticals we've just seen to make the proof
    as elegant as possible. *)

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
match b with
| BTrue => BTrue
| BFalse => BFalse
| BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
| BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
| BNot b1 => BNot (optimize_0plus_b b1)
| BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
end.

Example optimize_0plus_b_example1:
  optimize_0plus_b (BEq 
     (AMult (APlus (ANum 0) (APlus (ANum 0) (ANum 3)))
            (AMinus (ANum 5) (APlus (ANum 0) (ANum 1))))
     (APlus (ANum 2)
            (APlus (ANum 0)
                   (APlus (ANum 0) (ANum 1)))))
  = (BEq (AMult (ANum 3) (AMinus (ANum 5) (ANum 1)))
         (APlus (ANum 2) (ANum 1))).
Proof. simpl. reflexivity. Qed.  

Tactic Notation "bexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BTrue" | Case_aux c "BFalse"
  | Case_aux c "BEq"   | Case_aux c "BLe"
  | Case_aux c "BNot"  | Case_aux c "BAnd" ].

Theorem optimize_0plus_sound : forall a,
  aeval (optimize_0plus a) = aeval a.
Proof. intros. induction a; try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
  Case "ANum". reflexivity.
  Case "APlus". destruct a1; try(simpl; simpl in IHa1; rewrite IHa1; rewrite IHa2; reflexivity).
    SCase "a1 = ANum n". destruct n. simpl. assumption. simpl. rewrite IHa2. reflexivity.
Qed.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  intros. bexp_cases (induction b) Case; try(reflexivity;reflexivity).
  simpl; repeat (rewrite optimize_0plus_sound); reflexivity.
  simpl; repeat (rewrite optimize_0plus_sound); reflexivity.
  simpl. rewrite IHb. reflexivity.
  simpl. rewrite IHb1. rewrite IHb2. reflexivity.
Qed.
