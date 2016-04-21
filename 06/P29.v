Require Export D.



(** **** Exercise: 3 stars (nostutter)  *)
(** Formulating inductive definitions of predicates is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help at all.

    We say that a list of numbers "stutters" if it repeats the same
    number consecutively.  The predicate "[nostutter mylist]" means
    that [mylist] does not stutter.  Formulate an inductive definition
    for [nostutter].  (This is different from the [no_repeats]
    predicate in the exercise above; the sequence [1;4;1] repeats but
    does not stutter.) *)

Inductive nostutter:  list nat -> Prop :=
| ns_nil : nostutter []
| ns_single : forall n, nostutter [n]
| ns_cons : forall x1 x2 l, (x1<>x2) -> nostutter (x2::l) -> nostutter (x1::x2::l)
.

(** Make sure each of these tests succeeds, but you are free
    to change the proof if the given one doesn't work for you.
    Your definition might be different from mine and still correct,
    in which case the examples might need a different proof.
   
    The suggested proofs for the examples (in comments) use a number
    of tactics we haven't talked about, to try to make them robust
    with respect to different possible ways of defining [nostutter].
    You should be able to just uncomment and use them as-is, but if
    you prefer you can also prove each example with more basic
    tactics.  *)

Example test_nostutter_1:      nostutter [3;1;4;1;5;6].
Proof. apply ns_cons. 
  intro c. inversion c. apply ns_cons. intro c. inversion c. apply ns_cons. intro c. inversion c. apply ns_cons. intro c. inversion c. apply ns_cons. intro c. inversion c. apply ns_single. Qed.

(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_2:  nostutter [].
Proof. apply ns_nil. Qed.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_3:  nostutter [5].
Proof. apply ns_single. Qed.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
Proof. 
  unfold not. intro c. inversion c. inversion H3. unfold not in H6. apply H6. reflexivity. Qed.  

(* 
  Proof. intro.
  repeat match goal with 
    h: nostutter _ |- _ => inversion h; clear h; subst 
  end.
  contradiction H1; auto. Qed.
*)
