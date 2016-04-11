Require Export D.



(** **** Problem #25 : 3 stars, advanced (filter_exercise)  *)
(** This one is a bit challenging.  Pay attention to the form of your IH. *)

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
 
    intros.
    induction l.
    {
      inversion H.
    }
    {
       destruct (test x0) eqn:a. inversion H. rewrite a in H1.
       inversion H1.  rewrite <- a. rewrite H2. reflexivity.
       inversion H. rewrite a in H1. apply IHl. apply H1.
    }
Qed. 
  

