Require Export D.



(** **** Exercise: 3 stars, advanced (pup_to_n)  *)
(** Write an Imp program that sums the numbers from [1] to
   [X] (inclusive: [1 + 2 + ... + X]) in the variable [Y].
   Prove that this program executes as intended for X = 2
   (this latter part is trickier than you might expect). *)

Print bexp.

Definition pup_to_n : com :=
Y::=(ANum 0);;
WHILE (BNot (BEq (AId X) (ANum 0))) DO
  Y ::= (APlus (AId Y) (AId X));; X ::= (AMinus (AId X) (ANum 1))
END.



Example pup_to_2_ceval :
  pup_to_n / (update empty_state X 2) ||
    update (update (update (update (update (update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) X 0.
Proof.
  remember (update empty_state X 2) as st_X.
  remember (update st_X Y 0) as st_Y.
  apply E_Seq with st_Y.
  Case "assignment for Y". rewrite Heqst_Y.
   apply E_Ass. reflexivity.
  Case "WHILE LOOP".
    (* X = 2 *)
      apply E_WhileLoop with (update (update st_Y Y 2) X 1).
      simpl. rewrite Heqst_Y. rewrite Heqst_X. reflexivity. 
      apply E_Seq with (update st_Y Y (aeval st_Y (AId Y)+(aeval st_Y (AId X)))  ). apply E_Ass. reflexivity.
      rewrite Heqst_Y. rewrite Heqst_X. apply E_Ass. simpl. reflexivity. 
    (* X = 1 *)  
      apply E_WhileLoop with (update (update (update (update st_Y Y 2) X 1) Y 3) X 0).
      reflexivity.
      remember (update (update st_Y Y 2) X 1) as st_X1.  apply E_Seq with (update st_X1 Y (aeval st_X1 (APlus (AId Y) (AId X)))). apply E_Ass. simpl. reflexivity.
      assert (aeval st_X1 (APlus (AId Y) (AId X)) = 3). rewrite Heqst_X1. rewrite Heqst_Y. rewrite Heqst_X. reflexivity. rewrite H. apply E_Ass. rewrite Heqst_X1. reflexivity.
    (* X = 0 *)
      apply E_WhileEnd. reflexivity.
Qed.

