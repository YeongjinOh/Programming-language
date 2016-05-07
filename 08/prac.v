Require Export D.

Theorem eq_id_dec : forall (id1 id2:id),
  {id1 = id2} + {id1 <> id2}.
Proof.
  intros. destruct id1. destruct id2.
  destruct (eq_nat_dec n n0). left. rewrite e. reflexivity. 
  right. unfold not. intros. unfold not in n1. inversion H. contradiction. Qed.

Lemma eq_id : forall (T:Type) x (p q:T), 
                  (if eq_id_dec x x then p else q) = p.
Proof. intros. destruct (eq_id_dec x x). reflexivity.
apply ex_falso_quodlibet. apply n. reflexivity. Qed.

(*
Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x (* <----- NEW *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Inductive com : Type :=
  | CSkip : com
  | CAss : id → aexp → com
  | CSeq : com → com → com
  | CIf : bexp → com → com → com
  | CWhile : bexp → com → com.
*)

Definition fact_in_coq : com :=
  Z ::= AId X;;
  Y ::= ANum 1;;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    Y ::= AMult (AId Y) (AId Z);;
    Z ::= AMinus (AId Z) (ANum 1)
  END.


Definition plus2 : com :=
  X ::= (APlus (AId X) (ANum 2)).


Definition XtimesYinZ : com :=
  Z ::= (AMult (AId X) (AId Y)).

Definition subtract_slowly_body : com :=
  Z ::= AMinus (AId Z) (ANum 1) ;;
  X ::= AMinus (AId X) (ANum 1).




Example ceval_example1:
    (X ::= ANum 2;;
     IFB BLe (AId X) (ANum 1)
       THEN Y ::= ANum 3
       ELSE Z ::= ANum 4
     FI)
   / empty_state
   || (update (update empty_state X 2) Z 4).
Proof.
  (* We must supply the intermediate state *)
  apply E_Seq with (update empty_state X 2).
  Case "assignment command".
    apply E_Ass. reflexivity.
  Case "if command".
    apply E_IfFalse. reflexivity.
    apply E_Ass. reflexivity. Qed.

Theorem ceval_deterministic: forall c st st1 st2,
     c / st || st1 ->
     c / st || st2 ->
     st1 = st2.

Proof.
  intros c st st1 st2 E1 E2.

  generalize dependent st2.
  ceval_cases (induction E1) Case; intros st2 E2.
(*; inversion E2; subst; try reflexivity *)
  inversion E2. reflexivity.
  inversion E2.  subst. reflexivity.
  inversion E2. subst. rewrite IHE1_2 with st2. reflexivity. apply IHE1_1 in H1. rewrite H1. apply H4.
  inversion E2; subst. 
    SCase "true". apply IHE1. apply H6. 
    SCase "false". rewrite H in H5. inversion H5.
  inversion E2; subst.
    SCase "true". rewrite H in H5. inversion H5.
    SCase "false". apply IHE1. apply H6.
  inversion E2. 
    SCase "false". reflexivity.
    SCase "true". rewrite H in H2. inversion H2.
  inversion E2. subst. rewrite H in H4. inversion H4.
  subst. apply IHE1_2. apply IHE1_1 in H3. rewrite<-H3 in H6. apply H6.
Qed.



(****************************************************)
(*  induction loopdef; inversion Heqloopdef.  대신
  induction contra; inversion Heqloopdef; subst. !!!! *)
(****************************************************)
(** **** Exercise: 3 stars (loop_never_stops)  *)
Theorem loop_never_stops : forall st st',
  ~(loop / st || st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef eqn:Heqloopdef.
    (* Proceed by induction on the assumed derivation showing that
     [loopdef] terminates.  Most of the cases are immediately
     contradictory (and so can be solved in one step with
     [inversion]). *)
  induction contra; inversion Heqloopdef; subst.
  Case "E_WhileEnd". inversion H.
  Case "E_WhileLoop". apply IHcontra2. reflexivity.
Qed.

Check s_execute.
Print s_execute.

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat :=
match prog with
| [] => stack
| (SPush n):: tl => s_execute st (n::stack) tl
| (SLoad x) :: tl => s_execute st ((st x)::stack) tl
| (SPlus)::tl => match stack with
                | [] => []
                | [a] => []
                | a::b::t => s_execute st ((b+a)::t) tl
                end
| (SMinus)::tl => match stack with
                | [] => []
                | [a] => []
                | a::b::t => s_execute st ((b-a)::t) tl
                end
| (SMult)::tl => match stack with
                | [] => []
                | [a] => []
                | a::b::t => s_execute st ((b*a)::t) tl
                end
end.

Example s_execute1 :
       s_execute empty_state []
              [SPush 5; SPush 3; SPush 1; SMinus]
                 = [2; 5].
reflexivity. Qed.

Example s_execute2 :
       s_execute (update empty_state X 3) [3;4]
              [SPush 4; SLoad X; SMult; SPlus]
                 = [15; 4].
reflexivity. Qed.


(*
Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat :=
let newstack := 
  match prog with
    | [] => stack
    | (SPush n)::_ => n::stack
    | (SLoad id)::_ => (st id)::stack
    | SPlus::_  => match stack with
                        | n::(m::rest) => (m+n)::rest
                        | _ => stack
                      end
    | SMinus::_  => match stack with
                         | n::m::rest => (m-n)::rest
                         | _ => stack
                       end
    | SMult::_  => match stack with
                        | n::m::rest => (m*n)::rest
                        | _ => stack
                      end
  end in
  match prog with
    | [] => stack
    | instr::rest => s_execute st newstack rest
  end.
*)
Lemma s_execute_app : forall st p1 p2 stack,
  s_execute st stack (p1 ++ p2) = s_execute st (s_execute st stack p1) p2.
  intros st p1.
  induction p1.
  intros; reflexivity.
  intros.
  simpl. destruct a; try (rewrite IHp1; reflexivity).
  apply IHp1.
Qed. 

