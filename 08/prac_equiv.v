Require Export D.

Definition aequiv (a1 a2:aexp) : Prop :=
  forall st,
  aeval st a1 = aeval st a2.

Definition bequiv (b1 b2:bexp) : Prop :=
  forall st,
  beval st b1 = beval st b2.

Definition cequiv (c1 c2:com) : Prop :=
  forall st st',
  (c1/st||st') <-> (c2/st||st').

Definition prog_a : com :=
  WHILE BNot (BLe (AId X) (ANum 0)) DO
    X::=APlus (AId X) (ANum 1)
  END.

Definition prog_b : com :=
  IFB BEq (AId X) (ANum 0) THEN
    X::= APlus (AId X) (ANum 1);;
    Y::= ANum 1
  ELSE
    Y::= ANum 0
  FI;;
  X::= AMinus (AId X) (AId Y);;
  Y ::= ANum 0.

Theorem aequiv_example :
  aequiv (AMinus (AId X) (AId X)) (ANum 0).
Proof. unfold aequiv.  intros. simpl. omega. Qed.

Theorem bequiv_exampe :
  bequiv (BEq (AMinus (AId X) (AId X)) (ANum 0)) BTrue.
Proof. unfold bequiv. intros. simpl. assert (st X - st X = 0).
  omega. rewrite H. reflexivity. Qed.

Theorem skip_left : forall c, cequiv (SKIP;;c) c.
Proof. intros. unfold cequiv. split. 
  Case "->". intros. inversion H. subst. inversion H2. subst. assumption.
  Case "<-". intros. apply E_Seq with st. apply E_Skip. assumption. Qed.

Theorem IFB_true_simple: forall c1 c2,
  cequiv 
    (IFB BTrue THEN c1 ELSE c2 FI) 
    c1.
Proof. split; intros. inversion H; subst; try assumption. inversion H5. 
  apply E_IfTrue. reflexivity. assumption. Qed.


Theorem IFB_true: forall b c1 c2,
     bequiv b BTrue ->
     cequiv 
       (IFB b THEN c1 ELSE c2 FI) 
       c1.
Proof. intros. 
  split; intros. inversion H0; subst; try assumption. unfold bequiv in H. assert (beval st b=beval st BTrue). apply H. rewrite H6 in H1. inversion H1.
  apply E_IfTrue. unfold bequiv in H. simpl in H. apply H. assumption. Qed.

Theorem WHILE_false : forall b c,
     bequiv b BFalse ->
     cequiv
       (WHILE b DO c END)
       SKIP.

Proof. intros. unfold cequiv. intros.  split; intros. 
  Case "->". inversion H0; subst. apply E_Skip. unfold bequiv in H. rewrite H in H3. inversion H3.
  Case "<-". inversion H0. apply E_WhileEnd. unfold bequiv in H. apply H. Qed.





(***************************************************************)
(* H0에 대해 inversion 이 아닌 induction 을 쓴다!! *)
(***************************************************************)
Lemma WHILE_true_nonterm : forall b c st st',
     bequiv b BTrue ->
     ~( (WHILE b DO c END) / st || st' ).
Proof. intros. unfold not. intros. remember (WHILE b DO c END) as Hw. induction H0;  inversion HeqHw; subst.
  unfold bequiv in H. rewrite H in H0. inversion H0.
  contradiction.
Qed.


(* WHILE_true 는 WHILE_true_nonterm 을 써야 한다 !! *)

Theorem loop_unrolling: forall b c,
  cequiv
    (WHILE b DO c END)
    (IFB b THEN (c;; WHILE b DO c END) ELSE SKIP FI).
Proof. split; intros.
  Case "->". 
    inversion H; subst.
   SCase "False". apply E_IfFalse. assumption. apply E_Skip.
   SCase "True". apply E_IfTrue. assumption. apply E_Seq with st'0. assumption. assumption.
  Case "<-".
    inversion H; subst. 
    SCase "True". inversion H6; subst. apply E_WhileLoop with st'0; try assumption.
    SCase "False". inversion H6; subst. apply E_WhileEnd. assumption. Qed.


(*/////////////////////////////////////////////////////////////*)
(* update same을 쓰면 훨씬 깔끔 *)
(*/////////////////////////////////////////////////////////////*)

Theorem identity_assignment_first_try : forall (X:id),
  cequiv (X ::= AId X) SKIP.
Proof.
   intros. split; intro H.
     Case "->".
       inversion H; subst. simpl.
       replace (update st X (st X)) with st.
       constructor.
      apply functional_extensionality. intros. unfold update. destruct (eq_id_dec X x). rewrite e. reflexivity. reflexivity.
    Case "<-".
      inversion H; subst. remember (aeval st' (AId X)) as n eqn:Hn.    replace ((X::=AId X)/st'||st') with ((X::=AId X)/st'||update st' X n). apply E_Ass. symmetry. assumption. 
    assert (update st' X n = st'). apply functional_extensionality. intros. rewrite Hn. simpl. unfold update. destruct (eq_id_dec X x). rewrite e. reflexivity. reflexivity. rewrite H0. reflexivity. Qed.




