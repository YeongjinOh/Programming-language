Require Export D.

Theorem hoare_post_true : forall (P Q:Assertion) c, 
  (forall st, Q st) -> {{P}} c {{Q}}.
Proof. intros. unfold hoare_triple.
  intros. apply H. Qed.

Theorem hoare_post_false : forall (P Q:Assertion) c,
  (forall st, ~(P st)) -> {{P}} c {{Q}}.
Proof. intros. unfold hoare_triple. intros. apply H in H1. contradiction. Qed.

Theorem big_small : 
  (fun st => st X < 10) ->> (fun st => st X < 11).
Proof. unfold "->>".
intros. apply le_trans with 10. unfold "<" in H. assumption. apply le_S. apply le_n. Qed.

Theorem hoare_asgn : forall Q X a, 
  {{Q [X |-> a]}} (X ::= a) {{Q}}.
Proof. intros. unfold assn_sub. unfold hoare_triple. intros.
  inversion H; subst. assumption. Qed.


(* 이 문제의 포인트는, (X::=a) / st||st', st X = m 일 때, 
  st = (update st' X m) 인 것을 이해하는 것인 듯. *)
Theorem hoare_asgn_fwd :
  (forall {X Y: Type} {f g : X -> Y},
     (forall (x: X), f x = g x) -> f = g) ->
  forall m a P,
  {{fun st => P st /\ st X = m}}
    X ::= a
  {{fun st => P (update st X m) /\ st X = aeval (update st X m) a }}.
Proof.
  intros functional_extensionality m a P.
  unfold hoare_triple; intros.
  split. destruct H0.
  (* X를 바꿨지만, 바꾸기 전에 st X = m이었으니까, P 에도 X값이 m이되는 state를 넣어주면 성립한다 *)
Case "left". 
  assert (st = update st' X m). apply functional_extensionality. intros. 
  inversion H; subst. 
  unfold update. destruct (eq_id_dec X x). rewrite e. reflexivity. reflexivity. rewrite<-H2. assumption.
  Case "right".
  destruct H0. inversion H; subst.
  assert (st = (update (update st X (aeval st a)) X (st X))).
  unfold update. apply functional_extensionality. intros.
  destruct (eq_id_dec X x). rewrite e. reflexivity. reflexivity.
  rewrite<-H1. unfold update. rewrite eq_id. reflexivity.
  Qed.

(* 이건 존재하는게 뭔지 잘 생각해서 넣는 게 중요 *)
Theorem hoare_asgn_fwd_exists :
  (forall {X Y: Type} {f g : X -> Y},
     (forall (x: X), f x = g x) -> f = g) ->
  forall a P,
  {{fun st => P st}}
    X ::= a
  {{fun st => exists m, P (update st X m) /\
                st X = aeval (update st X m) a }}.
Proof.
  intros functional_extensionality a P.
  unfold hoare_triple. intros.
  exists (st X). inversion H; subst.
  assert (st = update (update st X (aeval st a)) X (st X)). apply functional_extensionality. intros. 
  unfold update. destruct (eq_id_dec X x); try rewrite e; try reflexivity.
  rewrite<-H1. split; try apply H0.
  unfold update. apply eq_id. Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof. unfold hoare_triple. intros. apply (H st st'). apply H1.
  unfold assert_implies in H0. apply (H0 st). assumption. Qed.


Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof. unfold hoare_triple; unfold assert_implies; intros.
  apply (H0 st'); apply (H st st'); assumption. Qed.


Example hoare_asgn_example1 :
  {{fun st => True}} (X ::= (ANum 1)) {{fun st => st X = 1}}.
Proof.
(* 내가 한거
  unfold hoare_triple. intros. 
  inversion H; subst. unfold update; apply eq_id. Qed.
*)
(* 모범? 답안 *)
  apply hoare_consequence_pre
    with (P' := (fun st => st X = 1) [ X |-> ANum 1]).  
 (* apply hoare_asgn.*)
  unfold assn_sub. unfold hoare_triple. intros.
  inversion H; subst. assumption.
(****************************************************) 
 unfold assert_implies. intros.
  reflexivity.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof. 
  intros P P' Q Q' c Hpre Hp.
  apply hoare_consequence_post.
  apply (hoare_consequence_pre P P' Q'); assumption.
Qed.

Example hoare_asgn_example1' :
  {{fun st => True}} 
  (X ::= (ANum 1)) 
  {{fun st => st X = 1}}.
Proof.
(* 내가 한게 더 깔끔한듯? 
 unfold hoare_triple. intros.
  inversion H; subst. simpl. reflexivity. Qed.
  *)

(* 이거 대신
  apply hoare_consequence_pre 
    with (P' := (fun st => st X = 1) [X|->ANum 1]). *)
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  unfold assert_implies. intros.
  reflexivity.
  Qed.


Lemma silly1 : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (forall x y : nat, P x y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof. intros. eapply H0. apply H with (y:=42). Qed. 
Qed.

Lemma silly2 :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof. intros. eapply H0. destruct H.
 (* apply H.*)
Abort.


Lemma silly2_fixed :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. 
(* 얘네 둘의 순서가 중요하다! *)
destruct HP as [y HP'].  eapply HQ. 
apply HP'.
Qed.

Lemma silly2_eassumption : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof. intros. destruct H. eapply H0. eassumption. Qed.

Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof. unfold hoare_triple. intros.
inversion H; subst. assumption. Qed.

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;;c2 {{R}}. 
Proof. unfold hoare_triple. intros P Q R c1 c2 H1 H2.
  intros st st' Hc Hp. inversion Hc; subst.
  eapply H1. eassumption.
  eapply H2. eassumption.
  assumption. Qed.
  

Example hoare_asgn_example3 : forall a n,
  {{fun st => aeval st a = n}} 
  (X ::= a;; SKIP) 
  {{fun st => st X = n}}. 
Proof. intros. apply hoare_seq with (Q := (fun st => st X = n)).
  unfold hoare_triple; intros. inversion H; subst. reflexivity.
  unfold hoare_triple; intros. inversion H; subst. reflexivity.
Qed.

(*
Definition swap_program : com :=
  (* FILL IN HERE *) admit.

 Theorem swap_exercise :
  {{fun st => st X <= st Y}} 
  swap_program
  {{fun st => st Y <= st X}}.
Proof. 
*)

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof. intros. unfold bassn. assumption. Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof. intros. unfold bassn, not. intros. rewrite H in H0. inversion H0. Qed.

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
  {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof. intros. unfold hoare_triple in *. intros.
  destruct (beval st b) eqn:Hb.  
  Case "True".
  inversion H1; subst. 
  apply (H st); try split; try assumption.
  rewrite Hb in H8. inversion H8.
  Case "False".
  inversion H1; subst.
  rewrite Hb in H8. inversion H8.
  apply (H0 st); try split; try assumption.
  unfold bassn. rewrite Hb. unfold not; intros; inversion H3.
Qed.

Lemma beq_nat_same : forall n, (beq_nat n 0 = true) -> n = 0.
Proof. intros. induction n. reflexivity. inversion H. Qed.

Example if_example : 
    {{fun st => True}} 
  IFB (BEq (AId X) (ANum 0)) 
    THEN (Y ::= (ANum 2)) 
    ELSE (Y ::= APlus (AId X) (ANum 1)) 
  FI
    {{fun st => st X <= st Y}}.
Proof. apply hoare_if; unfold hoare_triple; intros.
  Case "True".
  inversion H; subst. simpl.
  destruct H0. inversion H1. assert (st X = 0). apply beq_nat_same in H3. assumption.
 unfold update. rewrite eq_id. destruct (eq_id_dec Y X).
  apply le_n. rewrite H2. apply le_S. apply le_S. apply le_n.
  Case "False".
  inversion H; subst. simpl. unfold update.
  rewrite eq_id. destruct (eq_id_dec Y X). apply le_n.
  replace (st X + 1) with (S (st X)).  apply le_S, le_n. omega.
Qed.

(* if_minus_plus 까지만 함. 그 밑에꺼 연습할 것 *)
