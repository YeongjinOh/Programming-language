Require Export D.

(********** Discussion and Variations **********)

Inductive ev_list {X:Type} : list X -> Prop :=
| el_nil: ev_list []
| el_cc : forall x y l, ev_list l -> ev_list (x::y::l)
.

Lemma ev_list__ev_length: forall X (l:list X),
  ev_list l -> ev (length l).
Proof. intros. induction H.
  Case "el_nil". simpl. apply ev_0.
  Case "el_cc". simpl. apply ev_SS. apply IHev_list.
Qed.
 
Lemma ev_length__ev_list: forall X n,
  ev n -> forall (l:list X), n = length l -> ev_list l.
Proof. intros X n H. induction H. 
  Case "ev_0". destruct l.
    SCase "[]". intros. apply el_nil. 
    SCase "x::l". intros. inversion H.
  Case "ev_SS". intros. destruct l.
    SCase "[]". apply el_nil. destruct l.
    SCase "[x]". inversion H0. 
    SCase "x::x0::l". inversion H0. apply IHev in H2. apply el_cc. apply H2.
Qed.

Inductive pal {X:Type} : list X -> Prop :=
| pal_nil: pal []
| pal_sgl: forall (x:X), pal [x]
| pal_rcs: forall (x:X) (l:list X), pal l -> pal (x::(snoc l x)).

Theorem pal_app_rev : forall (X:Type) (l:list X), pal (l ++ (rev l)).
Proof.
  intros. induction l.
  Case "[]". simpl. apply pal_nil.
  Case "x::l". simpl. replace (x :: l ++ snoc (rev l) x) with (x :: snoc (l ++ rev l) x). apply pal_rcs. apply IHl.
    Lemma snoc_app_lem : forall (X:Type) (x:X) l1 l2, snoc (l1 ++ l2) x = l1 ++ snoc l2 x.
    Proof. intros. induction l1. reflexivity.
    simpl. rewrite IHl1. reflexivity. Qed.
  rewrite snoc_app_lem with (l2:=(rev l)). reflexivity.
Qed.

Theorem pal_rev : forall (X:Type) (l:list X), pal l -> l = rev l.
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

Print le.


Definition lt (n m:nat) := le (S n) m.

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (n*n).


Theorem sq_3_9 : square_of 3 9.
Proof.
  apply sq. Qed.

Inductive next_nat : nat -> nat -> Prop :=
  nxt : forall n, next_nat n (S n).
Theorem next_2_3 : next_nat 2 3.
Proof. apply nxt. Qed.

Print ev.
Inductive next_even : nat -> nat -> Prop :=
| ne_1 : forall n, ev (S n) -> next_even n (S n)
| ne_2 : forall n, ev (S (S n)) -> next_even n (S (S n)).

Lemma le_trans : forall m n o,
  m <= n -> n <= o -> m <= o.
Proof. intros m n o Hmn Hno. induction Hno as [|n o]. 
  Case "le_n". apply Hmn.
  Case "le_S". apply le_S. apply IHHno. assumption. Qed.

Theorem test_le3:  2<=1 -> 2+2=5.
Proof. intro H. inversion H. inversion H2. Qed.

Theorem O_le_n : forall n, 0<=n.
Proof. intros. induction n as [|n']. apply le_n. apply le_S. assumption. Qed.


(*********************************************************)
Print le.
Theorem n_le_m__Sn_le_Sm: forall n m, S n <= S m -> n <= m.
Proof. intros. inversion H. apply le_n. apply le_trans with (m:=n) (n:=S n) (o:=m). apply le_S. apply le_n. apply H2.  
Qed.

Theorem Sn_le_Sm__n_le_m: forall n m, n <= m -> S n <= S m.
Proof. intros. induction H. apply le_n. apply le_S. apply IHle. Qed.
(*********************************************************)

Lemma n_plus_O__n: forall n, n+0=n.
Proof. intros. induction n. reflexivity. simpl. rewrite->IHn. reflexivity. Qed.

Lemma a_Sb__S_a_b : forall a b, a + S b= S (a+b).
Proof. intros. induction a. reflexivity. simpl. rewrite IHa. reflexivity. Qed.

Lemma plus_comm: forall a b, a + b = b + a.
Proof. intros. induction a.
  Case "a". simpl. symmetry. apply n_plus_O__n.
  Case "S a". simpl. rewrite a_Sb__S_a_b. rewrite IHa. reflexivity. Qed.

Theorem le_plus_l: forall a b, a <= a + b.
Proof. intro a. induction a.
  Case "O". simpl. apply O_le_n.
  Case "S a". simpl. induction b.
    SCase "O". rewrite n_plus_O__n. apply le_n.
    SCase "S b". replace (a + S b) with (S (a + b)). apply le_S. apply IHb. symmetry. apply a_Sb__S_a_b. Qed. 

Theorem plus_lt: forall n1 n2 m,
  n1 + n2 < m -> n1 < m /\ n2 < m.
Proof. intros n1 n2 m. unfold "<". split.
  Case "n1". apply le_trans with (m:=S n1) (n:= S(n1+n2)) (o:=m).
    replace (S (n1 + n2)) with (S n1 + n2). apply le_plus_l.
    simpl. reflexivity. apply H.
  Case "n2". apply le_trans with (m:=S n2) (n:=S (n1 + n2)) (o:= m). replace (S (n1 + n2)) with (S n2 + n1). apply le_plus_l. simpl. rewrite plus_comm.  reflexivity. apply H. Qed.

Theorem lt_S: forall n m, n < m -> n < S m.
Proof. intros n m. unfold "<". intro H. apply le_S. apply H. Qed.


Theorem ble_nat_true: forall n m,
  ble_nat n m = true -> n <= m.
Proof. intros. generalize dependent n. induction m.
  Case "O". induction n.
    SCase "O". intros. apply le_n.
    SCase "S n". intros. inversion H. 
  Case "S m". intros. induction n.
    SCase "O". apply O_le_n.
    SCase "S n". inversion H. apply IHm in H1. apply Sn_le_Sm__n_le_m. assumption. Qed.


Theorem le_ble_nat: forall n m,
  n <= m -> ble_nat n m = true.
Proof. intro n. induction n.
  Case "O". intros. induction m.
    SCase "O". reflexivity. 
    SCase "S m". reflexivity.
  Case "S n". intros. induction m.
    SCase "O". inversion H.
    SCase "S m". simpl. apply IHn. apply n_le_m__Sn_le_Sm.
    assumption. Qed.

Theorem ble_nat_true_trans: forall n m o,
  ble_nat n m = true -> ble_nat m o = true -> ble_nat n o = true.
Proof. intros. apply ble_nat_true in H. apply ble_nat_true in H0.
  apply le_ble_nat. apply le_trans with (m:=n) (n:=m). assumption. assumption. Qed.

Theorem ble_nat_false: forall n m,
  ble_nat n m = false -> ~(n<=m).
Proof. intros. unfold not. intro Hnm. apply le_ble_nat in Hnm. rewrite H in Hnm. inversion Hnm. Qed.

Inductive R : nat -> nat -> nat -> Prop :=
| c1 : R 0 0 0
| c2 : forall m n o, R m n o -> R (S m) n (S o)
| c3 : forall m n o, R m n o -> R m (S n) (S o)
| c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
| c5 : forall m n o, R m n o -> R n m o.

Theorem R112 : R 1 1 2.
Proof. apply c2. apply c3. apply c1. Qed.

(***************************************************)
Theorem R_mno :forall m n o,  R m n o -> m + n = o.
Proof. intros. generalize dependent n. generalize dependent m. induction o.
  Case "O". intros. inversion H. reflexivity. inversion H0. inversion H7. subst. Abort.

Inductive RR: nat -> list nat -> Prop :=
| Rc1: RR 0 []
| Rc2: forall n l, RR n l -> RR (S n) (n::l)
| Rc3: forall n l, RR (S n) l -> RR n l.

  Theorem RR1210: RR 2 [1;2;1;0].
  Proof.  apply Rc2. apply Rc3. apply Rc3. apply Rc2. apply Rc2. apply Rc2. apply Rc1. Qed.



(********** Programming with Propositions **********)

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.
Theorem plus_fact_is_true : plus_fact.
Proof. reflexivity. Qed.

Definition true_for_zero (P:nat->Prop) : Prop :=
  P 0.
Definition true_for_all_numbers (P:nat -> Prop) : Prop :=
  forall n, P n.
Definition preserved_by_S (P:nat -> Prop): Prop :=
  forall (n:nat), P n -> P (S n).

Definition natural_number_induction: Prop :=
  forall (P:nat->Prop),
  true_for_zero P ->
    preserved_by_S P ->
      true_for_all_numbers P.

Definition combine_odd_even (Podd Peven : nat -> Prop) :
  nat -> Prop :=
fun n => if oddb n then Podd n else Peven n.

Theorem combbine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n:nat),
    (oddb n = true -> Podd n) ->
      (oddb n = false -> Peven n) ->
        combine_odd_even Podd Peven n.
Proof. intros. unfold combine_odd_even. destruct (oddb n) eqn:Hodd. apply H. reflexivity.  apply H0. reflexivity. Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
      oddb n = true ->
        Podd n.
Proof. intros. unfold combine_odd_even in H. rewrite H0 in H. assumption. Qed.

