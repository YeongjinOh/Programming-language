Require Export D.

Inductive pal {X:Type} : list X -> Prop :=
| pal_nil: pal []
| pal_sgl: forall (x:X), pal [x]
| pal_rcs: forall (x:X) (l:list X), pal l -> pal (x::(snoc l x)).

  (***** Helper of pal_rev2 *****)

      Lemma rev_snoc_lem : forall (X:Type) (x:X) (l:list X),
        rev (snoc l x) = x::(rev l).
      Proof. intros.  induction l as [|h l'].
        Case "[]". reflexivity.
        Case "h::l'". simpl. rewrite->IHl'. reflexivity. Qed.

      Lemma rev_involute : forall (X:Type) (l:list X),
        rev (rev l) = l.
      Proof. intros. induction l as [|x l'].
      Case "[]". reflexivity.
      Case "x::l'". simpl. rewrite->rev_snoc_lem with (l:=rev l'). rewrite IHl'. reflexivity. Qed.

      Lemma nil_revl_nil : forall (X:Type) (l:list X),
        [] = l -> [] = (rev l).
      Proof. intros. induction l as [|x l']. reflexivity. rewrite<-H. reflexivity.  Qed.

      Lemma revl_nil : forall (X:Type) (l:list X),
        [] = (rev l) -> [] = l.
      Proof. intros. apply nil_revl_nil in H. rewrite rev_involute in H. apply H. Qed.


Theorem pal_rev2 : forall (X:Type) (n:nat)  (l:list X),
  n = length l -> l = rev l -> pal l.
Proof. intros X n l. generalize dependent n.
  
  induction l. 
  Case "[]". intros. apply pal_nil. 
  Case "x::l". simpl. remember (rev l) as revl. induction  revl.
    SCase "revl=[]". simpl. intros. inversion H0. apply pal_sgl.
    SCase "x0::revl". simpl. intros. rewrite H0. inversion H0. 
      destruct n. inversion H. 
  Abort.


(***************************************************)


Lemma length_snoc : forall (X : Type) (v : X) (l : list X),
  length (snoc l v) = S (length l).
Proof.
  induction l.
  SCase "l = nil". reflexivity.
  SCase "l = cons". simpl. rewrite -> IHl.  reflexivity. Qed.

Lemma length_rev : forall (X : Type) (l : list X),
  length l = length (rev l).
Proof.
  induction l.
  SCase "l = nil". reflexivity.
  SCase "l = cons".
    simpl. rewrite -> length_snoc. rewrite <- IHl. reflexivity. Qed.

Lemma snoc_nil_false : forall (X : Type) (x : X) (l : list X),
  [] = snoc l x -> False.
Proof.
  intros.
  assert (C: length (@nil X) = S (length l)).
  Case "proof of assertion".
    rewrite -> H. rewrite -> length_snoc. reflexivity.
  inversion C. Qed.


Lemma rev_nil : forall (X : Type) (l : list X),
  [] = rev l <-> [] = l.
Proof.
  split.
  Case "->".
    intros.
    destruct l.
    SSCase "l = nil". reflexivity.
    SSCase "l = cons".
      simpl in H. apply snoc_nil_false in H. inversion H.
  Case "<-".
    intros.
    rewrite <- H. reflexivity. Qed.

Lemma cons_injective : forall (X : Type) (x : X) (l1 l2 : list X),
  l1 = l2 <-> x :: l1 = x :: l2.
Proof.
  split; intros; try (rewrite -> H); try inversion H; reflexivity. Qed.

Lemma snoc_injective : forall (X : Type) (x : X) (l1 l2 : list X),
  l1 = l2 <-> snoc l1 x = snoc l2 x.
Proof. 
  split.
  Case "->".
    intros. rewrite -> H. reflexivity.
  Case "<-".
    generalize dependent l2.
    induction l1.
    SCase "l1 = nil".
      intros. destruct l2.
      SSCase "l2 = nil". reflexivity.
      SSCase "l2 = cons".
        inversion H. apply snoc_nil_false in H2. inversion H2.
    SCase "l1 = cons".
      intros. destruct l2.
      SSCase "l2 = nil".
        inversion H. symmetry in H2. apply snoc_nil_false in H2. inversion H2.
      SSCase "l2 = cons".
        inversion H. apply cons_injective. apply IHl1. apply H2. Qed.

Section list_pal_n_ind.
  Variable X : Type.
  Variable P : list X -> Prop.

Hypothesis nil_case : P [].
  Hypothesis singleton_case : forall x : X, P [x].
  Hypothesis cons_snoc_case : forall (x : X) (l : list X), P l -> l = rev l -> P (x :: snoc l x).

Lemma length_0 : forall (l:list X),
  length l = 0 -> l=[].
Proof. intros. induction l. reflexivity.   inversion H. Qed.

 Fixpoint list_pal_n_ind (n : nat) (l : list X)  : n = length l -> l = rev l -> P l.
  destruct l as [| x l'].
  Case "l = nil".
    simpl. intros H1 H2. subst. apply nil_case.
  Case "l = cons".
    simpl. remember (rev l') as revl.
    destruct revl as [| revlx revl'].
    SCase "revl = nil".
      assert (Hl'nil: [] = l'). apply rev_nil. apply Heqrevl.
      intros Hlen Unused. subst.
      apply singleton_case.
    SCase "revl = cons".
      (* n = S (S n'') *)
      destruct n as [| n']. intros Hlen. inversion Hlen.
      intros Hlen H. inversion Hlen. inversion H.
      destruct n' as [| n''].
        symmetry in H1.  apply length_0 in H1. rewrite -> H1 in Heqrevl. inversion Heqrevl.
      (* Helper asserts *)
      assert (Hrevrevl': rev (rev l') = l'). apply rev_involutive.
      assert (Hl'revl': revl' = rev revl'). simpl in H. inversion H.
        rewrite <- Hrevrevl' in H5. rewrite <- Heqrevl in H5. simpl in H5. apply snoc_injective in H5.
        symmetry. apply H5.
      assert (Hlengthrevl': n'' = length revl').
        assert (length l' = length (snoc revl' revlx)). rewrite -> H3. reflexivity.
        rewrite <- H1 in H0. rewrite -> length_snoc in H0. inversion H0. reflexivity.
      (* Now case is easy *)
      apply cons_snoc_case. 
      apply list_pal_n_ind with (n := n''). assumption. assumption. assumption. Qed.
End list_pal_n_ind.


Theorem list_pal_ind : forall (X : Type) (P : list X -> Prop),
  P [] ->
  (forall x : X, P [x]) ->
  (forall (x : X) (l : list X), l = rev l -> P l -> P (x :: snoc l x)) ->
  forall l : list X, l = rev l -> P l. 
Proof.
  intros X P Pnil Psingleton Pconssnoc l Hlen.
  apply list_pal_n_ind with (n := length l).
  apply Pnil.
  intros. apply Psingleton.
  intros. apply Pconssnoc.
    apply H0. apply H. reflexivity. apply Hlen. Qed.





Theorem pal_theorem : forall (X : Type) (l : list X),
  l = rev l <-> pal l.
Proof.
  split.
  Case "->".
    apply list_pal_ind.
    apply pal_nil.
    intros x. apply pal_sgl.
    intros x l0 E H. apply pal_rcs. apply H.
  Case "<-".
    intros.
    induction H; simpl; try reflexivity.
    rewrite -> rev_snoc. rewrite <- IHpal. reflexivity. Qed.
