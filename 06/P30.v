Require Export D.



(** **** Exercise: 4 stars, advanced (pigeonhole principle)  *)
(** The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some 
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First a pair of useful lemmas (we already proved these for lists
    of naturals, but not for arbitrary lists). *)

Lemma plus_O : forall (n:nat), 
  n + 0 = n.
Proof. intros. induction n.
  Case "O". reflexivity.
  Case "S n". simpl. rewrite IHn. reflexivity. Qed.

Lemma app_nil : forall (X:Type) (l:list X),
  l ++ [] = l.
Proof. intros. induction l.
  Case "[]". reflexivity.
  Case "x::l". simpl. rewrite IHl. reflexivity. Qed.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof. 
  intros X l1. induction l1 as [|x l].
  Case "[]". intros. reflexivity.
  Case "x::l". intros. induction l2 as [|x' l'].
    SCase "[]". simpl. rewrite app_nil. rewrite plus_O. reflexivity. 
    SCase "x'::l'". simpl. apply f_equal. apply IHl.
Qed.


Lemma appears_in_app_split : forall (X:Type) (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  intros X x l. induction l.
  Case "[]". intros. inversion H.
  Case "x0::l". intros. inversion H.
    SCase "ai_here". exists []. exists l0. rewrite H2. reflexivity.
    SCase "ai_later". apply IHl in H1. inversion H1 as [l1 H1']. exists (x0::l1). inversion H1' as [l2 H2']. exists l2. simpl. rewrite<-H2'. reflexivity. Qed.

(** Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)

Print repeats.

(** Now here's a way to formalize the pigeonhole principle. List [l2]
    represents a list of pigeonhole labels, and list [l1] represents
    the labels assigned to a list of items: if there are more items
    than labels, at least two items must have the same label.  This
    proof is much easier if you use the [excluded_middle] hypothesis
    to show that [appears_in] is decidable, i.e. [forall x
    l, (appears_in x l) \/ ~ (appears_in x l)].  However, it is also
    possible to make the proof go through _without_ assuming that
    [appears_in] is decidable; if you can manage to do this, you will
    not need the [excluded_middle] hypothesis. *)

Lemma le_trans : forall m n o,
  m <= n -> n <= o -> m <= o.
Proof. intros m n o Hmn Hno. induction Hno as [|n o]. 
  Case "le_n". apply Hmn.
  Case "le_S". apply le_S. apply IHHno. assumption. Qed.


Lemma app_appears_in : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
induction xs.
  simpl. intros ys x H. case H.
    intros H1; inversion H1.
    auto.
  simpl. intros ys x0 H. inversion H.
    inversion H0.
      apply ai_here.
      apply ai_later. apply IHxs. inversion H0.
        rewrite <- H5. left. apply H2.
        left; apply H2.
    apply ai_later. apply IHxs. right; apply H0.
Qed.

Lemma app_appears_in_rev : forall (X:Type) (xs ys:list X) (x:X),
  excluded_middle -> 
  appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof. intros. generalize dependent ys. induction xs.
  Case "[]". intros.  simpl in H0. right. apply H0.
  Case "x::xs". intros.
  assert (x=x0 \/ x<>x0). apply H. destruct H1.
    SCase "x=x0". left. rewrite H1. apply ai_here.
    SCase "x<>x0". inversion H0. contradiction. apply IHxs in H3.
      destruct H3. left. apply ai_later. assumption. right. assumption. Qed.

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X), 
   excluded_middle -> 
   (forall x, appears_in x l1 -> appears_in x l2) -> 
   length l2 < length l1 -> 
   repeats l1.  
Proof.
   intros X l1. induction l1 as [|x l1'].
   Case "[]".
   { intros. inversion H1. }
   Case "x::l1'". 
  { intros.
assert (appears_in x l1' \/ ~(appears_in x l1')).
  apply H. destruct H2 as [Hx_in_l1'|Hx_not_in_l1'].
    SCase "appears_in x l1'". apply rp_base. apply Hx_in_l1'.
    SCase "~appears_in x l1'". apply rp_next.
assert (Hx_in_l2 : appears_in x l2). apply H0 with (x0:=x). apply ai_here.
    apply appears_in_app_split in Hx_in_l2. destruct Hx_in_l2 as [l2_left]. destruct proof as [l2_right Hl2].
    apply IHl1' with (l2:=l2_left++l2_right).

  (* first : excluded_middle *)
  apply H.

  (* Second appears_in *)
  intros.
assert (appears_in x0 l2). apply H0. apply ai_later. assumption.
assert (Hxeq : x=x0 \/ x<>x0).  apply H.
  destruct Hxeq as [Hxeq|Hxneq].
    SSCase "x=x0" (* which is contradiction *).
    rewrite<-Hxeq in H2. contradiction.
    SSCase "x<>x0". clear Hx_not_in_l1'. clear IHl1'.
    rewrite Hl2 in H3. apply app_appears_in_rev in H3. destruct H3.
      SSSCase "appears_in x0 l2_left". apply app_appears_in. left. assumption.
      SSSCase "appears_in x0 l2_right". inversion H3. rewrite H5 in Hxneq. contradiction Hxneq. reflexivity.
      apply app_appears_in. right. assumption. apply H.
  
  (* Third length *)
  rewrite Hl2 in H1.

    (* aux lemma for length *)
  Lemma length_app : forall (X:Type) (l1 l2:list X),
  length (l1++l2) = length (l2++l1).
Proof. 
  intros X l1. induction l1. intros. simpl. rewrite app_nil. reflexivity.
  intros.  induction l2. simpl. rewrite app_nil. reflexivity.
  simpl. rewrite<-IHl2. simpl. rewrite IHl1 with (l2:=x0::l2). simpl. rewrite IHl1. reflexivity. Qed. 

    Lemma Sn_lt_Sm_n_lt_m : forall n m,
    S n < S m -> n < m.
  Proof.  intros. unfold "<". unfold "<" in H. inversion H. apply le_n. apply le_trans with (m:=S n) (n:= S (S n)) (o:= m). apply le_S. apply le_n. apply H2. Qed.

  Lemma pred_length_le : forall (X:Type) (x:X) (l1 l2 l3:list X),
  length (l1 ++ x::l2) < length (x::l3) ->
    length (l1 ++ l2) < length l3.
Proof. intros. replace (length (l1 ++ x::l2)) with (length (x::l2 ++ l1)) in H. 
    replace (length (x :: l2 ++ l1)) with (S (length (l2++l1))) in H.
    replace (length (x :: l3)) with (S (length l3)) in H.
    apply Sn_lt_Sm_n_lt_m in H. rewrite length_app. apply H.
    reflexivity. reflexivity. apply length_app with (l1:=x::l2) (l2:=l1). Qed.
 
  (* Back to the proof of theorem *)
  apply pred_length_le in H1. assumption.
 }
Qed.

