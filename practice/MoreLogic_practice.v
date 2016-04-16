Require Export D.


(********** Existential Quantification **********)

Print ex.

Inductive ex (X:Type) (P : X->Prop) : Prop :=
 ex_intro : forall (witness:X), P witness -> ex X P.

Notation "'exists' x , p" := (ex _ (fun x => p))
    (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
    (at level 200, x ident, right associativity) : type_scope.


Example exists_example_1 : exists n, n + (n * n) = 6.
Proof. apply ex_intro with (witness:=2). constructor.  Qed.

Example exists_example_22 : exists n, n + (n * n) = 6.
Proof. exists 2. constructor.  Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) -> (exists o, n = 2 + o).
Proof. intros. inversion H as [m Hm]. exists (2+m).
  assumption. Qed.

Lemma exists_example_3 : exists (n:nat), even n /\ beautiful n.
Proof. exists 8. split.
  Case "even". unfold even. reflexivity.
  Case "beautiful". apply b_sum with (n:=3) (m:=5). apply b_3. apply b_5. Qed.

Definition Eng_e : Prop := ex nat (fun n => beautiful (S n)).
Example eng : Eng_e.
Proof. exists 2. apply b_3. Qed. 

Theorem dist_not_exists : forall (X:Type) (P: X -> Prop),
    (forall x, P x) -> ~(exists x, ~(P x)).
Proof. intros.  unfold not. intro Hcontra.
  inversion Hcontra. apply H0 in H. inversion H. Qed.



Print ex_falso_quodlibet.

Theorem not_exists_dist :
  excluded_middle ->
    forall (X:Type) (P:X -> Prop), ~(exists x, ~(P x)) -> 
      (forall x, P x).
Proof.
 unfold excluded_middle. unfold not.
  intros H X P H2 x. destruct H with (P:=P x).
  Case "P". apply H0.
  Case "~P". apply ex_falso_quodlibet. apply H2. exists x. assumption.
Qed.

Theorem dist_exsits_or : forall (X:Type) (P Q:X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
 intros. split.
  Case "->". intros. destruct H as [x]. inversion H.
    SCase "P x". left. exists x. assumption.     
    SCase "Q x". right. exists x. assumption.
  Case "<-". intros. destruct H.
    SCase "P x". destruct H as [x]. exists x. left. assumption.
    SCase "Q x". destruct H as [x]. exists x. right. assumption.
Qed.


(********** Evidence_Carrying Booleans **********)

Inductive sumbool (A B: Prop) : Set :=
| left : A -> sumbool A B
| right : B -> sumbool A B.

Notation "{ A } + { B }" := (sumbool A B) : type_scope.

Theorem eq_nat_dec : forall n m: nat, 
  {n = m} + {~(n = m)}.
Proof. intros n.
  induction n as [|n'].
  Case "O".
    intro m. destruct m as [|m'].
    SCase "O". left. reflexivity.
    SCase "S m". right. intros contra. inversion contra.
  Case "S n".
    intro m. destruct m as [|m'].
    SCase "O". right. intros contra. inversion contra.  
    SCase "S m". destruct IHn' with (m:=m').
      SSCase "left". left. rewrite e. reflexivity.
      SSCase "right". right. intros contra. inversion contra. apply n in H0. inversion H0.
Qed.

Definition override' {X:Type} (f:nat->X) (k:nat) (x:X) : nat->X :=
  fun (k':nat) => if eq_nat_dec k k' then x else f k'.

Theorem override_same' : forall (X:Type) x1 k1 k2 (f:nat ->X),
  f k1 = x1 -> (override' f k1 x1) k2 = f k2.
Proof. intros. unfold override'. destruct (eq_nat_dec k1 k2) eqn:Heq.
  Case "left".  rewrite<-e. symmetry. assumption. 
  Case "right". reflexivity. Qed.

Theorem override_shadow' : forall (X:Type) x1 x2 k1 k2 (f:nat->X),
  (override' (override' f k1 x2) k1 x1) k2 = (override' f k1 x1) k2.
Proof. intros. unfold override'. destruct (eq_nat_dec k1 k2) eqn:Heq.
  Case "left". reflexivity.
  Case "right". reflexivity.
Qed.


(********** Additional Exercises **********) 

Inductive all (X:Type) (P: X -> Prop) : list X -> Prop :=
|all_nil : all X P []
|all_cons :  forall hd tl, P hd -> all X P tl -> all X P (hd::tl)
.

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool := 
match l with
| [] => true
| hd::tl => andb (test hd) (forallb test tl)
end.

Theorem all_forallb : forall (X : Type) (test : X -> bool) (l : list X),
  all X (fun x => test x = true) l <-> forallb test l = true.
Proof.
  intros.  (*remember (fun x : X => test x = true) as P.*) split. 
  Case "->".
  {
     intro H. induction l as [|hd tl].
    SCase "[]". reflexivity. 
    SCase "hd::tl". simpl. unfold andb. destruct (forallb test tl) eqn:Htl. destruct (test hd) eqn:Hhd. reflexivity.
      inversion H. rewrite H2 in Hhd. inversion Hhd. 
      destruct (test hd) eqn:Hhd. inversion H. apply IHtl in H3. inversion H3.
      inversion H. rewrite H2 in Hhd. inversion Hhd.
  }
  Case "<-".
  {
    intro H. induction l as [|hd tl].
    SCase "[]". apply all_nil.   
    SCase "hd::tl". apply all_cons. inversion H.
      destruct (test hd) eqn:Hhd. symmetry. assumption. reflexivity.
     apply IHtl. inversion H. destruct (forallb test tl) eqn:Htl.
      symmetry. assumption. destruct (test hd) eqn:Hhd. reflexivity. reflexivity.
  }
 Qed.


(*********************************************************)
Inductive inorder_merge {X : Type} : list X -> list X -> list X -> Prop :=
| inorder_nil : inorder_merge [] [] []
| inorder_l1 : forall hd tl l2 l3,
  inorder_merge tl l2 l3 -> inorder_merge (hd::tl) l2 (hd::l3)
| inorder_l2 : forall l1 hd tl l3,
  inorder_merge l1 tl l3 -> inorder_merge l1 (hd::tl) (hd::l3)
.

Lemma same_tail : forall (X:Type) (x:X) t1 t2, x::t1 = x::t2 -> t1 = t2.
Proof. intros. inversion H. reflexivity. Qed.


Theorem filter_challenge : forall (X:Type) (l1 l2 l:list X) (test:X->bool),
  (filter test l1 = l1) -> (filter test l2 = []) -> inorder_merge l1 l2 l -> (filter test l = l1).
Proof.
 intros. induction H1.
  Case "inorder_nil". assumption.
  Case "inorder_l1". simpl. destruct (test hd) eqn:Hhd.
    SCase "true".  assert (Htl : filter test tl = tl).
    Proof. inversion H. rewrite Hhd in H3. apply same_tail in H3. assumption.
  apply IHinorder_merge in Htl. rewrite Htl. reflexivity. assumption.
    SCase "false". simpl in H. rewrite Hhd in H. inversion H.  inversion H. 
Abort.
(*************************************************************)

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
| ai_here : forall l, appears_in a (a::l)
| ai_later : forall b l, appears_in a l -> appears_in a (b::l).

Lemma appears_in_app: forall (X:Type) (xs ys : list X) (x:X),
  appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof. intros X xs. induction xs as [|hd tl].
  Case "[]". intros. replace ([]++ys) with ys in H. right. assumption. reflexivity. 
  Case "hd::tl". intros. inversion H.
    SCase "ai_here". left. apply ai_here.
    SCase "ai_later". apply IHtl in H1. destruct H1. left. apply ai_later. assumption. right. assumption. Qed.

Lemma app_appears_in: forall (X:Type) (xs ys:list X) (x:X),
  appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof. intros. destruct H.
  Case "left". induction xs as [|hd tl].
    SCase "[]". inversion H.
    SCase "hd::tl". replace ((hd::tl)++ys) with (hd::(tl++ys)).
      inversion H. apply ai_here. apply ai_later. apply IHtl. assumption. reflexivity.
  Case "right". induction xs as [|hd tl].
    SCase "[]". simpl. assumption.
    SCase "hd::tl". replace ((hd::tl)++ys) with (hd::(tl++ys)). 
      apply ai_later. assumption. reflexivity. Qed.

Definition disjoint (X:Type) (l1 l2:list X) : Prop :=
  forall (x:X), appears_in x (l1 ++ l2) -> (appears_in x l1 -> ~(appears_in x l2)) /\ (appears_in x l2 -> ~(appears_in x l1)).

Example dis_ex : disjoint nat [1;2] [4;5].
Proof. unfold disjoint. intros. split.
  Case "left". intro H2. inversion H2. 
    SCase "ai_here". unfold not. intro contra. inversion contra. inversion H4. inversion H7. 
    SCase "ai_later". unfold not. intro contra. inversion H1. rewrite H5 in contra. inversion contra as [|n l' contra2]. inversion contra2. inversion H9.
      inversion H5.
  Case "right".  intro H2. inversion H2. 
    SCase "ai_here". unfold not. intro contra. inversion contra. inversion H4. inversion H7. 
    SCase "ai_later". unfold not. intro contra. inversion H1. rewrite H5 in contra. inversion contra as [|n l' contra2]. inversion contra2. inversion H9.
      inversion H5. Qed.

Inductive no_repeats (X:Type) : list X ->  Prop :=
| nr_nil : no_repeats X []
| nr_cons : forall hd tl, no_repeats X tl -> ~(appears_in hd tl) -> no_repeats X (hd::tl)
.

Inductive nostutter: list nat -> Prop :=
| ns_nil : nostutter []
| ns_single : forall n, nostutter [n]
| ns_cons : forall x1 x2 tl, (x1<>x2) -> nostutter tl -> nostutter (x1::x2::tl)
.
Example nostutter_example_1 : nostutter [1;4;1].
Proof. apply ns_cons. intros contra. inversion contra. apply ns_single. Qed.



