Inductive list (X:Type) : Type :=
|nil : list X
|cons : X -> list X -> list X.

Fixpoint app (X:Type) (l1 l2:list X) : list X :=
 match l1 with
 | nil => l2
 | cons hd tl => cons X hd (app X tl l2)
  end.

Fixpoint snoc (X:Type) (l:list X) (v:X) : (list X) :=
  match l with
  | nil => cons X v (nil X)
  | cons hd tl => cons X hd (snoc X tl v)
  end.
  

Fixpoint rev (X:Type) (l:list X) : list X :=
match l with
| nil => nil X
| cons hd tl => snoc X (rev X tl) hd
end.

Check @nil. 

Definition mynil :=@nil nat.

Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with (x,y) => x end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with (x,y) => y end.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.

Require Export D.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  (* If we simply tell Coq apply trans_eq at this point,
     it can tell (by matching the goal against the
     conclusion of the lemma) that it should instantiate X
     with [nat], n with [a,b], and o with [e,f].
     However, the matching process doesn't determine an
     instantiation for m: we have to supply one explicitly
     by adding with (m:=[c,d]) to the invocation of
     apply. *)
  apply trans_eq with (m:=[c;d]). apply eq1. apply eq2. Qed.
