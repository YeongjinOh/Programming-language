(** **** SNU 4190.310, 2016 Spring *)

(** Assignment 06 *)
(** Due: 2016/04/24 23:59 *)

(* Important: 
   - Do NOT import other files.

   - You are NOT allowed to use the [admit] tactic.

   - You are NOT allowed to use the following tactics.
     [tauto], [intuition], [firstorder], [omega].

   - Just leave [exact GIVEUP] for those problems that you fail to prove.
*)

Definition GIVEUP {T: Type} : T.  Admitted.

Require Export Logic.

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

Definition even (n:nat) : Prop := 
  evenb n = true.

Inductive ev : forall (n: nat), Prop :=
  | ev_0 : ev O
  | ev_SS : forall (n:nat) (pf_evn :ev n), ev (S (S n))
.

Inductive beautiful : nat -> Prop :=
| b_0   : beautiful 0
| b_3   : beautiful 3
| b_5   : beautiful 5
| b_sum : forall n m (beuty_n:beautiful n) (beauty_m: beautiful m),
            beautiful (n+m)
.

Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n)
.

Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall (witness:X) (proof: P witness), ex X P.

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

Theorem eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  (* WORKED IN CLASS *)
  intros n.
  induction n as [|n'].
  Case "n = 0".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      left. reflexivity.
    SCase "m = S m'".
      right. intros contra. inversion contra.
  Case "n = S n'".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      right. intros contra. inversion contra.
    SCase "m = S m'". 
      destruct IHn' with (m := m') as [eq | neq].
      left. apply f_equal.  apply eq.
      right. intros Heq. inversion Heq as [Heq']. apply neq. apply Heq'.
Defined. 

Definition override' {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
  fun (k':nat) => if eq_nat_dec k k' then x else f k'.

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

Inductive repeats {X:Type} : list X -> Prop :=
| rp_base: forall x l, appears_in x l -> repeats (x::l)
| rp_next: forall x l, repeats l -> repeats (x::l)
.

