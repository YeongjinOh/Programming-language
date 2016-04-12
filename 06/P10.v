Require Export D.



(** 3 star (even__ev)  
    Note that proving [even__ev] directly is hard.
    You might find it easier to prove [even__ev_strong] first
    and then prove [even__ev] using it.
*)

Lemma even__ev_weak: forall n: nat,
  (even n -> ev n) /\ (even (S n) -> ev (S n)).
Proof.
  induction n. 
  Case "n = 0". split. intro H. apply ev_0. intro Hcontra. inversion Hcontra.
  Case "n = S n". inversion IHn. split. apply H0.
    intro HSS. apply ev_SS. unfold even in HSS. simpl in HSS. apply H. apply HSS. Qed.

Lemma even__ev_strong: forall n : nat, 
  (even (pred n) -> ev (pred n)) /\ (even n -> ev n).
Proof.
  induction n.
  Case "n = 0". simpl. split. intro H. apply ev_0. intro H. apply ev_0.
  Case "n = S n". simpl. apply even__ev_weak. Qed.

Theorem even__ev: forall n : nat,
  even n -> ev n.
Proof.
  intro. apply even__ev_strong.
  Qed.

