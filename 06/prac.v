Require Export D.



(** 1 star (double_even)  *)
Theorem double_even : forall n,
  ev (double n).
Proof.
  intro n. induction n. 
  Case "n = 0". simpl. apply ev_0.
  Case "n = S n". simpl. apply ev_SS. apply IHn.
  Qed.

(** 2 stars (ev_sum)  *)
Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof. 
  intros n m Hn Hm. induction Hn.
  Case "n = 0". simpl. apply Hm.
  simpl. apply ev_SS. apply IHHn. Qed.

(** 3 stars, advanced (ev_ev__ev)  *)
(** Finding the appropriate thing to do induction on is a
    bit tricky here: *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m. 
Proof.
  intros n m Hnm Hn. induction Hn. simpl in Hnm. apply Hnm.
  inversion Hnm. apply IHHn. apply pf_evn.
Qed.

(** 3 stars, optional (ev_plus_plus)  *)
(** Here's an exercise that just requires applying existing lemmas.  No
    induction or even case analysis is needed, but some of the rewriting
    may be tedious. 
    Hint: You can use [plus_comm], [plus_assoc], [double_plus], [double_even], [ev_sum], [ev_ev__ev].
*)

Check plus_comm.
Check plus_assoc.
Check double_plus.
Check double_even.
Check ev_sum.
Check ev_ev__ev.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p Hnm Hnp. 
  assert (Hnnmp : ev((n+m)+(n+p))).
  Proof. apply ev_sum with (n:=n+m) (m:=n+p). apply Hnm. apply Hnp. (* end of assertion *)
  assert (Hplus: n+m+(n+p) = double n+(m+p)).
  Proof. rewrite->plus_assoc. rewrite<-plus_assoc with (p:=n). rewrite -> plus_comm with (m:=n). rewrite->plus_assoc. rewrite -> double_plus. rewrite -> plus_assoc. reflexivity.
  rewrite->Hplus in Hnnmp. apply ev_ev__ev with (n:=double n) (m:= m+p) in Hnnmp. apply Hnnmp. apply double_even.
  Qed.


Theorem ev_plus_plus2 : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p Enm Enp.
  apply ev_sum with (n:=n+m) (m:=n+p) in Enm.
  (* (n + m) + (n + p) *)
  replace ((n+m) + (n+p)) with ((n + n) + (m + p)) in Enm.
  replace (n+n) with (double n) in Enm.
  apply ev_ev__ev with (m:=m+p) in Enm.
  apply Enm.
  replace (double n + (m + p) + (m + p)) with (double n + ((m + p) + (m + p))).
  replace  (m + p + (m + p)) with (double (m + p)).
  apply ev_sum.
  apply double_even.
  apply double_even.
  apply double_plus with (n:=m+p).
  apply plus_assoc with (n:=double n).
  apply double_plus.
  rewrite <- plus_assoc.
  replace (n+(m+p)) with (m+(n+ p)).
  rewrite plus_assoc.
  reflexivity.
  apply plus_swap'.
  apply Enp.
Qed.

Theorem even__ev : forall n : nat,
  (even n -> ev n) /\ (even (S n) -> ev (S n)).
Proof.
  induction n.
  Case "0". split.
    intros. apply ev_0.
    intros. inversion H.
  Case "S n". intros.
    split. apply IHn.
           intro. apply ev_SS. unfold even in H. simpl in H.
                  apply IHn. apply H.
Qed.
