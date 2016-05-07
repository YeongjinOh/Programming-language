Require Export D.



(** **** Exercise: 4 stars (no_whiles_terminating)  *)
(** Imp programs that don't involve while loops always terminate.
    State and prove a theorem [no_whiles_terminating] that says this. *)

(* Hint *)
Check andb_true_iff.

Tactic Notation "com_cases" tactic(first) ident(c) :=
    first;
      [ Case_aux c "CSKIP" | Case_aux c "CASS" | Case_aux c "CSEQ" | Case_aux c "CIf" | Case_aux c "CWHILE" ].

Theorem no_whiles_terminate: forall c st
    (NOWHL: no_whiles c = true),
  exists st', c / st || st'.
Proof.
  intros. generalize dependent st. com_cases (induction c) Case; intros.
  exists st. apply E_Skip.
  exists (update st i (aeval st a)). apply E_Ass. reflexivity.
  inversion NOWHL. rewrite andb_true_iff in H0. destruct H0. apply IHc1 with st in H. destruct H. apply IHc2 with x in H0. destruct H0. exists x0. apply E_Seq with x. apply H. apply H0.
  (* CIf *)
  inversion NOWHL.  rewrite andb_true_iff in H0. destruct H0.
  destruct (beval st b) eqn:Hb. 
  SCase "true". apply IHc1 with st in H. destruct H as [st']. exists st'. apply E_IfTrue; assumption.
  SCase "false". apply IHc2 with st in H0. destruct H0 as [st']. exists st'. apply E_IfFalse; assumption. 
  inversion NOWHL.
Qed.
