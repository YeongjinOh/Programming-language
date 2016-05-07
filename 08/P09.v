Require Export D.



(** **** Exercise: 2 stars (WHILE_true)  *)
(** Prove the following theorem. _Hint_: You'll want to use
    [WHILE_true_nonterm] here. *)

Lemma WHILE_true_nonterm : forall b c st st',
     bequiv b BTrue ->
     ~( (WHILE b DO c END) / st || st' ).
Proof. intros. unfold not. intros. remember (WHILE b DO c END) as Hw. induction H0;  inversion HeqHw; subst.
  unfold bequiv in H. rewrite H in H0. inversion H0.
  contradiction.
Qed.

Theorem WHILE_true: forall b c,
     bequiv b BTrue  ->
     cequiv 
       (WHILE b DO c END)
       (WHILE BTrue DO SKIP END).
Proof. 
  intros. split; intros.
  Case "->". 
    apply WHILE_true_nonterm in H0. inversion H0. assumption.
  Case "<-". 
    assert (~(WHILE BTrue DO SKIP END)/st||st'). apply (WHILE_true_nonterm BTrue SKIP st st'). unfold bequiv. reflexivity. contradiction.
Qed.

