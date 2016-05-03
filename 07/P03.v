Require Export D.



(** **** Exercise: 3 stars  (bevalR)  *)
(** Write a relation [bevalR] in the same style as
    [aevalR], and prove that it is equivalent to [beval].*)

    Print bexp.
    Print aevalR. 
Inductive bevalR: bexp -> bool -> Prop :=
| E_BTrue : bevalR BTrue true 
| E_BFalse : bevalR BFalse false
| E_BEq : forall (a1 a2:aexp) (n1 n2:nat), 
    a1 || n1 ->
    a2 || n2 ->
    bevalR (BEq a1 a2) (beq_nat n1 n2)
| E_BLe : forall (a1 a2:aexp) (n1 n2:nat),
    a1 || n1 ->
    a2 || n2 ->
    bevalR (BLe a1 a2) (ble_nat n1 n2)
| E_BNot : forall (b:bexp) (bv:bool),
    bevalR b bv ->
    bevalR (BNot b) (negb bv)
| E_BAnd : forall (b1 b2:bexp) (bv1 bv2:bool),
    bevalR b1 bv1 ->
    bevalR b2 bv2 ->
    bevalR (BAnd b1 b2) (andb bv1 bv2).

Tactic Notation "bexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BTrue" | Case_aux c "BFalse"
  | Case_aux c "BEq"   | Case_aux c "BLe" 
  | Case_aux c "BNot"  | Case_aux c "BAnd" ].

Tactic Notation "bevalR_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_BTrue" | Case_aux c "E_BFalse"
  | Case_aux c "E_BEq"   | Case_aux c "E_BLe" 
  | Case_aux c "E_BNot"  | Case_aux c "E_BAnd" ].

Lemma aevalR_a_aeval_a : forall a, a || aeval a.
Proof. intros. induction a; simpl; try constructor; assumption; assumption.
Qed.

Lemma bevalR_b_beval_b : forall b, bevalR b (beval b).
Proof. intros. induction b; simpl; constructor;
  try apply aevalR_a_aeval_a; try assumption. Qed.
 
Theorem beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
  split.
  Case "->". intros. bevalR_cases (induction H) SCase; simpl;  try (rewrite aeval_iff_aevalR in *; rewrite H; rewrite H0); try (rewrite IHbevalR); try (rewrite IHbevalR1); try (rewrite IHbevalR2); try reflexivity.
  Case "<-". intros. bexp_cases (destruct b) SCase; rewrite <- H; simpl; constructor; try apply aevalR_a_aeval_a; try apply bevalR_b_beval_b.
Qed.
