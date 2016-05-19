Require Export P03.



(** **** Exercise: 2 stars (hoare_asgn_example4)  *)
(** Translate this "decorated program" into a formal proof:
                   {{ True }} ->>
                   {{ 1 = 1 }}
    X ::= 1;;
                   {{ X = 1 }} ->>
                   {{ X = 1 /\ 2 = 2 }}
    Y ::= 2
                   {{ X = 1 /\ Y = 2 }}
*)

Example hoare_asgn_example4 :
  {{fun st => True}} (X ::= (ANum 1);; Y ::= (ANum 2)) 
  {{fun st => st X = 1 /\ st Y = 2}}.
Proof.
  apply hoare_seq with (Q:= (fun st => st X = 1)); unfold hoare_triple; intros.
  inversion H; subst. simpl. split.
  rewrite<-H0. reflexivity.
  reflexivity.
  unfold hoare_triple; intros.
  inversion H; subst. reflexivity.
Qed.

