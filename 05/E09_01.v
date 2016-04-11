Require Import P09.



Check contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).

