Require Export D.



(** **** Problem #6 : 3 stars (map_rev) *)
(** Show that [map] and [rev] commute.  You may need to define an
    auxiliary lemma. *)

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros. induction l. reflexivity.
  simpl. 
  Lemma map_snoc_lemma : forall (X Y:Type) (f:X->Y) (x:X) (l:list X), map f (snoc l x) = snoc (map f l) (f x).
  Proof. intros. induction l. reflexivity.
    simpl. rewrite -> IHl. reflexivity. Qed.
  rewrite -> map_snoc_lemma. rewrite -> IHl. reflexivity.
Qed.

