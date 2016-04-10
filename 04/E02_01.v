Require Import P02.



Check test_repeat1:
  repeat true 2 = cons true (cons true nil).

Check nil_app : forall X:Type, forall l:list X,
  app [] l = l.

Check snoc_with_append : forall X : Type,
                         forall l1 l2 : list X,
                         forall v : X,
  snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).

