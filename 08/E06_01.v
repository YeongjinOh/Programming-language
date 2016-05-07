Require Import P06.


Check skip_right: forall c,
  cequiv 
    (c;; SKIP) 
    c.

