Require Export D.
(** **** Problem #1 : 1 star (andb3) *)
(** Do the same for the [andb3] function below. This function should
    return [true] when all of its inputs are [true], and [false]
    otherwise. *)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
match b1,b2,b3 with
|true,true,true => true
|_,_,_ => false
end.

Example test_andb31:                 (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32:                 (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33:                 (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34:                 (andb3 true true false) = false.
Proof. reflexivity. Qed.

