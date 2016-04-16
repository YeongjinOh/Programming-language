Require Export D.

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.

Check (pair 3 5).

Definition fst (p:natprod) : nat :=
 match p with
| pair x y => x
end.

Definition snd (p:natprod) : nat :=
  match p with
| pair x y => y
end.

Notation "( x , y )" := (pair x y).

Eval compute in (fst (3,5)).

Definition swap_pari (p:natprod) : natprod :=
(snd p, fst p).
  
Inductive natlist : Type :=
| nil : natlist
| cons : nat -> natlist -> natlist.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count:nat) : natlist :=
  match count with
| O => nil
| S c => n::(repeat n c)
  end.

Fixpoint length (l:natlist) : nat :=
 match l with
| nil => O
| h::t => S (length t)
 end.

Fixpoint app (l1 l2:natlist) : natlist :=
match l1 with
|[] => l2
|hd::tl => hd::(app tl l2)
end.

Definition hd (default:nat) (l:natlist) : nat :=
match l with
| [] => default
| hd::tl => hd
end.

Definition tl (l:natlist) : natlist :=
match l with
| [] => []
| hd::tl => tl
end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
match l with
|[] => []
|hd::tl => if beq_nat hd 0 then nonzeros tl
          else hd::(nonzeros tl)
end.

Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
match l with
|[] => []
|hd::tl => if oddb hd then hd::(oddmembers tl)
          else oddmembers tl
end.

Example test_oddmembers: oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.


Fixpoint countoddmembers (l:natlist) : nat :=
match l with
|[] => O
|hd::tl => if oddb hd then S (countoddmembers tl)
          else countoddmembers tl
end.

Example test_countoddmembers1: countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers2: countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers3: countoddmembers nil = 0.
Proof. reflexivity. Qed.

Fixpoint snoc (l:natlist) (v:nat) : natlist :=
match l with
| [] => [v]
| hd::tl => hd::(snoc tl v)
end.

Fixpoint rev (l:natlist) : natlist :=
match l with
|[] => []
|hd::tl => snoc (rev tl) hd
end.
Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Inductive natoption : Type :=
|Some : nat ->natoption
|None : natoption
.

Fixpoint index (n:nat) (l:natlist) : natoption :=
match l with
|[] => None
|hd::tl => if beq_nat n 0 then Some hd
          else index (pred n) tl
end.

Example test_index1 : index 0 [4;5;6;7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2 : index 3 [4;5;6;7] = Some 7.
Proof. reflexivity. Qed.
Example test_index3 : index 10 [4;5;6;7] = None.
Proof. reflexivity. Qed.





