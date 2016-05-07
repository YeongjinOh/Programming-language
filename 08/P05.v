Require Export D.



(** Write a function which compiles an [aexp] into a stack
    machine program. The effect of running the program should be the
    same as pushing the value of the expression on the stack. *)

Fixpoint s_compile (e : aexp) : list sinstr :=
 match e with
| ANum n => [SPush n]
| AId i => [SLoad i]
| APlus a1 a2 => (s_compile a1)++(s_compile a2)++[SPlus]
| AMinus a1 a2 => (s_compile a1)++(s_compile a2)++ [SMinus]
| AMult a1 a2 => (s_compile a1)++(s_compile a2)++ [SMult]
end.

(** After you've defined [s_compile], prove the following to test
    that it works. *)

Example s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof.
  simpl. reflexivity.
Qed.

(** **** Exercise: 3 stars, advanced (stack_compiler_correct)  *)
(** The task of this exercise is to prove the correctness of the
    compiler implemented in the previous exercise.  Remember that
    the specification left unspecified what to do when encountering an
    [SPlus], [SMinus], or [SMult] instruction if the stack contains
    less than two elements.  (In order to make your correctness proof
    easier you may find it useful to go back and change your
    implementation!)

    Prove the following theorem, stating that the [compile] function
    behaves correctly.  You will need to start by stating a more
    general lemma to get a usable induction hypothesis; the main
    theorem will then be a simple corollary of this lemma. *)

Lemma s_execute_app : forall st stack e1 prog2,
  s_execute st stack (s_compile e1 ++ prog2)
    = s_execute st ((aeval st e1)::stack) prog2.
  Proof. intros. generalize dependent prog2. generalize dependent stack. aexp_cases (induction e1) Case; intros; try reflexivity.
 (* APlus *)
  simpl. assert (s_execute st stack (s_compile e1_1 ++ (s_compile e1_2 ++ [SPlus] ++ prog2)) = s_execute st (aeval st e1_1 :: stack) (s_compile e1_2 ++ [SPlus] ++ prog2)). apply IHe1_1. rewrite<-app_assoc. rewrite<-app_assoc. rewrite H. simpl. rewrite IHe1_2. reflexivity.
 (* AMinus *)
  simpl. assert (s_execute st stack (s_compile e1_1 ++ (s_compile e1_2 ++ [SMinus] ++ prog2)) = s_execute st (aeval st e1_1 :: stack) (s_compile e1_2 ++ [SMinus] ++ prog2)). apply IHe1_1. rewrite<-app_assoc. rewrite<-app_assoc. rewrite H. simpl. rewrite IHe1_2. reflexivity.
 (* AMult *)
  simpl. assert (s_execute st stack (s_compile e1_1 ++ (s_compile e1_2 ++ [SMult] ++ prog2)) = s_execute st (aeval st e1_1 :: stack) (s_compile e1_2 ++ [SMult] ++ prog2)). apply IHe1_1. rewrite<-app_assoc. rewrite<-app_assoc. rewrite H. simpl. rewrite IHe1_2. reflexivity.
Qed.

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  intros. aexp_cases (induction e) Case; try reflexivity; 
  simpl; rewrite s_execute_app; rewrite s_execute_app; reflexivity.
Qed.

