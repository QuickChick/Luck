Require Import List.

Require Import Coq.QArith.QArith_base.

Definition frac := Q.

Inductive Choice := 
  | Chose : nat -> nat -> Choice. 

Definition trace := list Choice.

(*
Axiom tape : Type.
Axiom frequency : forall {A}, list (nat * A) -> tape -> (A * tape).
Axiom frequency_chooses : 
  forall A (l : list (nat * A)) (t t': tape) (a : A), 
    (a, t') = frequency l t -> exists n, In (n,a) l.
Axiom tape_inhabited : tape.

Axiom frequency_possible :
  forall {A} (l : list (nat * A)) (t' : tape) 
         (n : nat) (a : A),
    In (n, a) l -> n <> O ->
    exists t, frequency l t = (a,t').
*)