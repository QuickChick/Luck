(* Valuations / maps *)
Require Export Coq.Structures.OrderedTypeEx.
Require Export MSetList.
Require Import FMapList.
Require Import FMapFacts.
Require Import Coq.Arith.EqNat.

Ltac clear_dup :=
  match goal with
    | [ H : ?X |- _ ] =>
      match goal with
        | [ H' : ?Y |- _ ] =>
          match H with
            | H' => fail 2
            | _ => unify X Y ; (clear H' || clear H)
          end
      end
  end.

Ltac clear_dups := repeat clear_dup.

Definition beq_unknown := beq_nat.
Module Map := FMapList.Make(Nat_as_OT).
(* Restrict a valuation to a set of unknowns *)
Module MapProp := FMapFacts.Properties Map.
Module MapFacts := FMapFacts.Facts Map.

Definition liftMaybe {A B} (f : A -> B) (m : option A) : option B :=
  match m with
  | Some a => Some (f a)
  | None   => None                   
  end.

Definition liftMaybe2 {A B C} (f : A -> B -> C) 
           (ma : option A) (mb : option B) : (option C) :=
  match ma, mb with
  | Some a, Some b => Some (f a b)
  | _,_ => None   
  end.

Definition liftMaybe3 {A B C D} (f : A -> B -> C -> D) 
(ma : option A) (mb : option B) (mc : option C)
: (option D) :=
  match ma, mb, mc with
  | Some a, Some b, Some c => Some (f a b c)
  | _,_,_ => None   
  end.

Require Import QArith.
Require Import Coq.PArith.BinPosDef.
Definition div (n m : nat) : Q := 
  Z_of_nat n # Pos.of_nat m.
Notation " a // b " := (div a b) (at level 40).