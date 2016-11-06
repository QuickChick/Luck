Require Import Util.
Require Import List. Import ListNotations.
Require Import ListSet.
Require Import Arith.

Definition tvar := nat.

Inductive type := 
  | TUnit : type
  | TVar  : tvar -> type
  | TSum  : type -> type -> type
  | TProd : type -> type -> type
  | TFun  : type -> type -> type
  | TMu   : type -> type.

Inductive isNonFunType : type -> Prop := 
  | NFUnit : isNonFunType TUnit
  | NFVar  : forall X, isNonFunType (TVar X)
  | NFSum  : forall T1 T2, 
      isNonFunType T1 ->
      isNonFunType T2 ->
      isNonFunType (TSum T1 T2)
  | NFProd  : forall T1 T2, 
      isNonFunType T1 ->
      isNonFunType T2 ->
      isNonFunType (TProd T1 T2)
  | NFMu : forall T,
      isNonFunType T ->
      isNonFunType (TMu T).

(* Associate unknowns with a type *)
Definition u_ctx := Map.t type.

(* Associate varibles with a type *)
Definition v_ctx := Map.t type.

Notation "∅" := (Map.empty type).

Definition var := nat.
Definition unknown := nat.

Inductive exp := 
  | Var     : forall (x : var), exp 
  | Unit    : exp
  | Rec     : forall (f x : var), type -> type -> exp -> exp
  | App     : exp -> exp -> exp                                     
  | Pair    : exp -> exp -> exp
  | CaseP   : exp -> forall (x y : var), exp -> exp
  | Inl     : type -> type -> exp -> exp
  | Inr     : type -> type -> exp -> exp 
  | Case    : exp -> forall (x : var), exp -> 
                     forall (y : var), exp -> exp
  | Fold    : type -> exp -> exp 
  | Unfold  : type -> exp -> exp 
  | U       : unknown -> exp
  | Inst    : exp -> exp -> exp -> exp
  | Bang    : exp -> exp 
  | Til     : exp -> type -> exp -> exp
(*  | Fix     : exp -> exp
    | FixU    : set unknown -> exp -> exp
    | Fresh   : var -> type -> exp -> exp
*).

Theorem eq_var_dec : forall x y : var, {x = y} + {~ (x = y)}.
decide equality.
Qed.

Theorem eq_unknown_dec : forall x y : unknown, {x = y} + {~ (x = y)}.
decide equality.
Qed.

Theorem eq_tvar_dec : forall x y : tvar, {x = y} + {~ (x = y)}.
decide equality.
Qed.

Fixpoint shift (c : nat) (T : type) : type :=
  match T with
    | TUnit => TUnit
    | TVar x => match lt_dec x c with
                  | left _  => TVar x 
                  | right _ => TVar (S x)
                end
    | TSum  T₁ T₂ => TSum (shift c T₁) (shift c T₂)
    | TProd T₁ T₂ => TProd (shift c T₁) (shift c T₂)
    | TFun  T₁ T₂ => TFun (shift c T₁) (shift c T₂)
    | TMu T' => shift (S c) T'
  end.

Fixpoint substT (x : tvar) (t t' : type) : type :=
  match t' with
    | TUnit => TUnit
    | TVar x' => 
      if eq_tvar_dec x x' then t
      else TVar x'
    | TSum t₁ t₂ =>
      TSum (substT x t t₁) (substT x t t₂)
    | TProd t₁ t₂ =>
      TProd (substT x t t₁) (substT x t t₂)
    | TFun t₁ t₂ =>
      TFun (substT x t t₁) (substT x t t₂)
    | TMu T =>
      TMu (substT (S x) (shift O t) T)
  end.

Definition NatType := 
  TMu (TSum TUnit (TVar O)).

Definition NatListType := 
  TMu (TSum TUnit (TProd NatType (TVar O))).

(*
Eval simpl in 
    substT O NatListType (TSum TUnit (TProd NatType (TVar O))).
*)

Reserved Notation "U ; Γ ⊢ e ↦ T" (at level 20).

Inductive has_type : 
  u_ctx -> v_ctx -> exp -> type -> Prop :=
| T_Var  : forall x U Γ T,
             Map.MapsTo x T Γ ->
             U; Γ ⊢ Var x ↦ T
| T_Unit : forall U Γ, 
             U; Γ ⊢ Unit ↦ TUnit
| T_Abs : forall U Γ Γ' T₁ T₂ f x e,
             Γ' = Map.add x T₁ 
                  (Map.add f (TFun T₁ T₂) Γ) ->
             U; Γ' ⊢ e ↦ T₂ ->
             U; Γ  ⊢ Rec f x T₁ T₂ e ↦ TFun T₁ T₂
| T_App : forall U Γ e₁ e₂ T₁ T₂, 
   U; Γ ⊢ e₁ ↦ TFun T₁ T₂ ->
   U; Γ ⊢ e₂ ↦ T₁ -> 
   U; Γ ⊢ App e₁ e₂ ↦ T₂
| T_Pair : forall U Γ e₁ e₂ T₁ T₂,
   U; Γ ⊢ e₁ ↦ T₁ ->
   U; Γ ⊢ e₂ ↦ T₂ -> 
   U; Γ ⊢ Pair e₁ e₂ ↦ TProd T₁ T₂
| T_CaseP : forall U Γ e x y e' T₁ T₂ T,
   U; Γ ⊢ e ↦ TProd T₁ T₂ ->
   U; Map.add x T₁ (Map.add y T₂ Γ) ⊢ e' ↦ T ->
   U; Γ ⊢ CaseP e x y (* T₁ T₂ *) e' ↦ T
| T_Inl : forall U Γ e T₁ T₂,
   U; Γ ⊢ e ↦ T₁ ->
   U; Γ ⊢ Inl T₁ T₂ e ↦ TSum T₁ T₂
| T_Inr : forall U Γ e T₁ T₂,
   U; Γ ⊢ e ↦ T₂ ->
   U; Γ ⊢ Inr T₁ T₂ e ↦ TSum T₁ T₂
| T_Case : forall U Γ e T₁ T₂ x e₁ y e₂ T,
   U; Γ ⊢ e ↦ TSum T₁ T₂ ->
   U; (Map.add x T₁ Γ) ⊢ e₁ ↦ T ->
   U; (Map.add y T₂ Γ) ⊢ e₂ ↦ T ->
   U; Γ ⊢ Case e x e₁ y e₂ ↦ T
| T_Fold : forall U Γ e T,
   U; Γ ⊢ e ↦ substT O (TMu T) T ->
   U; Γ ⊢ Fold (TMu T) e ↦ TMu T
| T_Unfold : forall U Γ e T,
   U; Γ ⊢ e ↦ TMu T ->
   U; Γ ⊢ Unfold (TMu T) e ↦ substT O (TMu T) T
(* TODO: Make these not fun types *)
| T_Unknown : forall U' Γ u T,
   Map.MapsTo u T U' ->                
   U'; Γ ⊢ U u ↦ T     
| T_Inst : forall U Γ e T₁ T₂ e₁ e₂,
   isNonFunType (TSum T₁ T₂) ->
   U; Γ ⊢ e ↦ TSum T₁ T₂ ->
   U; Γ ⊢ e₁ ↦ NatType ->
   U; Γ ⊢ e₂ ↦ NatType ->
   U; Γ ⊢ Inst e e₁ e₂ ↦ TSum T₁ T₂
| T_Bang : forall U Γ e T,
   isNonFunType T ->
   U; Γ ⊢ e ↦ T ->
   U; Γ ⊢ Bang e ↦ T
| T_Til : forall U Γ e₁ e₂ T₁ T₂,
   U; Γ ⊢ e₁ ↦ T₁ ->
   U; Γ ⊢ e₂ ↦ T₂ ->
   U; Γ ⊢ Til e₁ T₂ e₂ ↦ T₁

where "U ; Γ ⊢ e ↦ T" := (has_type U Γ e T).

Fixpoint subst (x:var) (s:exp) (e:exp) : exp :=
  match e with
  | Var x' => if eq_var_dec x x' then s else e
  | Unit   => Unit                                                
  | Rec f x' T₁ T₂ e => 
      Rec f x' T₁ T₂ 
          (if eq_var_dec x x' then e 
           else if eq_var_dec x f then e 
           else subst x s e)
  | App e1 e2 => App (subst x s e1) (subst x s e2)
  | Pair e1 e2 => Pair (subst x s e1) (subst x s e2)
  | CaseP e x' y' (* T₁ T₂ *) e' => 
    CaseP (subst x s e) x' y' (* T₁ T₂*)
         (if eq_var_dec x x' then e' 
          else if eq_var_dec x y' then e'
          else subst x s e')
  | Inl T₁ T₂ e => Inl T₁ T₂ (subst x s e)
  | Inr T₁ T₂ e => Inr T₁ T₂ (subst x s e)
  | Case e x' ex y' ey => 
    Case (subst x s e) x' 
         (if eq_var_dec x x' then ex else (subst x s ex))
         y' 
         (if eq_var_dec x y' then ey else (subst x s ey))
  | U u => U u
  | Inst e el er => Inst (subst x s e) (subst x s el) (subst x s er)
  | Bang e => Bang (subst x s e)
  | Fold T e => Fold T (subst x s e)
  | Unfold T e => Unfold T (subst x s e)
  | Til e₁ T₂ e₂ => Til (subst x s e₁) T₂ (subst x s e₂)
  end.

Notation "'[' x ':=' v ']' e" := (subst x v e) (at level 20).

Inductive is_value : exp -> Prop :=
  | VUnit    : is_value Unit
  | VU : forall u, is_value (U u)
  | VPair    : forall e₁ e₂, 
      is_value e₁ -> is_value e₂ ->
      is_value (Pair e₁ e₂)
  | VInl     : forall e T₁ T₂, 
      is_value e -> 
      is_value (Inl T₁ T₂ e)
  | VInr     : forall e T₁ T₂,
      is_value e -> 
      is_value (Inr T₁ T₂ e)
  | VRec     : forall f x T₁ T₂ e, 
      is_value (Rec f x T₁ T₂ e)
  | VFold : forall e T, 
      is_value e -> 
      is_value (Fold T e).
Inductive nat_denote : exp -> nat -> Prop :=
| Nat_O : 
    forall T T1 T2, 
      nat_denote (Fold T (Inl T1 T2 Unit)) O
| Nat_S :
    forall T T1 T2 e n,
      nat_denote e n ->
      nat_denote (Fold T (Inr T1 T2 e)) (S n).

Definition zero := 
  Fold NatType (Inl TUnit NatType Unit).

Lemma well_typed_zero : 
  ∅; ∅ ⊢ zero ↦ NatType.
unfold NatType.
constructor.
simpl.
destruct (eq_tvar_dec O O) eqn:Eq; 
try solve [exfalso; auto].
constructor.
constructor.
Qed. 

Definition one := 
  Fold NatType (Inr TUnit NatType 
               (zero)).

Lemma well_typed_one : 
  ∅; ∅ ⊢ one ↦ NatType.
constructor.
simpl.
destruct (eq_tvar_dec O O) eqn:Eq; 
try solve [exfalso; auto].
constructor.
constructor.
simpl.
destruct (eq_tvar_dec O O) eqn:Eq';
try solve [exfalso; auto].
constructor.
constructor.
Qed.

Ltac discharge_empty := 
  match goal with 
    | [ H : Map.MapsTo _ _ ∅ |- _ ] => 
      exfalso; apply MapProp.F.empty_mapsto_iff in H;
      auto
    | _ => idtac
  end.

Definition exp_nat_rect :=
fun (P : exp -> Type) 
  f f0 f1 f2 f3 f4 f5 f6 f7 (* f8 *) f9 f10 f11 f12
  f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 =>

fix F (e : exp) : P e :=
  match e with
  | Var v => f v
  | Unit => f0
  | Rec v v0 t1 t2 e0 => f1 v v0 t1 t2 e0 (F e0)
  | App e0 e1 => f2 e0 (F e0) e1 (F e1)
  | Pair e0 e1 => f3 e0 (F e0) e1 (F e1)
  | CaseP e0 v v0 e1 => f4 e0 (F e0) v v0 e1 (F e1)
  | Inl t t0 e0 => f5 t t0 e0 (F e0)
  | Inr t t0 e0 => f6 t t0 e0 (F e0)
  | Case e0 v e1 v0 e2 => f7 e0 (F e0) v e1 (F e1) v0 e2 (F e2)
  | Unfold t e0 => f9 t e0 (F e0)
  | U u => f10 u
  | Inst e0 e1 e2 => f11 e0 (F e0) e1 (F e1) e2 (F e2)
  | Bang e0 => f12 e0 (F e0)
  | Til e0 t1 e2 => f27 e0 (F e0) t1 e2 (F e2)
  | Fold t e0 => 
    match e0 with 
    | Var v => f13 t v
    | Unit => f14 t
    | Rec v v0 t1' t2' e0 => f15 t v v0 t1' t2' e0 (F e0)
    | App e0 e1 => f16 t e0 (F e0) e1 (F e1)
    | Pair e0 e1 => f17 t e0 (F e0) e1 (F e1)
    | CaseP e0 v v0 e1 => f18 t e0 (F e0) v v0 e1 (F e1)
    | Inl t1 t2 e0 => f19 t t1 t2 e0 (F e0)
    | Inr t1 t2 e0 => f20 t t1 t2 e0 (F e0)
    | Case e0 v e1 v0 e2 => f21 t e0 (F e0) v e1 (F e1) v0 e2 (F e2)
    | Fold t' e1 => f22 t t' e1 (F e1)
    | Unfold t' e0 => f23 t t' e0 (F e0)
    | U u => f24 t u
    | Inst e0 e1 e2 => f25 t e0 (F e0) e1 (F e1) e2 (F e2)
    | Bang e0 => f26 t e0 (F e0)
    | Til e0 t1 e2 => f28 t e0 (F e0) t1 e2 (F e2)
    end
  end.

Require Import ssreflect.
Lemma nat_denote_typed : 
forall e , is_value e -> 
  ∅ ; ∅ ⊢ e ↦ NatType ->
  exists n, nat_denote e n.
Proof.
move => e.
induction e using exp_nat_rect;
move => HV HT;
inversion HV; inversion HT; clear HV HT;
subst; try solve [unfold NatType in *; simpl in *; 
                  congruence];
discharge_empty;
match goal with 
  | [H : is_value _ |- _ ] =>
    try solve [inversion H]
end;
simpl in *;
destruct (eq_tvar_dec O O) 
  as [tmp | tmp] eqn:Eq;
try solve [exfalso; auto]; clear Eq tmp;
match goal with 
  | [H : ∅; ∅ ⊢ _ ↦ _ |- _] => 
    inversion H; subst; clear H
end;
discharge_empty.
+ (* Inl Unit *)
  inversion H0; inversion H3; 
  clear H0 H3; subst; simpl in *; 
  try congruence; discharge_empty;
  match goal with 
  | [H : is_value _ |- _ ] =>
    try solve [inversion H]
  end.
  exists O; econstructor; eauto.
+ (* Inr nat *)
  fold NatType in H3.
  inversion H0.
  move: {IHe} (IHe H1 H3) => [n Hn].
  exists (S n).
  econstructor; eauto.
Qed.  


(* Predicate (standard) Semantics *)
Reserved Notation "e ⇓ v" (at level 40).

Inductive pred : exp -> exp -> Prop :=
  | SVal : forall v,
      is_value v -> v ⇓ v
  | SApp : forall e₁ e₂ f x T₁ T₂ e v v₂,
      e₁ ⇓ Rec f x T₁ T₂ e ->
      e₂ ⇓ v₂ -> 
      ([f := (Rec f x T₁ T₂ e)] ([x := v₂] e)) ⇓ v ->
      (App e₁ e₂) ⇓ v
  | SPair : forall e₁ v₁ e₂ v₂,
      ~ (is_value (Pair e₁ e₂)) ->
      e₁ ⇓ v₁ -> e₂ ⇓ v₂ ->              
      (Pair e₁ e₂) ⇓ (Pair v₁ v₂)
  | SCaseP : forall e x y e' v₁ v₂ v', (* T₁ T₂,*)
      e ⇓ (Pair v₁ v₂) ->
      [y := v₂]([x := v₁] e') ⇓ v' ->
      (CaseP e x y (* T₁ T₂ *) e') ⇓ v'
  | SInl : forall e t1 t2 v, 
      ~ (is_value (Inl t1 t2 e)) ->
      e ⇓ v -> (Inl t1 t2 e) ⇓ (Inl t1 t2 v)
  | SInr : forall e v t1 t2, 
      ~ (is_value (Inr t1 t2 e)) ->
      e ⇓ v -> (Inr t1 t2 e) ⇓ (Inr t1 t2 v)
  | SCaseInl : forall e v x t1 t2 v₁ e₁ y e₂,
      e ⇓ (Inl t1 t2 v) -> 
      ([x := v] e₁) ⇓ v₁ ->
      (Case e x e₁ y e₂) ⇓ v₁
  | SCaseInr : forall e v x t1 t2 v₂ e₁ y e₂,
      e ⇓ (Inr t1 t2 v) -> 
      ([y := v] e₂) ⇓ v₂ ->
      (Case e x e₁ y e₂) ⇓ v₂
  | SInst : forall e e₁ e₂ v v₁ v₂ n₁ n₂,
              e ⇓ v -> e₁ ⇓ v₁ -> e₂ ⇓ v₂ ->
              nat_denote v₁ n₁ -> n₁ <> O ->
              nat_denote v₂ n₂ -> n₂ <> O ->
              (Inst e e₁ e₂) ⇓ v
  | SBang : forall e v, 
              e ⇓ v ->
              (Bang e) ⇓ v
  | SFold : forall e T v,
              ~ (is_value (Fold T e)) ->
              e ⇓ v ->
              Fold T e ⇓ Fold T v
  | SUnfold : forall e T v,
                e ⇓ Fold T v ->
                Unfold T e ⇓ v
  | STil : forall e₁ T₂ e₂ v v',
             e₁ ⇓ v ->
             e₂ ⇓ v' ->
             Til e₁ T₂ e₂ ⇓ v

where "e ⇓ v" := (pred e v).

Lemma pred_result_is_value : 
  forall e v, e ⇓ v -> is_value v.
intros e v H.
induction H; auto; try solve [constructor; auto].
inversion IHpred; auto.
Qed.

Inductive appears_free_in : var -> exp -> Prop :=
  | afi_var : forall x, 
      appears_free_in x (Var x)
  | afi_rec : forall y f x T₁ T₂ e,
      y <> f -> y <> x -> 
      appears_free_in y e ->
      appears_free_in y (Rec f x T₁ T₂ e)
  | afi_app_1 : forall x e1 e2,
      appears_free_in x e1 ->
      appears_free_in x (App e1 e2)
  | afi_app_2 : forall x e1 e2,
      appears_free_in x e2 ->
      appears_free_in x (App e1 e2)
  | afi_pair_1 : forall x e1 e2,
      appears_free_in x e1 ->
      appears_free_in x (Pair e1 e2)
  | afi_pair_2 : forall x e1 e2,
      appears_free_in x e2 ->
      appears_free_in x (Pair e1 e2)
  | afi_casep_1 : forall x x' y' e e',
      appears_free_in x e -> 
      appears_free_in x (CaseP e x' y' e')
  | afi_casep_2 : forall x x' y' e e', 
      x <> x' -> x <> y' ->
      appears_free_in x e' ->
      appears_free_in x (CaseP e x' y' e')
  | afi_inl : forall x t1 t2 e, 
      appears_free_in x e ->
      appears_free_in x (Inl t1 t2 e)
  | afi_inr : forall x t1 t2 e, 
      appears_free_in x e ->
      appears_free_in x (Inr t1 t2 e)
  | afi_case_1 : forall x e x' ex y' ey,
      appears_free_in x e ->
      appears_free_in x (Case e x' ex y' ey) 
  | afi_case_2 : forall x e x' ex y' ey,
      x <> x' -> appears_free_in x ex ->
      appears_free_in x (Case e x' ex y' ey) 
  | afi_case_3 : forall x e x' ex y' ey,
      x <> y' -> appears_free_in x ey ->
      appears_free_in x (Case e x' ex y' ey) 
  | afi_fold : forall x t e, 
      appears_free_in x e ->
      appears_free_in x (Fold t e)
  | afi_unfold : forall x t e, 
      appears_free_in x e ->
      appears_free_in x (Unfold t e)
  | afi_inst_1 : forall x e e1 e2,
      appears_free_in x e ->
      appears_free_in x (Inst e e1 e2)
  | afi_inst_2 : forall x e e1 e2,
      appears_free_in x e1 ->
      appears_free_in x (Inst e e1 e2)
  | afi_inst_3 : forall x e e1 e2,
      appears_free_in x e2 ->
      appears_free_in x (Inst e e1 e2)
  | afi_bang : forall x e,
      appears_free_in x e ->
      appears_free_in x (Bang e)
  | afi_til_1 : forall x e₁ T e₂,
      appears_free_in x e₁ ->
      appears_free_in x (Til e₁ T e₂)
  | afi_til_2 : forall x e₁ T e₂,
      appears_free_in x e₂ ->
      appears_free_in x (Til e₁ T e₂).

Definition closed (e : exp) :=
forall x, ~ (appears_free_in x e).

Ltac applyIH IH TF HTF :=
  match goal with
    | [ H : ?U; Map.add ?X ?T1 ?G 
                        ⊢ ?E ↦ ?T3 |- _ ] =>
      move : {IH} (IH U 
              (Map.add X T1 G)
               T3 H) => [TF HTF]
  end.

Lemma free_in_context :
forall x e,
  appears_free_in x e ->
  forall U Γ T, U; Γ ⊢ e ↦ T ->
  exists T', Map.MapsTo x T' Γ.
move => x e H;
induction H;
move => U Γ T' HT';
inversion HT'; subst; eauto;
applyIH IHappears_free_in TF HTF;
exists TF;
repeat (apply MapProp.F.add_mapsto_iff in HTF;
  move : HTF => [[Contra _] | [? HTF]];
  try solve [exfalso; auto]); eauto.
Qed.

Lemma typeable_empty__closed :
forall e T U, U; ∅ ⊢ e ↦ T -> closed e.
unfold closed.
move => e T U H x H'.
apply free_in_context with (x := x) in H; auto.
- move : H => [T' Contra].
  apply MapProp.F.empty_mapsto_iff in Contra.
  auto.
Qed.

Hint Constructors appears_free_in.

Ltac discharge_mapsto_add :=
    repeat (
      repeat match goal with 
        | [ |- Map.MapsTo _ _ (Map.add _ _ _) ] => 
          apply MapProp.F.add_mapsto_iff
        | [ H : Map.MapsTo _ _ (Map.add _ _ _) |- _ ] =>
          apply MapProp.F.add_mapsto_iff in H
        | [ H : _ \/ _ |- _ ] =>
          move : H => [[? ?] | [? ?]]
      end;
      try solve [left; auto]; 
      right; repeat split; auto).

Lemma context_invariance : forall Γ U e T, 
  U; Γ ⊢ e ↦ T -> 
  forall Γ', 
    (forall x T', appears_free_in x e -> 
                  Map.MapsTo x T' Γ -> 
                  Map.MapsTo x T' Γ') ->
  U; Γ' ⊢ e ↦ T.
Proof. 
move => Γ U e T H; induction H;
move => Γ₀ HM; 
try solve [ auto; econstructor;
  match goal with 
      | [ H  : _; _ ⊢ ?E ↦ _
        , IH : forall _, _ -> _; _ ⊢ ?E ↦ _
        |- _; _ ⊢ ?E ↦ _ ] => 
        apply IH; intros; apply HM; auto
  end
].
+ constructor. apply HM.
  constructor.
+ auto.
+ eapply T_Abs; eauto.
  apply IHhas_type.
  move => x' T' HFree HMap.
  rewrite H in HMap.
  discharge_mapsto_add.
+ eapply T_CaseP; auto.
  apply IHhas_type2; intros; discharge_mapsto_add.
+ eapply T_Case; auto.
    apply IHhas_type2; intros; discharge_mapsto_add.
    apply IHhas_type3; intros; discharge_mapsto_add.
+ constructor; auto.
+ constructor; auto.
+ constructor; auto.
Qed.

Lemma restrict_mapsto :
  forall u {A} (s s' : Map.t A) a,
    Map.MapsTo u a s ->
    Map.Equiv eq (MapProp.restrict s' s) s ->
    Map.MapsTo u a s'.
move => u A s s' a HMap [HIn HMapsTo].
specialize (HIn u).
assert (Map.In u s) by (exists a; auto).
move : HIn => [_ HIn].
move : {HIn} (HIn H) => [a' Ha'].
assert (a' = a) by (eapply HMapsTo; eauto).
assert (Hyp : Map.MapsTo u a' (MapProp.restrict s' s)) 
  by auto; clear Ha'.
apply MapProp.restrict_mapsto_iff in Hyp.
inversion Hyp; subst; auto.
Qed.

Lemma unknown_invariance : forall Γ U e T,
  U; Γ ⊢ e ↦ T -> 
  forall U', Map.Equiv eq (MapProp.restrict U' U) U ->
  U'; Γ ⊢ e ↦ T.
move => Γ U e T H; induction H; move => U₀ HU';
try solve [econstructor; eauto].
constructor; auto.
eapply restrict_mapsto; eauto.
Qed.

Lemma context_order_swap : 
 forall U x' x f T' Tx Tf e T Γ,
   x' <> x -> x' <> f ->
   U; Map.add x Tx (Map.add f Tf (Map.add x' T' Γ)) 
              ⊢ e ↦ T ->
   U; Map.add x' T' (Map.add x Tx (Map.add f Tf Γ)) 
              ⊢ e ↦ T.
intros.
eapply context_invariance; eauto; intros.
apply MapProp.F.add_mapsto_iff.
destruct (eq_var_dec x' x0) eqn:Eq1;
destruct (eq_var_dec x  x0) eqn:Eq2;
destruct (eq_var_dec f  x0) eqn:Eq3;
apply MapProp.F.add_mapsto_iff in H3;
move: H3 => [[? ?]|[? H3]]; 
try solve [subst; exfalso; auto];
try (
  apply MapProp.F.add_mapsto_iff in H3;
  move: H3 => [[? ?]|[? H3]]; 
  try solve [subst; exfalso; auto]
);
try (
  apply MapProp.F.add_mapsto_iff in H3;
  move: H3 => [[? ?]|[? H3]]; 
  try solve [subst; exfalso; auto]
); 
repeat (
  try solve [left; auto];
  right; split; auto;
  apply MapProp.F.add_mapsto_iff
).
Qed.

Lemma context_order_swap_small : 
 forall U x' x T' Tx e T Γ,
   x' <> x ->
   U; Map.add x Tx (Map.add x' T' Γ) ⊢ e ↦ T ->
   U; Map.add x' T' (Map.add x Tx Γ) ⊢ e ↦ T.
intros.
eapply context_invariance; eauto; intros.
apply MapProp.F.add_mapsto_iff.
destruct (eq_var_dec x' x0) eqn:Eq1;
destruct (eq_var_dec x  x0) eqn:Eq2;
apply MapProp.F.add_mapsto_iff in H2;
move: H2 => [[? ?]|[? H3]]; 
try solve [subst; exfalso; auto];
try (
  apply MapProp.F.add_mapsto_iff in H3;
  move: H3 => [[? ?]|[? H3]]; 
  try solve [subst; exfalso; auto]
);
try (
  apply MapProp.F.add_mapsto_iff in H3;
  move: H3 => [[? ?]|[? H3]]; 
  try solve [subst; exfalso; auto]
);
repeat (
  try solve [left; auto];
  right; split; auto;
  apply MapProp.F.add_mapsto_iff
).
Qed.

Lemma substitution_lemma : 
  forall e U Γ x e' t T, 
    U; Map.add x T Γ ⊢ e ↦ t ->
    U; ∅ ⊢ e' ↦ T ->
    U; Γ ⊢ [x := e'] e ↦ t.
move => e.
induction e;
move => U Γ x' e' T' T'' HT HSub;
try solve[inversion HT; econstructor; eauto].
+ simpl.
  destruct (eq_var_dec x' x) eqn:Eq; subst;
  inversion HT;
  apply MapProp.F.add_mapsto_iff in H2;
  move : H2 => [[? ?]|[? ?]]; try solve [exfalso; auto];
  subst; auto.
  - apply context_invariance with (Γ := ∅); auto; intros;
    apply MapProp.F.empty_mapsto_iff in H0;
    exfalso; auto.
  - constructor; auto.
+ simpl.
  destruct (eq_var_dec x' x) eqn:Eq1; 
  destruct (eq_var_dec x' f) eqn:Eq2;
  try solve [
    eapply context_invariance; eauto;
    move => y Ty Hf Hm;
    inversion Hf;
    apply MapProp.F.add_mapsto_iff in Hm;
    move : Hm => [[? ?]|[? ?]]; 
    try solve [subst; exfalso; auto]; auto ].
  inversion HT; subst; clear HT.
  econstructor; eauto.
  apply context_order_swap in H8.
  eapply IHe in H8; eauto.
  eauto.
  eauto.
+ simpl.
  inversion HT; subst.
  econstructor; [ eapply IHe1; eauto | ].
  destruct (eq_var_dec x' x) eqn:Eq1; 
  destruct (eq_var_dec x' y) eqn:Eq2;
  try solve [
    eapply context_invariance; eauto;
    move => z Tz Hf Hm;
    repeat (
      apply MapProp.F.add_mapsto_iff in Hm;
      move : Hm => [[? ?]|[? Hm]];
      try solve [exfalso; subst; auto];
      try apply MapProp.F.add_mapsto_iff;
      try solve [left; auto];
      try (right; split; auto)
    ); auto
  ].
  apply context_order_swap in H7.
  eapply IHe2 in H7; eauto.
  eauto.
  eauto.
+ simpl; inversion HT; subst.
  econstructor; [ eapply IHe1; eauto | | ].
  - destruct (eq_var_dec x' x) eqn:Eq.
    * { 
      eapply context_invariance; eauto;
      move => z Tz Hf Hm; 
      apply MapProp.F.add_mapsto_iff in Hm;
      move : Hm => [[? ?]|[? Hm]];
      apply MapProp.F.add_mapsto_iff;
      try solve [left; split; auto];
      subst; auto.
      right; split; auto.
      apply MapProp.F.add_mapsto_iff in Hm.
      move : Hm => [[? ?]|[? Hm]].
      try solve [exfalso; auto].
      auto.
      } 
    * apply context_order_swap_small in H8; auto.
      eapply IHe2 in H8; eauto.
  - destruct (eq_var_dec x' y) eqn:Eq.
    * { 
      eapply context_invariance; eauto;
      move => z Tz Hf Hm; 
      apply MapProp.F.add_mapsto_iff in Hm;
      move : Hm => [[? ?]|[? Hm]];
      apply MapProp.F.add_mapsto_iff;
      try solve [left; split; auto];
      subst; auto.
      right; split; auto.
      apply MapProp.F.add_mapsto_iff in Hm.
      move : Hm => [[? ?]|[? Hm]].
      try solve [exfalso; auto].
      auto.
      } 
    * apply context_order_swap_small in H9; auto.
      eapply IHe3 in H9; eauto.
Qed.

Theorem preservation : 
forall e v, e ⇓ v -> 
  forall U t, U; ∅ ⊢ e ↦ t -> U; ∅ ⊢ v ↦ t.
Proof.
move => e v H; induction H; move => U t Ht; auto;
try solve [inversion Ht; constructor; auto];
inversion Ht; subst; clear Ht.
+ move: {IHpred1} (IHpred1 U (TFun T₁0 t) H6) => HT.
  inversion HT; subst.
  eapply IHpred3; eauto.
  eapply substitution_lemma; eauto.
  eapply substitution_lemma; eauto.
+ eapply IHpred1 in H8.
  inversion H8; subst; clear H8.
  eapply IHpred2.
  eapply substitution_lemma; eauto.
  eapply substitution_lemma; eauto.
+ eapply IHpred1 in H9.
  inversion H9; subst; clear H9.
  eapply IHpred2.
  eapply substitution_lemma; eauto.
+ eapply IHpred1 in H9.
  inversion H9; subst; clear H9.
  eapply IHpred2.
  eapply substitution_lemma; eauto.
+ eapply IHpred1; eauto.
+ eapply IHpred; eauto.
+ eapply IHpred in H5; eauto.
  inversion H5; subst; eauto.
+ eapply IHpred1; eauto.
Qed.

Inductive is_base_value : exp -> Prop :=
  | IBUnit    : is_base_value Unit
  | IBPair    : forall e1 e2, 
                  is_base_value e1 -> is_base_value e2 ->
                  is_base_value (Pair e1 e2)
  | IBInl     : forall e t1 t2, 
                  is_base_value e -> 
                  is_base_value (Inl t1 t2 e)
  | IBInr     : forall e t1 t2, 
                  is_base_value e -> 
                  is_base_value (Inr t1 t2 e)
  | IBFold    : forall e t, 
                  is_base_value e ->
                  is_base_value (Fold t e).

Inductive base_value := 
  | BUnit : base_value
  | BPair : base_value -> base_value -> base_value
  | BInl  : type -> type -> base_value -> base_value
  | BInr  : type -> type -> base_value -> base_value
  | BFold : type -> base_value -> base_value.

Fixpoint base_to_exp (b : base_value)  : exp := 
  match b with
    | BUnit => Unit
    | BPair b1 b2 => 
      Pair (base_to_exp b1) (base_to_exp b2)
    | BInl t1 t2 b => Inl t1 t2 (base_to_exp b)
    | BInr t1 t2 b => Inr t1 t2 (base_to_exp b)
    | BFold t b => Fold t (base_to_exp b)
  end. 

Lemma base_to_exp_injective :
  forall b1 b2, 
    base_to_exp b1 = base_to_exp b2 ->
    b1 = b2.
induction b1 => b2 H; destruct b2; simpl in *; eauto; try inversion H.
- erewrite IHb1_1; eauto.
  erewrite IHb1_2; eauto.
- erewrite IHb1; eauto.
- erewrite IHb1; eauto.
- erewrite IHb1; eauto.
Qed. 

Fixpoint exp_to_base (e : exp) : option base_value :=
  match e with
    | Unit => Some BUnit
    | Inl t1 t2 e => liftMaybe (BInl t1 t2) (exp_to_base e)
    | Inr t1 t2 e => liftMaybe (BInr t1 t2) (exp_to_base e)
    | Pair e1 e2 => 
      liftMaybe2 BPair (exp_to_base e1) 
                       (exp_to_base e2)
    | Fold t e => liftMaybe (BFold t) (exp_to_base e)
    | _ => None
  end.

Lemma is_base_exp_to_base : 
  forall e, is_base_value e -> 
            exists b, exp_to_base e = Some b.
move => e H.
induction H.                         
- exists BUnit; auto.
- move : IHis_base_value1 => [b1 Hb1].
  move : IHis_base_value2 => [b2 Hb2].
  exists (BPair b1 b2); simpl.
  rewrite Hb1; rewrite Hb2; trivial.
- move : IHis_base_value => [b Hb].
  exists (BInl t1 t2 b); simpl; rewrite Hb; trivial.
- move : IHis_base_value => [b Hb].
  exists (BInr t1 t2 b); simpl; rewrite Hb; trivial.
- move : IHis_base_value => [b Hb].
  exists (BFold t b); simpl; rewrite Hb; trivial.
Qed.

Lemma base_to_exp_round : 
  forall b, exp_to_base (base_to_exp b) = Some b.
induction b; simpl; auto;
try rewrite IHb1; try rewrite IHb2; try rewrite IHb;
auto.
Qed.

Lemma exp_to_base_round : 
  forall b e, exp_to_base e = Some b -> base_to_exp b = e.
induction b; intros; simpl; auto.
destruct e; simpl in *; try congruence;
try solve [repeat match goal with 
  | [ H : context[exp_to_base ?E] |- _ ] =>
    destruct (exp_to_base E); simpl in *
end; try congruence].
+ destruct e; simpl in *; try congruence;
  try solve [repeat match goal with 
    | [ H : context[exp_to_base ?E] |- _ ] =>
      destruct (exp_to_base E); simpl in *
  end; try congruence].
  destruct (exp_to_base e1) eqn:H1;
  destruct (exp_to_base e2) eqn:H2;
  simpl in *; try congruence.
  inversion H; subst; clear H.
  eapply IHb1 in H1.
  eapply IHb2 in H2.
  subst; auto.
+ destruct e; simpl in *; try congruence;
  try solve [repeat match goal with 
    | [ H : context[exp_to_base ?E] |- _ ] =>
      destruct (exp_to_base E); simpl in *
  end; try congruence].
  destruct (exp_to_base e) eqn:H';
  simpl in *; try congruence.
  inversion H; subst; clear H.
  eapply IHb in H'.
  subst; auto.
+ destruct e; simpl in *; try congruence;
  try solve [repeat match goal with 
    | [ H : context[exp_to_base ?E] |- _ ] =>
      destruct (exp_to_base E); simpl in *
  end; try congruence].
  destruct (exp_to_base e) eqn:H';
  simpl in *; try congruence.
  inversion H; subst; clear H.
  eapply IHb in H'.
  subst; auto.
+ destruct e; simpl in *; try congruence;
  try solve [repeat match goal with 
    | [ H : context[exp_to_base ?E] |- _ ] =>
      destruct (exp_to_base E); simpl in *
  end; try congruence].
  destruct (exp_to_base e) eqn:H';
  simpl in *; try congruence.
  inversion H; subst; clear H.
  eapply IHb in H'.
  subst; auto.
Qed.

Lemma base_to_exp_is_value : 
  forall b e, base_to_exp b = e ->
              is_base_value e.
induction b; intros;
simpl in H; destruct e; try congruence;
inversion H; constructor; eauto.
Qed.

Inductive typed_base_val : base_value -> type -> Prop :=
| BaseType : forall b t, 
   ∅; ∅ ⊢ base_to_exp b ↦ t -> typed_base_val b t.

Lemma base_value_is_value : 
  forall e, is_base_value e -> is_value e.
Proof.
intros e H; induction H; intros; try constructor; auto.
Qed.

Theorem type_uniqueness : 
  forall T U e,
    U; ∅ ⊢ e ↦ T ->
    forall T',
    U; ∅ ⊢ e ↦ T' -> T = T'.
Proof.   
move => T U e H; induction H; move => T' HT';
inversion HT'; subst; eauto; try congruence;
try solve [eapply MapProp.F.MapsTo_fun; eauto].
- eapply IHhas_type1 in H5.
  inversion H5; eauto.
- eapply IHhas_type1 in H5; eauto.
  eapply IHhas_type2 in H7; eauto.
  subst; eauto.
- eapply IHhas_type1 in H8;
  inversion H8; subst.
  eapply IHhas_type2; eauto.
- eapply IHhas_type1 in H10; inversion H10; subst; eauto.
Qed.
