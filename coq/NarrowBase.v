Require Import List. Import ListNotations.
Require Import ListSet.

Require ssreflect.

Set Bullet Behavior "Strict Subproofs". 
Require Import Util.
Require Import Types.
Require Import Valuation.
Require Import Probability.
Require Import Constraints.
Require Import Bang.
Import CSet.

Reserved Notation " e ◂ k ⇒ q % ( e' , k' ) @ t" 
         (at level 40, no associativity).
Require Import QArith.

Inductive narrow : exp -> cset -> 
                   frac -> exp -> cset -> trace -> Prop :=
  | NVal : forall e k,
             is_value e ->
             e ◂ k ⇒ 1 % (e, k) @ nil 
  | NPair : 
      forall e₁ e₂ k v₁ v₂ k₂ k₁ tr₁ tr₂ q₁ q₂,
        ~ (is_value (Pair e₁ e₂)) ->
        e₁ ◂ k  ⇒ q₁ % (v₁, k₁) @ tr₁ ->
        e₂ ◂ k₁ ⇒ q₂ % (v₂, k₂) @ tr₂ ->
        (Pair e₁ e₂) ◂ k ⇒ (q₁ * q₂) % (Pair v₁ v₂, k₂) 
                            @ (tr₂ ++ tr₁)
  | NCaseP_Pair:
    forall e k q₁ k' tr₁ x y T₁ T₂ e' q₂ v₁ v₂
           vf kf tr₂,
      uts k; ∅ ⊢ e ↦ TProd T₁ T₂ ->
      e ◂ k ⇒ q₁ % (Pair v₁ v₂, k') @ tr₁ ->
      [y := v₂] ([x := v₁] e') ◂ k' ⇒ 
                  q₂ % (vf, kf) @ tr₂ ->
      CaseP e x y e' ◂ k ⇒ q₁ * q₂ % (vf, kf) @ (tr₂ ++ tr₁)
  | NCaseP_U : 
    forall e k q₁ k' tr₁ u₁ k₁ T₁ u₂ k₂ T₂ k₃ x y e' q₂ 
           vf kf tr₂ u,
      uts k; ∅ ⊢ e ↦ TProd T₁ T₂ ->
      e ◂ k ⇒ q₁ % (U u, k') @ tr₁ ->
      (u₁, k₁) = fresh k' T₁ ->
      (u₂, k₂) = fresh k₁ T₂ ->
      k₃ = unify_in k₂ (Pair (U u₁) (U u₂)) (U u) ->
      [y := U u₂] ([x := U u₁] e') ◂ k₃ ⇒ 
                  q₂ % (vf, kf) @ tr₂ ->
      CaseP e x y e' ◂ k ⇒ q₁ * q₂ % (vf, kf) @ (tr₂ ++ tr₁)
  | NInl : 
      forall e k q v k' tr T₁ T₂, 
        ~ (is_value (Inl T₁ T₂ e)) ->
        e ◂ k ⇒ q % (v, k') @ tr ->
        (Inl T₁ T₂ e) ◂ k  ⇒ q % (Inl T₁ T₂ v, k') @ tr
  | NInr : 
      forall e k q v k' tr T₁ T₂,
        ~ (is_value (Inr T₁ T₂ e)) ->
        e ◂ k ⇒ q % (v, k') @ tr ->
        (Inr T₁ T₂ e) ◂ k  ⇒ q % (Inr T₁ T₂ v, k') @ tr
  | NCase_Inl :
      forall k e T₁ T₂ q₁ k₀ tr₁ x e₁ y e₂ q₂ vf kf tr₂ v₁,
        uts k; ∅ ⊢ e ↦ TSum T₁ T₂ ->
        e ◂ k ⇒ q₁ % (Inl T₁ T₂ v₁, k₀) @ tr₁ ->
        [x := v₁] e₁ ◂ k₀ ⇒ q₂ % (vf, kf) @ tr₂ ->
        (Case e x e₁ y e₂) ◂ k ⇒ 
          (q₁ * q₂) % (vf, kf) @ 
          (tr₂ ++ tr₁)
  | NCase_Inr :
      forall k e T₁ T₂ q₁ k₀ tr₁ 
             x e₁ y e₂ q₂ vf kf tr₂ v₂,
        uts k; ∅ ⊢ e ↦ TSum T₁ T₂ ->
        e ◂ k ⇒ q₁ % (Inr T₁ T₂ v₂, k₀) @ tr₁ ->
        [y := v₂] e₂ ◂ k₀ ⇒ q₂ % (vf, kf) @ tr₂ ->
        (Case e x e₁ y e₂) ◂ k ⇒ 
          (q₁ * q₂) % (vf, kf) @ 
          (tr₂ ++ tr₁)
  | NCase_SAT_SAT_1 :
      forall k e T₁ T₂ q₁ u k₀ tr₁ u₁ k₁ u₂ k' k₁' k₂'
             x e₁ y e₂ q₂ vf kf tr₂,
        uts k; ∅ ⊢ e ↦ TSum T₁ T₂ ->
        e ◂ k ⇒ q₁ % (U u, k₀) @ tr₁ ->
        (u₁, k₁) = fresh k₀ T₁ ->
        (u₂, k') = fresh k₁ T₂ ->
        k₁' = unify_in k' (U u) (Inl T₁ T₂ (U u₁)) ->
        k₂' = unify_in k' (U u) (Inr T₁ T₂ (U u₂)) -> 
        sat k₁' -> sat k₂' ->
        [x := U u₁] e₁ ◂ k₁' ⇒ q₂ % (vf, kf) @ tr₂ ->
        (Case e x e₁ y e₂) ◂ k ⇒ 
          ((1#2) * q₁ * q₂) % (vf, kf) @ 
          (tr₂ ++ (cons (Chose 0 2) tr₁))
  | NCase_SAT_SAT_2 :
      forall k e T₁ T₂ q₁ u k₀ tr₁ u₁ k₁ u₂ k' k₁' k₂'
             x e₁ y e₂ q₂ vf kf tr₂,
        uts k; ∅ ⊢ e ↦ TSum T₁ T₂ ->
        e ◂ k ⇒ q₁ % (U u, k₀) @ tr₁ ->
        (u₁, k₁) = fresh k₀ T₁ ->
        (u₂, k') = fresh k₁ T₂ ->
        k₁' = unify_in k' (U u) (Inl T₁ T₂ (U u₁)) ->
        k₂' = unify_in k' (U u) (Inr T₁ T₂ (U u₂)) -> 
        sat k₁' -> sat k₂' ->
        [y := U u₂] e₂ ◂ k₂' ⇒ q₂ % (vf, kf) @ tr₂ ->
        (Case e x e₁ y e₂) ◂ k ⇒ 
          ((1#2) * q₁ * q₂) % (vf, kf) @ 
          (tr₂ ++ (cons (Chose 1 2) tr₁))
  | NCase_SAT_UNSAT :
      forall k e T₁ T₂ q₁ u k₀ tr₁ u₁ k₁ u₂ k' k₁' k₂'
             x e₁ y e₂ q₂ vf kf tr₂,
        uts k; ∅ ⊢ e ↦ TSum T₁ T₂ ->
        e ◂ k ⇒ q₁ % (U u, k₀) @ tr₁ ->
        (u₁, k₁) = fresh k₀ T₁ ->
        (u₂, k') = fresh k₁ T₂ ->
        k₁' = unify_in k' (U u) (Inl T₁ T₂ (U u₁)) ->
        k₂' = unify_in k' (U u) (Inr T₁ T₂ (U u₂)) -> 
        sat k₁' -> ~ (sat k₂') ->
        [x := U u₁] e₁ ◂ k₁' ⇒ q₂ % (vf, kf) @ tr₂ ->
        (Case e x e₁ y e₂) ◂ k ⇒ 
          (q₁ * q₂) % (vf, kf) @ 
          (tr₂ ++ tr₁)
  | NCase_UNSAT_SAT :
      forall k e T₁ T₂ q₁ u k₀ tr₁ u₁ k₁ u₂ k' k₁' k₂'
             x e₁ y e₂ q₂ vf kf tr₂,
        uts k; ∅ ⊢ e ↦ TSum T₁ T₂ ->
        e ◂ k ⇒ q₁ % (U u, k₀) @ tr₁ ->
        (u₁, k₁) = fresh k₀ T₁ ->
        (u₂, k') = fresh k₁ T₂ ->
        k₁' = unify_in k' (U u) (Inl T₁ T₂ (U u₁)) ->
        k₂' = unify_in k' (U u) (Inr T₁ T₂ (U u₂)) -> 
        ~ (sat k₁') -> sat k₂' ->
        [y := U u₂] e₂ ◂ k₂' ⇒ q₂ % (vf, kf) @ tr₂ ->
        (Case e x e₁ y e₂) ◂ k ⇒ 
          (q₁ * q₂) % (vf, kf) @ 
          (tr₂ ++ tr₁)
  | NApp : 
      forall e₁ k q₁ f x T T' e' k' tr₁ e₂ q₂ vf kf tr₂ k'' q₃ tr₃ v₂,
        e₁ ◂ k ⇒ q₁ % (Rec f x T T' e', k') @ tr₁ ->
        e₂ ◂ k' ⇒ q₂ % (v₂, k'') @ tr₂ -> 
        [f := Rec f x T T' e']([x := v₂] e') ◂ k'' ⇒ 
           q₃ % (vf, kf) @ tr₃ ->
        (App e₁ e₂) ◂ k ⇒ q₁ * q₂ * q₃ % (vf, kf) @ (tr₃ ++ tr₂ ++ tr₁)

  | NInst_SAT_SAT_1 :
      forall k e T₁ T₂ q₁ v k₁ tr₁ e₁ q₂ v₁ k₂ tr₂ q₂' k₂' tr₂' 
             e₂ q₃ v₂ k₃ tr₃ q₃' k₃' tr₃' n₁ n₂ u₁ k₄ u₂ k₅ kl kr,
      uts k; ∅ ⊢ e ↦ TSum T₁ T₂ ->
      e ◂ k ⇒ q₁ % (v, k₁) @ tr₁ ->
      e₁ ◂ k₁ ⇒ q₂ % (v₁, k₂) @ tr₂ ->
      sample' v₁ k₂ q₂' k₂' tr₂' ->
      e₂ ◂ k₂' ⇒ q₃ % (v₂, k₃) @ tr₃ ->
      sample' v₂ k₃ q₃' k₃' tr₃' ->
      nat_denote' k₃' v₁ n₁ -> n₁ <> O ->
      nat_denote' k₃' v₂ n₂ -> n₂ <> O ->
      (u₁, k₄) = fresh k₃' T₁ ->
      (u₂, k₅) = fresh k₄ T₂ ->
      kl = unify_in k₅ v (Inl T₁ T₂ (U u₁)) ->
      kr = unify_in k₅ v (Inr T₁ T₂ (U u₂)) ->
      sat kl -> sat kr -> 
      (Inst e e₁ e₂) ◂ k ⇒ 
         (n₁ // (n₁ + n₂)) * q₁ * q₂ * q₂' * q₃ * q₃' % (v, kl) 
         @ (Chose O 2 :: (tr₃' ++ tr₃ ++ tr₂' ++ tr₂ ++ tr₁))
  | NInst_SAT_SAT_2 :
      forall k e T₁ T₂ q₁ v k₁ tr₁ e₁ q₂ v₁ k₂ tr₂ q₂' k₂' tr₂' 
             e₂ q₃ v₂ k₃ tr₃ q₃' k₃' tr₃' n₁ n₂ u₁ k₄ u₂ k₅ kl kr,
      uts k; ∅ ⊢ e ↦ TSum T₁ T₂ ->
      e ◂ k ⇒ q₁ % (v, k₁) @ tr₁ ->
      e₁ ◂ k₁ ⇒ q₂ % (v₁, k₂) @ tr₂ ->
      sample' v₁ k₂ q₂' k₂' tr₂' ->
      e₂ ◂ k₂' ⇒ q₃ % (v₂, k₃) @ tr₃ ->
      sample' v₂ k₃ q₃' k₃' tr₃' ->
      nat_denote' k₃' v₁ n₁ -> n₁ <> O ->
      nat_denote' k₃' v₂ n₂ -> n₂ <> O ->
      (u₁, k₄) = fresh k₃' T₁ ->
      (u₂, k₅) = fresh k₄ T₂ ->
      kl = unify_in k₅ v (Inl T₁ T₂ (U u₁)) ->
      kr = unify_in k₅ v (Inr T₁ T₂ (U u₂)) ->
      sat kl -> sat kr -> 
      (Inst e e₁ e₂) ◂ k ⇒ 
         (n₂ // (n₁ + n₂)) * q₁ * q₂ * q₂' * q₃ * q₃' % (v, kr) 
         @ (Chose 1 2 :: (tr₃' ++ tr₃ ++ tr₂' ++ tr₂ ++ tr₁))
  | NInst_SAT_UNSAT :
      forall k e T₁ T₂ q₁ v k₁ tr₁ e₁ q₂ v₁ k₂ tr₂ q₂' k₂' tr₂' 
             e₂ q₃ v₂ k₃ tr₃ q₃' k₃' tr₃' n₁ n₂ u₁ k₄ u₂ k₅ kl kr,
      uts k; ∅ ⊢ e ↦ TSum T₁ T₂ ->
      e ◂ k ⇒ q₁ % (v, k₁) @ tr₁ ->
      e₁ ◂ k₁ ⇒ q₂ % (v₁, k₂) @ tr₂ ->
      sample' v₁ k₂ q₂' k₂' tr₂' ->
      e₂ ◂ k₂' ⇒ q₃ % (v₂, k₃) @ tr₃ ->
      sample' v₂ k₃ q₃' k₃' tr₃' ->
      nat_denote' k₃' v₁ n₁ -> n₁ <> O ->
      nat_denote' k₃' v₂ n₂ -> n₂ <> O ->
      (u₁, k₄) = fresh k₃' T₁ ->
      (u₂, k₅) = fresh k₄ T₂ ->
      kl = unify_in k₅ v (Inl T₁ T₂ (U u₁)) ->
      kr = unify_in k₅ v (Inr T₁ T₂ (U u₂)) ->
      sat kl -> ~ (sat kr) -> 
      (Inst e e₁ e₂) ◂ k ⇒ 
         (q₁ * q₂ * q₂' * q₃ * q₃') % (v, kl) 
         @ (tr₃' ++ tr₃ ++ tr₂' ++ tr₂ ++ tr₁)
  | NInst_UNSAT_SAT :
      forall k e T₁ T₂ q₁ v k₁ tr₁ e₁ q₂ v₁ k₂ tr₂ q₂' k₂' tr₂' 
             e₂ q₃ v₂ k₃ tr₃ q₃' k₃' tr₃' n₁ n₂ u₁ k₄ u₂ k₅ kl kr,
      uts k; ∅ ⊢ e ↦ TSum T₁ T₂ ->
      e ◂ k ⇒ q₁ % (v, k₁) @ tr₁ ->
      e₁ ◂ k₁ ⇒ q₂ % (v₁, k₂) @ tr₂ ->
      sample' v₁ k₂ q₂' k₂' tr₂' ->
      e₂ ◂ k₂' ⇒ q₃ % (v₂, k₃) @ tr₃ ->
      sample' v₂ k₃ q₃' k₃' tr₃' ->
      nat_denote' k₃' v₁ n₁ -> n₁ <> O ->
      nat_denote' k₃' v₂ n₂ -> n₂ <> O ->
      (u₁, k₄) = fresh k₃' T₁ ->
      (u₂, k₅) = fresh k₄ T₂ ->
      kl = unify_in k₅ v (Inl T₁ T₂ (U u₁)) ->
      kr = unify_in k₅ v (Inr T₁ T₂ (U u₂)) ->
      ~ (sat kl) -> sat kr -> 
      (Inst e e₁ e₂) ◂ k ⇒ 
         (q₁ * q₂ * q₂' * q₃ * q₃') % (v, kr) 
         @ (tr₃' ++ tr₃ ++ tr₂' ++ tr₂ ++ tr₁)
  | NBang : 
      forall e k q₁ v k₁ tr₁ q₂ k₂ tr₂,
      e ◂ k ⇒ q₁ % (v, k₁) @ tr₁ ->
      sample' v k₁ q₂ k₂ tr₂ ->
      (Bang e) ◂ k ⇒ q₁ * q₂ % (v, k₂) @ (tr₂ ++ tr₁)
  | NFold :
      forall e k q v k' tr T,
        ~ (is_value e) ->
        e ◂ k ⇒ q % (v, k') @ tr ->
        Fold T e ◂ k ⇒ q % (Fold T v, k') @ tr
  | NUnfold_Fold:
    forall e k q T v k' tr,
      e ◂ k ⇒ q % (Fold T v, k') @ tr ->
      Unfold T e ◂ k ⇒ q % (v, k') @ tr

  | NUnfold_U :
      forall e k q u k₁ tr u' k₂ T k₃, 
      e ◂ k ⇒ q % (U u, k₁) @ tr ->
      (u', k₂) = fresh k₁ (substT O (TMu T) T) ->
      k₃ = unify_in k₂ (U u) (Fold (TMu T) (U u')) ->
      Unfold (TMu T) e ◂ k ⇒ q % (U u', k₃) @ tr       

  | NTil : 
      forall e₁ k q₁ tr₁ v₁ k₁ T e₂ q₂ tr₂ k₂ v₂,
        e₁ ◂ k  ⇒ q₁ % (v₁, k₁) @ tr₁ ->
        e₂ ◂ k₁ ⇒ q₂ % (v₂, k₂) @ tr₂ ->
        Til e₁ T e₂ ◂ k ⇒ q₁ * q₂ % (v₁, k₂) @ (tr₂ ++ tr₁)

  where "e ◂ k ⇒ q % ( e' , k' ) @ tr" := 
    (narrow e k q e' k' tr).

Lemma narrow_is_value :
  forall e k q v k' tr,
    e ◂ k ⇒ q % (v, k') @ tr ->
    is_value v.
move => e k q v k' tr H; induction H; auto;
try solve [constructor; auto];
try solve [inversion IHnarrow; auto].
Qed.


Lemma narrow_increases_domain :
  forall e k q v k' tr,
  e ◂ k ⇒ q % (v, k') @ tr ->
  forall u, In u (domain k) -> In u (domain k').
move => e k q v k' tr H; induction H => u'' InK; eauto; subst;
try solve [
 eapply IHnarrow2; eauto;
 eapply unify_domain; eauto;
 right; right;
 erewrite <- (fresh_preserves_domain k₁); eauto;
 erewrite <- (fresh_preserves_domain k'); eauto];
try solve [
 eapply IHnarrow2; eauto;
 eapply unify_domain; eauto;
 right; right;
 erewrite <- (fresh_preserves_domain k₁); eauto;
 erewrite <- (fresh_preserves_domain k₀); eauto];
try solve[ 
  eapply unify_domain; eauto;
  right; right;
  erewrite <- (fresh_preserves_domain k₄); eauto;
  erewrite <- (fresh_preserves_domain k₃'); eauto;
  erewrite <- (sample_domain' v₂ k₃); eauto;
  eapply IHnarrow3; eauto;
  erewrite <- (sample_domain' v₁ k₂); eauto].
- erewrite <- (sample_domain' v k₁); eauto.
- eapply unify_domain; eauto; right; right.
  erewrite <- (fresh_preserves_domain k₁); eauto.
Qed.

Theorem narrow_decreasing : 
forall e k q v k' tr,
  e ◂ k ⇒ q % (v, k') @ tr -> lte k' k.
intros e k q v k' tr H.
induction H; auto;
repeat
  match goal with 
  | [ H : (_, _) = fresh _ _ |- _ ] => 
    apply fresh_preserves_lte in H
  | [ H : sample' _ _ _ _ _ |- _ ] => 
    apply sample_lte' in H
  end;
try match goal with
  | [ H : _ = unify_in _ _ _ |- _ ] =>
    eapply unify_in_lte in H; auto;
      try solve [repeat (constructor; auto)]
end;
try match goal with
  | [ H : _ = unify_in _ _ _ |- _ ] =>
    eapply unify_in_lte in H; auto;
      try solve [repeat (constructor; auto)]
end;
try match goal with
  | [ H : _ = unify_in _ _ _ |- _ ] =>
    eapply unify_in_lte in H; auto;
      try solve [repeat (constructor; auto)]
end;
try apply reflexivity; auto;
(* 10 should be big enough to avoid repeat in case of failure *)
try solve [do 7 (eapply transitivity; eauto)];
try solve [eapply narrow_is_value; eauto].
Qed.

Ltac restrict_solver := 
repeat  
  match goal with 
  | [ |- (uts (unify_in ?K2 _ _) ↘ _) ≡ _ ] =>
    erewrite  (unify_preserves_types K2) ; eauto
  | [ H : (_, ?K2) = fresh ?K1 _ 
      |- (uts ?K2 ↘ _) ≡ _ ] =>
    erewrite fresh_increases_types; eauto
  | |- (?U ⊕ ?u ↦ ?T) ↘ _ ≡ _ =>
    eapply restrict_transitive with (s' := U);
    [eapply (restrict_add u U (* (U ⊕ u ↦ T)*) T);
     try solve[eapply fresh_is_fresh_type; 
               eauto ] | ]
  | |- ?U ↘ ?U ≡ ?U =>
    eapply restrict_reflexive; eauto
  | [ H : sample' _ ?K1 _ ?K2 _ 
    |- (uts ?K2 ↘ _) ≡ _ ] => 
    eapply restrict_transitive 
      with (s':= uts K1);
    [ erewrite <- sample_preserves_types' | ];
    eauto; clear H
  | [ H : ?U1 ↘ ?U2 ≡ ?U2 |- ?U1 ↘ ?U3 ≡ ?U3 ] =>
    eapply (restrict_transitive U3 U2 U1); eauto
end.

Lemma narrow_increases_types : 
  forall e k q v k' tr, 
    e ◂ k ⇒ q % (v, k') @ tr ->
    uts k' ↘ uts k ≡ uts k.
move => e k q v k' tr H; induction H; 
try solve [subst; eapply restrict_reflexive; eauto];
subst;
restrict_solver.
Qed.

Hint Resolve restrict_reflexive.
Hint Resolve restrict_add.

(*
Ltac preservation_solver := 
  eauto;
    match goal with 
    | [ H : narrow _ _ _ _ _ _ |- _ ] => 
      apply narrow_increases_types in H
    | [ IH  : forall _, 
               _; _ ⊢ ?E ↦ _ ->
               well_typed_cset ?K -> _ ,
        HWT : well_typed_cset ?K ,
        HT  : uts ?K; _ ⊢ ?E ↦ ?T |- _ ] =>
      let HK' := fresh "HK" in
      let HT' := fresh "HT" in
      move: {IH} (IH T HT HWT) => [HK' HT']
    | [ IH  : forall _, 
               _; _ ⊢ Bang ?E ↦ _ ->
               well_typed_cset ?K1 -> _ ,
        HWT : well_typed_cset ?K1 ,
        HT  : uts ?K; ?G ⊢ ?E ↦ NatType |- _ ] =>
     assert (TMP : uts K1; G ⊢ Bang E ↦ NatType) 
     by (
       constructor; eauto;
       [repeat econstructor | ];
       eapply unknown_invariance; eauto; 
       eapply restrict_transitive; eauto);
     let HK' := fresh "HK" in
     let HT' := fresh "HT" in
     move: {IH} (IH NatType TMP HWT) => [HK' HT'];
     clear TMP        
    | [ H : narrow _ _ _ _ _ _ |- _ ] => 
      apply narrow_increases_types in H
    | [ IH : forall _, 
               uts ?K2; ?G ⊢ ?E ↦ _ ->
               well_typed_cset ?K2 -> _ ,
        HT : uts ?K1; ?G ⊢ ?E ↦ ?T ,
        HR : Map.Equiv eq 
               (MapProp.restrict (uts ?K2)
                                 (uts ?K1))
               (uts ?K1) |- _ ]=>
      eapply unknown_invariance in HT; eauto
    | [ H : uts ?K1; _ ⊢ ?E ↦ ?T |- 
            uts ?K2; _ ⊢ ?E ↦ ?T ] =>
      eapply unknown_invariance; eauto
    | [ H : _ = fresh ?K _ ,
        _ : well_typed_cset ?K |- _ ] => 
      let HWF := fresh "HWF" in
      let HEQ := fresh "HEQ" in
      remember H as HWF eqn:HEQ; clear HEQ;
      apply fresh_preserves_well_typed in HWF; eauto;
      let HWF1 := fresh "HWF" in
      let HEQ1 := fresh "HEQ" in
      remember H as HWF1 eqn:HEQ1; clear HEQ1;
      apply fresh_increases_used in HWF1; eauto;
      let HNotIn := fresh "HNotIn" in
      let HAdd   := fresh "HAdd" in 
      move : HWF1 => [HNotIn HAdd];
      clear H
    | [ H : ?K2 = unify_in ?K1 _ _ |- _ ] =>
      let H1 := fresh "HWF" in 
      remember H as H1 eqn:TMP; clear TMP;
      eapply unify_preserves_types in H; eauto;
      eapply unify_preserves_well_typed in H1; eauto
    | [ H : Map.Equiv eq (MapProp.restrict ?K3 ?K2) ?K2 |- 
        Map.Equiv eq (MapProp.restrict ?K3 ?K1) ?K1 ] =>
       eapply restrict_transitive with (s' := K2); eauto
    | [ H : ?K3 = Map.add _ _ ?K2 |-
        Map.Equiv eq (MapProp.restrict ?K3 ?K1) ?K1 ] =>
       eapply restrict_transitive with (s' := K2); eauto
    | [ |- ?K2; _ ⊢ U ?U1 ↦ ?T1 ] => constructor
    | [ H1 : ?K2 = Map.add ?U2 _ ?K1 , H2 : ?U1 <> ?U2 
        |- Map.MapsTo ?U1 ?T1 ?K2 ] =>
      rewrite H1;
      apply MapProp.F.add_mapsto_iff;
      right; split; auto
    | [ H1 : ?K2 = Map.add ?U1 ?T1 ?K1 
        |- Map.MapsTo ?U1 ?T1 ?K2 ] =>
      rewrite H1;
      apply MapProp.F.add_mapsto_iff;
      left; auto
  end.
*)

Ltac MapsToSolver := 
          subst; eapply MapProp.F.add_mapsto_iff;
          try solve [left; auto];
          right; split; auto.

Ltac solvePreservation :=
repeat match goal with 
  | [ H : narrow _ _ _ _ _ _ |- _ ] => 
    apply narrow_increases_types in H
  | [ IH : forall _, _ -> _ -> 
             well_typed_cset ?K /\ _
      |- well_typed_cset ?K ] => 
    eapply IH; eauto
  | [ IH : forall _, _ -> _ -> 
        _ /\ uts ?K; _ ⊢ ?V ↦ ?T
      |- uts ?K; _ ⊢ ?V ↦ ?T ] =>
    eapply IH; eauto
  | [ IH : forall _, _ -> _ -> 
        _ /\ uts ?K1; _ ⊢ ?V ↦ _
      |- uts ?K2; _ ⊢ ?V ↦ _ ] =>
    eapply unknown_invariance 
      with (U := uts K1); eauto;
    eapply IH; eauto
  | [ IH : uts ?K1; _ ⊢ ?E ↦ _
      |- uts ?K2; _ ⊢ ?E ↦ _ ] =>
    eapply unknown_invariance
     with (U := uts K1); eauto
  | |- _; _ ⊢ [_:=_]_ ↦ _ => 
    eapply substitution_lemma; eauto
  | [ H1 : ?U; ?G ⊢ ?E ↦ ?T1 
    , H2 : ?U; ?G ⊢ ?E ↦ ?T2 |- _ ] =>
    assert (TMP: T2 = T1)
      by (eapply type_uniqueness; eauto);
    clear H2; 
    inversion TMP; subst;
    clear TMP; eauto
  | [ H  : ?U1; _ ⊢ ?E ↦ ?T
    , IH : forall _, ?U1; _ ⊢ ?E ↦ _ -> _ -> 
             _ /\ ?U2; ?G ⊢ ?V ↦ _ 
    |- _ ] =>
    match goal with 
      | [ H : U2; _ ⊢ V ↦ T |- _ ] => fail
      | _ => 
        let HV := fresh "HT" in
        assert (HT: U2; G ⊢ V ↦ T)
        by (eapply IH; eauto);
        inversion HT; subst; eauto
    end
  | |- (_ ↘ _) ≡ _ =>
    restrict_solver
  | |- well_typed_cset (unify_in ?K ?V1 ?V2) =>
    eapply unify_preserves_well_typed; eauto
  | |- context[uts (unify_in ?K ?V1 ?V2)] =>
    rewrite unify_preserves_types; eauto
  | [ H1 : (?U1, ?K2) = fresh ?K1 ?T
    , H2 : (?U2, ?K3) = fresh ?K2 _
    |- Map.MapsTo ?U ?T (uts ?K3) ] =>
      erewrite (fresh_increases_types K2 U2 K3); eauto;
      MapsToSolver;
      try solve 
        [eapply (fresh_fresh_unknowns_neq_sym K1 U1 K2 U2); eauto];
      erewrite (fresh_increases_types K1 U1 K2); eauto;
      MapsToSolver
  | [ H  : (?U, ?K2) = fresh ?K1 ?T
    |- Map.MapsTo ?U ?T (uts ?K2) ] =>
      erewrite (fresh_increases_types K1 U K2); eauto;
      MapsToSolver

  | [ H  : (?U, ?K2) = fresh ?K1 ?T
    |- well_typed_cset ?K2 ] =>
    eapply (fresh_preserves_well_typed K1); eauto

(*
  | [ H : (_, ?K2) = fresh ?K1 _ 
    |- Map.Equiv eq (MapProp.restrict 
         (uts ?K2) _) _ ] =>
    eapply restrict_transitive 
    with (s' := uts K1); 
    [ solve [eapply fresh_increases_used in H; 
            eauto; inversion H; subst; eauto]
    | eauto ]
*)
(*  | _ => try econstructor; eauto  *)
end.


Hint Constructors has_type.
Theorem narrow_preservation :
forall e k q v k' tr, 
  e ◂ k ⇒ q % (v, k') @ tr ->
  forall T, 
  uts k; ∅ ⊢ e ↦ T ->
  well_typed_cset k ->
  well_typed_cset k' /\
  uts k'; ∅ ⊢ v ↦ T.
move => e k q v k' tr H; induction H; 
move => t' Ht' HK; try solve [split; auto];
inversion Ht'; subst; clear Ht'; split; auto;
try solve [solvePreservation; 
           econstructor; eauto;
           solvePreservation].
{ (* Rec case *)
assert (Hyp : T = T₁ /\ T' = t').
  eapply IHnarrow1 in HK; eauto.
  inversion HK.
  inversion H3; subst; eauto.
move: Hyp => [? ?]; subst; auto.
solvePreservation.
}
{ (* Rec case - 2 *)
assert (Hyp : T = T₁ /\ T' = t').
  eapply IHnarrow1 in HK; eauto.
  inversion HK.
  inversion H3; subst; eauto.
move: Hyp => [? ?]; subst; auto.
solvePreservation.
}
{ 
  solvePreservation;
  eapply sample_preserves_well_typed'; eauto;
  solvePreservation;
  eapply sample_preserves_well_typed'; eauto;
  solvePreservation.
}
{ 
  solvePreservation;
  eapply sample_preserves_well_typed'; eauto;
  solvePreservation;
  eapply sample_preserves_well_typed'; eauto;
  solvePreservation.
}
{ 
  solvePreservation;
  eapply sample_preserves_well_typed'; eauto;
  solvePreservation;
  eapply sample_preserves_well_typed'; eauto;
  solvePreservation.
}
{ 
  solvePreservation;
  eapply sample_preserves_well_typed'; eauto;
  solvePreservation;
  eapply sample_preserves_well_typed'; eauto;
  solvePreservation.
}
{ (* Bang case *)
eapply sample_preserves_well_typed'; eauto.
solvePreservation.
}
Qed.

