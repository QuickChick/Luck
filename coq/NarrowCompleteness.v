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
Require Import NarrowBase.

Require Import QArith.

Import CSet.

Lemma SubVal_base_reflexive : 
  forall e, is_base_value e ->
  forall s, SubVal s e e.
move => e H; induction H; move => s;
try constructor; eauto.
Qed.

Lemma SubVal_restrict_injective :
  forall v, is_value v -> 
  forall U Γ T, U; Γ ⊢ v ↦ T -> isNonFunType T ->     
  forall s v1, SubVal s v v1 ->
  forall s' v2, s' ↘ s ≡ s -> SubVal s' v v2 ->
  v1 = v2.
move => v H; induction H; 
move => U Γ T' HT' NF s v1 HS1 s' v2 HR HS2;
inversion HS1; inversion HS2; subst; auto.
- eapply restrict_mapsto in H1; eauto.
  assert (b = b0) by (eapply MapProp.F.MapsTo_fun; eauto).
  subst; auto.
- inversion HT'; subst; auto.
  inversion NF; subst; auto.
  assert (e1' = e1'0); eauto.
  assert (e2' = e2'0); eauto.
  subst; auto.
- inversion HT'; subst; auto.
  inversion NF; subst; auto.
  assert (e' = e'0); eauto.
  subst; auto.
- inversion HT'; subst; auto.
  inversion NF; subst; auto.
  assert (e' = e'0); eauto.
  subst; auto.
- inversion HT'; subst; auto.
  inversion NF.
- inversion HT'; subst; auto.
  inversion NF; subst; auto.
  assert (e' = e'0).
  {
    eapply IHis_value; eauto.
    eapply substT_preserves_NonFun; eauto.
  }
  subst; auto.
Qed.

Lemma SubVal_NonFun_is_base_value :
  forall v', is_value v' ->
  forall s v, SubVal s v v' ->
  forall U Γ T, U; Γ ⊢ v' ↦ T -> isNonFunType T ->
  is_base_value v'.
move => v' H; induction H; 
move => s v Sub U Γ T' HT' NF; 
try econstructor; eauto;
try solve [
  inversion Sub; subst; 
  inversion HT'; subst; 
  inversion NF; subst; eauto; 
  match goal with
    | [ H : base_to_exp _ = _ |- _ ] =>
      apply base_to_exp_is_value in H;
      inversion H; auto
  end].
- inversion Sub; subst; 
  inversion HT'; subst; 
  inversion NF; subst; eauto.
  + apply base_to_exp_is_value in H0;
    inversion H0; auto.
  + eapply IHis_value; eauto.
    eapply substT_preserves_NonFun; eauto.
Qed.

Lemma SubVal_exists :
  forall v, is_value v-> 
  forall U Γ T, U; Γ ⊢ v ↦ T -> isNonFunType T ->
  forall s' v', SubVal s' v v' ->
  forall s k, InK s' k -> InK (restrict s (domain k)) k ->
    exists v'', SubVal s v v''.
move => v H; induction H; 
move => U Γ T' HT' NF s' v' Sub s k In1 In2.
* exists Unit; constructor.
* inversion Sub; subst; auto.
  eapply restrict_domain_InK_2 in In2; eauto.
  eapply InK_domain in In2; eauto.  
  move: In2 => [_ H].
  eapply InK_domain in In1.
  assert (H' : In u (domain k)).
  { 
    eapply In1; eauto.
    exists b; eauto.
  }
  eapply H in H'.
  apply MapProp.restrict_in_iff in H'.
  move: H' => [[b' TMP] _].
  assert (Map.MapsTo u b' s) by auto; clear TMP.
  exists (base_to_exp b').
  eapply SubUnknown; eauto.
* inversion Sub; subst; auto.
  inversion HT'; subst; auto.
  inversion NF; subst; auto.
  assert (Hyp : exists v1, SubVal s e₁ v1).
  by (eapply IHis_value1; eauto).
  move: Hyp => [v1 HSub1].
  assert (Hyp : exists v2, SubVal s e₂ v2)
  by (eapply IHis_value2; eauto).
  move: Hyp => [v2 HSub2].
  exists (Pair v1 v2); constructor; auto.
* inversion Sub; subst; auto.
  inversion HT'; subst; auto.
  inversion NF; subst; auto.
  assert (Hyp: exists v, SubVal s e v) 
  by (eapply IHis_value; eauto).         
  move: Hyp => [v HSub].
  exists (Inl T₁ T₂ v); constructor; auto.
* inversion Sub; subst; auto.
  inversion HT'; subst; auto.
  inversion NF; subst; auto.
  assert (Hyp: exists v, SubVal s e v) 
  by (eapply IHis_value; eauto).         
  move: Hyp => [v HSub].
  exists (Inr T₁ T₂ v); constructor; auto.
* inversion HT'; subst; auto.
  inversion NF.
* inversion Sub; subst; auto.
  inversion HT'; subst; auto.
  inversion NF; subst; auto.
  assert (Hyp: exists v, SubVal s e v).
  {
    eapply IHis_value; eauto.
    eapply substT_preserves_NonFun; eauto.
  }
  move: Hyp => [v HSub].
  exists (Fold (TMu T0) v); constructor; auto.
Qed.

Lemma narrow_singleton_value : 
  forall k v v', singleton' k v v' ->
  is_value v -> sat k ->
  forall e q ve k' tr, e ◂ k ⇒ q % (ve, k') @ tr ->
    singleton' k' v v'.
move => k v v' HS; induction HS; 
move => HVal Sat e q ve k' tr HN; eauto;
inversion HVal; subst;
try econstructor; eauto.
- unfold singleton in *.
  move => s HIn.
  eapply narrow_decreasing in HN.
  unfold lte in HN.
  eapply HN in HIn.
  eapply H in HIn.
  move: Sat => [s' TMP].
  assert (HIn' : InK s' k) by auto. clear TMP.
  move: (restrict_domain_InK s' s k HIn') => 
    [In Map].
  assert (In' : Map.In u (s ↘ s')).  
  {
    eapply In; eauto.
    exists b; eauto.
  }
  move: In' => [b' Hbtmp].
  assert (Hb' : Map.MapsTo u b' (s ↘ s')) by auto. 
  clear Hbtmp.
  assert (b = b')
  by (eapply Map; eauto).
  subst.
  eapply MapProp.restrict_mapsto_iff; eauto.
Qed.

Lemma substU_val : 
  forall v (H : is_value v) s e, 
    SubVal s e v ->
    is_value e.
move => v H s e H'.
move : H.
induction H'; intros; 
auto; try constructor;
inversion H; auto.
Qed.

Lemma pred_is_value_value_eq:
  forall e v, is_value e -> e ⇓ v -> e = v.
intros e v H.
generalize dependent v.
induction H; intros v Hpred; inversion Hpred; auto.
- erewrite IHis_value1;
  erewrite IHis_value2;
  eauto.
- erewrite IHis_value; eauto.
- erewrite IHis_value; eauto.
- subst; eauto. 
  inversion Hpred; subst; eauto.
  erewrite IHis_value; eauto.
Qed.

Lemma base_value_subst :
  forall e, is_base_value e ->
    forall x v, e = [x := v] e.
Proof.
intros e H; induction H; intros; simpl; auto;
try solve [rewrite <- IHis_base_value; eauto].
rewrite <- IHis_base_value1; 
rewrite <- IHis_base_value2; 
eauto.
Qed.

Lemma substU_subst : 
  forall s e e', SubVal s e e' ->
  forall v v', SubVal s v v' ->
  forall x, SubVal s ([x := v] e) ([x:= v'] e').
move => s e e' H.
induction H; intros; simpl; auto;
  repeat match goal with 
    | [ |- context [eq_var_dec ?X ?Y] ] => 
      let eq := fresh "EQ" in
      destruct (eq_var_dec X Y) eqn:eq
    | _ => idtac
  end;
  eauto;
  try solve [econstructor; eauto].
- econstructor.
  + move : (base_to_exp_is_value b e H) => H'.
    eapply base_value_subst in H'.
    rewrite <- H'.
    eauto.
  + auto.
Qed.

Lemma substU_val_val : 
  forall e, is_value e -> 
  forall s e', SubVal s e e' -> 
  is_value e'.
Proof.
intros e H; induction H; intros; simpl in *; auto;
match goal with 
  | [ H : SubVal _ _ _ |- _ ] => 
    inversion H; try constructor; eauto
end.
apply base_value_is_value.
eapply base_to_exp_is_value; eauto.
Qed. 

Lemma subst_v_rec : 
  forall s v f x T T' e, 
    SubVal s v (Rec f x T T' e) ->
  exists e', v = Rec f x T T' e' 
             /\ SubVal s e' e.
Proof.
  move => s v f x T T' e HSub.
  inversion HSub; subst.
  - exists e0; auto.
  - apply base_to_exp_is_value in H.
    inversion H.
Qed.

Lemma fresh_fresh_add_add_equiv :
  forall k u₁ T₁ u₂ T₂ k₁ k₂ s s₁ s₂ b₁ b₂,
    (u₁, k₁) = fresh k T₁ ->
    (u₂, k₂) = fresh k₁ T₂ ->
    InK s k ->
    s₁ = Map.add u₂ b₂ s ->
    s₂ = Map.add u₁ b₁ s₁ ->
    Map.Equiv eq (MapProp.restrict s₂ s) s.
Proof.
move => k u₁ T₁ u₂ T₂ k₁ k₂ s s₁ s₂ b₁ b₂ 
        Fresh1 Fresh2 HIn Add1 Add2.
move: (fresh_is_fresh k u₁ k₁ T₁ Fresh1 s HIn) 
  => HNotIn1.
move: (fresh_preserves_InK k u₁ k₁ T₁ Fresh1 s) 
  => [/(_ HIn) HIn₁ _].
move: (fresh_is_fresh k₁ u₂ k₂ T₂ Fresh2 s HIn₁) 
  => HNotIn2.
move: (fresh_preserves_InK k₁ u₂ k₂ T₂ Fresh2 s) 
  => [/(_ HIn₁) HIn₂ _].
apply (restrict_transitive s s₁ s₂).
- subst; apply restrict_add; auto.
  move => Contra.
  rewrite MapProp.F.add_in_iff in Contra.
  move: Contra => [Contra | Contra].
  + apply (fresh_fresh_unknowns_neq 
             k u₁ k₁ u₂ k₂ T₁ T₂ 
             Fresh1 Fresh2); auto.
  + eauto.
- subst; apply restrict_add; auto.
Qed.

Lemma substU_restrict : 
  forall s e e' ,
    SubVal s e e' ->
    forall s', 
    Map.Equiv eq (MapProp.restrict s' s) s ->
    SubVal s' e e'.
move => s e e' HSub.
induction HSub; 
move => s' HEq;
try solve [constructor; auto].
(* U case *)
eapply SubUnknown; eauto.
eapply restrict_mapsto; eauto.
Qed.


Lemma SubVal_preservation : 
  forall U e T, 
    U; ∅ ⊢ e ↦ T -> 
  forall s e', SubVal s e e' ->
               well_typed_valuation U s ->
               U; ∅ ⊢ e' ↦ T.
move => U e T H; induction H; move => s es HSub HWT;
inversion HSub; subst; eauto.
inversion HWT; subst; eauto.
move: (H0 u b H2) => [T' [HM HT]].
assert (T = T') by (eapply MapProp.F.MapsTo_fun; eauto); 
  subst; eauto.
inversion HT; subst; eauto.
eapply unknown_invariance with (U := ∅); eauto.
eapply context_invariance; eauto.
move => x Tx HF Contra.
exfalso; eapply MapProp.F.empty_mapsto_iff; eauto.

split; intros.
split; intros; auto.
  apply MapProp.restrict_in_iff in H3; eauto.
  inversion H3; eauto.
  exfalso; eapply MapProp.F.empty_in_iff; eauto.
  exfalso; eapply MapProp.F.empty_mapsto_iff; eauto.
Qed.  

(*
Lemma bang_singleton : 
  forall e k q v k' tr,
    Bang e ◂ k ⇒ q % (v, k') @ tr ->
    sat k ->
    exists v', singleton' k' v v'.
move => e k q v k' tr H SAT.
inversion H; subst; eauto.
- inversion H0.
- eapply uniform_singleton' in H2; eauto.
  move: SAT => [s HIn].
  
  
  
    forall s v' n,
      InK s k -> SubVal s v v' ->Ban
      nat_denote v' = Some n ->
      nat_denote' v k' = Some n.
Proof.
induction v;
move => e k q k' tr HT HN s v' n HIn HSub HNat.
match goal with
| [ H1 : ?U; ?G ⊢ ?E ↦ NatType 
  , H2 : Bang ?E ◂ _ ⇒ _ % (?V, ?K) @ _ |- _] =>
  assert (uts K;G ⊢ V ↦ NatType)
end.

eapply narrow_preservation;
eauto; repeat econstructor.
eauto.
econstructor.
econstructor.
    by (eapply narrow_preservation; eauto;
        repeat econstructor)


{
inversion HT; subst; eauto;
repeat match goal with 
  | [H : Map.MapsTo _ _ ∅ |- _ ] =>
    exfalso; 
    eapply MapProp.F.empty_mapsto_iff in H;
    auto
end.
inversion HN; subst; eauto.
inversion H2; subst; eauto.
}
inversion H; subst; eauto;
try match goal with
  | [ H : is_value (Bang _) |- _ ] =>
    inversion H
end.
move => s v' n HIn HSub HNat.
*)
Ltac MapsToSolver := 
          subst; eapply MapProp.F.add_mapsto_iff;
          try solve [left; auto];
          right; split; auto;
          eapply MapProp.F.add_mapsto_iff;
          try solve [left; auto];
          right; split; auto.

Ltac substSolver :=
      subst;
      repeat match goal with 
        | |- SubVal ?S ([_ := _]_) ([_ := _]_) =>
          eapply substU_subst; eauto
        | [ H  : SubVal ?S1 ?E1 ?E2 
          |- SubVal ?S2 ?E1 ?E2 ] => 
          eapply substU_restrict; eauto
        | [ |- Map.Equiv eq 
               (MapProp.restrict (Map.add ?U1 ?T1 
                  (Map.add ?U2 ?T2 ?S)) _) _ ] =>
          eapply restrict_transitive with (s'0 := S); eauto
        | [ |- Map.Equiv eq 
               (MapProp.restrict (Map.add _ _ ?S) _) _ ] =>
          eapply restrict_transitive with (s' := S); eauto
        | [ H : Map.Equiv eq 
                  (MapProp.restrict ?S3 ?S2) ?S2 
            |- Map.Equiv eq 
                  (MapProp.restrict ?S3 ?S1) ?S1 ] =>
          eapply restrict_transitive with (s' := S2); eauto
      end; 
      eauto;
      try solve [ econstructor; eauto; MapsToSolver ];
      match goal with 
        | [ F1 : (?U1, _) = fresh ?K ?T1 
          , F2 : (?U2, _) = fresh _  ?T2 
          |- _ ] => 
          try solve [
            eapply (fresh_fresh_add_add_equiv K U1 T1 U2);
            eauto]
      end.

Ltac typeSolver :=
  subst;
  repeat match goal with 
    | |- _; _ ⊢ [_ := _]_ ↦ _ =>
       eapply substitution_lemma; eauto
    | [ H  : uts _; _ ⊢ ?E ↦ ?T 
      , H' : _ ◂ ?K1 ⇒ _ % (_, ?K2) @ _ 
      |- uts ?K2; _ ⊢ ?E ↦ ?T ] =>
        eapply unknown_invariance with (U := uts K1); eauto;
        eapply narrow_increases_types; eauto
    | [ H : _ ◂ _ ⇒ _ % (_ , ?K) @ _ 
      |- uts ?K; _ ⊢ _ ↦ _ ] =>
        eapply narrow_preservation in H; eauto;
        move : H => [_ H]; inversion H; eauto
    | |- uts (unify_in ?K _ _); _ ⊢ _ ↦ _ =>
        erewrite <- unify_preserves_types with (k := K); eauto
    | [ H : uts ?K1; _ ⊢ ?E ↦ ?T 
      |- uts ?K2; _ ⊢ ?E ↦ ?T ] => 
        eapply unknown_invariance with (U := uts K1); eauto
    | [ N : _ ◂ ?K1 ⇒ _ % (_, ?K2) @ _ 
      |- Map.Equiv eq (MapProp.restrict (uts ?K2) 
                                       (uts ?K1))
                   (uts ?K1) ] => 
        eapply narrow_increases_types; eauto
    | [ N : _ ◂ ?K1 ⇒ _ % (_, ?K2) @ _ 
      |- Map.Equiv eq (MapProp.restrict (uts ?K2) 
                                       (uts _))
                   (uts _) ] => 
      eapply restrict_transitive with (s' := uts K1); try solve [eapply narrow_increases_types; eauto]
    | [ N : _ ◂ ?K1 ⇒ _ % (_, ?K2) @ _ 
      |- Map.Equiv eq (MapProp.restrict (uts ?K2) 
                                       (uts _))
                   (uts _) ] => 
      eapply restrict_transitive with (s'0 := uts K1); try solve [eapply narrow_increases_types; eauto]

    | [ F : (_, ?K2) = fresh ?K1 _ |- _ ] =>
      eapply fresh_increases_types in F; eauto;
      rewrite F in *
    | |- Map.Equiv eq (MapProp.restrict (Map.add _ _ (Map.add  ?U ?T ?K2)) ?K2) ?K2 =>
      eapply restrict_transitive with (s'0 := Map.add U T K2); 
      eauto
    | |- Map.Equiv eq (MapProp.restrict (Map.add _ _ (Map.add _ _ ?K2)) ?K1) ?K1 =>
      eapply restrict_transitive with (s'0 := K2); eauto
    | |- Map.Equiv eq (MapProp.restrict (Map.add _ _ (Map.add  ?U ?T ?K2)) ?K2) ?K2 =>
      eapply restrict_transitive with (s' := Map.add U T K2); 
      eauto
    | |- Map.Equiv eq (MapProp.restrict (Map.add _ _ (Map.add _ _ ?K2)) ?K1) ?K1 =>
      eapply restrict_transitive with (s' := K2); eauto
    end; 
    try solve [econstructor; MapsToSolver].

Ltac absurd_base_value :=
  match goal with
    | [ H : base_to_exp _ = _ |- _ ] =>
      apply base_to_exp_is_value in H; inversion H
  end.

Ltac absurd_not_val HNotVal :=
  exfalso; apply HNotVal; apply base_value_is_value; 
  eapply base_to_exp_is_value; eauto.

Ltac notValSolver HNotVal :=
  repeat match goal with 
    | [ H : ~ is_value _ |- ~ is_value _ ] =>
      move => HVal; apply HNotVal; inversion HVal;
      econstructor
    | [ H : SubVal _ ?E1 ?E2 |- is_value ?E2 ] =>
      eapply (substU_val_val E1); eauto
  end.

Ltac well_typed_solver := 
  repeat match goal with 
    | [ H : _ ◂ ?K1 ⇒ _ % (_, ?K2) @ _ 
        |- well_typed_cset ?K2 ] => 
      eapply narrow_preservation; eauto
    | [ H : (_, ?K2) = fresh ?K1 _ 
        |- well_typed_cset ?K2 ] => 
      eapply fresh_preserves_well_typed; eauto
    | [ H : ?K2 = unify_in ?K1 _ _ 
        |- well_typed_cset ?K2 ] =>
      eapply unify_preserves_well_typed; eauto
  end.

Ltac splitSolver := 
  repeat (split; 
          try solve [eapply restrict_transitive; eauto];
          try solve [repeat econstructor; eauto];
          try solve [econstructor; eauto; 
                     eapply substU_restrict; eauto]).

Ltac solve_maps :=
          match goal with 
            | [ H1 : Map.MapsTo ?U1 ?B3 (Map.add ?U1 ?B1 _)
              , H2 : Map.MapsTo ?U2 ?B4 (Map.add ?U1 _ 
                                        (Map.add ?U2 ?B2 ?S))
              |- _ ] =>
            rewrite MapProp.F.add_mapsto_iff in H1;
            move: H1 => [[_ Eq1] | [Contra _]];
            [ rewrite MapProp.F.add_mapsto_iff in H2;
              move: H2 => [[Contra _] | [_ H2]] | ];
            try solve [exfalso; auto];
            rewrite MapProp.F.add_mapsto_iff in H2;
            move: H2 => [[_ Eq2] | [Contra _]];
            try solve [exfalso; auto]; subst;
            eapply SubUnknown with (b := BPair B3 B4); eauto
          end.

Ltac discharge_IH IH s e k T Hyp :=
  specialize (IH s e k T);
  match goal with 
    | [ H : _ -> _ -> _ -> _ -> ?Res |- _ ] =>
      assert (Hyp : Res); [eapply H | ]; clear H; eauto
  end;
  try solve [substSolver];
  try solve [well_typed_solver];
  try solve [typeSolver].

Theorem narrow_complete :
forall e' v, e' ⇓ v -> 
  forall s e k T ,
  InK s k ->
  SubVal s e e' ->
  uts k; ∅ ⊢ e ↦ T ->
  well_typed_cset k ->
  exists v' k' s', 
    Map.Equiv eq (MapProp.restrict s' s) s /\
    InK s' k' 
    /\ SubVal s' v' v
    /\ exists q tr, e ◂ k ⇒ q % (v', k') @ tr.
intros e' v H.
induction H as 
  [ (* val   *) v HisVal 
  | (* app   *) e₁ e₂ f x T T' e' v v₂ Hpred IH1 Hpred2 IH2 Hpred3 IH3
  | (* pair  *) e₁ v₁ e₂ v₂ HNotVal Hpred1 IH1 Hpred2 IH2
  | (* casep *) e x y e' v₁ v₂ v' Hpred1 IH1 Hpred2 IH2
  | (* inl   *) e T₁ T₂ v HNotVal HPred IH
  | (* inr   *) e v T₁ T₂ HNotVal HPred IH
  | (* case-inl *) e v x T₁ T₂ v₁ e₁ y e₂ HPred1 IH1 HPred2 IH2
  | (* case-inr *) e v x T₁ T₂ v₁ e₁ y e₂ HPred1 IH1 HPred2 IH2
  | (* inst *) e e₁ e₂ v v₁ v₂ n₁ n₂ Pred IH Pred₁ IH₁ 
                 Pred₂ IH₂ Nat₁ NZ₁ Nat₂ NZ₂ 
  | (* bang *) e v HPred IH
  | (* fold *) e T v HNotVal HPred IH
  | (* unfold *) e T v HPred IH
  | (* til *) e₁ T₂ e₂ v₁ v₂ Hpred1 IH1 Hpred2 IH2 ].
- move => s e k T HIn HSub HT HWT.
  exists e. exists k. exists s.
  repeat (split; auto).
  exists 1.
  exists nil.
  constructor; eapply substU_val; eauto.
- move => s e k T'' HIn HSub HT'' HWT.
  inversion HSub; subst; try solve [absurd_base_value].
  inversion HT''; subst.
  discharge_IH IH1 s e1 k (TFun T₁ T'') Hyp.
  move : Hyp.
  intros (v' & k' & s' & HEquiv & HIn' & HSub' 
             & q₁ & tr₁ & HNarrow).
  
  (* Hacky stuff only for rec case *)
  move: (subst_v_rec s' v' f x T T' e' HSub') => 
    [e'' [Hv' HSub'']].

  assert (HTv' : uts k'; ∅ ⊢ v' ↦ TFun T₁ T'')
    by (eapply narrow_preservation; eauto).
  rewrite Hv' in HTv'; inversion HTv'; subst; eauto.
  (* End Hacky stuff *)

  discharge_IH IH2 s' e2 k' T₁ Hyp.
  move : Hyp.
  intros (v2 & k'' & s'' & HEquiv2 & HIn2 & HSub2
             & q₂ & tr₂ & HNarrow2).

  remember ([f := Rec f x T₁ T'' e'']([x := v2] e'')) as es.

  assert (HN : uts k'' ↘ uts k' ≡ uts k')
  by (eapply narrow_increases_types; eauto).
  discharge_IH IH3 s'' es k'' T'' Hyp.
  {
    subst; eauto.
    eapply substitution_lemma; eauto.
    eapply substitution_lemma; eauto.
    eapply unknown_invariance; eauto.
    eapply narrow_preservation; eauto.
    eapply unknown_invariance; eauto.
    eapply narrow_increases_types; eauto.
    eapply narrow_preservation; eauto.
    eapply unknown_invariance; eauto.
  }
  {
    eapply narrow_preservation; eauto.
    eapply unknown_invariance; eauto.
    eapply narrow_increases_types; eauto.
    eapply narrow_preservation; eauto.
  } 
  move: Hyp. 
  intros (vf & kf & sf & HEquiv3 & HIn3 & HSub3
             & q₃ & tr₃ & Narrow3).

  exists vf; exists kf; exists sf.
  repeat (split; try eapply restrict_transitive; eauto).
  exists (q₁ * q₂ * q₃); exists (tr₃ ++ tr₂ ++ tr₁).
  subst; econstructor; eauto.
- move => s e k T HIn HSub HTe HWF.
  inversion HSub; subst; try solve [absurd_not_val HNotVal].
  inversion HTe; subst.
  
  discharge_IH IH1 s e1 k T₁ Hyp. 
  move: Hyp => [v' [k' [s' [HEq [HIn' [HSub' 
                           [q₁ [tr₁ Hnarrow]]]]]]]].

  discharge_IH IH2 s' e2 k' T₂ Hyp.
  move: Hyp => [v'' [k'' [s'' [HEq' [HIn'' [HSub'' 
                         [q₂ [tr₂ Hnarrow2]]]]]]]].

  exists (Pair v' v''); exists k''; exists s''.
  splitSolver.
  exists (q₁ * q₂); exists (tr₂ ++ tr₁).
  subst; econstructor; eauto.
  notValSolver HNotVal.
- move => s ed k T HIn HSub HTed HWF.
  inversion HSub; subst; try solve [absurd_base_value].
  inversion HTed; subst.
  discharge_IH IH1 s e0 k (TProd T₁ T₂) Hyp.
  move: Hyp => [v0 [k' [s' [HEq [HIn' [HSub' 
                       [q₁ [tr₁ Hnarrow]]]]]]]].

  inversion HSub'; subst.
  * { (* Pair case - easy *)
      remember ([y:=e2]([x:=e1]eb)) as es.
      discharge_IH IH2 s' es k' T Hyp.
      move: Hyp => [vf [kf [sf [HEq' [HIn'' [HSub'' 
                               [q₂ [tr₂ HN2]]]]]]]].
    exists vf; exists kf; exists sf.
    splitSolver.
    exists (q₁ * q₂). exists (tr₂ ++ tr₁).
    eapply NCaseP_Pair; eauto; subst; eauto.
  }
  * { (* Unknown case - harder :) *)
    destruct (fresh k' T₁) as [u₁ k₁] eqn:Fresh1.
    destruct (fresh k₁ T₂) as [u₂ k₂] eqn:Fresh2.
    symmetry in Fresh1; symmetry in Fresh2.
   
    remember (unify_in k₂ (Pair (U u₁) (U u₂)) (U u)) as k₃.
    remember ([y := U u₂]([x := U u₁] eb)) as es.    
   
    destruct b; simpl in *; try congruence.
    inversion H.
    remember (Map.add u₂ b2 s') as s''.
    remember (Map.add u₁ b1 s'') as sf.
    assert (Hyp: u <> u₁ /\ u <> u₂ /\ u₁ <> u₂)
      by (eapply fresh_fresh_all_unknowns_neq with (k := k');
          eauto; exists (BPair b1 b2); eauto).
    move: Hyp => [NEq1 [NEq2 NEq3]].

    discharge_IH IH2 sf es k₃ T Hyp.
    (* Inclusion : InK sf k₃ *)
    { 
      rewrite Heqk₃.
      apply unify_spec; eauto;
      try solve [repeat econstructor].
      split.
      - {
         erewrite <- (fresh_preserves_domain k₁ u₂ k₂); eauto.
         erewrite <- (fresh_preserves_domain k' u₁ k₁); eauto.
         eapply (fresh_preserves_InK k₁ u₂ k₂); eauto.
         eapply (fresh_preserves_InK k' u₁ k₁); eauto.
         rewrite InK_equiv; eauto.
         move:(restrict_domain_InK s' sf k' HIn')=>HEqRestrict.
         eapply Equiv_transitive 
           with (s2 := (MapProp.restrict sf s')); 
           eauto; clear HEqRestrict.
         eapply (fresh_fresh_add_add_equiv k' u₁ T₁ u₂ T₂); 
           eauto.
        }
      - move => v; split => HInP.
        * inversion HInP;
          repeat match goal with 
            | [H : SubVal _ (U _) _ |- _ ] =>
              inversion H; subst; clear H
          end; solve_maps;
          MapsToSolver.
        * (* Reverse case... *)
          inversion HInP; subst.
          remember (Map.add u₁ b1 (Map.add u₂ b2 s')) as sf.
          
          assert (Map.MapsTo u (BPair b1 b2) sf)
          by MapsToSolver.
          assert (Hb : b = BPair b1 b2)
          by (eapply MapProp.F.MapsTo_fun; eauto).
          rewrite Hb; simpl; constructor; auto.
          eapply SubUnknown; eauto; MapsToSolver. 
          eapply SubUnknown; eauto; MapsToSolver.
  } (* Proved inclusion *)
  {
    typeSolver.
    {
    rewrite unify_preserves_types; eauto.
    eapply restrict_transitive with (s'0 := uts k₁); eauto.
    pose proof Fresh2.
    eapply fresh_increases_types in Fresh2; eauto.
    rewrite Fresh2.
    apply (restrict_add u₂ (uts k₁)); auto.
    eapply fresh_is_fresh_type; eauto.
    eapply restrict_transitive with (s'0 := uts k'); eauto.
    pose proof Fresh1.
    eapply fresh_increases_types in Fresh1; eauto.
    rewrite Fresh1.
    apply (restrict_add u₁ (uts k')); auto.
    eapply fresh_is_fresh_type; eauto.
    eapply narrow_increases_types; eauto.
    }
    {
    rewrite unify_preserves_types; eauto.
    constructor.
    eapply fresh_increases_types in Fresh1; eauto.
    eapply fresh_increases_types in Fresh2; eauto.
    rewrite Fresh2.
    rewrite Fresh1.
    eapply MapProp.F.add_mapsto_iff; eauto.
    right; split; auto.
    eapply MapProp.F.add_mapsto_iff; eauto.
    }
    {
    rewrite unify_preserves_types; eauto.
    constructor.
    eapply fresh_increases_types in Fresh2; eauto.
    rewrite Fresh2.
    eapply MapProp.F.add_mapsto_iff; eauto.
    }
  }
  move: Hyp => [vr [kr [sr [HEqr [HInr [HSubr [q₂ [tr₂ HN]]]]]]]].
  exists vr; exists kr; exists sr.
  split.
    eapply restrict_transitive; eauto.
    eapply restrict_transitive with (s'0 := s'); eauto.
    eapply (fresh_fresh_add_add_equiv k' u₁ T₁ u₂); eauto.
  splitSolver. (* TODO: Update *)
  exists (q₁ * q₂). exists (tr₂ ++ tr₁).
  eapply NCaseP_U; subst; eauto.
  }
- move => s e' k T HIn HSub HTe HWF.
  inversion HSub; subst; try solve [absurd_not_val HNotVal].
  inversion HTe; subst.
  discharge_IH IH s e0 k T₁ Hyp;    
  move : Hyp => [v' [k' [s' [HEq [HIn' [HSub' 
                        [q [tr Hnarrow]]]]]]]].
  exists (Inl T₁ T₂ v'); exists k'; exists s'.
  splitSolver.
  exists q; exists tr.
  econstructor; notValSolver HNotVal; eauto.
- move => s e' k T HIn HSub HTe HWF.
  inversion HSub; subst; try solve [absurd_not_val HNotVal].
  inversion HTe; subst.
  discharge_IH IH s e0 k T₂ Hyp.
  move : Hyp => [v' [k' [s' [HEq [HIn' [HSub' 
                        [q [tr Hnarrow]]]]]]]].
  exists (Inr T₁ T₂ v'); exists k'; exists s'.
  splitSolver.
  exists q; exists tr.
  econstructor; notValSolver HNotVal; eauto.
- move => s e' k T HIn HSub HTe HWF.
  inversion HSub; subst; try solve [absurd_base_value].
  inversion HTe; subst.
  (* Verify that that the types are the same *)
  assert (Hyp : T₁0 = T₁ /\ T₂0 = T₂).
  { 
    eapply SubVal_preservation in H3; eauto.
    eapply preservation in HPred1; eauto.
    inversion HPred1; subst; eauto.
  } inversion Hyp; clear Hyp; subst.
  discharge_IH IH1 s e0 k (TSum T₁ T₂) Hyp.
  move: Hyp =>
    [v' [k₁ [s₁ [HEq [HIn' [HSub' [q₁ [tr₁ HNarrow]]]]]]]].
  inversion HSub'; subst.
  + { (* NCaseInl *)
    discharge_IH IH2 s₁ ([x:=e1]ex) k₁ T Hyp.
    move: Hyp => 
      [v₁' [k₂ [s₂ [HEq' [HIn'' [HSub'' [q₂ [tr₂ HN2]]]]]]]].
    exists v₁'; exists k₂; exists s₂.
    splitSolver.
    }
  + { (* NCaseU *)
     destruct (fresh k₁ T₁) as [u₁ k₂] eqn:Fresh₁; 
     symmetry in Fresh₁.
     destruct (fresh k₂ T₂) as [u₂ k₃] eqn:Fresh₂; 
     symmetry in Fresh₂.
     assert (InK s₁ k₃) by (
       apply (fresh_preserves_InK k₂ u₂ k₃ T₂); auto;
       rewrite <- fresh_preserves_InK; eauto
     ).
     destruct b; simpl in H; try congruence.
     inversion H; subst.
     remember (unify_in k₃ (U u) (Inl T₁ T₂ (U u₁))) as k₁'.
     remember (unify_in k₃ (U u) (Inr T₁ T₂ (U u₂))) as k₂'.
     remember (Map.add u₁ b s₁) as s₂.

     assert (Hyp: u <> u₁ /\ u <> u₂ /\ u₁ <> u₂)
     by (
      eapply (fresh_fresh_all_unknowns_neq u k₁ u₁ k₂ u₂ k₃);
      eauto;
      exists (BInl T₁ T₂ b); auto
     );
     move: Hyp => [NEq1 [NEq2 NEq3]].

     assert (HInK1' : InK s₂ k₁').

     { (* InK s₂ k₁' *)
      rewrite Heqk₁'.
      apply unify_spec; eauto;
      try solve [repeat econstructor].
      split.
      - { 
         erewrite <- (fresh_preserves_domain k₂ u₂ k₃); eauto.
         erewrite <- (fresh_preserves_domain k₁ u₁ k₂); eauto.
         eapply (fresh_preserves_InK k₂ u₂ k₃); eauto.
         eapply (fresh_preserves_InK k₁ u₁ k₂); eauto.
         rewrite InK_equiv; eauto.
         move:(restrict_domain_InK s₁ s₂ k₁ HIn')=>HEqRestrict.
         eapply Equiv_transitive 
           with (s2 := (MapProp.restrict s₂ s₁)); 
           eauto; clear HEqRestrict.
         rewrite Heqs₂; apply restrict_add; auto.
         eapply fresh_is_fresh; eauto.
       }
     - {move => v; split => HInP.
        * repeat match goal with 
            | [H : SubVal _ (U _) _ |- _ ] =>
              inversion H; subst; clear H
          end. 
          eapply MapProp.F.add_mapsto_iff in H5.
          move: H5 => [[Contra _] | [_ HM]];
          [try solve [exfalso; apply NEq1; auto] | ].
          assert (b0 = b1) 
          by (eapply MapProp.F.MapsTo_fun; eauto).
          subst.
          rewrite H4.
          econstructor; eauto.
          econstructor; eauto.
          MapsToSolver.
        * (* Reverse case... *)
          inversion HInP; subst.
          remember (Map.add u₁ b s₁) as s₂.
          repeat match goal with 
            | [H : SubVal _ (U _) _ |- _ ] =>
              inversion H; subst; clear H
          end. 
          econstructor; eauto.
          assert (b = b0) by (
            eapply MapProp.F.add_mapsto_iff in H5; eauto;
            move: H5 => [[_ HM] | [Contra _]]; auto;
            try solve [exfalso; auto]); subst.
          eauto.
          MapsToSolver.
       }
     }

     discharge_IH IH2 s₂ ([x := U u₁] ex) k₁' T Hyp.

     { 
       substSolver.
       apply restrict_add; auto.
       eapply fresh_is_fresh; eauto.
     }

     {
       typeSolver.
       { 
        rewrite unify_preserves_types; eauto.
        eapply restrict_transitive with (s' := uts k₂); eauto.
        pose proof Fresh₂.
        eapply fresh_increases_types in Fresh₂; eauto.
        rewrite Fresh₂.
        apply (restrict_add u₂ (uts k₂)); auto.
        eapply fresh_is_fresh_type; eauto.
        eapply restrict_transitive with (s' := uts k₁); eauto.
        pose proof Fresh₁.
        eapply fresh_increases_types in Fresh₁; eauto.
        rewrite Fresh₁.
        apply (restrict_add u₁ (uts k₁)); auto.
        eapply fresh_is_fresh_type; eauto.
        eapply narrow_increases_types; eauto.
        }
        {
        rewrite unify_preserves_types; eauto.
        constructor.
        eapply fresh_increases_types in Fresh₁; eauto.
        eapply fresh_increases_types in Fresh₂; eauto.
        rewrite Fresh₂.
        rewrite Fresh₁.
        eapply MapProp.F.add_mapsto_iff; eauto.
        right; split; auto.
        eapply MapProp.F.add_mapsto_iff; eauto.
        }
     }
     move: Hyp =>
       [vf [kf [sf [HEqf [HInKf [HSubf [q₂ [tr₂ HN2]]]]]]]].
     exists vf; exists kf; exists sf.
     split; auto. 
     eapply restrict_transitive; eauto.
     eapply restrict_transitive with (s':= s₁); eauto.
     rewrite Heqs₂.
     apply restrict_add; auto.
     eapply fresh_is_fresh; eauto.
     repeat split; auto.

     destruct (sat_dec k₂') eqn:Sat.
     * exists ((1#2) * q₁ * q₂).
       exists (tr₂ ++ cons (Chose 0 2) tr₁).
       eapply NCase_SAT_SAT_1; eauto.
       eapply InK_sat; eauto.
     * exists (q₁ * q₂).
       exists (tr₂ ++ tr₁).
       eapply NCase_SAT_UNSAT; eauto.
       eapply InK_sat; eauto.
    }
- move => s e' k T HIn HSub HTe HWF.
  inversion HSub; subst; try solve [absurd_base_value].
  inversion HTe; subst.
  (* Verify that that the types are the same *)
  assert (Hyp : T₁0 = T₁ /\ T₂0 = T₂).
  { 
    eapply SubVal_preservation in H3; eauto.
    eapply preservation in HPred1; eauto.
    inversion HPred1; subst; eauto.
  } inversion Hyp; clear Hyp; subst.
  discharge_IH IH1 s e0 k (TSum T₁ T₂) Hyp.
  move: Hyp =>
    [v' [k₁ [s₁ [HEq [HIn' [HSub' [q₁ [tr₁ HNarrow]]]]]]]].
  inversion HSub'; subst.
  + { (* NCaseInr *)
    discharge_IH IH2 s₁ ([y:=e1]ey) k₁ T Hyp.
    move: Hyp => 
      [v₁' [k₂ [s₂ [HEq' [HIn'' [HSub'' [q₂ [tr₂ HN2]]]]]]]].
    exists v₁'; exists k₂; exists s₂.
    splitSolver.
    exists (q₁ * q₂).
    exists (tr₂ ++ tr₁).
    eapply NCase_Inr; eauto.
    }
  + { (* NCaseU *)
     destruct (fresh k₁ T₁) as [u₁ k₂] eqn:Fresh₁; 
     symmetry in Fresh₁.
     destruct (fresh k₂ T₂) as [u₂ k₃] eqn:Fresh₂; 
     symmetry in Fresh₂.
     assert (InK s₁ k₃) by (
       apply (fresh_preserves_InK k₂ u₂ k₃ T₂); auto;
       rewrite <- fresh_preserves_InK; eauto
     ).
     destruct b; simpl in H; try congruence.
     inversion H; subst.
     remember (unify_in k₃ (U u) (Inl T₁ T₂ (U u₁))) as k₁'.
     remember (unify_in k₃ (U u) (Inr T₁ T₂ (U u₂))) as k₂'.
     remember (Map.add u₂ b s₁) as s₂.

     assert (Hyp: u <> u₁ /\ u <> u₂ /\ u₁ <> u₂)
     by (
      eapply (fresh_fresh_all_unknowns_neq u k₁ u₁ k₂ u₂ k₃);
      eauto;
      exists (BInr T₁ T₂ b); auto
     );
     move: Hyp => [NEq1 [NEq2 NEq3]].

     assert (HInK1' : InK s₂ k₂').

     { (* InK s₂ k₂' *)
      rewrite Heqk₂'.
      apply unify_spec; eauto;
      try solve [repeat econstructor].
      split.
      - { 
         erewrite <- (fresh_preserves_domain k₂ u₂ k₃); eauto.
         erewrite <- (fresh_preserves_domain k₁ u₁ k₂); eauto.
         eapply (fresh_preserves_InK k₂ u₂ k₃); eauto.
         eapply (fresh_preserves_InK k₁ u₁ k₂); eauto.
         rewrite InK_equiv; eauto.
         move:(restrict_domain_InK s₁ s₂ k₁ HIn')=>HEqRestrict.
         eapply Equiv_transitive 
           with (s2 := (MapProp.restrict s₂ s₁)); 
           eauto; clear HEqRestrict.
         rewrite Heqs₂; apply restrict_add; auto.
         eapply fresh_is_fresh; eauto.
         eapply fresh_preserves_InK; eauto.
       }
     - {move => v; split => HInP.
        * repeat match goal with 
            | [H : SubVal _ (U _) _ |- _ ] =>
              inversion H; subst; clear H
          end. 
          eapply MapProp.F.add_mapsto_iff in H5.
          move: H5 => [[Contra _] | [_ HM]];
          [try solve [exfalso; apply NEq2; auto] | ].
          assert (b0 = b1) 
          by (eapply MapProp.F.MapsTo_fun; eauto).
          subst.
          rewrite H4.
          econstructor; eauto.
          econstructor; eauto.
          MapsToSolver.
        * (* Reverse case... *)
          inversion HInP; subst.
          remember (Map.add u₁ b s₁) as s₂.
          repeat match goal with 
            | [H : SubVal _ (U _) _ |- _ ] =>
              inversion H; subst; clear H
          end. 
          econstructor; eauto.
          assert (b = b0) by (
            eapply MapProp.F.add_mapsto_iff in H5; eauto;
            move: H5 => [[_ HM] | [Contra _]]; auto;
            try solve [exfalso; auto]); subst.
          eauto.
          MapsToSolver.
       }
     }

     discharge_IH IH2 s₂ ([y := U u₂] ey) k₂' T Hyp.

     { 
       substSolver.
       apply restrict_add; auto.
       eapply fresh_is_fresh; eauto.
       eapply fresh_preserves_InK; eauto.
     }
          {
       typeSolver.
       { 
        rewrite unify_preserves_types; eauto.
        eapply restrict_transitive with (s' := uts k₂); eauto.
        pose proof Fresh₂.
        eapply fresh_increases_types in Fresh₂; eauto.
        rewrite Fresh₂.
        eapply (restrict_add u₂ (uts k₂)); eauto.
        eapply fresh_is_fresh_type; eauto.
        eapply restrict_transitive with (s' := uts k₁); eauto.
        pose proof Fresh₁.
        eapply fresh_increases_types in Fresh₁; eauto.
        rewrite Fresh₁.
        eapply (restrict_add u₁ (uts k₁)); eauto.
        eapply fresh_is_fresh_type; eauto.
        eapply narrow_increases_types; eauto.
        }
        {
        rewrite unify_preserves_types; eauto.
        constructor.
        eapply fresh_increases_types in Fresh₁; eauto.
        eapply fresh_increases_types in Fresh₂; eauto.
        rewrite Fresh₂.
        rewrite Fresh₁.
        eapply MapProp.F.add_mapsto_iff; eauto.
        }
     }
     move: Hyp =>
       [vf [kf [sf [HEqf [HInKf [HSubf [q₂ [tr₂ HN2]]]]]]]].
     exists vf; exists kf; exists sf.
     split; auto. 
     eapply restrict_transitive; eauto.
     eapply restrict_transitive with (s':= s₁); eauto.
     rewrite Heqs₂.
     apply restrict_add; auto.
     eapply fresh_is_fresh; eauto.
     eapply fresh_preserves_InK; eauto.
     repeat split; auto.

     destruct (sat_dec k₁') eqn:Sat.
     * exists ((1#2) * q₁ * q₂).
       exists (tr₂ ++ cons (Chose 1 2) tr₁).
       eapply NCase_SAT_SAT_2; eauto.
       eapply InK_sat; eauto.
     * exists (q₁ * q₂).
       exists (tr₂ ++ tr₁).
       eapply NCase_UNSAT_SAT; eauto.
       eapply InK_sat; eauto.
    }
- move => s e' k T HIn HSub HT HWT.
  inversion HSub; subst; try solve [absurd_base_value].
  inversion HT; subst.
  discharge_IH IH s e0 k (TSum T₁ T₂) Hyp.
  move: Hyp =>
      [v' [k₁ [s₁ [HEq [HInK' [HSub₁ [q₁ [tr₁ HN₁]]]]]]]].

  pose proof HN₁ as HR1.
  eapply narrow_increases_types in HR1; eauto.
  assert (uts k₁; ∅ ⊢ e0 ↦ TSum T₁ T₂) 
  by (eapply unknown_invariance; eauto).
  assert (uts k₁; ∅ ⊢ el ↦ NatType) 
  by (eapply unknown_invariance; eauto).
  assert (uts k₁; ∅ ⊢ er ↦ NatType) 
  by (eapply unknown_invariance; eauto).

  pose proof HN₁ as WT₁.
  eapply narrow_preservation in WT₁; eauto.
  move: WT₁ => [WT₁ HTV'].

  discharge_IH IH₁ s₁ el k₁ NatType Hyp.
  move: Hyp =>
      [v₁' [k₂ [s₂ [HEq₁ [HInK₁ [HSub₂ [q₂ [tr₂ HN₂]]]]]]]].

  pose proof HN₂ as HR2.
  eapply narrow_increases_types in HR2; eauto.
  assert (uts k₂; ∅ ⊢ e0 ↦ TSum T₁ T₂) 
  by (eapply unknown_invariance; eauto).
  assert (uts k₂; ∅ ⊢ el ↦ NatType) 
  by (eapply unknown_invariance; eauto).
  assert (uts k₂; ∅ ⊢ er ↦ NatType) 
  by (eapply unknown_invariance; eauto).
  
  pose proof HN₂ as WT₂.
  eapply narrow_preservation in WT₂; eauto.
  move: WT₂ => [WT₂ HTV1'].
  
  assert (Hyp : exists k₂', InK s₂ k₂' /\ 
          exists q₂' tr₂', sample' v₁' k₂ q₂' k₂' tr₂').
  { eapply sample_spec_1'; auto.
    - eapply narrow_is_value; eauto.
    - eapply narrow_preservation; eauto.
    - repeat (econstructor; eauto).
    - eassumption.
  }
  move: Hyp => [k₂' [HIn2' [q₂' [tr₂' Sample1]]]].

  pose proof Sample1 as HR2'.
  eapply sample_preserves_types' in HR2'; eauto.

  pose proof Sample1 as WT₂'.
  eapply sample_preserves_well_typed' in WT₂'; eauto.

  discharge_IH IH₂ s₂ er k₂' NatType Hyp.
  { (* TODO: Move to type solver *)
    eapply unknown_invariance; eauto.
    rewrite <- HR2'.
    eapply restrict_reflexive; eauto.
  } 
  move: Hyp =>
      [v₂' [k₃ [s₃ [HEq₂ [HInK₂ [HSub₃ [q₃ [tr₃ HN₃]]]]]]]].

  pose proof HN₃ as HR3.
  eapply narrow_increases_types in HR3; eauto.
  assert (uts k₃; ∅ ⊢ e0 ↦ TSum T₁ T₂). {
    eapply unknown_invariance; eauto.
    rewrite HR2'; eauto.
  } 
  assert (uts k₃; ∅ ⊢ el ↦ NatType). {
    eapply unknown_invariance; eauto.
    rewrite HR2'; eauto.
  }
  assert (uts k₃; ∅ ⊢ er ↦ NatType). {
    eapply unknown_invariance; eauto.
    rewrite HR2'; eauto.
  }
  pose proof HN₃ as WT₃.
  eapply narrow_preservation in WT₃; eauto; 
  [ | rewrite <- HR2'; eauto].
  move: WT₃ => [WT₃ HTV2'].

  assert (Hyp : exists k₃', InK s₃ k₃' /\ 
          exists q₃' tr₃', sample' v₂' k₃ q₃' k₃' tr₃').
  { eapply sample_spec_1'; eauto.
    - eapply narrow_is_value; eauto.
    - repeat (econstructor; eauto).
  }
  move: Hyp => [k₃' [HIn3' [q₃' [tr₃' Sample2]]]].

  pose proof Sample2 as HR3'.
  eapply sample_preserves_types' in HR3'; eauto.
  pose proof Sample2 as WT₃'.
  eapply sample_preserves_well_typed' in WT₃'; eauto.

  (* Start simulating the narrowing mechanism *)
  destruct (fresh k₃' T₁) as [u₁ k₄] eqn:Fresh₁; 
    symmetry in Fresh₁.
  destruct (fresh k₄ T₂) as [u₂ k₅] eqn:Fresh₂; 
    symmetry in Fresh₂.
  assert (HInK₃ : InK s₃ k₅)
  by (
    eapply (fresh_preserves_InK k₄ u₂ k₅); eauto;
    eapply (fresh_preserves_InK k₃' u₁ k₄); eauto
  ).

  assert (HR30 : s₃ ↘ s ≡ s)
  by repeat (eapply restrict_transitive; eauto).

  assert (HTV'3 : uts k₃; ∅ ⊢ v' ↦ TSum T₁ T₂). {
    eapply unknown_invariance; eauto.
    eapply restrict_transitive; eauto.
    rewrite <- HR2'.
    eapply restrict_transitive; eauto.
  }

  assert (Val : is_value v')
  by (eapply narrow_is_value; eauto).

  (* Work towards nat denotations in k₃' *)  
  assert (Sat3: sat k₃)
  by (exists s₃; auto).

  move: (uniform_singleton' v₂' k₃ q₃' k₃' tr₃' Sample2 Sat3)
         => [v₂'' HV2''].
  
  assert (TMP: v₂ = v₂'')
  by (eapply Singleton_SubVal with (k := k₃'); eauto).
  subst.

  assert (Nat2: nat_denote' k₃' v₂' n₂)
  by (exists v₂''; eauto).

  assert (Sat2: sat k₂)
  by (exists s₂; auto).

  move: (uniform_singleton' v₁' k₂ q₂' k₂' tr₂' Sample1 Sat2)
         => [v₁'' HV1''].
  
  assert (TMP: v₁ = v₁'')
  by (eapply Singleton_SubVal with (k := k₂'); eauto).
  subst.

  assert (HS : singleton' k₃ v₁' v₁'').
  {
    eapply narrow_singleton_value; eauto.
    eapply narrow_is_value; eauto.
    exists s₂; eauto.
  }
  eapply uniform_preserves_singleton' in HS; eauto.

  assert (Nat1: nat_denote' k₃' v₁' n₁)
  by (exists v₁''; eauto).

  remember (unify_in k₅ v (Inl T₁ T₂ (U u₁))) as kl.
  remember (unify_in k₅ v (Inr T₁ T₂ (U u₂))) as kr.

  inversion Val; subst; eauto;
  inversion HTV'3; subst; eauto.

  - { (* Unknown case *)
      inversion HSub₁; subst; auto.

      remember (unify_in k₅ (U u)
                         (Inl T₁ T₂ (U u₁))) as kl.
      remember (unify_in k₅ (U u) 
                         (Inr T₁ T₂ (U u₂))) as kr.

      assert (WT₅ : well_typed_cset k₅)
      by (eapply fresh_preserves_well_typed; eauto;
          eapply fresh_preserves_well_typed; eauto).

      assert (HR31 : s₃ ↘ s₁ ≡ s₁)
      by (eapply restrict_transitive with (s' := s₂); eauto).

      assert (Map: Map.MapsTo u b s₃)
      by (eapply restrict_mapsto; eauto).

      assert (NotIn1 : ~ (Map.In u₁ (uts k₃)))
      by (rewrite HR3'; eapply fresh_is_fresh_type; eauto).
      
      assert (NotIn2' : ~ (Map.In u₂ (uts k₄)))
      by (eapply fresh_is_fresh_type; eauto).

      assert (NotIn2 : ~ (Map.In u₂ (uts k₃))).
      {
        apply fresh_increases_types in Fresh₁; auto.
        move => In.
        rewrite Fresh₁ in NotIn2'.
        apply NotIn2'.
        eapply MapProp.F.add_in_iff; auto.
        right; rewrite <- HR3'; auto.
      }

      assert (HR53 : uts k₅ ↘ uts k₃ ≡ uts k₃).
      {
        eapply restrict_transitive with (s' := uts k₄).
          apply fresh_increases_types in Fresh₂; auto.
          rewrite Fresh₂.
          apply restrict_add; auto.
          apply fresh_increases_types in Fresh₁; auto.
          rewrite Fresh₁.
          rewrite HR3'.
          apply restrict_add; auto.
          rewrite <- HR3'; auto.
      }

      assert (HTB : typed_base_val b (TSum T₁ T₂)).
      {
        assert (WTV : well_typed_valuation (uts k₅) s₃).
        by (eapply WT₅; eauto).
        
        inversion WTV; subst; auto.
        eapply H15 in Map; eauto.
        move: Map => [T' [Map' TB]].
        assert (Map.MapsTo u (TSum T₁ T₂) (uts k₅)).
        by (eapply restrict_mapsto; eauto).
        assert (T' = TSum T₁ T₂)
        by (eapply MapProp.F.MapsTo_fun; eauto).
        subst; auto.
      }

      assert (Hyp: u <> u₁ /\ u <> u₂ /\ u₁ <> u₂).
      {
        eapply fresh_fresh_all_unknowns_neq with (k := k₃');
        eauto.
        exists b; eauto.
      }
      move: Hyp => [NEq1 [NEq2 NEq3]].

      inversion HTB; subst; auto.
      destruct b; inversion H15; subst; auto.

      { (* INL CASE! *) 
        remember (unify_in k₅ (U u)
                           (Inl T₁ T₂ (U u₁))) as kl.
        remember (unify_in k₅ (U u) 
                           (Inr T₁ T₂ (U u₂))) as kr.

        remember (s₃ ⊕ u₁ ↦ b) as s₄.
        assert (HR4 : s₄ ↘ s₃ ≡ s₃).
        { 
          rewrite Heqs₄.
          eapply restrict_transitive with (s' := s₃); eauto. 
          apply restrict_add; auto.
          eapply fresh_is_fresh; eauto.  
        }
        
        assert (HInKl : InK s₄ kl).
        { (* InK (s₃ ⊕ u₁ ↦ b) kl *)
            rewrite Heqkl.
            - eapply unify_spec; eauto.
            + repeat constructor; eauto.
            + split; auto.
              * { 
                move: (restrict_domain_InK s₃ s₄ k₅ HInK₃)
                  => HR.
                subst.
                eapply InK_equiv in HR.
                eapply HR; eauto.
                eapply InK_equiv; eauto.
                }
              * {
                move => v; split; move => HSUB;
                inversion HSUB; subst; auto.
                - {
                  assert (b0 = BInl T₁ T₂ b).
                  {
                    eapply MapProp.F.add_mapsto_iff in H20.
                    move: H20 => [[C _] | [_ Map']].
                    + exfalso.
                      apply NEq1; auto.
                    + assert (Map.MapsTo u (BInl T₁ T₂ b) s₃)
                      by (eapply restrict_mapsto; eauto).
                      eapply MapProp.F.MapsTo_fun; eauto.
                  }
                  subst; simpl.
                  constructor; auto.
                  econstructor; eauto.
                  eapply MapProp.F.add_mapsto_iff; left; auto.
                  }
                - { 
                    inversion H23; subst; eauto.
                    eapply MapProp.F.add_mapsto_iff in H20;
                      eauto.
                    move: H20 => [[_ ?] | [C _]].
                    + subst.
                      econstructor.
                      instantiate (1:= BInl T₁ T₂ b0).
                      simpl; auto.
                      eapply restrict_mapsto; eauto.
                    + exfalso; apply C; auto.
                  }
                }
          } (* InK (s₃ ⊕ u₁ ↦ b) kl *)

          exists (U u).
          exists kl.
          exists s₄.
          split; auto.
            eapply restrict_transitive; eauto.
          repeat (split; auto).
          + subst; auto.
          + { (* SubVal s₄ Inl e1 Inl e' *)
              econstructor; eauto.
              eapply restrict_mapsto; eauto.
            }
          + destruct (sat_dec kr) as [SAT | UNSAT].
            {  (* SAT kr *)
              exists (n₁ // (n₁ + n₂) * q₁ * q₂ * q₂' * q₃ * q₃').
              exists(Chose 0 2 :: tr₃' ++ tr₃ ++ tr₂' ++ tr₂ ++ tr₁).
               econstructor; eauto.
               exists s₄; subst; auto.
            }
            { (* ~ SAT kr *)
              exists (q₁ * q₂ * q₂' * q₃ * q₃').
              exists(tr₃' ++ tr₃ ++ tr₂' ++ tr₂ ++ tr₁).
              econstructor; eauto.
              exists s₄; subst; auto.
            } 
      }
      { (* INR Case *)
        remember (unify_in k₅ (U u)
                           (Inl T₁ T₂ (U u₁))) as kl.
        remember (unify_in k₅ (U u) 
                           (Inr T₁ T₂ (U u₂))) as kr.

        remember (s₃ ⊕ u₂ ↦ b) as s₄.
        assert (HR4 : s₄ ↘ s₃ ≡ s₃).
        { 
          rewrite Heqs₄.
          eapply restrict_transitive with (s' := s₃); eauto. 
          apply restrict_add; auto.
          eapply fresh_is_fresh; eauto.  
          eapply fresh_preserves_InK; eauto.
        }
        
        assert (HInKr : InK s₄ kr).
        { (* InK (s₃ ⊕ u₁ ↦ b) kr *)
            rewrite Heqkr.
            - eapply unify_spec; eauto.
            + repeat constructor; eauto.
            + split; auto.
              * { 
                move: (restrict_domain_InK s₃ s₄ k₅ HInK₃)
                  => HR.
                subst.
                eapply InK_equiv in HR.
                eapply HR; eauto.
                eapply InK_equiv; eauto.
                }
              * {
                move => v; split; move => HSUB;
                inversion HSUB; subst; auto.
                - {
                  assert (b0 = BInr T₁ T₂ b).
                  {
                    eapply MapProp.F.add_mapsto_iff in H20.
                    move: H20 => [[C _] | [_ Map']].
                    + exfalso.
                      apply NEq2; auto.
                    + eapply MapProp.F.MapsTo_fun; eauto.
                  }
                  subst; simpl.
                  constructor; auto.
                  econstructor; eauto.
                  eapply MapProp.F.add_mapsto_iff; left; auto.
                  }
                - { 
                    inversion H23; subst; eauto.
                    eapply MapProp.F.add_mapsto_iff in H20;
                      eauto.
                    move: H20 => [[_ ?] | [C _]].
                    + subst.
                      econstructor.
                      instantiate (1:= BInr T₁ T₂ b0).
                      simpl; auto.
                      eapply restrict_mapsto; eauto.
                    + exfalso; apply C; auto.
                  }
                }
          } (* InK (s₃ ⊕ u₁ ↦ b) kl *)

          exists (U u).
          exists kr.
          exists s₄.
          split; auto.
            eapply restrict_transitive; eauto.
          repeat (split; auto).
          + subst; auto.
          + { (* SubVal s₄ Inl e1 Inl e' *)
              econstructor; eauto.
              eapply restrict_mapsto; eauto.
            }
          + destruct (sat_dec kl) as [SAT | UNSAT].
            {  (* SAT kr *)
              exists (n₂ // (n₁ + n₂) * q₁ * q₂ * q₂' * q₃ * q₃').
              exists(Chose 1 2 :: tr₃' ++ tr₃ ++ tr₂' ++ tr₂ ++ tr₁).
               econstructor; eauto.
               exists s₄; subst; auto.
            }
            { (* ~ SAT kr *)
              exists (q₁ * q₂ * q₂' * q₃ * q₃').
              exists(tr₃' ++ tr₃ ++ tr₂' ++ tr₂ ++ tr₁).
              eapply NInst_UNSAT_SAT; eauto.
              exists s₄; subst; auto.
            } 
      }
    }
  - { (* Inl case *) 
      inversion HSub₁; subst; auto.

      remember (unify_in k₅ (Inl T₁ T₂ e1)
                         (Inl T₁ T₂ (U u₁))) as kl.
      remember (unify_in k₅ (Inl T₁ T₂ e1) 
                         (Inr T₁ T₂ (U u₂))) as kr.

      (* not sat kr *)
      assert (~ (sat kr)).
      {
        move => [s' TMP].
        assert (Hs' : InK s' kr) by auto; clear TMP.
        rewrite Heqkr in Hs'.
        apply unify_spec in Hs'.
        move: Hs' => [HIns' ContraSub].
        move: (ContraSub (Inl T₁ T₂ e')) => [Contra _].
        assert (Hyp: exists v', SubVal s' (Inl T₁ T₂ e1) v').
        {
          eapply SubVal_exists with (k := k₅) (s':= s₃);
            eauto.
          eapply substU_restrict; eauto.
          eapply restrict_transitive with (s'0 := s₂); eauto.
        }          
        move: Hyp => [v' HV'].
        inversion HV'; subst; auto.
        eapply ContraSub in HV'; auto.
        inversion HV'.
        assumption.
        repeat constructor.
      }
      
      assert (Base: is_base_value e').
      {
        eapply SubVal_NonFun_is_base_value 
          with (s := s₃) (T := T₁); eauto.
          eapply substU_val_val with (e := e1); eauto.
          eapply substU_restrict; eauto.
          eapply restrict_transitive with (s' := s₂); eauto.
          eapply SubVal_preservation 
            with (U := uts k₃) (s := s₃) (e := e1); eauto.
          eapply substU_restrict; eauto.
          eapply restrict_transitive with (s' := s₂); eauto.
          inversion H2; auto.
      }

      eapply is_base_exp_to_base in Base; eauto.
      move: Base => [b Hb].

      remember (s₃ ⊕ u₁ ↦ b) as s₄.
      assert (HR4 : s₄ ↘ s₃ ≡ s₃).
      { 
        rewrite Heqs₄.
        eapply restrict_transitive with (s' := s₃); eauto. 
        apply restrict_add; auto.
        eapply fresh_is_fresh; eauto.  
      }
      
      assert (HInKl : InK (s₃ ⊕ u₁ ↦ b) kl).
      { (* InK (s₃ ⊕ u₁ ↦ b) kl *)
          rewrite Heqkl.
          - eapply unify_spec; eauto.
          + repeat constructor; eauto.
          + split; auto.
            * { 
              move: (restrict_domain_InK s₃ s₄ k₅ HInK₃)
                => HR.
              subst.
              eapply InK_equiv in HR.
              eapply HR; eauto.
              eapply InK_equiv; eauto.
              }
            * {
              move => v; split; move => HSUB;
              inversion HSUB; subst; auto.
              - {
                assert (e' = e'0).
                {
                  eapply (SubVal_restrict_injective e1)
                    with (s := s₁) (s' := s₃ ⊕ u₁ ↦ b); eauto.
                  inversion H2; subst; auto.
                  eapply restrict_transitive; eauto.
                  eapply restrict_transitive with (s' := s₂);
                    eauto.
                }
                subst.
                constructor.
                econstructor; eauto.
                eapply exp_to_base_round; eauto.
                eapply MapProp.F.add_mapsto_iff; eauto.
                }
              - { 
                  constructor.
                  inversion H23; subst; eauto.
                  eapply MapProp.F.add_mapsto_iff in H20;
                    eauto.
                  move: H20 => [[_ ?] | [C _]].
                  + subst.
                    eapply exp_to_base_round in Hb; eauto.
                    rewrite Hb.
                    eapply substU_restrict; eauto.
                    eapply restrict_transitive; eauto.
                    eapply restrict_transitive with (s' := s₂); eauto.
                  + exfalso; apply C; auto.
                }
              }
        } (* InK (s₃ ⊕ u₁ ↦ b) kl *)

      exists (Inl T₁ T₂ e1).
      exists kl.
      exists s₄.
      split; auto.
        eapply restrict_transitive; eauto.
      repeat (split; auto).
      + subst; auto.
      + { (* SubVal s₄ Inl e1 Inl e' *)
          constructor.
          eapply substU_restrict; eauto.
          subst.
          eapply restrict_transitive; eauto.
          eapply restrict_transitive with (s' := s₂); eauto.
        }
      +  exists (q₁ * q₂ * q₂' * q₃ * q₃').
         exists (tr₃' ++ tr₃ ++ tr₂' ++ tr₂ ++ tr₁).
         econstructor; eauto.
         exists s₄; subst; auto.
    }         
  - { (* Inr case *) 
      inversion HSub₁; subst; auto.

      remember (unify_in k₅ (Inr T₁ T₂ e1)
                         (Inl T₁ T₂ (U u₁))) as kl.
      remember (unify_in k₅ (Inr T₁ T₂ e1) 
                         (Inr T₁ T₂ (U u₂))) as kr.

      (* not sat kr *)
      assert (~ (sat kl)).
      {
        move => [s' TMP].
        assert (Hs' : InK s' kl) by auto; clear TMP.
        rewrite Heqkl in Hs'.
        apply unify_spec in Hs'.
        move: Hs' => [HIns' ContraSub].
        move: (ContraSub (Inr T₁ T₂ e')) => [Contra _].
        assert (Hyp: exists v', SubVal s' (Inr T₁ T₂ e1) v').
        {
          eapply SubVal_exists with (k := k₅) (s':= s₃);
            eauto.
          eapply substU_restrict; eauto.
          eapply restrict_transitive with (s'0 := s₂); eauto.
        }          
        move: Hyp => [v' HV'].
        inversion HV'; subst; auto.
        eapply ContraSub in HV'; auto.
        inversion HV'.
        assumption.
        repeat constructor.
      }
      
      assert (Base: is_base_value e').
      {
        eapply SubVal_NonFun_is_base_value 
          with (s := s₃) (T := T₂); eauto.
          eapply substU_val_val with (e := e1); eauto.
          eapply substU_restrict; eauto.
          eapply restrict_transitive with (s' := s₂); eauto.
          eapply SubVal_preservation 
            with (U := uts k₃) (s := s₃) (e := e1); eauto.
          eapply substU_restrict; eauto.
          eapply restrict_transitive with (s' := s₂); eauto.
          inversion H2; auto.
      }

      eapply is_base_exp_to_base in Base; eauto.
      move: Base => [b Hb].

      remember (s₃ ⊕ u₂ ↦ b) as s₄.
      assert (HR4 : s₄ ↘ s₃ ≡ s₃).
      { 
        rewrite Heqs₄.
        eapply restrict_transitive with (s' := s₃); eauto. 
        apply restrict_add; auto.
        eapply fresh_is_fresh; eauto.
        eapply fresh_preserves_InK; eauto.
      }
      
      assert (HInKl : InK (s₃ ⊕ u₂ ↦ b) kr).
      { (* InK (s₃ ⊕ u₂ ↦ b) kr *)
          rewrite Heqkr.
          - eapply unify_spec; eauto.
          + repeat constructor; eauto.
          + split; auto.
            * { 
              move: (restrict_domain_InK s₃ s₄ k₅ HInK₃)
                => HR.
              subst.
              eapply InK_equiv in HR.
              eapply HR; eauto.
              eapply InK_equiv; eauto.
              }
            * {
              move => v; split; move => HSUB;
              inversion HSUB; subst; auto.
              - {
                assert (e' = e'0).
                {
                  eapply (SubVal_restrict_injective e1)
                    with (s := s₁) (s' := s₃ ⊕ u₂ ↦ b); eauto.
                  inversion H2; subst; auto.
                  eapply restrict_transitive; eauto.
                  eapply restrict_transitive with (s' := s₂);
                    eauto.
                }
                subst.
                constructor.
                econstructor; eauto.
                eapply exp_to_base_round; eauto.
                eapply MapProp.F.add_mapsto_iff; eauto.
                }
              - { 
                  constructor.
                  inversion H23; subst; eauto.
                  eapply MapProp.F.add_mapsto_iff in H20;
                    eauto.
                  move: H20 => [[_ ?] | [C _]].
                  + subst.
                    eapply exp_to_base_round in Hb; eauto.
                    rewrite Hb.
                    eapply substU_restrict; eauto.
                    eapply restrict_transitive; eauto.
                    eapply restrict_transitive with (s' := s₂); eauto.
                  + exfalso; apply C; auto.
                }
              }
        } (* InK (s₃ ⊕ u₁ ↦ b) kl *)

      exists (Inr T₁ T₂ e1).
      exists kr.
      exists s₄.
      split; auto.
        eapply restrict_transitive; eauto.
      repeat (split; auto).
      + subst; auto.
      + { (* SubVal s₄ Inr e1 Inr e' *)
          constructor.
          eapply substU_restrict; eauto.
          subst.
          eapply restrict_transitive; eauto.
          eapply restrict_transitive with (s' := s₂); eauto.
        }
      +  exists (q₁ * q₂ * q₂' * q₃ * q₃').
         exists (tr₃' ++ tr₃ ++ tr₂' ++ tr₂ ++ tr₁).
         eapply NInst_UNSAT_SAT; eauto.
         exists s₄; subst; auto.
    }         
(* Bang *)
- move => s e' k T HInK HSub HTe' HWF.
  inversion HSub; subst; try solve [absurd_base_value].
  inversion HTe'; subst.
  discharge_IH IH s e0 k T Hyp.
  move : Hyp => 
    [v' [k' [s' [HEq [HInK' [HSub' [q₁ [tr₁ HNarrow]]]]]]]].
  assert (HV : is_value v')
  by (eapply narrow_is_value; eauto).
  assert (HT: uts k'; ∅ ⊢ v' ↦ T)
  by (eapply narrow_preservation; eauto).
  move : (sample_spec_1' v' HV k' s' v T HT H0 HInK' HSub') => [kf [HInf [q₂ [tr₂ HU]]]].
  exists v'; exists kf; exists s'.
  repeat (split; auto).
  exists (q₁ * q₂).
  exists (tr₂ ++ tr₁).
  econstructor; eauto.
- move => s e' k T' HIn HSub HTe HWF.
  inversion HSub; subst; try solve [absurd_not_val HNotVal].
  inversion HTe; subst.
  discharge_IH IH s e0 k (substT O (TMu T0) T0) Hyp;
  move : Hyp => [v' [k' [s' [HEq [HIn' [HSub' 
                        [q [tr Hnarrow]]]]]]]].
  exists (Fold (TMu T0) v'); exists k'; exists s'.
  splitSolver.
  exists q; exists tr.
  econstructor; notValSolver HNotVal; eauto.

- move => s e' k T' HIn HSub HTe' HWF.
  inversion HSub; subst; try solve [absurd_base_value].
  inversion HTe'; subst.
  discharge_IH IH s e0 k (TMu T0) Hyp.
  move: Hyp => [v0 [k' [s' [HEq [HIn' [HSub' 
                       [q₁ [tr₁ Hnarrow]]]]]]]].
  inversion HSub'; subst.
  * { (* Unknown case - harder :) *)
    destruct (fresh k' (substT O (TMu T0) T0))
        as [u' k₁] eqn:Fresh; symmetry in Fresh.

    destruct b; simpl in *; try congruence.
    inversion H; subst; eauto.
    remember (unify_in k₁ (U u) (Fold (TMu T0) (U u'))) 
      as k₂.
    remember (Map.add u' b s') as s''.

    assert (Neq: u <> u').
    { move => Contra; eapply fresh_is_fresh; subst; eauto.
      exists (BFold (TMu T0) b); eauto. }

    assert (HR: s'' ↘ s' ≡ s').
    { subst; apply restrict_add; auto.
      eapply fresh_is_fresh; eauto. } 
    exists (U u'); exists k₂; exists s''.
    split; [eapply restrict_transitive; eauto | ].
    repeat (split; auto).
    { (* Inclusion *)
      rewrite Heqk₂.
      apply unify_spec; eauto;
      try solve [repeat econstructor].
      split.
      - {
         erewrite <- (fresh_preserves_domain k' u' k₁); 
          eauto.
         eapply (fresh_preserves_InK k' u' k₁); eauto.
         rewrite InK_equiv; eauto.
         move:(restrict_domain_InK s' s'' k' HIn')=>
           HEqRestrict.
         eapply Equiv_transitive 
           with (s2 := (MapProp.restrict s'' s')); 
           eauto; clear HEqRestrict.
        } 
      - move => v; split => HInP.
        * { 
          inversion HInP; subst.
          assert (b0 = BFold (TMu T0) b).
          { eapply MapProp.F.MapsTo_fun; eauto. 
            MapsToSolver. }
          subst.
          constructor.
          fold base_to_exp.
          econstructor; eauto.
          MapsToSolver.
          }
        * {
          inversion HInP;
          repeat match goal with 
            | [H : SubVal _ (U _) _ |- _ ] =>
              inversion H; subst; clear H
          end; subst; eauto. 
          assert (b0 = b).
          { eapply MapProp.F.add_mapsto_iff in H9; eauto.
            move: H9 => [[_ ?]|[C _]]; auto.
            exfalso; apply C; auto. }
          subst; 
          econstructor; eauto. 
          MapsToSolver.
          }
    }
    
  { (* SubVal *) 
    econstructor; eauto.
    MapsToSolver.
  } 
  
  exists q₁. exists tr₁.
  eapply NUnfold_U; subst; eauto.
  
  }
  * { (*  fold - easy *)
      
    exists e1; exists k'; exists s'.
    splitSolver.
    }
- move => s e' k T₁ HIn HSub HTe HWF.
  inversion HSub; subst; try solve [absurd_base_value].
  inversion HTe; subst.
  discharge_IH IH1 s e1 k T₁ Hyp.
  move : Hyp => 
    [v' [k' [s' [HEq [HInK' [HSub' [q₁ [tr₁ HNarrow]]]]]]]].
  discharge_IH IH2 s' e2 k' T₂ Hyp.
  move : Hyp => 
    [v'' [k'' [s'' [HEq2 [HInK2 [HSub2 [q₂ [tr₂ HNarrow2]]]]]]]].
  exists v'. exists k''. exists s''.
  splitSolver.
  + eapply substU_restrict; eauto.
  + exists (q₁ * q₂). exists (tr₂ ++ tr₁).
    econstructor; eauto.
Qed.
