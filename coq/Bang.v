Require Import Util.
Require Import Types.
Require Import Probability.
Require Import Constraints.
Require Import Valuation.
Import CSet.

Require Import QArith.

Inductive sample' : 
  exp -> cset -> frac -> cset -> trace -> Prop := 
| UST_U : forall u k q k' tr,
    sample u k q k' tr ->
    sample' (U u) k q k' tr

| UST_Unit : forall k,
    sample' Unit k 1 k nil

| UST_Pair : forall v1 v2 k q1 q2 k1 k2 tr1 tr2,
    sample' v1 k q1 k1 tr1 ->
    sample' v2 k1 q2 k2 tr2 ->
    sample' (Pair v1 v2) k (q1 * q2) k2 (tr2 ++ tr1)

| UST_Inl : forall v k q k' tr t1 t2 ,
    sample' v k q k' tr ->
    sample' (Inl t1 t2 v) k q k' tr

| UST_Inr : forall v k q k' tr t1 t2,
    sample' v k q k' tr ->
    sample' (Inr t1 t2 v) k q k' tr

| UST_Fold : forall T v k q k' tr,
    sample' v k q k' tr ->
    sample' (Fold T v) k q k' tr.

Lemma sample_preserves_types' :  
  forall e k q k' tr, 
    sample' e k q k' tr -> 
    uts k = uts k'.
Proof.
move => e k q k' tr H; induction H; auto.
- eapply sample_preserves_types; eauto.
- rewrite IHsample'1; auto.
Qed. 

Lemma sample_preserves_well_typed' :  
  forall e k q k' tr, 
    sample' e k q k' tr -> 
    well_typed_cset k ->
    well_typed_cset k'.
Proof.
move => e k q k' tr H; induction H; auto.
- eapply sample_preserves_well_typed; eauto.
Qed.

Lemma uniform_sat' : 
  forall v k q k' tr,
    sample' v k q k' tr -> sat k ->
    sat k'.
move => v k q k' tr H; induction H => SAT; 
eauto.
eapply uniform_sat; eauto.
Qed.

Lemma sample_lte' : 
  forall v k q k' tr,
    sample' v k q k' tr ->
    lte k' k.
Proof.  
  induction v; intros; try inversion H; eauto.
  - apply reflexivity.
  - eapply transitivity; eauto.
  - subst. eapply sample_lte; eauto.
Qed.

Ltac discharge_IH_Bang IH s e k T Hyp :=
  specialize (IH s e k T);
  match goal with 
    | [ H : _ -> _ -> _ -> _ -> ?Res |- _ ] =>
      assert (Hyp : Res); [eapply H | ]; clear H; eauto
  end; eauto.

Lemma shift_preserves_NonFun : 
  forall T, isNonFunType T ->
  forall n, isNonFunType (Types.shift n T).
move => T H; induction H; move => n; simpl; eauto;
try solve [econstructor; eauto].
destruct (lt_dec X n); econstructor.
Qed. 

Lemma substT_preserves_NonFun :
  forall T , isNonFunType T ->
  forall T', isNonFunType T' ->
  forall n, isNonFunType (substT n T' T).
move => T H; induction H; move => T' HT HT'; simpl; eauto;
match goal with 
  | |- context[eq_tvar_dec O ?X]  => 
    destruct (eq_tvar_dec O X)
  | _ => idtac
end; simpl; eauto;
try solve [inversion HT; subst; econstructor; eauto].
- destruct (eq_tvar_dec HT' X); eauto.
  econstructor.
econstructor.
eapply IHisNonFunType.
eapply shift_preserves_NonFun; eauto.
Qed.

Lemma sample_spec_1' : 
  forall v (H : is_value v) k s v' T, 
    uts k; ∅ ⊢ v ↦ T ->
    isNonFunType T ->
    InK s k -> SubVal s v v' ->
    exists k', InK s k' /\
      exists q tr, sample' v k q k' tr.
move => v H; induction H;
move => k s v' T' HT' HNF HInK HSub;
inversion HSub; subst;
inversion HT'; subst.
- exists k.
  split; auto.
  exists 1; exists nil.
  econstructor; eauto.
- move: (sample_spec_1 u k s b HInK H1) =>
    [k' [HInK' [q [tr H]]]].
  exists k'.
  split; auto.
  exists q; exists tr.
  econstructor; eauto.
- discharge_IH_Bang IHis_value1 k s e1' T₁ Hyp.
    inversion HNF; eauto.
  move: Hyp => [k₁ [HInK₁ [q₁ [tr₁ H1]]]].
  discharge_IH_Bang IHis_value2 k₁ s e2' T₂ Hyp.
    erewrite <- sample_preserves_types'; eauto.
    inversion HNF; eauto.
  move: Hyp => [k₂ [HInK₂ [q₂ [tr₂ H2]]]].
  exists k₂.
  split; auto.
  exists (q₁ * q₂).
  exists (tr₂ ++ tr₁).
  econstructor; eauto.
- discharge_IH_Bang IHis_value k s e' T₁ Hyp.
    inversion HNF; eauto.
  move: Hyp => [k' [HInK' [q [tr H']]]].
  exists k'.
  split; auto.
  exists q; exists tr.
  econstructor; eauto.
- discharge_IH_Bang IHis_value k s e' T₂ Hyp.
    inversion HNF; eauto.
  move: Hyp => [k' [HInK' [q [tr H']]]].
  exists k'.
  split; auto.
  exists q; exists tr.
  econstructor; eauto.
- inversion HNF.
- discharge_IH_Bang IHis_value k s e' (substT O (TMu T0) T0) Hyp.
    inversion HNF; subst; eauto.
    eapply substT_preserves_NonFun; eauto.
  
  move: Hyp => [k' [HInK' [q [tr H']]]].
  exists k'.
  split; auto.
  exists q; exists tr.
  econstructor; eauto.
Qed.  

Lemma sample_spec_2' : 
  forall v k q k' tr,
    sample' v k q k' tr ->
  forall s, InK s k' -> InK s k.
move => v k q k' tr H; induction H => s In; eauto.
eapply sample_spec_2; eauto.
Qed. 

Inductive singleton' (k : cset) 
: exp -> exp -> Prop :=
| Sing_Unit : singleton' k Unit Unit
| Sing_Pair : 
    forall v1 v1' v2 v2',
    singleton' k v1 v1' ->
    singleton' k v2 v2' ->
    singleton' k (Pair v1  v2) 
                 (Pair v1' v2')
| Sing_Inl : 
    forall T1 T2 v v',
      singleton' k v v' ->
      singleton' k (Inl T1 T2 v) (Inl T1 T2 v')
| Sing_Inr :
    forall T1 T2 v v',
      singleton' k v v' ->
      singleton' k (Inr T1 T2 v) (Inr T1 T2 v')
| Sing_Fold :
    forall T v v',
      singleton' k v v' ->
      singleton' k (Fold T v) (Fold T v')
| Sing_U :
    forall u b,
      singleton k u b ->
      singleton' k (U u) (base_to_exp b).

Lemma SubVal_singleton' : 
  forall k v v', 
    singleton' k v v' ->
    forall s, InK s k -> SubVal s v v'.
move => k v v' H; induction H; move => s HIn;
econstructor; eauto.
Qed.

Lemma uniform_preserves_singleton' :
  forall v k q k' tr,
    sample' v k q k' tr ->
    sat k -> 
    forall v' v'', singleton' k  v' v'' ->
                   singleton' k' v' v''.
move => v k q k' tr H; induction H;
move => SAT v' v'' HS; eauto.
- induction HS; subst; eauto;
  econstructor; eauto.
  eapply uniform_preserves_singleton; eauto.
- induction HS; subst; eauto;
  econstructor; eauto.
  assert (singleton' k2 (U u) (base_to_exp b)).
  {
    eapply IHsample'2; eauto.
    eapply uniform_sat'; eauto.
    eapply IHsample'1; eauto.
    econstructor; eauto.
  }
  inversion H2; subst.
  erewrite base_to_exp_injective; eauto.
Qed.

Lemma uniform_singleton' : 
  forall v k q k' tr,
    sample' v k q k' tr -> sat k ->
    exists v', singleton' k' v v'.
move => v k q k' tr H; 
induction H; move => SAT; eauto.
- eapply uniform_singleton in H; auto.
  move: H => [v Hv].
  exists (base_to_exp v); 
  econstructor; eauto.
- exists Unit; econstructor; eauto.
- move: (IHsample'1 SAT) => [v1' H1].
  eapply uniform_sat' in H; eauto.
  move: (IHsample'2 H) => [v2' H2].
  exists (Pair v1' v2'); auto.
  simpl; auto.
  eapply uniform_preserves_singleton' in H1; 
    eauto.
  econstructor; eauto.
- move: (IHsample' SAT) => [v' Hv].
  exists (Inl t1 t2 v'); econstructor; eauto.
- move: (IHsample' SAT) => [v' Hv].
  exists (Inr t1 t2 v'); econstructor; eauto.
- move: (IHsample' SAT) => [v' Hv].
  exists (Fold T v'); econstructor; eauto.
Qed.


Definition nat_denote' k e n : Prop :=
  exists v, singleton' k e v /\ nat_denote v n.

Lemma Singleton_SubVal : 
  forall s v v', SubVal s v v' ->
  forall k v'', InK s k -> singleton' k v v'' ->
  v' = v''.
move => s v v' HSub; induction HSub;
move => k v'' HIn HS; 
inversion HS; subst; eauto.
- erewrite IHHSub1; eauto.
  erewrite IHHSub2; eauto.
- erewrite IHHSub; eauto.
- erewrite IHHSub; eauto.
- move: (H2 s HIn) => H.
  assert (b = b0).
    eapply MapProp.F.MapsTo_fun; eauto.
  subst; auto.
- erewrite IHHSub; eauto.
Qed.

Lemma sample_domain' :
  forall v k q k' tr,
    sample' v k q k' tr ->
    domain k = domain k'.
move => v k q k' tr H; induction H; eauto.
- eapply sample_domain; eauto.
- rewrite IHsample'1; eauto.
Qed.