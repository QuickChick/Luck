Require Import List. Import ListNotations.
Require Import ListSet.

Require ssreflect.

Require Import Util.
Require Import Types.
Require Import Valuation.
Require Import Probability.
Require Import Constraints.
Require Import Bang.
Require Import NarrowBase.
Require Import NarrowCompleteness.

Require Import QArith.

Set Bullet Behavior "Strict Subproofs". 

Import CSet.

Lemma SubVal_domain : 
  forall s' v v',
  SubVal s' v v' ->
  forall s, s' ↘ s ≡ s ->
  (forall u, InExp u v -> Map.In u s) ->
  SubVal s v v'.
move => s' v v' H; induction H; move => s In HR;
try constructor; eauto;
try match goal with
  | [ H : forall _, _ -> _ -> SubVal _ ?E ?E' 
      |- SubVal _ ?E ?E' ] =>
    eapply H; eauto; 
    move => ? ?;
    eapply HR; constructor (solve [auto])
end.
econstructor; eauto.
assert (Map.In u s).
by (eapply HR; constructor; auto).
move: H1 => [b' TMP].
assert (Hb' : Map.MapsTo u b' s) by auto; clear TMP.
assert (b = b')
by (eapply MapProp.F.MapsTo_fun; eauto;
    eapply restrict_mapsto; eauto).
subst; auto.
Qed.

Lemma InExp_subst : 
  forall e u x v,
    InExp u ([x := v] e) ->
    InExp u v \/ InExp u e.
induction e => u' x' v' In; simpl in *;
repeat match goal with 
  | [ H : context[eq_var_dec ?X ?Y] |- _ ] =>
    let H' := fresh "H" in
    destruct (eq_var_dec X Y); simpl in H
end; auto;
  inversion In; subst; eauto;
  try solve [right; constructor (solve [eauto])];
  try solve [match goal with 
    | [ H  : InExp ?U ([?X := ?V]?E),
        IH : forall _ _ _, InExp _ ([_:=_]?E) -> _ |- _] =>
      eapply IH in H; inversion H; eauto;
      right; constructor (solve [eauto])
  end].
Qed.

Hint Constructors InExp.
Hint Resolve narrow_increases_domain.
Hint Resolve unify_domain.
Lemma narrow_domain :
  forall e k q v k' tr,
  e ◂ k ⇒ q % (v, k') @ tr ->
  (forall u, InExp u e -> In u (domain k)) ->
  forall u, InExp u v -> In u (domain k').
move => e k q v k' tr H; induction H => InK u'' HIn.
- eapply InK; eauto.
- inversion HIn; subst; eauto.
- eapply IHnarrow2; eauto.
  move => u In'.
  eapply InExp_subst in In'.  
  move: In' => [InV2 | /InExp_subst [InV1 | InE]]; eauto.
- eapply IHnarrow2; subst; eauto.
  move => ? In.
  eapply InExp_subst in In.  
  move: In => [In | /InExp_subst [In | In]]; eauto.
  + inversion In; subst.
    eapply unify_domain; eauto.
  + inversion In; subst.
    eapply unify_domain; eauto.
  + eapply unify_domain; eauto.
    right; right.
    erewrite <- (fresh_preserves_domain k₁); eauto.
    erewrite <- (fresh_preserves_domain k'); eauto.
- inversion HIn; subst; eauto.
- inversion HIn; subst; eauto.
- eapply IHnarrow2; eauto.
  move => ? In.
  eapply InExp_subst in In.
  move: In => [InV1 | InE1]; eauto.
- eapply IHnarrow2; eauto.
  move => ? In.
  eapply InExp_subst in In.
  move: In => [In | In]; eauto.
- eapply IHnarrow2; eauto.
  move => ? In.
  eapply InExp_subst in In.
  move: In => [In | In]; subst; eauto.
  + inversion In; subst; eauto.
    eapply unify_domain; eauto.
  + eapply unify_domain; eauto.
    right; right.
    erewrite <- (fresh_preserves_domain k₁); eauto.
    erewrite <- (fresh_preserves_domain k₀); eauto.
- eapply IHnarrow2; eauto.
  move => ? In.
  eapply InExp_subst in In.
  move: In => [In | In]; subst; eauto.
  + inversion In; subst; eauto.
    eapply unify_domain; eauto.
  + eapply unify_domain; eauto.
    right; right.
    erewrite <- (fresh_preserves_domain k₁); eauto.
    erewrite <- (fresh_preserves_domain k₀); eauto.
- eapply IHnarrow2; eauto.
  move => ? In.
  eapply InExp_subst in In.
  move: In => [In | In]; subst.
  + inversion In; subst; eauto.
    eapply unify_domain; eauto.
  + eapply unify_domain; eauto.
    right; right.
    erewrite <- (fresh_preserves_domain k₁); eauto.
    erewrite <- (fresh_preserves_domain k₀); eauto.
- eapply IHnarrow2; eauto.
  move => ? In.
  eapply InExp_subst in In.
  move: In => [In | In]; subst.
  + inversion In; subst; eauto.
    eapply unify_domain; eauto.
  + eapply unify_domain; eauto.
    right; right.
    erewrite <- (fresh_preserves_domain k₁); eauto.
    erewrite <- (fresh_preserves_domain k₀); eauto.
- eapply IHnarrow3; eauto.
  move => u' In.
  move: In => /InExp_subst [In | /InExp_subst [In | In]];
             eauto.
  eapply narrow_increases_domain; eauto.
- subst; eapply unify_domain; eauto.
- subst; eapply unify_domain ; eauto.
- subst; eapply unify_domain ; eauto. 
- subst; eapply unify_domain ; eauto. 
- erewrite <- sample_domain'; eauto.
- eapply IHnarrow; eauto.
  inversion HIn; eauto.
- eapply IHnarrow; eauto.
- subst; eapply unify_domain; eauto.
- eapply narrow_increases_domain; eauto.
Qed.

Hint Constructors SubVal.
Ltac discharge11 H arg1 Hyp :=
  specialize (H arg1);
  match goal with 
    | [H : ?H1 -> ?Res |- _] => 
      assert H1; [eauto | 
      assert (Hyp : Res); [eapply H; eauto | ]];
      clear H
  end.

Lemma InExp_SubVal : 
  forall v s, 
    (forall u, InExp u v -> Map.In u s) ->
  exists v', SubVal s v v'.
induction v=> s In; eauto;
try solve [
  discharge11 IHv s Hyp;
  move: Hyp => [v' Sub]; eauto];
try solve [
  discharge11 IHv1 s Hyp;
  move: Hyp => [v1' Sub1];
  discharge11 IHv2 s Hyp;
  move: Hyp => [v2' Sub2];
  eauto];
try solve [
  discharge11 IHv1 s Hyp;
  move: Hyp => [v1' Sub1];
  discharge11 IHv2 s Hyp;
  move: Hyp => [v2' Sub2];
  discharge11 IHv3 s Hyp;
  move: Hyp => [v3' Sub3];
  eauto].
- discharge11 In u Hyp.
  move: Hyp => [b Tmp].
  exists (base_to_exp b); eauto.
Qed.


Lemma SubVal_subst' : 
  forall e s x v v' es,
    SubVal s v v' ->
    SubVal s ([x:=v]e) es ->
    exists e', SubVal s e e'.
induction e => s x' v v' es SubV Sub; simpl in *; eauto.
- destruct (eq_var_dec x' x) eqn:H; eauto.
  destruct (eq_var_dec x' f) eqn:H'; eauto.
  inversion Sub; subst; eauto.
  eapply IHe in H6; eauto.
  move: H6 => [e'' He'']; eauto.
- inversion Sub; subst; eauto.
  eapply IHe1 in H1; eauto.
  eapply IHe2 in H3; eauto.
  move: H1 => [e1'' H1'];
  move: H3 => [e2'' H2']; eauto.
- inversion Sub; subst; eauto.
  eapply IHe1 in H1; eauto.
  eapply IHe2 in H3; eauto.
  move: H1 => [e1'' H1'];
  move: H3 => [e2'' H2']; eauto.
- inversion Sub; subst; eauto. 
  destruct (eq_var_dec x' x) eqn:H; eauto.
  + eapply IHe1 in H4; eauto.
    move: H4 => [e1'' H1']; eauto.
  + destruct (eq_var_dec x' y) eqn:H'; eauto.
    * eapply IHe1 in H4; eauto.
      move: H4 => [e1'' H1']; eauto.
    * eapply IHe1 in H4; eauto.
      move: H4 => [e1'' H1']; eauto.
      eapply IHe2 in H5; eauto.
      move: H5 => [e2'' H2']; eauto.
- inversion Sub; subst; eauto.
  eapply IHe in H3; eauto.
  move: H3 => [e'' H']; eauto.
- inversion Sub; subst; eauto.
  eapply IHe in H3; eauto.
  move: H3 => [e'' H']; eauto.
- inversion Sub; subst; eauto.
  destruct (eq_var_dec x' x) eqn:H1;
  destruct (eq_var_dec x' y) eqn:H2.
  + eapply IHe1 in H5; eauto;
    move: H5 => [e1'' H1']; eauto.
  + eapply IHe1 in H5; eauto;
    move: H5 => [e1'' H1']; eauto.
    eapply IHe3 in H7 ;eauto.
    move: H7 => [e3'' H3']; eauto.
  + eapply IHe1 in H5; eauto;
    move: H5 => [e1'' H1']; eauto.
    eapply IHe2 in H6 ;eauto.
    move: H6 => [e2'' H2']; eauto.
  + eapply IHe1 in H5; eauto;
    move: H5 => [e1'' H1']; eauto.
    eapply IHe2 in H6 ;eauto.
    move: H6 => [e2'' H2']; eauto.
    eapply IHe3 in H7 ;eauto.
    move: H7 => [e3'' H3']; eauto.
- inversion Sub; subst; eauto.
  eapply IHe in H2; eauto.
  move: H2 => [e'' H']; eauto.
- inversion Sub; subst; eauto.
  eapply IHe in H2; eauto.
  move: H2 => [e'' H']; eauto.
- inversion Sub; subst; eauto.
  eapply IHe1 in H2; eauto.
  eapply IHe2 in H4; eauto.
  eapply IHe3 in H5; eauto.
  move: H2 => [e1'' H1'];
  move: H4 => [e2'' H2']; 
  move: H5 => [e3'' H3']; eauto.
- inversion Sub; subst; eauto.
  eapply IHe in H0; eauto.
  move: H0 => [e'' H']; eauto.
- inversion Sub; subst; eauto.
  eapply IHe1 in H3; eauto.
  eapply IHe2 in H4; eauto.
  move: H3 => [e1'' H1'];
  move: H4 => [e2'' H2']; eauto.             
Qed.

Lemma SubVal_restrict_injective' :
  forall s e e',
    SubVal s e e' ->
  forall s' e'', s' ↘ s ≡ s ->
                 SubVal s' e e'' ->
    e'' = e'.
move => s e e' Sub; induction Sub; 
move => s' e'' HR Sub'; inversion Sub'; 
        subst; eauto;
f_equal; eauto.
eapply MapProp.F.MapsTo_fun; eauto.
eapply restrict_mapsto; eauto.
Qed.

Lemma subst_base :
  forall b x v, base_to_exp b = [x := v](base_to_exp b).
induction b => x v; simpl; eauto;
try erewrite <- IHb1; eauto;
try erewrite <- IHb2; eauto;
try erewrite <- IHb; eauto.
Qed.

Lemma SubVal_subst_strong : 
  forall e s x v v' es,
    SubVal s v v' ->
    SubVal s ([x:=v]e) es ->
    exists e', SubVal s e e' /\ es = [x:=v']e'.
induction e => s x' v v' es SubV Sub; simpl in *; eauto.
- destruct (eq_var_dec x' x) eqn:H; eauto.
  + exists (Var x).
    split; auto.
    simpl; rewrite H; auto.
    eapply SubVal_restrict_injective'; eauto.
  + exists (Var x).
    split; auto.
    simpl; rewrite H; auto.
    inversion Sub; auto.
- inversion Sub; subst; auto.
  exists Unit; eauto.
- destruct (eq_var_dec x' x) eqn:H; eauto;
  destruct (eq_var_dec x' f) eqn:H'; eauto.
  + inversion Sub; subst; eauto.
    exists (Rec f x t t0 e').
    split; auto.        
    simpl; rewrite H; auto.
  + inversion Sub; subst; eauto.
    exists (Rec f x t t0 e').
    split; auto.        
    simpl; rewrite H; auto.
  + inversion Sub; subst; eauto.
    exists (Rec f x t t0 e').
    split; auto.        
    simpl; rewrite H'; rewrite H; auto.
  + inversion Sub; subst; eauto.
    eapply IHe in H6; eauto.
    move: H6 => [e'' [? ?]]; eauto.
    exists (Rec f x t t0 e''); eauto.
    split; auto.
    simpl; rewrite H; rewrite H'; auto.
    subst; auto.
- inversion Sub; subst; eauto.
  eapply IHe1 in H1; eauto.
  eapply IHe2 in H3; eauto.
  move: H1 => [e1'' [? ?]];
  move: H3 => [e2'' [? ?]]; eauto.
  exists (App e1'' e2''); split; auto.
  simpl; subst; auto.
- inversion Sub; subst; eauto.
  eapply IHe1 in H1; eauto.
  eapply IHe2 in H3; eauto.
  move: H1 => [e1'' [? ?]];
  move: H3 => [e2'' [? ?]]; eauto.
  exists (Pair e1'' e2''); split; auto.
  simpl; subst; auto.
- inversion Sub; subst; eauto. 
  destruct (eq_var_dec x' x) eqn:H; eauto.
  + eapply IHe1 in H4; eauto.
    move: H4 => [e1'' [? ?]]; eauto.
    exists (CaseP e1'' x y eb'); split; auto.
    simpl; rewrite H; subst; auto.
  + destruct (eq_var_dec x' y) eqn:H'; eauto.
    * eapply IHe1 in H4; eauto.
      move: H4 => [e1'' [? ?]]; eauto.
      exists (CaseP e1'' x y eb'); split; auto.
      simpl; rewrite H; rewrite H'; subst; auto.
    * eapply IHe1 in H4; eauto.
      move: H4 => [e1'' [? ?]]; eauto.
      eapply IHe2 in H5; eauto.
      move: H5 => [e2'' [? ?]]; eauto.
      exists (CaseP e1'' x y e2''); split; auto.
      simpl; rewrite H; rewrite H'; subst; eauto.
- inversion Sub; subst; eauto.
  eapply IHe in H3; eauto.
  move: H3 => [e'' [? ?]]; eauto.
  exists (Inl t t0 e''); split; simpl; subst; auto.
- inversion Sub; subst; eauto.
  eapply IHe in H3; eauto.
  move: H3 => [e'' [? ?]]; eauto.
  exists (Inr t t0 e''); split; simpl; subst; auto.
- inversion Sub; subst; eauto.
  destruct (eq_var_dec x' x) eqn:H1;
  destruct (eq_var_dec x' y) eqn:H2.
  + eapply IHe1 in H5; eauto;
    move: H5 => [e1'' [? ?]]; eauto.
    exists (Case e1'' x ex' y ey'); split; auto.
    simpl; rewrite H1; rewrite H2; subst; auto.
  + eapply IHe1 in H5; eauto;
    move: H5 => [e1'' [? ?]]; eauto.
    eapply IHe3 in H7 ;eauto.
    move: H7 => [e3'' [? ?]]; eauto.
    exists (Case e1'' x ex' y e3''); split; auto.
    simpl; rewrite H1; rewrite H2; subst; auto.
  + eapply IHe1 in H5; eauto;
    move: H5 => [e1'' [? ?]]; eauto.
    eapply IHe2 in H6 ;eauto.
    move: H6 => [e2'' [? ?]]; eauto.
    exists (Case e1'' x e2'' y ey'); split; auto.
    simpl; rewrite H1; rewrite H2; subst; auto.
  + eapply IHe1 in H5; eauto;
    move: H5 => [e1'' [? ?]]; eauto.
    eapply IHe2 in H6 ;eauto.
    move: H6 => [e2'' [? ?]]; eauto.
    eapply IHe3 in H7 ;eauto.
    move: H7 => [e3'' [? ?]]; eauto.
    exists (Case e1'' x e2'' y e3''); split; auto.
    simpl; rewrite H1; rewrite H2; subst; auto.
- inversion Sub; subst; eauto.
  eapply IHe in H2; eauto.
  move: H2 => [e'' [? ?]]; eauto.
  exists (Fold t e''); split; simpl; subst; auto.
- inversion Sub; subst; eauto.
  eapply IHe in H2; eauto.
  move: H2 => [e'' [? ?]]; eauto.
  exists (Unfold t e''); split; simpl; subst; auto.
- inversion Sub; subst; eauto.
  exists (base_to_exp b).
  split; auto.
  eapply subst_base; eauto.
- inversion Sub; subst; eauto.
  eapply IHe1 in H2; eauto.
  eapply IHe2 in H4; eauto.
  eapply IHe3 in H5; eauto.
  move: H2 => [e1'' [? ?]];
  move: H4 => [e2'' [? ?]]; 
  move: H5 => [e3'' [? ?]]; eauto.
  exists (Inst e1'' e2'' e3''); split; simpl; subst; auto.
- inversion Sub; subst; eauto.
  eapply IHe in H0; eauto.
  move: H0 => [e'' [? ?]]; eauto.
  exists (Bang e''); split; simpl; subst; auto.
- inversion Sub; subst; eauto.
  eapply IHe1 in H3; eauto.
  eapply IHe2 in H4; eauto.
  move: H3 => [e1'' [? ?]].
  move: H4 => [e2'' [? ?]].
  exists (Til e1'' t e2''); split; simpl; subst; auto.
Qed.

Lemma SubVal_val_val' : 
  forall e' : exp,
    is_value e' ->
  forall s e, SubVal s e e' ->
    is_value e.
move => e' H; induction H;
move => s e₀ Sub; inversion Sub; subst; eauto;
constructor; eauto.
Qed.

Ltac discharge_IHs IH s e Hyp :=
  specialize (IH s e);
  match goal with 
    | [ H : ?H1 -> ?H2 -> ?H3 -> ?Res 
      |- _ ] =>
      let HIn  := fresh "In" in
      let HSub := fresh "Sub" in 
      let HInK := fresh "InK" in
      assert (HIn : H1); [ eauto | 
      assert (HSub: H2); [ eauto |
      assert (HInK: H3); [ eauto |
      assert (Hyp : Res); [eapply H | ]; clear H; 
                           clear_dups]]]; eauto
  end.

Theorem narrow_soundness : 
  forall e k q v k' tr,
    e ◂ k ⇒ q % (v, k') @ tr ->
  forall s' vs , 
    InK s' k' -> SubVal s' v vs -> 
    (forall u, InExp u e -> In u (domain k)) ->
  exists s es, 
     s' ↘ s ≡ s /\ InK s k /\ SubVal s e es /\
    es ⇓ vs.
Proof.
move => e k q v k' tr H; induction H; 
move => s' vs HIn' HSub' HInK.
- exists s'; exists vs.
  repeat (split; auto).
  constructor; auto.
  eapply substU_val_val; eauto.
- inversion HSub'; subst; auto.
  discharge_IHs IHnarrow2 s' e2' Hyp.
  move: Hyp => [s1 [e2 [HR2 [HIn2 [HSub2 HN2]]]]].
  discharge_IHs IHnarrow1 s1 e1' Hyp.
  { eapply SubVal_domain; eauto.
    move => u In'.
    eapply InK_domain; eauto.
    eapply narrow_domain; eauto.
  }
  move: Hyp => [s [e1 [HR1 [HIn1 [HSub1 HN1]]]]].
  assert (SubVal s (Pair e₁ e₂) (Pair e1 e2)).
  { constructor; eauto.
    eapply SubVal_domain; eauto.
    move => u In'.
    eapply InK_domain; eauto.
  }
  exists s. exists (Pair e1 e2).
  split; [eapply restrict_transitive; eauto | ].
  repeat (split; auto).
  + constructor; eauto.
    move => Val.
    apply H; auto.
    eapply SubVal_val_val'; eauto.
- discharge_IHs IHnarrow2 s' vs Hyp.
  { move => ? /InExp_subst [HIn | /InExp_subst [HIn | HIn]].
    - eapply narrow_domain; eauto.
    - eapply narrow_domain; eauto.
    - eapply narrow_increases_domain; eauto.
  }
  move: Hyp => [s1 [eb' [HR2 [HIn2 [HSub2 HP2]]]]].
  assert(forall u, InExp u (Pair v₁ v₂) -> In u (domain k')).
  { intros; eapply narrow_domain; eauto. }
  assert (Hyp : exists v2', SubVal s1 v₂ v2').
  {
    eapply InExp_SubVal; eauto.
    move => ? In.
    eapply InK_domain; eauto.
  }    
  move: Hyp => [v2' Sub2].
  assert (Hyp: exists v1', SubVal s1 v₁ v1').
  { 
    eapply InExp_SubVal; eauto.
    move => ? In.
    eapply InK_domain; eauto.
  }
  move: Hyp => [v1' Sub1].
  discharge_IHs IHnarrow1 s1 (Pair v1' v2') Hyp.
  move: Hyp => [s [es' [HR1 [HIn1 [HSub1 HP1]]]]].
  pose proof HSub2.
  eapply SubVal_subst' in HSub2; eauto.
  move: HSub2 => [? Sub'].
  eapply SubVal_subst' in Sub'; eauto.
  move: Sub' => [e'' Sub'].
  exists s. exists (CaseP es' x y e'').
  split; [eapply restrict_transitive | ]; eauto.
  repeat (split; eauto);
  econstructor; eauto.
  + eapply SubVal_domain; eauto.
    move=> ? In.
    eapply InK_domain; eauto.
  + assert (SubVal s1 ([y:=v₂]([x:=v₁]e')) 
                      ([y:=v2']([x:=v1']e'')))
    by repeat (eapply substU_subst; eauto).
    assert (eb' =   [y := v2']([x := v1']e'')).
    { eapply SubVal_restrict_injective' with (s' := s1); 
      eauto. }
    rewrite <- H5; eauto.
- discharge_IHs IHnarrow2 s' vs Hyp; subst.
  { move => ? /InExp_subst [HIn | /InExp_subst [HIn | HIn]].
    - eapply unify_domain; eauto.
    - eapply unify_domain; eauto.
    - eapply unify_domain; eauto.
      right; right.
      erewrite <- (fresh_preserves_domain k₁); eauto.
      erewrite <- (fresh_preserves_domain k'); eauto.
  }      
  move: Hyp => [s1 [eb' [HR2 [HIn2 [HSub2 HP2]]]]].
  (* remember (restrict s1 (domain k')) as s0.*)
  pose proof HIn2.
  eapply unify_spec in HIn2; eauto;
    try solve [repeat constructor].
  move: HIn2 => [In2 Sub].
  assert (InK (restrict s1 (domain k')) k').
  {
    eapply fresh_preserves_InK; eauto.
    eapply fresh_preserves_InK; eauto.
    erewrite (fresh_preserves_domain k' u₁ k₁); eauto.
    erewrite (fresh_preserves_domain k₁ u₂ k₂); eauto.
  }
  
  assert(Tmp : In u (domain k'))
  by (eapply narrow_domain; eauto).
  
  eapply InK_domain in Tmp; eauto.
  move: Tmp => [b Tmp].
  assert (Map: Map.MapsTo u b (restrict s1 (domain k')))
         by auto; clear Tmp.
  
  discharge_IHs IHnarrow1 (restrict s1 (domain k')) 
                (base_to_exp b) Hyp.
  move: Hyp => [s [e'' [HR1 [HIn1 [HSub1 HP1]]]]].

  (* I hate everything *)  
  assert (SU : SubVal s1 (U u) (base_to_exp b))
  by (econstructor; eauto;
      eapply restrict_mapsto_iff; eauto).

  apply Sub in SU.
  inversion SU; subst; eauto.
  pose proof HSub2 as HSub2'.
  eapply SubVal_subst' in HSub2'; eauto.
  move: HSub2' => [? HSub2'].
  eapply SubVal_subst' in HSub2'; eauto.
  move: HSub2' => [es Sub'].
  
  exists s.
  exists (CaseP e'' x y es).
  split; [ | repeat split; auto].
  + eapply restrict_transitive; eauto.
    eapply restrict_transitive 
      with (s'0:= restrict s1 (domain k')); eauto.
    eapply Restrict_restrict; eauto.
  + econstructor; eauto.
    eapply SubVal_domain; eauto.
    * eapply restrict_transitive 
      with (s'0:= restrict s1 (domain k')); eauto.
      eapply Restrict_restrict; eauto.
    * move => ? In.
      eapply InK_domain; eauto.
  + econstructor; eauto.
    * instantiate (1:= e2').
      instantiate (1:= e1').
      rewrite H8.
      eauto.
    * assert (SubVal s1 ([y:=U u₂]([x:=U u₁]e')) 
                      ([y:=e2']([x:=e1']es)))
    by repeat (eapply substU_subst; eauto).
    assert (eb' =   [y := e2']([x := e1']es)).
    { eapply SubVal_restrict_injective' with (s' := s1);
      eauto. }
    rewrite <- H7; eauto.
- inversion HSub'; subst; eauto.
  discharge_IHs IHnarrow s' e' Hyp.
  move: Hyp => [s [es [HR [HIn [HSub HP]]]]].
  exists s; exists (Inl T₁ T₂ es).
  repeat (split; auto).
  + econstructor; eauto.
    notValSolver H; subst; eauto.
    eapply SubVal_val_val'; eauto.
- inversion HSub'; subst; eauto.
  discharge_IHs IHnarrow s' e' Hyp.
  move: Hyp => [s [es [HR [HIn [HSub HP]]]]].
  exists s; exists (Inr T₁ T₂ es).
  repeat (split; auto).
  + econstructor; eauto.
    notValSolver H; subst; eauto.
    eapply SubVal_val_val'; eauto.
- discharge_IHs IHnarrow2 s' vs Hyp.
  { move => ? /InExp_subst [HIn | HIn].
    - eapply narrow_domain; eauto.
    - eapply narrow_increases_domain; eauto.
  }
  move: Hyp => [s1 [e1 [HR2 [HIn2 [HSub2 HP2]]]]].

  assert(forall u, InExp u (Inl T₁ T₂ v₁) -> 
                   In u (domain k₀)).
  { intros; eapply narrow_domain; eauto. }
  assert (Hyp : exists v1', SubVal s1 v₁ v1').
  {
    eapply InExp_SubVal; eauto.
    move => ? In.
    eapply InK_domain; eauto.
  }    
  move: Hyp => [v1' Sub1].
  
  discharge_IHs IHnarrow1 s1 (Inl T₁ T₂ v1') Hyp.
  move: Hyp => [s [es [HR1 [HIn1 [HSub1 HP1]]]]].
  exists s.
  pose proof HSub2.
  eapply SubVal_subst' in HSub2; eauto.
  move: HSub2 => [e1' Sub'].
  assert (TMP: exists e2', SubVal s1 e₂ e2').
  {
    eapply InExp_SubVal; eauto.
    move => ? In.
    eapply InK_domain; eauto.
  } 
  move: TMP => [e2' Sub2'].
  exists (Case es x e1' y e2').
  split; [eapply restrict_transitive; eauto |].
  repeat (split; auto).
  + econstructor; eauto;
    eapply SubVal_domain; eauto; intros;
    eapply InK_domain; eauto.
  + econstructor; eauto.
    assert (SubVal s1 ([x:=v₁]e₁) ([x:=v1']e1'))
      by (eapply substU_subst; eauto).
    assert (Eq : [x:=v1']e1' = e1).
    { eapply SubVal_restrict_injective' with (s' := s1); 
      eauto. }
    rewrite Eq; eauto.
- discharge_IHs IHnarrow2 s' vs Hyp.
  { move => ? /InExp_subst [HIn | HIn].
    - eapply narrow_domain; eauto.
    - eapply narrow_increases_domain; eauto.
  }
  move: Hyp => [s1 [e2 [HR2 [HIn2 [HSub2 HP2]]]]].

  assert(forall u, InExp u (Inr T₁ T₂ v₂) -> 
                   In u (domain k₀)).
  { intros; eapply narrow_domain; eauto. }
  assert (Hyp : exists v2', SubVal s1 v₂ v2').
  {
    eapply InExp_SubVal; eauto.
    move => ? In.
    eapply InK_domain; eauto.
  }    
  move: Hyp => [v2' Sub2].
  
  discharge_IHs IHnarrow1 s1 (Inr T₁ T₂ v2') Hyp.
  move: Hyp => [s [es [HR1 [HIn1 [HSub1 HP1]]]]].
  exists s.
  pose proof HSub2.
  eapply SubVal_subst' in HSub2; eauto.
  move: HSub2 => [e2' Sub'].
  assert (TMP: exists e1', SubVal s1 e₁ e1').
  {
    eapply InExp_SubVal; eauto.
    move => ? In.
    eapply InK_domain; eauto.
  } 
  move: TMP => [e1' Sub1'].
  exists (Case es x e1' y e2').
  split; [eapply restrict_transitive; eauto |].
  repeat (split; auto).
  + econstructor; eauto;
    eapply SubVal_domain; eauto; intros;
    eapply InK_domain; eauto.
  + eapply SCaseInr; eauto.
    assert (SubVal s1 ([y:=v₂]e₂) ([y:=v2']e2'))
      by (eapply substU_subst; eauto).
    assert (Eq : [y:=v2']e2' = e2).
    { eapply SubVal_restrict_injective' with (s' := s1); 
      eauto. }
    rewrite Eq; eauto.
- discharge_IHs IHnarrow2 s' vs Hyp; subst.
  { move => ? /InExp_subst [HIn | HIn].
    - eapply unify_domain; eauto.
    - eapply unify_domain; eauto.
      right; right.
      erewrite <- (fresh_preserves_domain k₁); eauto.
      erewrite <- (fresh_preserves_domain k₀); eauto.
  }
  move: Hyp => [s1 [e1 [HR2 [HIn2 [HSub2 HP2]]]]].

  pose proof HIn2.
  eapply unify_spec in HIn2; eauto;
    try solve [repeat constructor].
  move: HIn2 => [In2 Sub].
  assert (InK (restrict s1 (domain k₀)) k₀).
  {
    eapply fresh_preserves_InK; eauto.
    eapply fresh_preserves_InK; eauto.
    erewrite (fresh_preserves_domain k₀ u₁ k₁); eauto.
    erewrite (fresh_preserves_domain k₁ u₂ k'); eauto.
  }

  assert(Tmp : In u (domain k₀))
  by (eapply narrow_domain; eauto).
  
  eapply InK_domain in Tmp; eauto.
  move: Tmp => [b Tmp].
  assert (Map: Map.MapsTo u b (restrict s1 (domain k₀)))
         by auto; clear Tmp.
    
  discharge_IHs IHnarrow1 (restrict s1 (domain k₀)) 
                (base_to_exp b) Hyp.
  move: Hyp => [s [e'' [HR1 [HIn1 [HSub1 HP1]]]]].

  assert (SU : SubVal s1 (U u) (base_to_exp b))
  by (econstructor; eauto;
      eapply restrict_mapsto_iff; eauto).

  apply Sub in SU.
  inversion SU; subst; eauto.
  pose proof HSub2 as HSub2'.
  eapply SubVal_subst' in HSub2'; eauto.
  move: HSub2' => [e1' HSub1'].
  
  assert (TMP: exists e2', SubVal s1 e₂ e2').
  {
    eapply InExp_SubVal; eauto.
    move => ? In.
    eapply InK_domain; eauto.
    eapply unify_domain; eauto.
    right; right.
    erewrite <- (fresh_preserves_domain k₁ u₂ k'); eauto.
    erewrite <- (fresh_preserves_domain k₀ u₁ k₁); eauto.
  } 
  move: TMP => [e2' HSub2'].
  
  assert (s1 ↘ s ≡ s).
  {
    eapply restrict_transitive 
      with (s'0:= restrict s1 (domain k₀)); eauto.
    eapply Restrict_restrict; eauto.
  }


  exists s.
  exists (Case e'' x e1' y e2').
  split; [ | repeat split; auto].
  + eapply restrict_transitive; eauto.
  + econstructor; eauto.
    eapply SubVal_domain; eauto.
    * move => ? In.
      eapply InK_domain; eauto.
    * eapply SubVal_domain; eauto.
      move => ? In.
      eapply InK_domain; eauto.
  + econstructor; eauto.
    * instantiate (1 := e').
      instantiate (1 := T₂). 
      instantiate (1 := T₁).
      rewrite H12; eauto.
    * assert (SubVal s1 ([x:=U u₁]e₁) ([x:=e']e1')).
        by repeat (eapply substU_subst; eauto).
      assert (EQ: e1 = [x := e']e1').
      { eapply SubVal_restrict_injective' with (s' := s1);
      eauto. }
      rewrite <- EQ; eauto.
- discharge_IHs IHnarrow2 s' vs Hyp; subst.
  { move => ? /InExp_subst [HIn | HIn].
    - eapply unify_domain; eauto.
    - eapply unify_domain; eauto.
      right; right.
      erewrite <- (fresh_preserves_domain k₁); eauto.
      erewrite <- (fresh_preserves_domain k₀); eauto.
  }
  move: Hyp => [s1 [e2 [HR2 [HIn2 [HSub2 HP2]]]]].

  pose proof HIn2.
  eapply unify_spec in HIn2; eauto;
    try solve [repeat constructor].
  move: HIn2 => [In2 Sub].
  assert (InK (restrict s1 (domain k₀)) k₀).
  {
    eapply fresh_preserves_InK; eauto.
    eapply fresh_preserves_InK; eauto.
    erewrite (fresh_preserves_domain k₀ u₁ k₁); eauto.
    erewrite (fresh_preserves_domain k₁ u₂ k'); eauto.
  }

  assert(Tmp : In u (domain k₀))
  by (eapply narrow_domain; eauto).
  
  eapply InK_domain in Tmp; eauto.
  move: Tmp => [b Tmp].
  assert (Map: Map.MapsTo u b (restrict s1 (domain k₀)))
         by auto; clear Tmp.
    
  discharge_IHs IHnarrow1 (restrict s1 (domain k₀)) 
                (base_to_exp b) Hyp.
  move: Hyp => [s [e'' [HR1 [HIn1 [HSub1 HP1]]]]].

  assert (SU : SubVal s1 (U u) (base_to_exp b))
  by (econstructor; eauto;
      eapply restrict_mapsto_iff; eauto).

  apply Sub in SU.
  inversion SU; subst; eauto.
  pose proof HSub2 as HSub2'.
  eapply SubVal_subst' in HSub2'; eauto.
  move: HSub2' => [e2' HSub2'].
  
  assert (TMP: exists e1', SubVal s1 e₁ e1').
  {
    eapply InExp_SubVal; eauto.
    move => ? In.
    eapply InK_domain; eauto.
    eapply unify_domain; eauto.
    right; right.
    erewrite <- (fresh_preserves_domain k₁ u₂ k'); eauto.
    erewrite <- (fresh_preserves_domain k₀ u₁ k₁); eauto.
  } 
  move: TMP => [e1' HSub1'].
  
  assert (s1 ↘ s ≡ s).
  {
    eapply restrict_transitive 
      with (s'0:= restrict s1 (domain k₀)); eauto.
    eapply Restrict_restrict; eauto.
  }

  exists s.
  exists (Case e'' x e1' y e2').
  split; [ | repeat split; auto].
  + eapply restrict_transitive; eauto.
  + econstructor; eauto.
    eapply SubVal_domain; eauto.
    * move => ? In.
      eapply InK_domain; eauto.
    * eapply SubVal_domain; eauto.
      move => ? In.
      eapply InK_domain; eauto.
  + eapply SCaseInr; eauto.
    * instantiate (1 := e').
      instantiate (1 := T₂). 
      instantiate (1 := T₁).
      rewrite H12; eauto.
    * assert (SubVal s1 ([y:=U u₂]e₂) ([y:=e']e2')).
        by repeat (eapply substU_subst; eauto).
      assert (EQ: e2 = [y := e']e2').
      { eapply SubVal_restrict_injective' with (s' := s1);
      eauto. }
      rewrite <- EQ; eauto.
- discharge_IHs IHnarrow2 s' vs Hyp; subst.
  { move => ? /InExp_subst [HIn | HIn].
    - eapply unify_domain; eauto.
    - eapply unify_domain; eauto.
      right; right.
      erewrite <- (fresh_preserves_domain k₁); eauto.
      erewrite <- (fresh_preserves_domain k₀); eauto.
  }
  move: Hyp => [s1 [e1 [HR2 [HIn2 [HSub2 HP2]]]]].

  pose proof HIn2.
  eapply unify_spec in HIn2; eauto;
    try solve [repeat constructor].
  move: HIn2 => [In2 Sub].
  assert (InK (restrict s1 (domain k₀)) k₀).
  {
    eapply fresh_preserves_InK; eauto.
    eapply fresh_preserves_InK; eauto.
    erewrite (fresh_preserves_domain k₀ u₁ k₁); eauto.
    erewrite (fresh_preserves_domain k₁ u₂ k'); eauto.
  }

  assert(Tmp : In u (domain k₀))
  by (eapply narrow_domain; eauto).
  
  eapply InK_domain in Tmp; eauto.
  move: Tmp => [b Tmp].
  assert (Map: Map.MapsTo u b (restrict s1 (domain k₀)))
         by auto; clear Tmp.
    
  discharge_IHs IHnarrow1 (restrict s1 (domain k₀)) 
                (base_to_exp b) Hyp.
  move: Hyp => [s [e'' [HR1 [HIn1 [HSub1 HP1]]]]].

  assert (SU : SubVal s1 (U u) (base_to_exp b))
  by (econstructor; eauto;
      eapply restrict_mapsto_iff; eauto).

  apply Sub in SU.
  inversion SU; subst; eauto.
  pose proof HSub2 as HSub2'.
  eapply SubVal_subst' in HSub2'; eauto.
  move: HSub2' => [e1' HSub1'].
  
  assert (TMP: exists e2', SubVal s1 e₂ e2').
  {
    eapply InExp_SubVal; eauto.
    move => ? In.
    eapply InK_domain; eauto.
    eapply unify_domain; eauto.
    right; right.
    erewrite <- (fresh_preserves_domain k₁ u₂ k'); eauto.
    erewrite <- (fresh_preserves_domain k₀ u₁ k₁); eauto.
  } 
  move: TMP => [e2' HSub2'].
  
  assert (s1 ↘ s ≡ s).
  {
    eapply restrict_transitive 
      with (s'0:= restrict s1 (domain k₀)); eauto.
    eapply Restrict_restrict; eauto.
  }


  exists s.
  exists (Case e'' x e1' y e2').
  split; [ | repeat split; auto].
  + eapply restrict_transitive; eauto.
  + econstructor; eauto.
    eapply SubVal_domain; eauto.
    * move => ? In.
      eapply InK_domain; eauto.
    * eapply SubVal_domain; eauto.
      move => ? In.
      eapply InK_domain; eauto.
  + econstructor; eauto.
    * instantiate (1 := e').
      instantiate (1 := T₂). 
      instantiate (1 := T₁).
      rewrite H12; eauto.
    * assert (SubVal s1 ([x:=U u₁]e₁) ([x:=e']e1')).
        by repeat (eapply substU_subst; eauto).
      assert (EQ: e1 = [x := e']e1').
      { eapply SubVal_restrict_injective' with (s' := s1);
      eauto. }
      rewrite <- EQ; eauto.
- discharge_IHs IHnarrow2 s' vs Hyp; subst.
  { move => ? /InExp_subst [HIn | HIn].
    - eapply unify_domain; eauto.
    - eapply unify_domain; eauto.
      right; right.
      erewrite <- (fresh_preserves_domain k₁); eauto.
      erewrite <- (fresh_preserves_domain k₀); eauto.
  }
  move: Hyp => [s1 [e2 [HR2 [HIn2 [HSub2 HP2]]]]].

  pose proof HIn2.
  eapply unify_spec in HIn2; eauto;
    try solve [repeat constructor].
  move: HIn2 => [In2 Sub].
  assert (InK (restrict s1 (domain k₀)) k₀).
  {
    eapply fresh_preserves_InK; eauto.
    eapply fresh_preserves_InK; eauto.
    erewrite (fresh_preserves_domain k₀ u₁ k₁); eauto.
    erewrite (fresh_preserves_domain k₁ u₂ k'); eauto.
  }

  assert(Tmp : In u (domain k₀))
  by (eapply narrow_domain; eauto).
  
  eapply InK_domain in Tmp; eauto.
  move: Tmp => [b Tmp].
  assert (Map: Map.MapsTo u b (restrict s1 (domain k₀)))
         by auto; clear Tmp.
    
  discharge_IHs IHnarrow1 (restrict s1 (domain k₀)) 
                (base_to_exp b) Hyp.
  move: Hyp => [s [e'' [HR1 [HIn1 [HSub1 HP1]]]]].

  assert (SU : SubVal s1 (U u) (base_to_exp b))
  by (econstructor; eauto;
      eapply restrict_mapsto_iff; eauto).

  apply Sub in SU.
  inversion SU; subst; eauto.
  pose proof HSub2 as HSub2'.
  eapply SubVal_subst' in HSub2'; eauto.
  move: HSub2' => [e2' HSub2'].
  
  assert (TMP: exists e1', SubVal s1 e₁ e1').
  {
    eapply InExp_SubVal; eauto.
    move => ? In.
    eapply InK_domain; eauto.
    eapply unify_domain; eauto.
    right; right.
    erewrite <- (fresh_preserves_domain k₁ u₂ k'); eauto.
    erewrite <- (fresh_preserves_domain k₀ u₁ k₁); eauto.
  } 
  move: TMP => [e1' HSub1'].
  
  assert (s1 ↘ s ≡ s).
  {
    eapply restrict_transitive 
      with (s'0:= restrict s1 (domain k₀)); eauto.
    eapply Restrict_restrict; eauto.
  }

  exists s.
  exists (Case e'' x e1' y e2').
  split; [ | repeat split; auto].
  + eapply restrict_transitive; eauto.
  + econstructor; eauto.
    eapply SubVal_domain; eauto.
    * move => ? In.
      eapply InK_domain; eauto.
    * eapply SubVal_domain; eauto.
      move => ? In.
      eapply InK_domain; eauto.
  + eapply SCaseInr; eauto.
    * instantiate (1 := e').
      instantiate (1 := T₂). 
      instantiate (1 := T₁).
      rewrite H12; eauto.
    * assert (SubVal s1 ([y:=U u₂]e₂) ([y:=e']e2')).
        by repeat (eapply substU_subst; eauto).
      assert (EQ: e2 = [y := e']e2').
      { eapply SubVal_restrict_injective' with (s' := s1);
      eauto. }
      rewrite <- EQ; eauto.
- discharge_IHs IHnarrow3 s' vs Hyp.
  { move => ? /InExp_subst [HIn | /InExp_subst [HIn | HIn]].
    - eapply narrow_increases_domain; eauto. 
      eapply narrow_domain; eauto.
    - eapply narrow_domain; eauto. 
    - eapply narrow_increases_domain; eauto.
      eapply narrow_domain; eauto.
  }
  move: Hyp => [s2 [eb' [HR2 [HIn2 [HSub2 HP2]]]]].

  assert(forall u, InExp u (Rec f x T T' e') -> 
                   In u (domain k'')).
  { intros. 
    eapply narrow_increases_domain; eauto.
    eapply narrow_domain; eauto. 
  }
  assert (Hyp : exists v', SubVal s2 v₂ v').
  {
    eapply InExp_SubVal; eauto.
    move => ? In.
    eapply InK_domain; eauto.
    eapply narrow_domain; eauto.
  }
  move: Hyp => [v2 Sub2].
  discharge_IHs IHnarrow2 s2 v2 Hyp.
  move: Hyp => [s1 [es' [HR1 [HIn1 [HSub1 HP1]]]]].

  assert (Hyp : exists v', SubVal s1 (Rec f x T T' e') v').
  {
    eapply InExp_SubVal; eauto.
    move => ? In.
    eapply InK_domain; eauto.
    eapply narrow_domain; eauto.
  }    
  move: Hyp => [v' Sub'].

  discharge_IHs IHnarrow1 s1 v' Hyp.
  move: Hyp => [s0 [e1 [HR0 [HIn0 [HSub0 HP0]]]]].

  inversion Sub'; subst; eauto.

  exists s0. 
  exists (App e1 es').
  split; [repeat (eapply restrict_transitive; eauto) | ]; eauto.
  repeat (split; eauto);
  econstructor; eauto.
  + eapply SubVal_domain; eauto.
    move=> ? In.
    eapply InK_domain; eauto.
  + pose proof HSub2 as HSub2'.
    eapply SubVal_subst_strong in HSub2'; eauto;
    [ | eapply substU_restrict; eauto].
    move: HSub2' => [? [HSub2' Eq1]].
    eapply SubVal_subst_strong in HSub2'; eauto.
    move: HSub2' => [e'' [HSub2' Eq2]].
    rewrite Eq2 in Eq1.
    subst; eauto.
    assert (e'' = e'0).
    {
      eapply SubVal_restrict_injective' with (s' := s2); eauto.
    }
    subst; auto.
- subst. pose proof HIn' as HU.
  eapply unify_spec in HU; eauto.
  move: HU => [InR Sub].
  assert (In' : InK (restrict s' (domain k₃')) k₃').
  { subst.
    erewrite (fresh_preserves_domain k₃'); eauto.
    erewrite (fresh_preserves_domain k₄); eauto.
    eapply (fresh_preserves_InK k₃'); eauto.
    eapply (fresh_preserves_InK k₄); eauto.
  }

  move: H5 => [v1' [S1 Nat1]].
  move: H7 => [v2' [S2 Nat2]].

  eapply SubVal_singleton' in S1; eauto.
  eapply SubVal_singleton' in S2; eauto.

  discharge_IHs IHnarrow3 (restrict s' (domain k₃')) v2' Hyp.
  { eapply sample_spec_2'; eauto. }
  { move => ? HIn.
    erewrite <- (sample_domain' _ k₂); eauto. }
  move: Hyp => [s2 [e2' [HR2 [HIn2 [Sub2 P2]]]]].
  
  discharge_IHs IHnarrow2 (restrict s2 (domain k₂)) v1' Hyp.
  { eapply sample_spec_2'; eauto.
    erewrite (sample_domain' _ k₂); eauto.
    eapply InK_equiv; eauto.
    eapply Equiv_transitive with (s2 ↘ s2); eauto.
    eapply restrict_domain_InK; eauto.
  } 
  { eapply SubVal_domain; eauto.
    + eapply restrict_transitive; eauto.
      eapply Restrict_restrict; eauto.
    + move => ? In''.
      eapply InK_domain; eauto.
      eapply narrow_domain; eauto.
  }
  move: Hyp => [s1 [e1' [HR1 [HIn1 [Sub1 P1]]]]].

  assert (R : s' ↘ restrict s1 (domain k₁) ≡ 
                 restrict s1 (domain k₁)).
  {
    eapply restrict_transitive with (s'0 := s2) ; eauto.
      * eapply restrict_transitive 
        with (s'0 := restrict s' (domain k₃')); eauto.
        eapply Restrict_restrict; eauto.
      * eapply restrict_transitive 
        with (s'0:=restrict s2 (domain k₂)); eauto.
        eapply Restrict_restrict; eauto.
        eapply restrict_transitive; eauto.
        eapply Restrict_restrict; eauto.
  }
  
  discharge_IHs IHnarrow1 (restrict s1 (domain k₁)) vs Hyp.
  { eapply InK_equiv; eauto.
    eapply Equiv_transitive with (s1 ↘ s1); eauto.
    eapply restrict_domain_InK; eauto.
  }
  { eapply SubVal_domain; eauto.
    move => ? In''.
    eapply InK_domain; eauto.
    eapply narrow_domain; eauto.
  }
  move: Hyp => [s [es [HR [HIn [Sub' P]]]]].
  
  exists s.
  exists (Inst es e1' e2').
  split; [eapply restrict_transitive; eauto |].
  repeat (split; auto).
  + econstructor; eauto.
    { eapply SubVal_domain; eauto.
      - eapply restrict_transitive 
          with (restrict s1 (domain k₁)); eauto.
        eapply Restrict_restrict; eauto.
      - move => ? HI.
        eapply InK_domain; eauto.
    } 
    { eapply SubVal_domain; eauto.
      - eapply restrict_transitive 
          with (restrict s2 (domain k₂)); eauto.
        + eapply Restrict_restrict; eauto.
        + eapply restrict_transitive; eauto.
          eapply restrict_transitive 
            with (restrict s1 (domain k₁)); eauto.
          eapply Restrict_restrict; eauto.
      - move => ? HI.
        eapply InK_domain; eauto.
    } 
  + econstructor; eauto.
  + eapply narrow_is_value; eauto.
  + repeat (econstructor).
- subst. pose proof HIn' as HU.
  eapply unify_spec in HU; eauto.
  move: HU => [InR Sub].
  assert (In' : InK (restrict s' (domain k₃')) k₃').
  { subst.
    erewrite (fresh_preserves_domain k₃'); eauto.
    erewrite (fresh_preserves_domain k₄); eauto.
    eapply (fresh_preserves_InK k₃'); eauto.
    eapply (fresh_preserves_InK k₄); eauto.
  }

  move: H5 => [v1' [S1 Nat1]].
  move: H7 => [v2' [S2 Nat2]].

  eapply SubVal_singleton' in S1; eauto.
  eapply SubVal_singleton' in S2; eauto.

  discharge_IHs IHnarrow3 (restrict s' (domain k₃')) v2' Hyp.
  { eapply sample_spec_2'; eauto. }
  { move => ? HIn.
    erewrite <- (sample_domain' _ k₂); eauto. }
  move: Hyp => [s2 [e2' [HR2 [HIn2 [Sub2 P2]]]]].
  
  discharge_IHs IHnarrow2 (restrict s2 (domain k₂)) v1' Hyp.
  { eapply sample_spec_2'; eauto.
    erewrite (sample_domain' _ k₂); eauto.
    eapply InK_equiv; eauto.
    eapply Equiv_transitive with (s2 ↘ s2); eauto.
    eapply restrict_domain_InK; eauto.
  } 
  { eapply SubVal_domain; eauto.
    + eapply restrict_transitive; eauto.
      eapply Restrict_restrict; eauto.
    + move => ? In''.
      eapply InK_domain; eauto.
      eapply narrow_domain; eauto.
  }
  move: Hyp => [s1 [e1' [HR1 [HIn1 [Sub1 P1]]]]].

  assert (R : s' ↘ restrict s1 (domain k₁) ≡ 
                 restrict s1 (domain k₁)).
  {
    eapply restrict_transitive with (s'0 := s2) ; eauto.
      * eapply restrict_transitive 
        with (s'0 := restrict s' (domain k₃')); eauto.
        eapply Restrict_restrict; eauto.
      * eapply restrict_transitive 
        with (s'0:=restrict s2 (domain k₂)); eauto.
        eapply Restrict_restrict; eauto.
        eapply restrict_transitive; eauto.
        eapply Restrict_restrict; eauto.
  }
  
  discharge_IHs IHnarrow1 (restrict s1 (domain k₁)) vs Hyp.
  { eapply InK_equiv; eauto.
    eapply Equiv_transitive with (s1 ↘ s1); eauto.
    eapply restrict_domain_InK; eauto.
  }
  { eapply SubVal_domain; eauto.
    move => ? In''.
    eapply InK_domain; eauto.
    eapply narrow_domain; eauto.
  }
  move: Hyp => [s [es [HR [HIn [Sub' P]]]]].
  
  exists s.
  exists (Inst es e1' e2').
  split; [eapply restrict_transitive; eauto |].
  repeat (split; auto).
  + econstructor; eauto.
    { eapply SubVal_domain; eauto.
      - eapply restrict_transitive 
          with (restrict s1 (domain k₁)); eauto.
        eapply Restrict_restrict; eauto.
      - move => ? HI.
        eapply InK_domain; eauto.
    } 
    { eapply SubVal_domain; eauto.
      - eapply restrict_transitive 
          with (restrict s2 (domain k₂)); eauto.
        + eapply Restrict_restrict; eauto.
        + eapply restrict_transitive; eauto.
          eapply restrict_transitive 
            with (restrict s1 (domain k₁)); eauto.
          eapply Restrict_restrict; eauto.
      - move => ? HI.
        eapply InK_domain; eauto.
    } 
  + econstructor; eauto.
  + eapply narrow_is_value; eauto.
  + repeat (econstructor).
- subst. pose proof HIn' as HU.
  eapply unify_spec in HU; eauto.
  move: HU => [InR Sub].
  assert (In' : InK (restrict s' (domain k₃')) k₃').
  { subst.
    erewrite (fresh_preserves_domain k₃'); eauto.
    erewrite (fresh_preserves_domain k₄); eauto.
    eapply (fresh_preserves_InK k₃'); eauto.
    eapply (fresh_preserves_InK k₄); eauto.
  }

  move: H5 => [v1' [S1 Nat1]].
  move: H7 => [v2' [S2 Nat2]].

  eapply SubVal_singleton' in S1; eauto.
  eapply SubVal_singleton' in S2; eauto.

  discharge_IHs IHnarrow3 (restrict s' (domain k₃')) v2' Hyp.
  { eapply sample_spec_2'; eauto. }
  { move => ? HIn.
    erewrite <- (sample_domain' _ k₂); eauto. }
  move: Hyp => [s2 [e2' [HR2 [HIn2 [Sub2 P2]]]]].
  
  discharge_IHs IHnarrow2 (restrict s2 (domain k₂)) v1' Hyp.
  { eapply sample_spec_2'; eauto.
    erewrite (sample_domain' _ k₂); eauto.
    eapply InK_equiv; eauto.
    eapply Equiv_transitive with (s2 ↘ s2); eauto.
    eapply restrict_domain_InK; eauto.
  } 
  { eapply SubVal_domain; eauto.
    + eapply restrict_transitive; eauto.
      eapply Restrict_restrict; eauto.
    + move => ? In''.
      eapply InK_domain; eauto.
      eapply narrow_domain; eauto.
  }
  move: Hyp => [s1 [e1' [HR1 [HIn1 [Sub1 P1]]]]].

  assert (R : s' ↘ restrict s1 (domain k₁) ≡ 
                 restrict s1 (domain k₁)).
  {
    eapply restrict_transitive with (s'0 := s2) ; eauto.
      * eapply restrict_transitive 
        with (s'0 := restrict s' (domain k₃')); eauto.
        eapply Restrict_restrict; eauto.
      * eapply restrict_transitive 
        with (s'0:=restrict s2 (domain k₂)); eauto.
        eapply Restrict_restrict; eauto.
        eapply restrict_transitive; eauto.
        eapply Restrict_restrict; eauto.
  }
  
  discharge_IHs IHnarrow1 (restrict s1 (domain k₁)) vs Hyp.
  { eapply InK_equiv; eauto.
    eapply Equiv_transitive with (s1 ↘ s1); eauto.
    eapply restrict_domain_InK; eauto.
  }
  { eapply SubVal_domain; eauto.
    move => ? In''.
    eapply InK_domain; eauto.
    eapply narrow_domain; eauto.
  }
  move: Hyp => [s [es [HR [HIn [Sub' P]]]]].
  
  exists s.
  exists (Inst es e1' e2').
  split; [eapply restrict_transitive; eauto |].
  repeat (split; auto).
  + econstructor; eauto.
    { eapply SubVal_domain; eauto.
      - eapply restrict_transitive 
          with (restrict s1 (domain k₁)); eauto.
        eapply Restrict_restrict; eauto.
      - move => ? HI.
        eapply InK_domain; eauto.
    } 
    { eapply SubVal_domain; eauto.
      - eapply restrict_transitive 
          with (restrict s2 (domain k₂)); eauto.
        + eapply Restrict_restrict; eauto.
        + eapply restrict_transitive; eauto.
          eapply restrict_transitive 
            with (restrict s1 (domain k₁)); eauto.
          eapply Restrict_restrict; eauto.
      - move => ? HI.
        eapply InK_domain; eauto.
    } 
  + econstructor; eauto.
  + eapply narrow_is_value; eauto.
  + repeat (econstructor).
- subst. pose proof HIn' as HU.
  eapply unify_spec in HU; eauto.
  move: HU => [InR Sub].
  assert (In' : InK (restrict s' (domain k₃')) k₃').
  { subst.
    erewrite (fresh_preserves_domain k₃'); eauto.
    erewrite (fresh_preserves_domain k₄); eauto.
    eapply (fresh_preserves_InK k₃'); eauto.
    eapply (fresh_preserves_InK k₄); eauto.
  }

  move: H5 => [v1' [S1 Nat1]].
  move: H7 => [v2' [S2 Nat2]].

  eapply SubVal_singleton' in S1; eauto.
  eapply SubVal_singleton' in S2; eauto.

  discharge_IHs IHnarrow3 (restrict s' (domain k₃')) v2' Hyp.
  { eapply sample_spec_2'; eauto. }
  { move => ? HIn.
    erewrite <- (sample_domain' _ k₂); eauto. }
  move: Hyp => [s2 [e2' [HR2 [HIn2 [Sub2 P2]]]]].
  
  discharge_IHs IHnarrow2 (restrict s2 (domain k₂)) v1' Hyp.
  { eapply sample_spec_2'; eauto.
    erewrite (sample_domain' _ k₂); eauto.
    eapply InK_equiv; eauto.
    eapply Equiv_transitive with (s2 ↘ s2); eauto.
    eapply restrict_domain_InK; eauto.
  } 
  { eapply SubVal_domain; eauto.
    + eapply restrict_transitive; eauto.
      eapply Restrict_restrict; eauto.
    + move => ? In''.
      eapply InK_domain; eauto.
      eapply narrow_domain; eauto.
  }
  move: Hyp => [s1 [e1' [HR1 [HIn1 [Sub1 P1]]]]].

  assert (R : s' ↘ restrict s1 (domain k₁) ≡ 
                 restrict s1 (domain k₁)).
  {
    eapply restrict_transitive with (s'0 := s2) ; eauto.
      * eapply restrict_transitive 
        with (s'0 := restrict s' (domain k₃')); eauto.
        eapply Restrict_restrict; eauto.
      * eapply restrict_transitive 
        with (s'0:=restrict s2 (domain k₂)); eauto.
        eapply Restrict_restrict; eauto.
        eapply restrict_transitive; eauto.
        eapply Restrict_restrict; eauto.
  }
  
  discharge_IHs IHnarrow1 (restrict s1 (domain k₁)) vs Hyp.
  { eapply InK_equiv; eauto.
    eapply Equiv_transitive with (s1 ↘ s1); eauto.
    eapply restrict_domain_InK; eauto.
  }
  { eapply SubVal_domain; eauto.
    move => ? In''.
    eapply InK_domain; eauto.
    eapply narrow_domain; eauto.
  }
  move: Hyp => [s [es [HR [HIn [Sub' P]]]]].
  
  exists s.
  exists (Inst es e1' e2').
  split; [eapply restrict_transitive; eauto |].
  repeat (split; auto).
  + econstructor; eauto.
    { eapply SubVal_domain; eauto.
      - eapply restrict_transitive 
          with (restrict s1 (domain k₁)); eauto.
        eapply Restrict_restrict; eauto.
      - move => ? HI.
        eapply InK_domain; eauto.
    } 
    { eapply SubVal_domain; eauto.
      - eapply restrict_transitive 
          with (restrict s2 (domain k₂)); eauto.
        + eapply Restrict_restrict; eauto.
        + eapply restrict_transitive; eauto.
          eapply restrict_transitive 
            with (restrict s1 (domain k₁)); eauto.
          eapply Restrict_restrict; eauto.
      - move => ? HI.
        eapply InK_domain; eauto.
    } 
  + econstructor; eauto.
  + eapply narrow_is_value; eauto.
  + repeat (econstructor).
- discharge_IHs IHnarrow s' vs Hyp.
  { eapply sample_spec_2'; eauto. }
  move: Hyp => [s [es [HR [HIn [HSub HP]]]]].
  exists s.
  exists (Bang es).
  repeat (split; auto).
  econstructor; eauto.
- inversion HSub'; subst; eauto.
  discharge_IHs IHnarrow s' e'  Hyp.
  move: Hyp => [s [es [HR [HIn [HSub HP]]]]].
  exists s. exists (Fold T es).
  repeat (split; auto).
  econstructor; eauto.
  move => Val.
  inversion Val; subst;
  eapply H; eauto.
  eapply SubVal_val_val'; eauto.
- discharge_IHs IHnarrow s' (Fold T vs) Hyp.
  move: Hyp => [s [es [HR [HIn [HSub HP]]]]].
  exists s.
  exists (Unfold T es).
  repeat (split; auto).
  econstructor; eauto.
- pose proof HIn'.
  subst.
  eapply unify_spec in HIn'; eauto;
    try solve [repeat constructor].
  move: HIn' => [In' Sub'].
  assert (InK (restrict s' (domain k₁)) k₁).
  { 
    eapply fresh_preserves_InK; eauto.
    erewrite (fresh_preserves_domain k₁ u' k₂); eauto.
  }
  
  assert(Tmp : In u (domain k₁))
  by (eapply narrow_domain; eauto).
  
  eapply InK_domain in Tmp; eauto.
  move: Tmp => [b Tmp].
  assert (Map: Map.MapsTo u b (restrict s' (domain k₁)))
         by auto; clear Tmp.
  
  discharge_IHs IHnarrow (restrict s' (domain k₁)) 
                (base_to_exp b) Hyp.
  move: Hyp => [s [e'' [HR1 [HIn1 [HSub1 HP1]]]]].

  (* I hate everything *)  
  assert (SU : SubVal s' (U u) (base_to_exp b))
  by (econstructor; eauto;
      eapply restrict_mapsto_iff; eauto).

  apply Sub' in SU.
  inversion SU; subst; eauto.

  exists s.
  exists (Unfold (TMu T) e'').
  split; [ | repeat split; auto].
  + eapply restrict_transitive; eauto.
    eapply restrict_transitive 
      with (s'0:= restrict s' (domain k₁)); eauto.
    eapply Restrict_restrict; eauto.
  + econstructor; eauto.
    rewrite <- H6 in HP1.
    inversion H4; subst; eauto.
    inversion HSub'; subst; eauto.
    assert (b0 = b1)
    by (eapply MapProp.F.MapsTo_fun; eauto).
    subst; eauto.
- assert (TMP: exists v2, SubVal s' v₂ v2).
  {
    eapply InExp_SubVal; eauto.
    move => ? In.
    eapply InK_domain; eauto.
    eapply narrow_domain; eauto.
  }
  move: TMP => [v2 HV2].
  discharge_IHs IHnarrow2 s' v2 Hyp.
  move: Hyp => [s [e2 [HR [HIn [HSub HP]]]]].
  discharge_IHs IHnarrow1 s vs Hyp.
  {
    eapply SubVal_domain; eauto.
    move => u InU.
    eapply InK_domain; eauto.
    eapply narrow_domain; eauto.
  }
  move: Hyp => [s0 [e0 [HR0 [HIn0 [HSub0 HP0]]]]].
  exists s0; exists (Til e0 T e2).
  split; [repeat (eapply restrict_transitive; eauto) |].
  repeat (split; auto).
  + econstructor; eauto.
    eapply SubVal_domain; eauto.
    move => u InU.
    eapply InK_domain; eauto.
  + econstructor; eauto.
Qed.    
