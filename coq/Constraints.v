Require Import List. Import ListNotations.
Require Import ListSet.

Require Import Util.
Require Import Types.
Require Import Valuation.
Require Import Probability.

Set Bullet Behavior "Strict Subproofs". 

Module Type CSET.
  Parameter cset : Type.
  Parameter empty : cset.

  Parameter uts : cset -> Map.t type.
  Parameter domain : cset -> set unknown.

  Parameter domain_is_used : 
    forall u k, In u (domain k) -> 
                Map.In u (uts k).

  Parameter denotation : cset -> ValSet.t.

  Definition InK s k : Prop :=
    ValSet.In s (denotation k). 

  Parameter InK_domain : 
    forall s k, InK s k ->
    forall u, Map.In u s <-> In u (domain k).  

  Definition well_typed_cset k : Prop :=
    forall s, InK s k -> 
      well_typed_valuation (uts k) s.

  Parameter fresh : 
    cset -> type -> (unknown * cset).

  Parameter fresh_increases_types : 
    forall k u k' t , 
      (u, k') = fresh k t ->
      uts k' = Map.add u t (uts k).

  Parameter fresh_is_fresh_type : 
    forall k u k' t , 
      (u, k') = fresh k t ->
      ~ (Map.In u (uts k)).      

  Parameter fresh_preserves_denotation :
    forall k u k' t,
      (u, k') = fresh k t ->
      denotation k = denotation k'.

  Parameter fresh_preserves_domain : 
    forall k u k' t , 
      (u, k') = fresh k t ->
      domain k = domain k'.

  Parameter unify_in : cset -> exp -> exp -> cset.

  Parameter unify_preserves_types : 
    forall k v1 v2,
      uts (unify_in k v1 v2) = uts k.

  Parameter unify_domain :
    forall k v1 v2, 
    forall u, In u (domain (unify_in k v1 v2)) <->
              InExp u v1 \/ InExp u v2 \/ In u (domain k).
  (* Type information for v1 v2 means k' not (necessarily) unsat *)
  Parameter unify_preserves_well_typed :
    forall k v1 v2 k', 
      k' = unify_in k v1 v2 ->
      well_typed_cset k ->
      well_typed_cset k'.

  Parameter unify_spec : 
    forall k v1 v2 s, 
      is_value v1 -> is_value v2 ->
      ((InK (restrict s (domain k)) k /\
      (forall v, SubVal s v1 v <-> SubVal s v2 v)) <->
      InK s (unify_in k v1 v2)).

  Parameter disj : cset -> cset -> cset -> cset.
  
  Definition sat (k : cset) : Prop :=
    exists s, ValSet.In s (denotation k).
  
  Parameter sat_dec : forall (k : cset), {sat k} + {~ (sat k)}.

  Definition singleton k u b : Prop := 
    forall s, 
      InK s k -> Map.MapsTo u b s.

  Parameter sample : unknown -> cset -> 
                             frac -> cset -> trace -> Prop.

  Parameter sample_preserves_types :
    forall u k q k' tr,
      sample u k q k' tr ->
      uts k = uts k'.

  Parameter sample_domain :
    forall u k q k' tr,
      sample u k q k' tr ->
      domain k = domain k'.

  Parameter uniform_singleton : 
    forall u k q k' tr,
    sample u k q k' tr -> sat k ->
    exists v, singleton k' u v.

  Parameter sample_preserves_well_typed :
    forall u k q k' tr,
      sample u k q k' tr ->
      well_typed_cset k -> well_typed_cset k'.

  Parameter sample_spec_1 : 
    forall u k s v, 
      InK s k -> Map.MapsTo u v s ->
      exists k', InK s k' /\ 
                 exists q tr, sample u k q k' tr.

  Parameter sample_spec_2 :
    forall u k q k' tr, 
      sample u k q k' tr ->
    forall s, InK s k' -> InK s k.


  Parameter uniform_preserves_singleton :
    forall u k q k' tr,
    sample u k q k' tr -> sat k ->
    forall u' v, singleton k  u' v ->
                 singleton k' u' v.

  Parameter uniform_sat : 
    forall u k q k' tr, 
      sample u k q k' tr -> sat k ->
      sat k'.

  Definition lte (k1 k2 : cset) : Prop := 
    (forall u, In u (domain k2) -> 
       In u (domain k1)) /\
    (forall s, InK s k1 -> 
       InK (restrict s (domain k2)) k2).

End CSET.

(* TODO: Module implementation. For now : QC in Haskell *)
Module CSet : CSET.

  Definition cset := 
    option (Map.t type * Map.t (set exp)).

  Definition empty : cset := 
    Some (Map.empty type, Map.empty (set exp)).

  Definition uts (k : cset) : Map.t type.
    admit. Defined.

  Definition domain (k : cset) : set unknown.
    admit. Defined.

  Parameter domain_is_used : 
    forall u k, In u (domain k) -> 
                Map.In u (uts k).

  Definition denotation : cset -> ValSet.t. admit. Defined.

  Definition InK s k :=
    ValSet.In s (denotation k).

  Definition well_typed_cset (k : cset) : Prop :=
    forall s, InK s k -> well_typed_valuation (uts k) s.

  Lemma InK_domain : 
    forall s k, InK s k ->
    forall u, Map.In u s <-> In u (domain k).                
  Admitted.

  Definition fresh : cset -> type -> (unknown * cset). 
  admit. Defined.

  Lemma fresh_increases_types : 
    forall k u k' t , 
      (u, k') = fresh k t ->
      uts k' = Map.add u t (uts k).
  Admitted.

  Lemma fresh_is_fresh_type : 
    forall k u k' t , 
      (u, k') = fresh k t ->
      ~ (Map.In u (uts k)).      
  Admitted.

  Lemma fresh_preserves_denotation :
    forall k u k' t,
      (u, k') = fresh k t ->
      denotation k = denotation k'.
  Admitted. 

  (* These might be provable from the above two *)
  Lemma fresh_preserves_domain : 
    forall k u k' t, 
      (u, k') = fresh k t ->
      domain k = domain k'.
  Admitted.

  Definition unify_in : cset -> exp -> exp -> cset.
  admit. Defined.

  Lemma unify_preserves_types : 
    forall k v1 v2,
      uts (unify_in k v1 v2) = uts k.
  Admitted.

  Lemma unify_domain :
    forall k v1 v2, 
    forall u, In u (domain (unify_in k v1 v2)) <->
              InExp u v1 \/ InExp u v2 \/ In u (domain k).
  Admitted.

  Lemma unify_preserves_well_typed :
    forall k v1 v2 k', 
      k' = unify_in k v1 v2 ->
      well_typed_cset k ->
      well_typed_cset k'.
  Admitted.

  Lemma unify_spec : 
    forall k v1 v2 s, 
      is_value v1 -> is_value v2 ->
      ((InK (restrict s (domain k)) k /\
      (forall v, SubVal s v1 v <-> SubVal s v2 v)) <->
      InK s (unify_in k v1 v2)).
  Admitted.

  Definition disj : cset -> cset -> cset -> cset. 
    admit. Defined.

  Definition sat (k : cset) : Prop :=
    exists s, ValSet.In s (denotation k).
  
  Definition sat_dec : forall (k : cset), {sat k} + {~ (sat k)}.
    admit. Defined.

  Definition singleton k u b : Prop :=
    forall s, InK s k -> Map.MapsTo u b s.

  Definition sample : unknown -> cset -> 
                              frac -> cset -> trace -> Prop.
     admit. Defined.

  Lemma sample_domain :
    forall u k q k' tr,
      sample u k q k' tr ->
      domain k = domain k'.
  Admitted.

  Lemma sample_preserves_types :
    forall u k q k' tr,
      sample u k q k' tr ->
      uts k = uts k'.
  Admitted.

  Lemma sample_preserves_well_typed :
    forall u k q k' tr,
      sample u k q k' tr ->
      well_typed_cset k -> well_typed_cset k'.
  Admitted.

  Lemma sample_spec_1 : 
    forall u k s v, 
      InK s k -> Map.MapsTo u v s ->
      exists k', InK s k' /\ 
                 exists q tr, sample u k q k' tr.
  Admitted.

  Lemma sample_spec_2 :
    forall u k q k' tr, 
      sample u k q k' tr ->
    forall s, InK s k' -> InK s k.
  Admitted.

  Lemma uniform_singleton : 
    forall u k q k' tr,
    sample u k q k' tr -> sat k ->
    exists v, singleton k' u v.
  Admitted.

  Lemma uniform_preserves_singleton :
    forall u k q k' tr,
    sample u k q k' tr -> sat k ->
    forall u' v, singleton k  u' v ->
                 singleton k' u' v.
  Admitted.

  Lemma uniform_sat : 
    forall u k q k' tr, 
      sample u k q k' tr -> sat k ->
      sat k'.
  Admitted.

  Definition lte (k1 k2 : cset) : Prop := 
    (forall u, In u (domain k2) -> 
       In u (domain k1)) /\
    (forall s, InK s k1 -> 
       InK (restrict s (domain k2)) k2).

End CSet.

Import CSet.

Lemma InK_equiv : 
  forall s s' k,
    Map.Equiv eq s s' ->
    (InK s k <-> InK s' k).
Proof.
  move => s s' k Eq; split => In;
  unfold InK in *.
  - eapply SetProp.In_1; eauto.
  - eapply SetProp.In_1; eauto.
    apply symmetry; auto.
Qed.

Lemma fresh_preserves_InK :
  forall k u k' t, 
    (u, k') = fresh k t ->
    (forall s, InK s k <-> InK s k').
Proof.
  move => k u k' T Fresh s; split => In; 
  unfold InK in *.
  - erewrite <- fresh_preserves_denotation; 
    eauto.
  - erewrite fresh_preserves_denotation; 
    eauto.
Qed.

Lemma fresh_is_fresh : 
    forall k u k' t, 
      (u, k') = fresh k t ->
      forall s, InK s k ->
                ~ (Map.In u s).
Proof.
  move => k u k' T Fresh s In In'.
  eapply fresh_is_fresh_type; eauto.
  eapply domain_is_used; eauto.
  eapply InK_domain; eauto.
Qed.

Lemma restrict_domain_InK :
  forall s s' k,
    InK s k ->
    Map.Equiv eq (restrict s' (domain k))
                 (MapProp.restrict s' s).  
move => s s' k HIn.
split.
- move => u; split => In.
  + eapply restrict_in_iff in In; eauto.
    move: In => [InS InD].
    eapply MapProp.restrict_in_iff; eauto.
    split; auto.
    eapply InK_domain; eauto.
  + eapply restrict_in_iff; eauto.
    eapply MapProp.restrict_in_iff in In.
    move: In => [In1 In2].
    split; auto.
    eapply InK_domain; eauto.
- move => u e es Map1 Map2.
  eapply restrict_mapsto_iff in Map1.
  eapply MapProp.restrict_mapsto_iff in Map2.
  move: Map2 => [Map2 _].
  eapply MapProp.F.MapsTo_fun; eauto.
Qed.

Lemma restrict_domain_InK_2 :
  forall s k s',
    InK s k ->
    InK (restrict s' (domain k)) k ->
    InK (MapProp.restrict s' s) k.
move => s k s' In1 In2.
eapply SetProp.In_1; eauto.
eapply restrict_domain_InK; eauto.
Qed.

Lemma fresh_preserves_lte : 
  forall k k' u t, 
    (u, k') = fresh k t -> lte k' k.
Proof.
  move => k k' u T Fresh; split. 
  - move => u' In.
    erewrite <- fresh_preserves_domain; eauto.
  - move => s In.
    erewrite fresh_preserves_domain; eauto.
    eapply fresh_preserves_InK; eauto.
    eapply InK_equiv; eauto.
    eapply transitivity with (y := s ↘ s).
    + eapply restrict_domain_InK; eauto.
    + eapply restrict_reflexive; eauto.
Qed.

Lemma fresh_preserves_well_typed :   
  forall k u k' t,
    (u, k') = fresh k t ->
    well_typed_cset k ->
    well_typed_cset k'.
move => k u k' t F WT s HIn.
constructor.
move => u' b Map.
pose proof Map as H.
eapply WT in H; eauto.
- move: H => [T [H1 H2]].
  exists T; split; auto.
  erewrite fresh_increases_types; eauto.
  eapply MapProp.F.add_mapsto_iff.
  right; split; auto.
  move => Eq; subst.
  eapply fresh_is_fresh_type; eauto.
  exists T; eauto.
- unfold InK.
  erewrite fresh_preserves_denotation; eauto.
Qed.


Instance lte_reflexive : Reflexive lte.
Proof.
  unfold Reflexive, lte => k; split; auto.
  move => s HInK.
  unfold InK in *.
  erewrite restrict_domain_InK; eauto.
  eapply SetProp.In_1; eauto.
  symmetry.
  eapply restrict_reflexive; eauto.
Qed.

Instance lte_transitive : Transitive lte.
Proof. 
  unfold Transitive, lte.
  move => k1 k2 k3 H1 H2.
  split.
  - move => u In.
    eapply H1; eapply H2; eauto.
  - move => s In. 
    apply H1 in In.
    apply H2 in In.
    eapply InK_equiv; eauto.
    eapply restrict_subset; eauto.
    eapply H2.
Qed.

Lemma fresh_fresh_unknowns_neq : 
  forall k u k' u' k'' t1 t2 ,
    (u, k') = fresh k t1 ->
    (u', k'') = fresh k' t2 ->
    u <> u'.
move => k u k' u' k'' t1 t2 F1 F2 Eq.
subst.
eapply (fresh_is_fresh_type k'); eauto.
erewrite fresh_increases_types; eauto.
apply MapProp.F.add_in_iff.
left; auto.
Qed.

Lemma fresh_fresh_unknowns_neq_sym : 
  forall k u k' u' k'' t1 t2 ,
    (u, k') = fresh k t1 ->
    (u', k'') = fresh k' t2 ->
    u' <> u.
move => k u k' u' k'' t1 t2 F1 F2 Eq.
subst.
eapply (fresh_is_fresh_type k'); eauto.
erewrite fresh_increases_types; eauto.
apply MapProp.F.add_in_iff.
left; auto.
Qed.


Lemma fresh_fresh_all_unknowns_neq : 
  forall u k u₁ k₁ u₂ k₂ s t1 t2,
    InK s k -> Map.In u s ->
    (u₁, k₁) = fresh k  t1 ->
    (u₂, k₂) = fresh k₁ t2 ->
    u <> u₁ /\ u <> u₂ /\ u₁ <> u₂.
move => u k u₁ k₁ u₂ k₂ s t1 t2 
        HInK HInMap Fresh₁ Fresh₂.
repeat split.
- move => Eq; subst.
  eapply fresh_is_fresh in HInMap; eauto.
- move => Eq; subst.
  eapply fresh_is_fresh in HInMap; eauto.
  rewrite fresh_preserves_InK in HInK; eauto.
- eapply fresh_fresh_unknowns_neq; eauto.
Qed.  

Lemma fresh_unknown_mapsto_neq : 
  forall k u u' k' s t ,
    (u', k') = fresh k t->
    InK s k -> Map.In u s ->
    u <> u'.
move => k u u' k' s t Fresh HIn HIn' Eq.
subst.
eapply fresh_is_fresh; eauto.
Qed.

Lemma InK_sat : 
  forall s k, InK s k -> sat k.
move => s k HIn.
exists s; auto.
Qed.

Lemma sample_lte : 
  forall u k k' q tr,
    sample u k q k' tr -> lte k' k.
move => u k k' q tr S; split.
- move => u' In.
  erewrite <- sample_domain; eauto.
- move => s In.
  eapply InK_equiv; eauto.
  + eapply restrict_domain_InK; eauto.
    eapply sample_spec_2; eauto.
  + eapply InK_equiv; eauto.
    * eapply restrict_reflexive; eauto.
    * eapply sample_spec_2; eauto.
Qed.

Lemma unify_in_lte : 
  forall k p₁ p₂ k',
    is_value p₁ -> is_value p₂ ->
    k' = unify_in k p₁ p₂ -> lte k' k.
move => k p1 p2 V1 V2 k' U; split; auto.
- move => u In.
  rewrite U.
  eapply unify_domain; eauto.
- move => s In.
  rewrite U in In.
  eapply unify_spec in In; eauto.
  inversion In; auto.
Qed.

(*
Lemma InExpTyped : 
  forall u v, InExp u v -> 
  forall UTS Γ T, UTS; Γ ⊢ v ↦ T ->
  exists T', UTS; Γ ⊢ U u ↦ T'.                  
move => u v H; induction H; 
move => UTS Γ T' HT';
inversion HT'; subst; eauto; clear HT';
match goal with 
  | [ IH : forall _ _ _, _; _ ⊢ ?E ↦ _ -> _ ,
      H  : _; _ ⊢ ?E ↦ _ |- _ ] =>
    eapply IH in H; eauto; 
    move: H => [T'' HT''];
              exists T'';
    econstructor; eauto;
    inversion HT''; eauto
end.
Qed.    

Lemma unify_preserves_well_typed :
    forall k v1 v2 k' T,
      is_value v1 -> is_value v2 ->
      uts k; ∅ ⊢ v1 ↦ T -> 
      uts k; ∅ ⊢ v2 ↦ T ->
      k' = unify_in k v1 v2 ->
      well_typed_cset k ->
      well_typed_cset k'.
move => k v1 v2 k' T V1 V2 HT1 HT2 U WT s HIn; subst.
constructor; auto.
move => u b Map.
assert (Hyp: In u (domain (unify_in k v1 v2))).
{
  eapply InK_domain; eauto.
  exists b; auto.
}
eapply unify_domain in Hyp.
apply unify_spec in HIn; auto.
move: HIn => [HIn Sub].
move: Hyp => [InE | [InE | InE]].
- assert (Hyp: exists T', uts k; ∅ ⊢ U u ↦ T')
  by (eapply InExpTyped; eauto).
  move: Hyp => [T' HT'].
  inversion HT'; subst; eauto.
  exists T'; split; auto.
  + erewrite unify_preserves_types; eauto.
  + constructor; auto.
    unfold well_typed_cset in *.
    eapply WT in HIn; auto.

    eapply WT in InK0; eauto.
    

move: In => [In Sub].*)