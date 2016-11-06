Require Import List. Import ListNotations.
Require Import ListSet.

Require Import Util.
Require Import Types.

(* Valuations / maps *)
Require Export Coq.Structures.OrderedTypeEx.
Require Export MSetList.
Require Import FMapList.
Require Import FMapFacts.
Require Import MSetFacts.
Require Import Coq.Arith.EqNat.

Set Bullet Behavior "Strict Subproofs". 


(* INV: forall valuations: is_value exp *)
Definition valuation := Map.t base_value.

Inductive well_typed_valuation U (s : valuation) : Prop :=
| ValType : 
   (forall u b, Map.MapsTo u b s -> 
    exists T, Map.MapsTo u T U /\ typed_base_val b T) ->
   well_typed_valuation U s.

Inductive SubVal (s : valuation) : exp -> exp -> Prop :=
  | SubVar  : forall x, SubVal s (Var x) (Var x)
  | SubUnit : SubVal s Unit Unit
  | SubRec  : 
      forall f x T T' e e', SubVal s e e' -> 
        SubVal s (Rec f x T T' e) (Rec f x T T' e')
  | SubApp : 
      forall e1 e1' e2 e2',
        SubVal s e1 e1' ->
        SubVal s e2 e2' ->
        SubVal s (App e1 e2) (App e1' e2')
  | SubPair : 
      forall e1 e1' e2 e2',
        SubVal s e1 e1' ->
        SubVal s e2 e2' ->
        SubVal s (Pair e1 e2) (Pair e1' e2')
  | SubCaseP :
      forall e e' x y eb eb',
        SubVal s e e' ->
        SubVal s eb eb' ->
        SubVal s (CaseP e  x y eb) 
                 (CaseP e' x y eb')
  | SubInl : 
      forall e e' t1 t2, SubVal s e e' -> 
        SubVal s (Inl t1 t2 e) (Inl t1 t2 e')
  | SubInr : 
      forall e e' t1 t2, SubVal s e e' -> 
        SubVal s (Inr t1 t2 e) (Inr t1 t2 e')
  | SubCase : 
      forall e e' x ex ex' y ey ey',
        SubVal s e e' ->
        SubVal s ex ex' ->
        SubVal s ey ey' -> 
        SubVal s (Case e x ex y ey) 
                 (Case e' x ex' y ey')
  | SubUnknown :
      forall (u : unknown) (b : base_value) (e : exp),
        base_to_exp b = e ->             
        Map.MapsTo u b s -> 
        SubVal s (U u) e
  | SubInst : 
      forall e e' el el' er er',
        SubVal s e e' ->
        SubVal s el el' ->
        SubVal s er er' -> 
        SubVal s (Inst e el er) (Inst e' el' er')
  | SubBang : 
      forall e e',
        SubVal s e e' -> SubVal s (Bang e) (Bang e')
  | SubFold :
      forall e e' t, 
        SubVal s e e' ->
        SubVal s (Fold t e) (Fold t e')
  | SubUnfold :
      forall e e' t, 
        SubVal s e e' ->
        SubVal s (Unfold t e) (Unfold t e')
  | SubTil :
      forall e1 e1' t e2 e2', 
        SubVal s e1 e1' ->
        SubVal s e2 e2' ->
        SubVal s (Til e1 t e2) (Til e1' t e2').

Notation " s' ↘ s " :=
  (MapProp.restrict s' s) (at level 60).

Notation " s ≡ s' " := 
  (Map.Equiv eq s s') (at level 60).

Notation " s ⊕ x ↦ a " :=
  (Map.add x a s) (at level 60).

Lemma restrict_reflexive : 
  forall {T} (s : Map.t T), (s ↘ s) ≡ s.
move => s.
unfold Map.Equiv; split.
- move => u; split.
  + move => HIn.
    rewrite MapProp.restrict_in_iff in HIn.
    move : HIn => [? _]; trivial.
  + move => HIn.
    apply MapProp.restrict_in_iff; split; trivial.
- move => u v v' HMaps HMaps'.
  rewrite MapProp.restrict_mapsto_iff in HMaps.
  move : HMaps => [HMaps HIn].
  eapply MapFacts.MapsTo_fun; eauto.
Qed.  

Lemma restrict_transitive : 
  forall {T} (s s' s'': Map.t T),
    s'' ↘ s' ≡ s' -> 
    s'  ↘ s  ≡ s  ->
    s'' ↘ s  ≡ s.
unfold Map.Equiv.
move => T s s' s'' [HIn1 HMapsTo1] [HIn2 HMapsTo2];
  split.
- move {HMapsTo1 HMapsTo2} => u; split.
  + move => HIn.
    rewrite MapProp.restrict_in_iff in HIn.
    move : HIn => [_ ?]; trivial.
  + move => HIn.
    apply MapProp.restrict_in_iff; split; auto.
    move : {HIn2} (HIn2 u) => [_ H22].
    specialize (H22 HIn); clear HIn.
    rewrite MapProp.restrict_in_iff in H22.
    move : H22 => [HIn' _].
    move : {HIn1} (HIn1 u) => [_ H12].
    specialize (H12 HIn'); clear HIn'.
    rewrite MapProp.restrict_in_iff in H12.
    move : H12 => [? _]; assumption.
- move => u v v' HMapsTouv HMapsTouv'.
  rewrite MapProp.restrict_mapsto_iff in HMapsTouv.
  move : HMapsTouv => [HMapsTouv HInus].
  move : {HIn2} (HIn2 u) => [_ HIn_ur].
  specialize (HIn_ur HInus).
  rewrite MapProp.restrict_in_iff in HIn_ur.
  move : HIn_ur => [HInus' _].
  move : HInus' => [v'' H].
  (* This is because it can't be folded. Why? *)
  assert (HMapsTouv'' : Map.MapsTo u v'' s') by auto.
  clear H.
  assert (v = v'').
    eapply HMapsTo1; eauto.
    rewrite MapProp.restrict_mapsto_iff.
    split; auto. exists v''; auto.
  assert (v'' = v').
    eapply HMapsTo2; eauto.
    rewrite MapProp.restrict_mapsto_iff.
    split; auto.
  subst; auto.
Qed.

Lemma Equiv_transitive : 
  forall {T} (s1 s2 s3 : Map.t T),
    s1 ≡ s2 -> s2 ≡ s3 -> s1 ≡ s3.
move => T s1 s2 s3 [H12In H12M] [H23In H23M].
split.
- move => u.
  split.
  + move => HIn.
    apply H23In.
    apply H12In.
    auto.
  + move => HIn.
    apply H12In.
    apply H23In.
    auto.
- move => u e e' HM HM'.
  assert (Map.In u s1) by (exists e; auto).
  apply H12In in H.
  move : H => [e'' HAux].
  assert (HM'' : Map.MapsTo u e'' s2) 
    by auto; clear HAux.
  assert (e  = e'') by (eapply H12M; eauto).
  assert (e'' = e') by (eapply H23M; eauto).
  subst; auto.
Qed.
  
(* TODO: remove extra argument :) *)
Lemma restrict_add : 
  forall {T} u (s : Map.t T) a, 
    ~ (Map.In u s) ->
    ((s ⊕ u ↦ a) ↘ s) ≡ s.
move => T u s a HNotIn.
split.
- move => u'.
  split.
  * move => HIn.
    destruct (eq_unknown_dec u u') eqn:Eq.
    + subst.
      rewrite MapProp.restrict_in_iff in HIn.
      exfalso.
      apply HNotIn.
      apply HIn.
    + rewrite MapProp.restrict_in_iff in HIn.
      move: HIn => [H1 H2].
      auto.
  * move => HIn.
    destruct (eq_unknown_dec u u') eqn:Eq; 
    subst; 
    apply MapProp.restrict_in_iff;
    split; auto;
    apply MapProp.F.add_in_iff;
    [left | right]; auto.
- move => u' e e' H1 H2. 
  destruct (eq_unknown_dec u u') eqn:Eq.
  + rewrite MapProp.restrict_mapsto_iff in H1.
    move : H1 => [_ ?];
    subst; exfalso; auto.
  + rewrite MapProp.restrict_mapsto_iff in H1.
    move : H1 => [H1 H1'].
    subst.
    rewrite MapProp.F.add_mapsto_iff in H1.
    move : H1 => [[? ?] | [? ?]]; subst.
    * exfalso; auto.
    * eapply MapProp.F.MapsTo_fun; eauto.
Qed.

Lemma restrict_find :
  forall u {A} (s s' : Map.t A) a,
    Map.Equiv eq (MapProp.restrict s' s) s ->
    Map.find (elt := A) u s  = Some a ->
    Map.find (elt := A) u s' = Some a.
unfold Map.Equiv.
move => u A s s' a [HIn HMapsTo] HFind.
rewrite <- MapFacts.find_mapsto_iff in *.
assert (Map.In u s) by (exists a; auto).
move : {HIn} (HIn u) => [_ HIn].
move : {HIn} (HIn H) => [a' Ha'].
assert (a' = a) by (eapply HMapsTo; eauto).
assert (Hyp : Map.MapsTo u a' (MapProp.restrict s' s)) 
  by auto; clear Ha'.
rewrite MapProp.restrict_mapsto_iff in Hyp.
inversion Hyp; subst; auto.
Qed.

Definition restrict (s : valuation) (us : set unknown) :=
  MapProp.filter (fun key _ => 
              set_mem eq_unknown_dec key us) s.

Lemma restrict_mapsto_iff : 
  forall u b s us, Map.MapsTo u b (restrict s us) ->
                   Map.MapsTo u b s.
move => u b s us Map.
eapply MapProp.filter_iff in Map.
inversion Map; auto.
solve_proper.
Qed.

Lemma restrict_in_iff : 
  forall u s us, Map.In u (restrict s us) <->
                   Map.In u s /\ In u us.
move => u s us; split. 
* move => [b Map].
  split.
  - exists b.
    eapply restrict_mapsto_iff; eauto.
  - unfold restrict in Map.
    eapply MapProp.filter_iff in Map; eauto.
    + move: Map => [_ Mem].
      eapply set_mem_correct1 in Mem.
      auto.
    + solve_proper.
* move => [[b Map] In].
  exists b.
  eapply MapProp.filter_iff; eauto.
  + solve_proper.
  + split; auto.
    eapply set_mem_correct2; auto.
Qed.

Lemma restrict_subset : 
  forall s us1 us2, 
    (forall u, In u us2 -> In u us1) ->
    restrict s us2 ≡ 
      restrict (restrict s us1) us2.
move => s us1 us2 Sub.
split; auto.
- move => u; split.
  + move => [b Map]. 
    exists b. 
    eapply MapProp.filter_iff; eauto;
    eapply MapProp.filter_iff in Map; eauto;
    try solve [solve_proper].
    split; auto.
    * eapply MapProp.filter_iff; eauto;
      try solve [solve_proper].
      move: Map => [Map Mem].
      split; eauto.
      apply set_mem_correct1 in Mem.
      apply Sub in Mem.
      apply set_mem_correct2; auto.
    * move: Map => [Map Mem]; auto.
  + move => [b Map]; exists b.
    eapply MapProp.filter_iff; eauto;
    eapply MapProp.filter_iff in Map; eauto;
    try solve [solve_proper].
    move: Map => [Map Mem].
    eapply MapProp.filter_iff in Map;
        try solve [solve_proper].
    move: Map => [Map Mem'].
    split; eauto.
- move => k e e' Map1 Map2.
  eapply MapProp.filter_iff in Map1;
  eapply MapProp.filter_iff in Map2;
    try solve [solve_proper].
  move: Map1 => [Map1 _].
  move: Map2 => [Map2 _].
  eapply MapProp.filter_iff in Map2; 
    try solve [solve_proper].
  move: Map2 => [Map2 _].
  eapply MapProp.F.MapsTo_fun; eauto. 
Qed.

Lemma Restrict_restrict :
  forall s us, 
    Map.Equiv eq (MapProp.restrict s (restrict s us))
                 (restrict s us).
move => s us.
split.
- move => k; split.
  + move => In1.
    eapply MapProp.restrict_in_iff in In1.
    move: In1 => [? ?]; eauto.
  + move => In1.
    eapply MapProp.restrict_in_iff; eauto.
    split; auto.
    move: In1 => [e H'].
    assert (H : Map.MapsTo k e (restrict s us)) by auto; 
      clear H'.
    eapply MapProp.filter_iff in H; eauto.
    move: H => [H1 H2]; exists e; auto.
    solve_proper.
- move => k e e' Map1 Map2.
  eapply MapProp.restrict_mapsto_iff in Map1.
  move: Map1 => [? ?].
  eapply MapProp.filter_iff in Map2; eauto.
  move: Map2 => [? ?].
  eapply MapProp.F.MapsTo_fun; eauto.
  solve_proper.
Qed.

(* TODO: Implement this waaaay in the future *)
Module valuation_as_OWL <: OrderedTypeWithLeibniz.

  Definition t := valuation.

  Definition eq : t -> t -> Prop := 
    Map.Equiv eq.

  Definition eq_refl : forall x : t, eq x x. 
    move => x; unfold eq.
    apply MapProp.F.Equal_Equiv.
    apply MapProp.F.Equal_refl.
  Defined.

  Definition eq_sym : forall x y : t, eq x y -> eq y x.
    move => x y Eq; unfold eq in *.
    apply MapProp.F.Equal_Equiv.
    apply MapProp.F.Equal_sym.
    apply MapProp.F.Equal_Equiv.
    auto.
  Defined.

  Definition eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
    move => x y z Eq1 Eq2; unfold eq in *.
    apply MapProp.F.Equal_Equiv.
    eapply MapProp.F.Equal_trans;
      eapply MapProp.F.Equal_Equiv; eauto.
  Defined.

  Definition lt (x y : t) : Prop.
    admit. Defined.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
    admit.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
    admit.
  Qed.

  Definition eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
    admit.
  Qed.

  Definition eq_leibniz : forall (x y : t), eq x y -> x = y.
    admit. Defined.
 
  Instance eq_equiv : Equivalence eq.
    admit. Defined.

  Instance lt_strorder : StrictOrder lt.
    admit. Qed.

  Instance lt_compat : Proper (eq==>eq==>iff) lt.
    admit. Qed.
  
  Definition compare (x y : t) : comparison.
    admit. Defined.

  Lemma compare_spec_aux : forall s s', CompSpec eq lt s s' (compare s s').
    admit. Qed.

  Lemma compare_spec : forall s s', 
   CompSpec eq lt s s' (compare s s').
    admit. Qed.
End valuation_as_OWL.

Module ValSet := MSetList.MakeWithLeibniz(valuation_as_OWL).
Module SetProp := MSetFacts.Facts ValSet.

Inductive InExp : var -> exp -> Prop :=
  | in_unknown : forall u, 
      InExp u (U u)
  | in_rec : forall y f x T₁ T₂ e,
      InExp y e ->
      InExp y (Rec f x T₁ T₂ e)
  | in_app_1 : forall x e1 e2,
      InExp x e1 ->
      InExp x (App e1 e2)
  | in_app_2 : forall x e1 e2,
      InExp x e2 ->
      InExp x (App e1 e2)
  | in_pair_1 : forall x e1 e2,
      InExp x e1 ->
      InExp x (Pair e1 e2)
  | in_pair_2 : forall x e1 e2,
      InExp x e2 ->
      InExp x (Pair e1 e2)
  | in_casep_1 : forall x x' y' e e',
      InExp x e -> 
      InExp x (CaseP e x' y' e')
  | in_casep_2 : forall x x' y' e e', 
      InExp x e' ->
      InExp x (CaseP e x' y' e')
  | in_inl : forall x t1 t2 e, 
      InExp x e ->
      InExp x (Inl t1 t2 e)
  | in_inr : forall x t1 t2 e, 
      InExp x e ->
      InExp x (Inr t1 t2 e)
  | in_case_1 : forall x e x' ex y' ey,
      InExp x e ->
      InExp x (Case e x' ex y' ey) 
  | in_case_2 : forall x e x' ex y' ey,
      InExp x ex ->
      InExp x (Case e x' ex y' ey) 
  | in_case_3 : forall x e x' ex y' ey,
      InExp x ey ->
      InExp x (Case e x' ex y' ey) 
  | in_fold : forall x t e, 
      InExp x e ->
      InExp x (Fold t e)
  | in_unfold : forall x t e, 
      InExp x e ->
      InExp x (Unfold t e)
  | in_inst_1 : forall x e e1 e2,
      InExp x e ->
      InExp x (Inst e e1 e2)
  | in_inst_2 : forall x e e1 e2,
      InExp x e1 ->
      InExp x (Inst e e1 e2)
  | in_inst_3 : forall x e e1 e2,
      InExp x e2 ->
      InExp x (Inst e e1 e2)
  | in_bang : forall x e,
      InExp x e ->
      InExp x (Bang e)
  | in_til_1 : forall x e1 t e2,
      InExp x e1 ->
      InExp x (Til e1 t e2)
  | in_til_2 : forall x e1 t e2,
      InExp x e2 ->
      InExp x (Til e1 t e2).
