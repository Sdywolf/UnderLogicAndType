From ContextLogic Require Export FormulaSemantics.
From ContextLogic Require Import FormulaConnectives.
From ContextAlgebra Require Import ResourceInterface ResourceAlgebra.

(** * Noninterference in Context Logic

    [FLow x] says that x has one value throughout a capability.  This uses
    the existing, overlap-compatible product: both factors mention x, so
    their pairwise compatibility forces agreement on x.  No new connective
    and no context types are needed. *)
Section Noninterference.
Context {V : Type} `{ValueSig V}.
Local Remove Hints store_lookup store_insert store_union store_singleton store_empty : typeclass_instances.
Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation StoreT := (gmap atom V) (only parsing).
Local Notation "m ⊨ P" := (res_models m P) (at level 70).

Definition FBound (x : atom) : Formula (V := V) :=
  FOver (FAtom (qual_top_on {[LVFree x]})).
Definition FLow (x : atom) : Formula (V := V) := FStar (FBound x) (FBound x).
Definition FNoninterference (l o : atom) : Formula (V := V) :=
  FFibVars {[LVFree l]} (FLow o).

Lemma FBound_fv x : formula_fv (FBound x) = {[x]}.
Proof.
  unfold FBound. rewrite formula_fv_over, formula_fv_atom,
    qual_vars_top_on, lvars_fv_singleton_free. reflexivity.
Qed.

Lemma FLow_fv x : formula_fv (FLow x) = {[x]}.
Proof. unfold FLow. rewrite formula_fv_star, !FBound_fv. set_solver. Qed.

Lemma FNoninterference_fv l o :
  formula_fv (FNoninterference l o) = {[l; o]}.
Proof.
  unfold FNoninterference. rewrite formula_fv_fibvars,
    lvars_fv_singleton_free, FLow_fv. set_solver.
Qed.

Lemma FBound_spec m x : m ⊨ FBound x <-> x ∈ world_dom (m : WorldT).
Proof.
  split.
  - intros Hm. pose proof (res_models_scoped _ _ Hm) as Hscope.
    unfold formula_scoped_in_world in Hscope. rewrite FBound_fv in Hscope.
    set_solver.
  - intros Hx. apply res_models_over_FAtom_intro_store_holds.
    + change (formula_fv (FBound x) ⊆ world_dom (m : WorldT)).
      rewrite FBound_fv. set_solver.
    + intros σ Hσ. unfold qualifier_holds_store, qual_top_on.
      assert (Hlc : lc_lvars {[LVFree x]}).
      { intros z Hz. apply elem_of_singleton in Hz. subst z. done. }
      exists Hlc.
      assert (Hsub : lvars_fv {[LVFree x]} ⊆ dom (σ : StoreT)).
      { rewrite lvars_fv_singleton_free, (wfworld_store_dom m σ Hσ).
        set_solver. }
      exists Hsub. exact I.
Qed.

Lemma project_store_of_le (a m : WfWorldT) σ :
  a ⊑ m -> (m : WorldT) σ ->
  (a : WorldT) (store_restrict σ (world_dom (a : WorldT))).
Proof.
  intros Hle Hσ.
  assert (Hmem : (res_restrict m (world_dom (a : WorldT)) : WorldT)
    (store_restrict σ (world_dom (a : WorldT)))).
  { exists σ. auto. }
  rewrite (res_restrict_eq_of_le a m Hle) in Hmem. exact Hmem.
Qed.

Lemma restrict_singleton_lookup (σ τ : StoreT) x :
  σ !! x = τ !! x -> store_restrict σ {[x]} = store_restrict τ {[x]}.
Proof.
  intros Heq. apply (map_eq (M:=gmap atom)). intros y. rewrite !storeA_restrict_lookup.
  destruct (decide (y ∈ ({[x]} : aset))) as [Hy|Hy]; [|reflexivity].
  apply elem_of_singleton in Hy. subst y. exact Heq.
Qed.

Lemma FLow_spec (m : WfWorldT) x :
  m ⊨ FLow x <->
  x ∈ world_dom (m : WorldT) /\
  forall σ τ, (m : WorldT) σ -> (m : WorldT) τ -> σ !! x = τ !! x.
Proof.
  split.
  - intros Hlow.
    pose proof (res_models_scoped _ _ Hlow) as Hscope.
    unfold formula_scoped_in_world in Hscope. rewrite FLow_fv in Hscope.
    split; [set_solver|].
    apply res_models_star_iff in Hlow as [a [b [Hc [Hle [Ha Hb]]]]].
    apply FBound_spec in Ha. apply FBound_spec in Hb.
    pose proof (res_product_le_l a b Hc) as Hal.
    pose proof (res_product_le_r a b Hc) as Hbl.
    assert (Ham : a ⊑ m) by (etransitivity; eauto).
    assert (Hbm : b ⊑ m) by (etransitivity; eauto).
    intros σ τ Hσ Hτ.
    pose proof (project_store_of_le a m σ Ham Hσ) as Hσa.
    pose proof (project_store_of_le b m τ Hbm Hτ) as Hτb.
    assert (Hxσ : x ∈ dom (σ : StoreT)).
    { rewrite (wfworld_store_dom m σ Hσ). set_solver. }
    assert (Hxτ : x ∈ dom (τ : StoreT)).
    { rewrite (wfworld_store_dom m τ Hτ). set_solver. }
    apply elem_of_dom in Hxσ as [v Hv].
    apply elem_of_dom in Hxτ as [w Hw].
    rewrite Hv, Hw. f_equal.
    eapply (Hc _ _ Hσa Hτb x v w).
    + rewrite storeA_restrict_lookup. destruct decide; [exact Hv|contradiction].
    + rewrite storeA_restrict_lookup. destruct decide; [exact Hw|contradiction].
  - intros [Hx Hagree].
    destruct (world_wf m) as [[σ Hσ] _].
    set (s := store_restrict σ {[x]}).
    set (one := (exist _ (singleton_world s) (wf_singleton_world s) : WfWorldT)).
    assert (Hdom : dom (s : StoreT) = {[x]}).
    { unfold s. rewrite storeA_restrict_dom, (wfworld_store_dom m σ Hσ).
      set_solver. }
    assert (Hproj : res_restrict m {[x]} = one).
    { apply wfworld_eq_by_dom_stores.
      - rewrite res_restrict_dom. change (world_dom (m : WorldT) ∩ {[x]} = dom (s : StoreT)).
        rewrite Hdom. set_solver.
      - intros τ. change ((exists ρ, (m : WorldT) ρ /\ store_restrict ρ {[x]} = τ) <-> τ = s).
        split.
        + intros [ρ [Hρ <-]]. apply restrict_singleton_lookup. apply Hagree; assumption.
        + intros ->. exists σ. auto. }
    assert (Hc : world_compat one one).
    { intros τ ρ Hτ Hρ. change (τ = s) in Hτ. change (ρ = s) in Hρ.
      subst τ ρ. apply map_compat_refl. }
    assert (Hprod : res_product one one Hc = one).
    { apply wfworld_eq_by_dom_stores.
      - rewrite res_product_dom. set_solver.
      - intros τ. change ((exists a b, a = s /\ b = s /\ storeA_compat a b /\ τ = a ∪ b) <-> τ = s).
        split.
        + intros [a [b [-> [-> [_ ->]]]]]. apply map_union_idemp.
        + intros ->. exists s, s. repeat split; try apply map_compat_refl.
          symmetry. apply map_union_idemp. }
    apply res_models_star_intro with (m1 := one) (m2 := one) (Hc := Hc).
    + rewrite Hprod, <- Hproj. apply res_restrict_le.
    + apply FBound_spec. change (x ∈ dom (s : StoreT)). rewrite Hdom. set_solver.
    + apply FBound_spec. change (x ∈ dom (s : StoreT)). rewrite Hdom. set_solver.
Qed.

(** Substitution by a low-input fiber leaves the distinct output slot alone. *)
Lemma FLow_msubst_fresh (σ : StoreT) x :
  x ∉ dom (σ : StoreT) -> formula_msubst_store σ (FLow x) = FLow x.
Proof.
  intros Hfresh.
  assert (Hq : qual_msubst_store σ (qual_top_on {[LVFree x]}) =
      qual_top_on {[LVFree x]}).
  { apply qual_ext.
    - cbn [qual_msubst_store qual_mlsubst qual_top_on qual_lvars].
      rewrite atom_store_to_lvar_store_dom.
      apply set_eq. intros z. rewrite elem_of_difference.
      split; [tauto|]. intros Hz. split; [exact Hz|].
      apply elem_of_singleton in Hz. subst z.
      rewrite <- lvars_fv_elem, lvars_fv_of_atoms. exact Hfresh.
    - intros s1 s2 _. reflexivity. }
  unfold FLow, FBound.
  change (FStar (FOver (FAtom (qual_msubst_store σ (qual_top_on {[LVFree x]}))))
    (FOver (FAtom (qual_msubst_store σ (qual_top_on {[LVFree x]})))) = FStar (FBound x) (FBound x)).
  rewrite Hq. reflexivity.
Qed.

(** The forall-forall condition is a theorem about the existing formula,
    rather than a new state-quantification constructor. Scope is explicit:
    both l and o must be present, and the two variable names are distinct. *)
Theorem FNoninterference_spec (m : WfWorldT) l o :
  l <> o ->
  (m ⊨ FNoninterference l o <->
   {[l; o]} ⊆ world_dom (m : WorldT) /\
   forall σ τ, (m : WorldT) σ -> (m : WorldT) τ ->
     σ !! l = τ !! l -> σ !! o = τ !! o).
Proof.
  intros Hlo. split.
  - intros Hni. apply res_models_FFibVars_iff in Hni as [Hscope [_ Hfib]].
    unfold formula_scoped_in_world in Hscope.
    change (formula_fv (FNoninterference l o) ⊆ world_dom (m : WorldT)) in Hscope.
    rewrite FNoninterference_fv in Hscope.
    split; [exact Hscope|]. intros σ τ Hσ Hτ Heq.
    destruct (res_fiber_from_projection_of_store_any_domain m {[l]} σ Hσ)
      as [mfib [Hproj Hσfib]].
    assert (Hdom : dom (store_restrict σ {[l]} : StoreT) = {[l]}).
    { rewrite storeA_restrict_dom, (wfworld_store_dom m σ Hσ). set_solver. }
    specialize (Hfib (store_restrict σ {[l]}) mfib).
    rewrite lvars_fv_singleton_free in Hfib.
    specialize (Hfib Hproj).
    rewrite FLow_msubst_fresh in Hfib by (rewrite Hdom; set_solver).
    apply FLow_spec in Hfib as [_ Hagree].
    apply Hagree; [exact Hσfib|].
    destruct Hproj as [_ Hraw]. change ((mfib : WorldT) = raw_fiber (m : WorldT) (store_restrict σ {[l]})) in Hraw.
    change ((mfib : WorldT) τ). rewrite Hraw.
    split; [exact Hτ|].
    change (store_restrict τ (dom (store_restrict σ {[l]} : StoreT)) = store_restrict σ {[l]}).
    rewrite Hdom. apply restrict_singleton_lookup. symmetry. exact Heq.
  - intros [Hscope Hni]. apply res_models_FFibVars_intro.
    + change (formula_fv (FNoninterference l o) ⊆ world_dom (m : WorldT)).
      rewrite FNoninterference_fv. exact Hscope.
    + intros z Hz. apply elem_of_singleton in Hz. subst z. done.
    + intros σ mfib Hproj. rewrite lvars_fv_singleton_free in Hproj.
      pose proof (res_fiber_from_projection_store_dom_subset m mfib {[l]} σ Hproj) as Hdom.
      rewrite FLow_msubst_fresh by set_solver.
      apply FLow_spec. split.
      * rewrite (res_fiber_from_projection_world_dom m mfib {[l]} σ Hproj).
        set_solver.
      * intros τ ρ Hτ Hρ. apply Hni.
        -- eapply res_fiber_from_projection_store_source; eauto.
        -- eapply res_fiber_from_projection_store_source; eauto.
        -- pose proof (res_fiber_from_projection_store_restrict_input m mfib {[l]} σ τ Hproj Hτ) as Hτl.
           pose proof (res_fiber_from_projection_store_restrict_input m mfib {[l]} σ ρ Hproj Hρ) as Hρl.
           assert (Heq : store_restrict τ {[l]} = store_restrict ρ {[l]}) by congruence.
           pose proof (f_equal (fun s : StoreT => s !! l) Heq) as Hl.
           rewrite !storeA_restrict_lookup in Hl.
           destruct decide; [exact Hl|set_solver].
Qed.

End Noninterference.
