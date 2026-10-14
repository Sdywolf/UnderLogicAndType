From ContextLogic Require Export FormulaNoninterference.
From ContextLogic Require Export FormulaConnectives.
From ContextQualifier Require Export SupportPadding.
From ContextAlgebra Require Import ResourceCore ResourceInterfaceFacts.

(** Semantic result-type prototype.  This deliberately does not extend the
    compiled [context_ty] grammar or claim a [has_context_type] derivation.
    [RTObserve] lifts the document's observation discipline to an entire
    result type; qualifier padding alone cannot impose cross-run agreement. *)
Inductive fiber_result_ty : Type :=
  | RTBound
  | RTLow
  | RTObserve (X : aset) (tau : fiber_result_ty).

Section FiberResult.
Context {V : Type} `{ValueSig V}.
Local Remove Hints store_lookup store_insert store_union store_singleton store_empty : typeclass_instances.
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation "m ⊨ P" := (res_models m P) (at level 70).

(** Low is precisely persistence of a bound result, rather than a new
    primitive relational assertion.  This justifies the schematic Low_b =
    square Over[b|top], with basic typing supplied separately. *)
Lemma low_result_singleton (m : WfWorldT) o :
  m ⊨ FLow o ->
  exists s : Store (V := V), dom s = {[o]} /\
    res_restrict m {[o]} =
      (exist _ (singleton_world s) (wf_singleton_world s) : WfWorldT).
Proof.
  intros Hlow. apply FLow_spec in Hlow as [Ho Hagree].
  destruct (world_wf m) as [[s0 Hs0] _].
  exists (store_restrict s0 {[o]}). split.
  - change (dom (store_restrict s0 {[o]} : gmap atom V) = {[o]}).
    rewrite storeA_restrict_dom, (wfworld_store_dom m s0 Hs0). set_solver.
  - apply wfworld_eq_by_dom_stores.
    + change (world_dom (res_restrict m {[o]} : WorldT) =
        dom (store_restrict s0 {[o]} : gmap atom V)).
      rewrite res_restrict_dom, storeA_restrict_dom,
        (wfworld_store_dom m s0 Hs0). reflexivity.
    + intros t. change ((exists s, (m : WorldT) s /\ store_restrict s {[o]} = t)
        <-> t = store_restrict s0 {[o]}).
      split.
      * intros [s [Hs <-]]. apply restrict_singleton_lookup. apply Hagree; assumption.
      * intros ->. exists s0. auto.
Qed.

Theorem low_result_persistence (m : WfWorldT) o :
  m ⊨ FLow o <-> m ⊨ FPersist (FBound o).
Proof.
  split.
  - intros Hlow. destruct (low_result_singleton m o Hlow) as [s [Hdom Hsingle]].
    apply res_models_persist_iff. exists s. rewrite FBound_fv.
    split; [exact Hdom|]. split; [exact Hsingle|].
    apply FBound_spec. change (o ∈ dom s). rewrite Hdom. set_solver.
  - intros Hpersist. apply res_models_persist_iff in Hpersist as [s [Hdom [Hsingle _]]].
    rewrite FBound_fv in Hdom, Hsingle.
    change (dom (s : gmap atom V) = {[o]}) in Hdom.
    apply FLow_spec. split.
    + pose proof (f_equal (fun w : WfWorldT => world_dom (w : WorldT)) Hsingle) as Hd.
      change (world_dom (res_restrict m {[o]} : WorldT) = dom (s : gmap atom V)) in Hd.
      rewrite res_restrict_dom in Hd.
      rewrite Hdom in Hd. set_solver.
    + intros t u Ht Hu.
      pose proof (res_restrict_singleton_store_eq m {[o]} s t Hsingle Ht) as Ht'.
      pose proof (res_restrict_singleton_store_eq m {[o]} s u Hsingle Hu) as Hu'.
      assert (Heq : store_restrict t {[o]} = store_restrict u {[o]}) by congruence.
      pose proof (f_equal (fun s : Store (V := V) => s !! o) Heq) as Hlookup.
      change ((store_restrict t {[o]} : gmap atom V) !! o =
        (store_restrict u {[o]} : gmap atom V) !! o) in Hlookup.
      rewrite !storeA_restrict_lookup in Hlookup.
      destruct decide; [exact Hlookup|set_solver].
Qed.

Fixpoint fiber_result_denote (tau : fiber_result_ty) (o : atom) : Formula (V := V) :=
  match tau with
  | RTBound => FBound o
  | RTLow => FLow o
  | RTObserve X tau => FFibVars (lvars_of_atoms X) (fiber_result_denote tau o)
  end.

Definition ni_result_ty (l : atom) := RTObserve {[l]} RTLow.

(** Use the actual qualifier dot to specify the fiber observation set.
    Unlike padding a plain Over-top result, the body still demands Low. *)
Definition padded_low_result_ty (l : atom) : fiber_result_ty :=
  RTObserve
    (qual_dom (qual_pad {[LVFree l]} (qual_top_on (V := V) ∅))) RTLow.

Lemma padded_low_result_eq l : padded_low_result_ty l = ni_result_ty l.
Proof.
  unfold padded_low_result_ty, ni_result_ty, qual_dom.
  rewrite qual_pad_vars, qual_vars_top_on.
  replace ({[LVFree l]} ∪ ∅ : lvset) with ({[LVFree l]} : lvset) by set_solver.
  rewrite lvars_fv_singleton_free. reflexivity.
Qed.

Lemma ni_result_denote l o :
  fiber_result_denote (ni_result_ty l) o = FNoninterference l o.
Proof.
  unfold ni_result_ty. cbn [fiber_result_denote].
  unfold lvars_of_atoms, FNoninterference.
  assert (Hs : set_map LVFree ({[l]} : aset) = ({[LVFree l]} : lvset))
    by set_solver.
  rewrite Hs. reflexivity.
Qed.

Theorem ni_result_spec (m : WfWorldT) l o :
  l <> o ->
  (m ⊨ fiber_result_denote (ni_result_ty l) o <->
   {[l; o]} ⊆ world_dom (m : WorldT) /\
   forall s t, (m : WorldT) s -> (m : WorldT) t ->
     s !! l = t !! l -> s !! o = t !! o).
Proof. intros Hlo. rewrite ni_result_denote. apply FNoninterference_spec, Hlo. Qed.

(** Function contracts quantify over input capabilities, rather than one
    execution.  [run] must supply the complete output image, not a chosen run. *)
Definition has_fiber_function_type
    (pre : Formula (V := V)) (tau : fiber_result_ty) (o : atom)
    (run : WfWorldT -> WfWorldT) : Prop :=
  forall m, m ⊨ pre -> run m ⊨ fiber_result_denote tau o.

End FiberResult.
