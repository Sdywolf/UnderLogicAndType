From Denotation Require Import Notation TypeDenote TypePersistBase TypePersistSingleton.
From ContextTyping Require Import FiberResult.

(** Bridge to an actual existing [context_ty].  The semantic integer examples
    do not pretend to be CoreLang terms, but Low itself has a native type. *)
Definition low_context_ty (b : base_ty) : context_ty :=
  CTPersist (CTOver b qual_top).

Lemma top_over_no_free_vars b : fv_cty (CTOver b qual_top) = ∅.
Proof.
  unfold fv_cty. rewrite context_ty_lvars_over_fv.
  unfold qual_dom. cbn [qual_vars qual_top_on].
  apply lvars_fv_singleton_bound.
Qed.

Theorem low_context_ty_intro (Delta : gmap atom ty) b o (m : WfWorldT) :
  m ⊨ TyDenote[Delta; CTOver b qual_top; tret (vfvar o)] ->
  m ⊨ FLow o ->
  m ⊨ TyDenote[Delta; low_context_ty b; tret (vfvar o)].
Proof.
  intros Hbase Hlow.
  destruct (low_result_singleton m o Hlow) as [s [Hdom Hsingle]].
  unfold low_context_ty.
  eapply ty_denote_persist_ret_fvar_intro_singleton with (σ := s).
  - rewrite top_over_no_free_vars. set_solver.
  - rewrite top_over_no_free_vars. set_solver.
  - rewrite top_over_no_free_vars. replace (∅ ∪ {[o]} : aset) with ({[o]} : aset) by set_solver.
    exact Hsingle.
  - exact Hbase.
Qed.
