From ContextTyping Require Import FiberResult.
From ContextLogicExamples Require Import HypraSecure.
From ContextAlgebra Require Import ResourceCore ResourceInterface.
From Stdlib Require Import ZArith Lia.

(** The *same* signed-integer transformer used by the logic example.
    These are semantic function-type inhabitants, not CoreLang derivations. *)
Module HypraSecureTyping.
Import HypraSecure.
Local Existing Instance integer_values.
Local Open Scope Z_scope.
Local Remove Hints store_lookup store_insert store_union store_singleton store_empty : typeclass_instances.
Local Notation WorldT := (World (V := Z)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := Z)) (only parsing).
Local Notation "m ⊨ P" := (res_models m P) (at level 70).

Definition inputs_bound : Formula (V := Z) := FAnd (FBound high) (FBound low).
Definition low_inputs : Formula (V := Z) := FAnd (FBound high) (FLow low).
Definition ni_function_type (f : Z -> Z -> Z) : Prop :=
  has_fiber_function_type inputs_bound (padded_low_result_ty (V := Z) low) out (outputs f).
Definition low_function_type (f : Z -> Z -> Z) : Prop :=
  has_fiber_function_type low_inputs RTLow out (outputs f).
Definition pointwise_ni (f : Z -> Z -> Z) : Prop :=
  forall h1 h2 l, f h1 l = f h2 l.

Definition two_inputs (h1 h2 l : Z) : WfWorldT.
Proof.
  refine (exist _ {| worldA_dom := {[high; low]};
    worldA_stores := fun s => s = input h1 l \/ s = input h2 l |} _).
  split.
  - exists (input h1 l). left. reflexivity.
  - intros s [-> | ->]; unfold input; rewrite dom_insert_L, dom_singleton_L; reflexivity.
Defined.

Lemma two_inputs_bound h1 h2 l : two_inputs h1 h2 l ⊨ inputs_bound.
Proof.
  unfold inputs_bound. rewrite res_models_and_iff, !FBound_spec. simpl. set_solver.
Qed.

Lemma two_inputs_low h1 h2 l : two_inputs h1 h2 l ⊨ low_inputs.
Proof.
  unfold low_inputs. rewrite res_models_and_iff, FBound_spec, FLow_spec. split.
  - simpl. set_solver.
  - split; [simpl; set_solver|].
    intros s t [-> | ->] [-> | ->]; vm_compute; reflexivity.
Qed.

Lemma input_high h l : input h l !! high = Some h.
Proof. apply lookup_insert_eq. Qed.
Lemma input_low h l : input h l !! low = Some l.
Proof. unfold input. rewrite lookup_insert_ne; [apply lookup_singleton_eq|discriminate]. Qed.

Theorem ni_function_type_iff f : ni_function_type f <-> pointwise_ni f.
Proof.
  split.
  - intros Hty h1 h2 l.
    specialize (Hty (two_inputs h1 h2 l) (two_inputs_bound h1 h2 l)).
    unfold ni_function_type, has_fiber_function_type in Hty.
    rewrite padded_low_result_eq, ni_result_denote in Hty.
    apply FNoninterference_spec in Hty; [|discriminate].
    destruct Hty as [_ Hrel].
    specialize (Hrel (run f (input h1 l)) (run f (input h2 l))).
    assert (H1 : (outputs f (two_inputs h1 h2 l) : WorldT) (run f (input h1 l))).
    { exists (input h1 l). split; [left|]; reflexivity. }
    assert (H2 : (outputs f (two_inputs h1 h2 l) : WorldT) (run f (input h2 l))).
    { exists (input h2 l). split; [right|]; reflexivity. }
    specialize (Hrel H1 H2).
    rewrite !run_low, !input_low in Hrel.
    specialize (Hrel eq_refl). rewrite !run_out, !input_high, !input_low in Hrel.
    cbn in Hrel. congruence.
  - intros Hni m Hpre. rewrite padded_low_result_eq, ni_result_denote.
    apply res_models_and_iff in Hpre as [Hh Hl].
    apply FBound_spec in Hh. apply FBound_spec in Hl.
    apply FNoninterference_spec; [discriminate|]. split.
    + change ({[low; out]} ⊆ {[out]} ∪ world_dom (m : WorldT)). set_solver.
    + intros s t [s0 [Hs ->]] [t0 [Ht ->]] Heq.
      rewrite !run_low in Heq. rewrite !run_out, Heq. f_equal. apply Hni.
Qed.

Theorem low_function_type_iff f : low_function_type f <-> pointwise_ni f.
Proof.
  split.
  - intros Hty h1 h2 l.
    specialize (Hty (two_inputs h1 h2 l) (two_inputs_low h1 h2 l)).
    apply FLow_spec in Hty as [_ Hrel].
    assert (H1 : (outputs f (two_inputs h1 h2 l) : WorldT) (run f (input h1 l))).
    { exists (input h1 l). split; [left|]; reflexivity. }
    assert (H2 : (outputs f (two_inputs h1 h2 l) : WorldT) (run f (input h2 l))).
    { exists (input h2 l). split; [right|]; reflexivity. }
    specialize (Hrel _ _ H1 H2).
    rewrite !run_out, !input_high, !input_low in Hrel. cbn in Hrel. congruence.
  - intros Hni m Hpre. apply res_models_and_iff in Hpre as [_ Hl].
    apply FLow_spec in Hl as [_ Hagree]. apply FLow_spec. split.
    + change (out ∈ {[out]} ∪ world_dom (m : WorldT)). set_solver.
    + intros s t [s0 [Hs ->]] [t0 [Ht ->]].
      rewrite !run_out, (Hagree _ _ Hs Ht). f_equal. apply Hni.
Qed.

(** A low-only result refinement is sufficient; existentially choosing its
    summary makes it exact for this total deterministic fragment.  The
    summary is specification data, never a function of the secret. *)
Theorem ni_iff_low_summary f :
  ni_function_type f <-> exists g : Z -> Z, forall h l, f h l = g l.
Proof.
  rewrite ni_function_type_iff. split.
  - intros Hni. exists (fun l => f 0 l). intros. apply Hni.
  - intros [g Hg] h1 h2 l. rewrite !Hg. reflexivity.
Qed.

Example secure_has_ni_type : ni_function_type secure.
Proof. apply ni_function_type_iff. intros h1 h2 l. rewrite !secure_result. reflexivity. Qed.

Example secure_has_low_type : low_function_type secure.
Proof. apply low_function_type_iff. intros h1 h2 l. rewrite !secure_result. reflexivity. Qed.

Example first_if_rejected : ~ ni_function_type first_if.
Proof.
  rewrite ni_function_type_iff. intros Hni.
  specialize (Hni 1 (-1) 3). vm_compute in Hni. discriminate.
Qed.

Example constant_has_ni_type : ni_function_type (fun _ _ => 7).
Proof. apply ni_function_type_iff. intros h1 h2 l. reflexivity. Qed.

(** Requiring global output agreement would incorrectly reject secure. *)
Example secure_not_globally_low :
  ~ (forall m, m ⊨ inputs_bound -> outputs secure m ⊨ FLow out).
Proof.
  intros Hty.
  set (s0 := input 1 0). set (s1 := input 1 1).
  assert (Hdom : dom s0 = dom s1).
  { unfold s0, s1, input. rewrite !dom_insert_L, !dom_singleton_L. reflexivity. }
  set (m := (exist _ (singleton_world s0) (wf_singleton_world s0) : WfWorldT)).
  set (n := (exist _ (singleton_world s1) (wf_singleton_world s1) : WfWorldT)).
  assert (Hsum : raw_sum_defined m n) by exact Hdom.
  specialize (Hty (res_sum m n Hsum)).
  assert (Hb : res_sum m n Hsum ⊨ inputs_bound).
  { unfold inputs_bound. rewrite res_models_and_iff, !FBound_spec. split; unfold m; simpl;
      unfold s0, input; rewrite dom_insert_L, dom_singleton_L; set_solver. }
  apply Hty in Hb. apply FLow_spec in Hb as [_ Hrel].
  assert (H0 : (outputs secure (res_sum m n Hsum) : WorldT) (run secure s0)).
  { exists s0. split; [left|]; reflexivity. }
  assert (H1 : (outputs secure (res_sum m n Hsum) : WorldT) (run secure s1)).
  { exists s1. split; [right|]; reflexivity. }
  specialize (Hrel _ _ H0 H1). vm_compute in Hrel. discriminate.
Qed.

End HypraSecureTyping.
