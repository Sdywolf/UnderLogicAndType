From ContextLogic Require Import FormulaNoninterference.
From ContextAlgebra Require Import ResourceCore ResourceInterface.
From Stdlib Require Import ZArith Lia.

(** * Hypra Fig. 2: secure, at the Context Logic layer

    Source: Dardinier, Li, Mueller, "Hypra: A Deductive Program Verifier
    for Hyper Hoare Logic", OOPSLA 2024, Fig. 2.
    https://doi.org/10.1145/3689756

    The two conditionals are modeled directly as an integer state transformer,
    not as a CoreLang term or a context-typing derivation.  In particular,
    negative secret inputs and low inputs are retained. *)
Module HypraSecure.
Local Open Scope Z_scope.
Local Instance integer_values : ValueSig Z :=
  {| valuesig_eqdec := _; valuesig_inhabited := _ |}.
Local Remove Hints store_lookup store_insert store_union store_singleton store_empty : typeclass_instances.
Local Notation WorldT := (World (V := Z)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := Z)) (only parsing).
Local Notation StoreT := (gmap atom Z) (only parsing).
Local Notation "m ⊨ P" := (res_models m P) (at level 70).

Definition high : atom := 1%positive.
Definition low : atom := 2%positive.
Definition out : atom := 3%positive.

Definition first_if (h l : Z) : Z := if Z.gtb h 0 then 2 * l else l.
Definition secure (h l : Z) : Z :=
  let o := first_if h l in
  if Z.leb h 0 then o + l else o.

Lemma secure_result h l : secure h l = (2 * l)%Z.
Proof.
  unfold secure, first_if. rewrite Z.gtb_ltb.
  destruct (Z.ltb 0 h) eqn:Hpos; destruct (Z.leb h 0) eqn:Hnonpos;
    try apply Z.ltb_lt in Hpos; try apply Z.ltb_ge in Hpos;
    try apply Z.leb_le in Hnonpos; try apply Z.leb_gt in Hnonpos; lia.
Qed.

(** Lookups are totalized outside the program's input domain. The main
    specifications require the input variables to be bound. *)
Definition run (f : Z -> Z -> Z) (σ : StoreT) : StoreT :=
  <[out := f (default 0%Z (σ !! high)) (default 0%Z (σ !! low))]> σ.

Lemma run_low f σ : run f σ !! low = σ !! low.
Proof. unfold run. rewrite lookup_insert_ne; [reflexivity|discriminate]. Qed.

Lemma run_out f σ :
  run f σ !! out = Some (f (default 0%Z (σ !! high)) (default 0%Z (σ !! low))).
Proof. apply lookup_insert_eq. Qed.

(** Exact image of all input states, including all secret choices. The
    nonempty-world invariant follows from nonemptiness of the input world. *)
Definition outputs (f : Z -> Z -> Z) (m : WfWorldT) : WfWorldT.
Proof.
  refine (exist _ {| worldA_dom := {[out]} ∪ world_dom (m : WorldT);
    worldA_stores := fun τ => exists σ, (m : WorldT) σ /\ τ = run f σ |} _).
  split.
  - destruct (world_wf m) as [[σ Hσ] _]. exists (run f σ). exists σ. auto.
  - intros τ [σ [Hσ ->]]. unfold run. rewrite dom_insert_L.
    rewrite (wfworld_store_dom m σ Hσ). reflexivity.
Defined.

(** Pointwise functional correctness, followed by the hyperproperty on
    arbitrary input sets, not merely on a fixed pair of executions. *)
Theorem secure_noninterference (m : WfWorldT) :
  {[high; low]} ⊆ world_dom (m : WorldT) ->
  outputs secure m ⊨ FNoninterference low out.
Proof.
  intros Hscope. apply FNoninterference_spec; [discriminate|]. split.
  - change ({[low; out]} ⊆ {[out]} ∪ world_dom (m : WorldT)). set_solver.
  - intros τ1 τ2 [σ1 [Hσ1 ->]] [σ2 [Hσ2 ->]] Heq.
    rewrite !run_low in Heq. rewrite !run_out, !secure_result, Heq. reflexivity.
Qed.

(** The exact shape of Hypra's requires/ensures: low input agreement implies
    low output agreement. This also covers inputs following only one branch. *)
Theorem secure_hypertriple (m : WfWorldT) :
  high ∈ world_dom (m : WorldT) ->
  m ⊨ FLow low -> outputs secure m ⊨ FLow out.
Proof.
  intros _ Hlow. apply FLow_spec in Hlow as [_ Hagree].
  apply FLow_spec. split.
  - change (out ∈ {[out]} ∪ world_dom (m : WorldT)). set_solver.
  - intros τ1 τ2 [σ1 [Hσ1 ->]] [σ2 [Hσ2 ->]].
    rewrite !run_out, !secure_result, (Hagree σ1 σ2 Hσ1 Hσ2). reflexivity.
Qed.

(** A concrete pair follows opposite secret branches with the same low input.
    The first if leaks, whereas the complete program repairs that difference. *)
Definition input (h l : Z) : StoreT := {[high := h; low := l]}.
Definition opposite_inputs : WfWorldT.
Proof.
  refine (exist _ {| worldA_dom := {[high; low]};
    worldA_stores := fun σ => σ = input 1 3 \/ σ = input (-1) 3 |} _).
  split.
  - exists (input 1 3). left. reflexivity.
  - intros σ [-> | ->]; unfold input; rewrite dom_insert_L, dom_singleton_L; reflexivity.
Defined.

Example opposite_branches_secure :
  outputs secure opposite_inputs ⊨ FNoninterference low out.
Proof. apply secure_noninterference. reflexivity. Qed.

Example first_if_not_noninterfering :
  ~ (outputs first_if opposite_inputs ⊨ FNoninterference low out).
Proof.
  intros Hni. apply FNoninterference_spec in Hni; [|discriminate].
  destruct Hni as [_ Hrel].
  assert (Hpos : (outputs first_if opposite_inputs : WorldT) (run first_if (input 1 3))).
  { exists (input 1 3). split; [left|]; reflexivity. }
  assert (Hneg : (outputs first_if opposite_inputs : WorldT) (run first_if (input (-1) 3))).
  { exists (input (-1) 3). split; [right|]; reflexivity. }
  specialize (Hrel _ _ Hpos Hneg ltac:(vm_compute; reflexivity)).
  vm_compute in Hrel. discriminate.
Qed.

End HypraSecure.
