From ContextQualifier Require Export Qualifier.

(** The qualifier-level dot of Fiber-Guided Support Refinement, Section 1.
    Declared observation support is data, even for a constant predicate. *)
Section SupportPadding.
Context {V : Type} `{ValueSig V}.

Lemma pad_incl (X D : lvset) : D ⊆ X ∪ D.
Proof. set_solver. Qed.

Definition qual_pad (X : lvset) (q : qualifier (V := V)) : qualifier :=
  tqual (X ∪ qual_vars q)
    (fun s => qual_prop q
      (lstore_on_restrict (qual_vars q) s (pad_incl X (qual_vars q)))).

Lemma qual_pad_vars X (q : qualifier (V := V)) :
  qual_vars (qual_pad X q) = X ∪ qual_vars q.
Proof. reflexivity. Qed.

Lemma qual_pad_empty (q : qualifier (V := V)) : qual_pad ∅ q = q.
Proof.
  apply qual_ext; [cbn [qual_pad qual_vars]; set_solver|].
  intros s1 s2 Heq. cbn [qual_pad].
  assert (Hs : lstore_on_restrict (qual_vars q) s1
      (pad_incl ∅ (qual_vars q)) = s2).
  { destruct s1 as [s1 Hd1], s2 as [s2 Hd2]. cbn in Heq.
    apply lstore_on_ext. change (storeA_restrict s1 (qual_vars q) = s2).
    rewrite Heq. apply storeA_map_eq. intros x. rewrite storeA_restrict_lookup.
    destruct decide as [Hx|Hx]; [reflexivity|].
    symmetry. apply not_elem_of_dom. rewrite Hd2. exact Hx. }
  change (qual_prop q (lstore_on_restrict (qual_vars q) s1
    (pad_incl ∅ (qual_vars q))) <-> qual_prop q s2).
  rewrite Hs. reflexivity.
Qed.

Lemma qual_pad_top X D :
  qual_pad X (qual_top_on (V := V) D) = qual_top_on (X ∪ D).
Proof. apply qual_ext; [reflexivity|]. intros; reflexivity. Qed.

End SupportPadding.
