From ContextTypingExamples Require Import HypraSecureTyping.
From ContextLogicExamples Require Import HypraSecure.
From Stdlib Require Import List ZArith Lia.
Import ListNotations.

Module HypraSecureVC.
Import HypraSecure HypraSecureTyping.
Local Open Scope Z_scope.

(** A finite symbolic path summary.  Arithmetic guards are Props; validating
    these VCs is not claimed to decide arbitrary Rocq predicates. *)
Record path := Path {
  path_guard : Z -> Z -> Prop;
  path_result : Z -> Z -> Z
}.

Definition paths_sound (f : Z -> Z -> Z) (ps : list path) : Prop :=
  forall p, List.In p ps -> forall h l,
    path_guard p h l -> f h l = path_result p h l.
Definition paths_cover (ps : list path) : Prop :=
  forall h l, exists p, List.In p ps /\ path_guard p h l.

(** Self-composition: keep the same low input; do not equate secrets or
    require the two executions to follow the same branch. *)
Definition path_pair_vc (pq : path * path) : Prop :=
  forall h1 h2 l,
    path_guard (fst pq) h1 l -> path_guard (snd pq) h2 l ->
    path_result (fst pq) h1 l = path_result (snd pq) h2 l.

Definition vcgen (ps : list path) : list (path * path) :=
  List.flat_map (fun p => List.map (fun q => (p,q)) ps) ps.
Definition vcs_valid (ps : list path) : Prop :=
  forall pq, List.In pq (vcgen ps) -> path_pair_vc pq.

Lemma vcgen_member ps p q :
  List.In (p,q) (vcgen ps) <-> List.In p ps /\ List.In q ps.
Proof.
  unfold vcgen. rewrite List.in_flat_map. split.
  - intros [a [Ha Hpair]]. apply List.in_map_iff in Hpair.
    destruct Hpair as [b [Heq Hb]]. inversion Heq. subst. auto.
  - intros [Hp Hq]. exists p. split; [exact Hp|]. apply List.in_map. exact Hq.
Qed.

(** Soundness AND completeness for supplied exact finite path summaries. *)
Theorem vcgen_correct f ps :
  paths_sound f ps -> paths_cover ps ->
  (vcs_valid ps <-> ni_function_type f).
Proof.
  intros Hsound Hcover. rewrite ni_function_type_iff. split.
  - intros Hvc h1 h2 l.
    destruct (Hcover h1 l) as [p [Hp Hgp]].
    destruct (Hcover h2 l) as [q [Hq Hgq]].
    rewrite (Hsound p Hp h1 l Hgp), (Hsound q Hq h2 l Hgq).
    apply (Hvc (p,q)); [apply vcgen_member; auto|exact Hgp|exact Hgq].
  - intros Hni [p q] Hpair h1 h2 l Hgp Hgq.
    apply vcgen_member in Hpair as [Hp Hq]. cbn in *.
    rewrite <- (Hsound p Hp h1 l Hgp), <- (Hsound q Hq h2 l Hgq).
    apply Hni.
Qed.

(** Both original ifs: first tests h>0, second tests h<=0.
    Enumerating all four paths retains the two contradictory paths too. *)
Definition secure_path (first second : bool) : path :=
  Path
    (fun h _ => (if first then 0 < h else h <= 0) /\
                (if second then h <= 0 else 0 < h))
    (fun _ l => let o := if first then 2*l else l in
                if second then o+l else o).
Definition secure_paths : list path :=
  [secure_path true true; secure_path true false;
   secure_path false true; secure_path false false].

Lemma secure_paths_sound : paths_sound secure secure_paths.
Proof.
  intros p Hp h l Hg. simpl in Hp.
  destruct Hp as [Hp|[Hp|[Hp|[Hp|[]]]]]; subst p;
    cbn [secure_path path_guard path_result] in *;
    try lia;
    unfold secure, first_if; rewrite Z.gtb_ltb;
    destruct (Z.ltb 0 h) eqn:Hpos; destruct (Z.leb h 0) eqn:Hnonpos;
    try apply Z.ltb_lt in Hpos; try apply Z.ltb_ge in Hpos;
    try apply Z.leb_le in Hnonpos; try apply Z.leb_gt in Hnonpos; lia.
Qed.

Lemma secure_paths_cover : paths_cover secure_paths.
Proof.
  intros h l. destruct (Z_lt_ge_dec 0 h) as [Hpos|Hnonpos].
  - exists (secure_path true false). split.
    + unfold secure_paths. right. left. reflexivity.
    + cbn [secure_path path_guard]. split; lia.
  - exists (secure_path false true). split.
    + unfold secure_paths. right. right. left. reflexivity.
    + cbn [secure_path path_guard]. split; lia.
Qed.

Example secure_generates_sixteen_vcs : List.length (vcgen secure_paths) = 16%nat.
Proof. reflexivity. Qed.

Theorem secure_vcs_valid : vcs_valid secure_paths.
Proof.
  intros [p q] Hpq h1 h2 l Hgp Hgq.
  apply vcgen_member in Hpq as [Hp Hq]. simpl in Hp, Hq.
  destruct Hp as [Hp|[Hp|[Hp|[Hp|[]]]]]; subst p;
  destruct Hq as [Hq|[Hq|[Hq|[Hq|[]]]]]; subst q;
    cbn [secure_path path_guard path_result fst snd] in *; lia.
Qed.

Theorem secure_typed_via_vcs : ni_function_type secure.
Proof.
  apply (proj1 (vcgen_correct secure secure_paths secure_paths_sound secure_paths_cover)).
  exact secure_vcs_valid.
Qed.

(** The mixed-branch obligation is essential: neither branch by itself
    establishes agreement between executions following opposite branches. *)
Example secure_opposite_branches_vc :
  path_pair_vc (secure_path true false, secure_path false true).
Proof. intros h1 h2 l H1 H2. cbn. lia. Qed.

Definition first_if_path (positive : bool) : path :=
  Path (fun h _ => if positive then 0<h else h<=0)
       (fun _ l => if positive then 2*l else l).
Definition first_if_paths := [first_if_path true; first_if_path false].

Lemma first_if_paths_sound : paths_sound first_if first_if_paths.
Proof.
  intros p Hp h l Hg. simpl in Hp. destruct Hp as [Hp|[Hp|[]]]; subst p;
    cbn [first_if_path path_guard path_result] in *;
    unfold first_if; rewrite Z.gtb_ltb;
    destruct (Z.ltb 0 h) eqn:Htest;
    try apply Z.ltb_lt in Htest; try apply Z.ltb_ge in Htest; try lia; reflexivity.
Qed.

Lemma first_if_paths_cover : paths_cover first_if_paths.
Proof.
  intros h l. destruct (Z_lt_ge_dec 0 h) as [Hpos|Hnonpos].
  - exists (first_if_path true). split; [simpl; auto|exact Hpos].
  - exists (first_if_path false). split; [simpl; auto|]. cbn [first_if_path path_guard]. lia.
Qed.

Example first_if_vcs_rejected : ~ vcs_valid first_if_paths.
Proof.
  intros Hvc. apply first_if_rejected.
  apply (proj1 (vcgen_correct first_if first_if_paths
    first_if_paths_sound first_if_paths_cover)). exact Hvc.
Qed.

Example first_if_mixed_vc_counterexample :
  path_guard (first_if_path true) 1 3 /\
  path_guard (first_if_path false) (-1) 3 /\
  path_result (first_if_path true) 1 3 <>
    path_result (first_if_path false) (-1) 3.
Proof. cbn. lia. Qed.

End HypraSecureVC.
