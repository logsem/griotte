From iris.algebra Require Import gmap.
From iris.base_logic.lib Require Import gen_heap ghost_map mono_nat.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
From griotte Require Import addresses machine_word region_keys.

(** * The allocation registry

    Every allocation ever made gets an identifier [ι] (ghost only). The
    registry records its range and its lifecycle status, which only moves
    forward: [ALive → APainting → AQuar → ADead]. Entries are never removed
    and identifiers are never reused.

    - [alloc_obj ι b e] (persistent): [ι] covers [[b, e)].
    - [ι ↦st{q} s] (fractional, exact): [ι] is currently in state [s].
    - [ι ⊒ s] (persistent): [ι] has reached at least [s].
    - [reg_auth R]: the authority, holding the hidden half of every status. *)

Inductive AllocLifecycle := ALive | APainting | AQuar | ADead.

Global Instance alloc_lifecycle_eq_dec : EqDecision AllocLifecycle.
Proof. solve_decision. Defined.

Definition lifecycle_enc (s : AllocLifecycle) : nat :=
  match s with ALive => 0 | APainting => 1 | AQuar => 2 | ADead => 3 end.

Lemma lifecycle_enc_inj s s' : lifecycle_enc s = lifecycle_enc s' → s = s'.
Proof. by destruct s, s'. Qed.

(** The registry state: [ι ↦ (base, end, γι, status)]. *)
Definition RegState := gmap AId (Addr * Addr * gname * AllocLifecycle).

Definition reg_names (R : RegState) : gmap AId (Addr * Addr * gname) :=
  fst <$> R.

Class allocRegistryPreG Σ := {
  registry_ghost_mapG :: ghost_mapG Σ AId (Addr * Addr * gname);
  registry_mono_natG :: mono_natG Σ;
}.

Definition allocRegistryΣ : gFunctors :=
  #[ghost_mapΣ AId (Addr * Addr * gname); mono_natΣ].

Global Instance subG_allocRegistryΣ {Σ} :
  subG allocRegistryΣ Σ → allocRegistryPreG Σ.
Proof. solve_inG. Qed.

Class allocRegistryG Σ := {
  registry_preG :: allocRegistryPreG Σ;
  registry_name : gname;
}.

(** [share n] is the fraction of a status token held by each of the [n] cells
    of an allocation, and by the allocator. Together with the client half,
    [1/2 + (n+1) · share n = 1]. *)
Definition share (n : nat) : Qp := (/ (2 * pos_to_Qp (Pos.of_succ_nat n)))%Qp.

Lemma share_sum n : (1/2 + pos_to_Qp (Pos.of_succ_nat n) * share n = 1)%Qp.
Proof.
  rewrite /share Qp.inv_mul_distr Qp.mul_assoc (Qp.mul_comm _ (/2)%Qp)
    -Qp.mul_assoc Qp.mul_inv_r Qp.mul_1_r.
  assert ((/2)%Qp = (1/2)%Qp) as -> by (by rewrite /Qp.div Qp.mul_1_l).
  apply Qp.half_half.
Qed.

Section registry.
  Context `{!allocRegistryG Σ}.

  Definition alloc_obj (ι : AId) (b e : Addr) : iProp Σ :=
    ∃ γ, ι ↪[registry_name]□ (b, e, γ).

  Definition st_own (ι : AId) (q : Qp) (s : AllocLifecycle) : iProp Σ :=
    ∃ b e γ, ι ↪[registry_name]□ (b, e, γ) ∗
             mono_nat_auth_own γ (q / 2) (lifecycle_enc s).

  Definition st_lb (ι : AId) (s : AllocLifecycle) : iProp Σ :=
    ∃ b e γ, ι ↪[registry_name]□ (b, e, γ) ∗ mono_nat_lb_own γ (lifecycle_enc s).

  Definition reg_auth (R : RegState) : iProp Σ :=
    ghost_map_auth registry_name 1 (reg_names R) ∗
    [∗ map] ι ↦ x ∈ R, mono_nat_auth_own x.1.2 (1/2) (lifecycle_enc x.2).

End registry.

Notation "ι ↦st{ q } s" := (st_own ι q s)
  (at level 20, q at level 50, format "ι  ↦st{ q }  s") : bi_scope.
Notation "ι ⊒ s" := (st_lb ι s) (at level 20) : bi_scope.

Section registry_lemmas.
  Context `{!allocRegistryG Σ}.

  Global Instance alloc_obj_persistent ι b e : Persistent (alloc_obj ι b e).
  Proof. apply _. Qed.
  Global Instance alloc_obj_timeless ι b e : Timeless (alloc_obj ι b e).
  Proof. apply _. Qed.
  Global Instance st_lb_persistent ι s : Persistent (ι ⊒ s).
  Proof. apply _. Qed.
  Global Instance st_lb_timeless ι s : Timeless (ι ⊒ s).
  Proof. apply _. Qed.
  Global Instance st_own_timeless ι q s : Timeless (ι ↦st{q} s).
  Proof. apply _. Qed.
  Global Instance reg_auth_timeless R : Timeless (reg_auth R).
  Proof. apply _. Qed.

  Global Instance st_own_fractional ι s : Fractional (λ q, ι ↦st{q} s)%I.
  Proof.
    intros q1 q2. iSplit.
    - iIntros "(%b & %e & %γ & #H & A)". rewrite Qp.div_add_distr.
      iDestruct "A" as "[A1 A2]". iSplitL "A1"; iExists b, e, γ; iFrame "#∗".
    - iIntros "[(%b & %e & %γ & #H & A1) (%b' & %e' & %γ' & #H' & A2)]".
      iDestruct (ghost_map_elem_agree with "H H'") as %Heq. simplify_eq.
      iExists b', e', γ'. iFrame "#". rewrite Qp.div_add_distr.
      iCombine "A1 A2" as "A". iFrame.
  Qed.

  Global Instance st_own_as_fractional ι q s :
    AsFractional (ι ↦st{q} s) (λ q, ι ↦st{q} s)%I q.
  Proof. split; [done | apply _]. Qed.

  Lemma alloc_obj_agree ι b e b' e' :
    alloc_obj ι b e -∗ alloc_obj ι b' e' -∗ ⌜b = b' ∧ e = e'⌝.
  Proof.
    iIntros "(%γ & H) (%γ' & H')".
    by iDestruct (ghost_map_elem_agree with "H H'") as %[=].
  Qed.

  Lemma st_own_alloc_obj ι q s :
    ι ↦st{q} s -∗ ∃ b e, alloc_obj ι b e.
  Proof. iIntros "(%b & %e & %γ & #H & _)". iExists b, e, γ. iFrame "H". Qed.

  Lemma st_lb_alloc_obj ι s :
    ι ⊒ s -∗ ∃ b e, alloc_obj ι b e.
  Proof. iIntros "(%b & %e & %γ & #H & _)". iExists b, e, γ. iFrame "H". Qed.

  Lemma st_own_valid_2 ι q1 q2 s1 s2 :
    ι ↦st{q1} s1 -∗ ι ↦st{q2} s2 -∗ ⌜s1 = s2⌝.
  Proof.
    iIntros "(%b & %e & %γ & #H & A) (%b' & %e' & %γ' & #H' & B)".
    iDestruct (ghost_map_elem_agree with "H H'") as %Heq. simplify_eq.
    iDestruct (mono_nat_auth_own_agree with "A B") as %[_ Hs].
    iPureIntro. by apply lifecycle_enc_inj.
  Qed.

  Lemma st_lb_get ι q s : ι ↦st{q} s -∗ ι ⊒ s.
  Proof.
    iIntros "(%b & %e & %γ & #H & A)".
    iDestruct (mono_nat_lb_own_get with "A") as "#L".
    iExists b, e, γ. iFrame "#".
  Qed.

  Lemma st_lb_mono ι s s' :
    lifecycle_enc s' ≤ lifecycle_enc s → ι ⊒ s -∗ ι ⊒ s'.
  Proof.
    iIntros (Hle) "(%b & %e & %γ & #H & #L)".
    iExists b, e, γ. iFrame "H". by iApply mono_nat_lb_own_le.
  Qed.

  (** A live share and a quarantine witness are contradictory, for any
      fraction: the witness says the status is at least [AQuar]. *)
  Lemma live_quar_false ι q : ι ↦st{q} ALive -∗ ι ⊒ AQuar -∗ False.
  Proof.
    iIntros "(%b & %e & %γ & #H & A) (%b' & %e' & %γ' & #H' & L)".
    iDestruct (ghost_map_elem_agree with "H H'") as %Heq. simplify_eq.
    iDestruct (mono_nat_lb_own_valid with "A L") as %[_ Hle]. simpl in Hle. lia.
  Qed.

  Lemma st_own_rep {A} ι s q (l : list A) :
    ι ↦st{q} s ∗ ([∗ list] _ ∈ l, ι ↦st{q} s) ⊣⊢
    ι ↦st{pos_to_Qp (Pos.of_succ_nat (length l)) * q} s.
  Proof.
    induction l as [|x l IH]; simpl.
    - rewrite Qp.mul_1_l. iSplit; [iIntros "[$ _]" | iIntros "$"].
    - rewrite -Pos.add_1_r -pos_to_Qp_add Qp.mul_add_distr_r Qp.mul_1_l
        (st_own_fractional ι s) -IH.
      iSplit; [iIntros "($ & $ & $)" | iIntros "[($ & $) $]"].
  Qed.

  (** The split at allocation and, read right to left, the summation in [free]:
      the client half, the allocator's share, and one share per element of [l]. *)
  Lemma st_own_split_alloc {A} ι (l : list A) :
    ι ↦st{1} ALive ⊣⊢
    ι ↦st{1/2} ALive ∗
    ι ↦st{share (length l)} ALive ∗
    [∗ list] _ ∈ l, ι ↦st{share (length l)} ALive.
  Proof. rewrite st_own_rep -(st_own_fractional ι ALive) share_sum //. Qed.

  (** ** The authority *)

  Lemma reg_lookup_own R ι q s :
    reg_auth R -∗ ι ↦st{q} s -∗
    ⌜∃ b e γ, R !! ι = Some (b, e, γ, s)⌝.
  Proof.
    iIntros "[Hmap Hauths] (%b & %e & %γ & #H & A)".
    iDestruct (ghost_map_lookup with "Hmap H") as %Hlookup.
    rewrite /reg_names lookup_fmap in Hlookup.
    apply fmap_Some in Hlookup as ([[[b' e'] γ'] s'] & HR & Heq).
    simplify_eq/=.
    iDestruct (big_sepM_lookup with "Hauths") as "Ha"; first exact HR.
    iDestruct (mono_nat_auth_own_agree with "Ha A") as %[_ Hs].
    apply lifecycle_enc_inj in Hs. subst. eauto.
  Qed.

  Lemma reg_lookup_lb R ι s :
    reg_auth R -∗ ι ⊒ s -∗
    ⌜∃ b e γ s', R !! ι = Some (b, e, γ, s') ∧ lifecycle_enc s ≤ lifecycle_enc s'⌝.
  Proof.
    iIntros "[Hmap Hauths] (%b & %e & %γ & #H & L)".
    iDestruct (ghost_map_lookup with "Hmap H") as %Hlookup.
    rewrite /reg_names lookup_fmap in Hlookup.
    apply fmap_Some in Hlookup as ([[[b' e'] γ'] s'] & HR & Heq).
    simplify_eq/=.
    iDestruct (big_sepM_lookup with "Hauths") as "Ha"; first exact HR.
    iDestruct (mono_nat_lb_own_valid with "Ha L") as %[_ Hle].
    eauto 10.
  Qed.

  Lemma reg_lookup_obj R ι b e :
    reg_auth R -∗ alloc_obj ι b e -∗
    ⌜∃ γ s, R !! ι = Some (b, e, γ, s)⌝.
  Proof.
    iIntros "[Hmap _] (%γ & #H)".
    iDestruct (ghost_map_lookup with "Hmap H") as %Hlookup.
    rewrite /reg_names lookup_fmap in Hlookup.
    apply fmap_Some in Hlookup as ([[[b' e'] γ'] s'] & HR & Heq).
    simplify_eq/=. eauto.
  Qed.

  Lemma reg_lookup_lb_obj R ι s b e :
    reg_auth R -∗ ι ⊒ s -∗ alloc_obj ι b e -∗
    ⌜∃ γ s', R !! ι = Some (b, e, γ, s') ∧ lifecycle_enc s ≤ lifecycle_enc s'⌝.
  Proof.
    iIntros "HR #Hlb #Hobj".
    iDestruct (reg_lookup_lb with "HR Hlb") as %(b' & e' & γ & s' & Hlookup & Hle).
    iDestruct (reg_lookup_obj with "HR Hobj") as %(γ' & s'' & Hlookup').
    rewrite Hlookup in Hlookup'. simplify_eq. eauto.
  Qed.

  (** The generic transition: the full token moves forward. *)
  Lemma reg_step R ι b e γ s s' :
    R !! ι = Some (b, e, γ, s) →
    lifecycle_enc s ≤ lifecycle_enc s' →
    reg_auth R -∗ ι ↦st{1} s ==∗
    reg_auth (<[ι := (b, e, γ, s')]> R) ∗ ι ↦st{1} s'.
  Proof.
    iIntros (HR Hle) "[Hmap Hauths] (%b' & %e' & %γ' & #H & A)".
    iDestruct (ghost_map_lookup with "Hmap H") as %Hlookup.
    rewrite /reg_names lookup_fmap HR in Hlookup. simplify_eq/=.
    iDestruct (big_sepM_insert_acc with "Hauths") as "[Ha Hclose]"; first exact HR.
    iCombine "Ha A" as "A".
    iMod (mono_nat_own_update (lifecycle_enc s') with "A") as "[A _]"; first done.
    iEval (rewrite -Qp.half_half) in "A". iDestruct "A" as "[A1 A2]".
    iModIntro. iSplitR "A2".
    - iSplitL "Hmap".
      + rewrite /reg_names fmap_insert /= insert_id; first iFrame.
        rewrite lookup_fmap HR //.
      + iApply ("Hclose" $! (b', e', γ', s')). iFrame.
    - iExists b', e', γ'. iFrame "∗#".
  Qed.

  (** Allocating a new identifier. *)
  Lemma reg_alloc R ι b e :
    R !! ι = None →
    reg_auth R ==∗
    ∃ γ, reg_auth (<[ι := (b, e, γ, ALive)]> R) ∗ alloc_obj ι b e ∗ ι ↦st{1} ALive.
  Proof.
    iIntros (HR) "[Hmap Hauths]".
    iMod (mono_nat_own_alloc (lifecycle_enc ALive)) as (γ) "[A _]".
    iMod (ghost_map_insert_persist ι (b, e, γ) with "Hmap") as "[Hmap #H]".
    { rewrite /reg_names lookup_fmap HR //. }
    iEval (rewrite -Qp.half_half) in "A". iDestruct "A" as "[A1 A2]".
    iModIntro. iExists γ. iSplitR "A2".
    - iSplitL "Hmap".
      + rewrite /reg_names fmap_insert //.
      + rewrite big_sepM_insert //. iFrame.
    - iSplit; first (iExists γ; iFrame "H").
      iExists b, e, γ. iFrame "∗#".
  Qed.

  Lemma reg_lookup_None R ι b e :
    reg_auth R -∗ alloc_obj ι b e -∗ ⌜R !! ι ≠ None⌝.
  Proof.
    iIntros "HR Hobj".
    iDestruct (reg_lookup_obj with "HR Hobj") as %(γ & s & Hlookup).
    by rewrite Hlookup.
  Qed.

End registry_lemmas.

Lemma registry_init `{!allocRegistryPreG Σ} :
  ⊢ |==> ∃ (rg : allocRegistryG Σ), reg_auth (Σ := Σ) ∅.
Proof.
  iMod (ghost_map_alloc_empty (K := AId) (V := (Addr * Addr * gname)%type))
    as (γ) "Hmap".
  iModIntro. iExists {| registry_name := γ |}.
  rewrite /reg_auth /reg_names fmap_empty big_sepM_empty. by iFrame.
Qed.

(** * The client half of the status token (D35)

    While [ι] is live, half of its status token is split by an instance of
    [FreeAuth] into the part kept by the allocator and the part held by the
    client that may free [ι]. The allocator only uses the split law. *)
Class FreeAuth (Σ : gFunctors) `{!allocRegistryG Σ} := {
  free_auth_kept : AId → iProp Σ;
  free_auth_held : AId → iProp Σ;
  free_auth_kept_timeless ι :: Timeless (free_auth_kept ι);
  free_auth_held_timeless ι :: Timeless (free_auth_held ι);
  free_auth_split ι : free_auth_kept ι ∗ free_auth_held ι ⊣⊢ ι ↦st{1/2} ALive;
}.

(** * Heap-cell points-to (D17)

    A heap cell of [ι] carries one share of [ι]'s status token, with the range
    of [ι]. The region machinery uses the same atom over region keys,
    [k ↦ₖ v]: on a non-heap key it is the plain points-to. *)
Section heap_pointsto.
  Context `{!allocRegistryG Σ, !gen_heapGS Addr Word Σ}.

  Definition key_share (k : LAddr) : iProp Σ :=
    match k with
    | LNonHeap _ => emp
    | LHeap a ι =>
        ∃ b e, ⌜(b <= a < e)%a⌝ ∗ alloc_obj ι b e ∗ ι ↦st{share (finz.dist b e)} ALive
    end%I.

  Definition key_pointsto (k : LAddr) (v : Word) : iProp Σ :=
    match k with
    | LNonHeap a => pointsto (L:=Addr) (V:=Word) a (DfracOwn 1) v
    | LHeap a ι => pointsto (L:=Addr) (V:=Word) a (DfracOwn 1) v ∗ key_share (LHeap a ι)
    end%I.

  Global Instance key_share_timeless k : Timeless (key_share k).
  Proof. destruct k; apply _. Qed.
  Global Instance key_pointsto_timeless k v : Timeless (key_pointsto k v).
  Proof. destruct k; apply _. Qed.

End heap_pointsto.

Notation "k ↦ₖ v" := (key_pointsto k v) (at level 20) : bi_scope.
Notation "a ↦ₕ[ ι ] v" := (key_pointsto (LHeap a ι) v)
  (at level 20, format "a  ↦ₕ[ ι ]  v") : bi_scope.

Section heap_pointsto_lemmas.
  Context `{!allocRegistryG Σ, !gen_heapGS Addr Word Σ}.

  Definition heap_region_pointsto (ι : AId) (b e : Addr) (ws : list Word) : iProp Σ :=
    [∗ list] a;w ∈ finz.seq_between b e; ws, a ↦ₕ[ι] w.

  Lemma key_pointsto_eq k v :
    k ↦ₖ v ⊣⊢ pointsto (L:=Addr) (V:=Word) (laddr_addr k) (DfracOwn 1) v ∗ key_share k.
  Proof. destruct k; simpl; [by rewrite right_id | done]. Qed.

  Lemma key_pointsto_nonheap a v :
    LNonHeap a ↦ₖ v ⊣⊢ pointsto (L:=Addr) (V:=Word) a (DfracOwn 1) v.
  Proof. done. Qed.

  Lemma heap_pointsto_valid_2 k k' v v' :
    laddr_addr k = laddr_addr k' → k ↦ₖ v -∗ k' ↦ₖ v' -∗ False.
  Proof.
    iIntros (Heq) "H H'". rewrite !key_pointsto_eq Heq.
    iDestruct "H" as "[H _]". iDestruct "H'" as "[H' _]".
    iDestruct (pointsto_valid_2 with "H H'") as %[Hv _]. done.
  Qed.

  (** The share of a cell is live: it refutes a quarantine witness. *)
  Lemma heap_pointsto_quar_false a ι v :
    a ↦ₕ[ι] v -∗ ι ⊒ AQuar -∗ False.
  Proof.
    iIntros "[_ (%b & %e & _ & _ & Hs)] Hq".
    iApply (live_quar_false with "Hs Hq").
  Qed.

  Lemma heap_pointsto_alloc_obj a ι v b e :
    alloc_obj ι b e -∗ a ↦ₕ[ι] v -∗ ⌜(b <= a < e)%a⌝.
  Proof.
    iIntros "Hobj [_ (%b' & %e' & %Hin & Hobj' & _)]".
    by iDestruct (alloc_obj_agree with "Hobj Hobj'") as %[-> ->].
  Qed.

  Lemma heap_pointsto_split a ι v b e :
    alloc_obj ι b e -∗
    a ↦ₕ[ι] v -∗
    pointsto (L:=Addr) (V:=Word) a (DfracOwn 1) v ∗
    ι ↦st{share (finz.dist b e)} ALive.
  Proof.
    iIntros "Hobj [$ (%b' & %e' & %Hin & Hobj' & Hs)]".
    by iDestruct (alloc_obj_agree with "Hobj Hobj'") as %[-> ->].
  Qed.

  (** A whole allocation's cells, split into memory and shares, and back. *)
  Lemma heap_region_pointsto_split ι b e ws :
    alloc_obj ι b e -∗
    heap_region_pointsto ι b e ws ∗-∗
    ([∗ list] a;w ∈ finz.seq_between b e; ws, pointsto (L:=Addr) (V:=Word) a (DfracOwn 1) w) ∗
    ([∗ list] _ ∈ finz.seq_between b e, ι ↦st{share (finz.dist b e)} ALive).
  Proof.
    iIntros "#Hobj". rewrite /heap_region_pointsto.
    iSplit.
    - iIntros "H".
      iAssert ([∗ list] a;w ∈ finz.seq_between b e; ws,
        pointsto (L:=Addr) (V:=Word) a (DfracOwn 1) w ∗
        ι ↦st{share (finz.dist b e)} ALive)%I with "[H]" as "H".
      { iApply (big_sepL2_impl with "H"). iIntros "!>" (k a w _ _) "Ha".
        iApply (heap_pointsto_split with "Hobj Ha"). }
      rewrite big_sepL2_sep big_sepL2_const_sepL_l. iDestruct "H" as "[$ [_ $]]".
    - iIntros "[Hmem Hs]".
      iDestruct (big_sepL2_length with "Hmem") as %Hlen.
      iAssert ([∗ list] a;w ∈ finz.seq_between b e; ws,
        pointsto (L:=Addr) (V:=Word) a (DfracOwn 1) w ∗
        ι ↦st{share (finz.dist b e)} ALive)%I with "[Hmem Hs]" as "H".
      { rewrite big_sepL2_sep big_sepL2_const_sepL_l. iFrame. done. }
      iApply (big_sepL2_impl with "H"). iIntros "!>" (k a w Ha _) "[Ha Hs]".
      iFrame "Ha". iExists b, e. iFrame "Hobj Hs". iPureIntro.
      apply elem_of_finz_seq_between. by eapply list_elem_of_lookup_2.
  Qed.

End heap_pointsto_lemmas.

(* The notation [[[b, e]] ↦ₕ[ι] [[ws]]] is in [memory_region]. *)
