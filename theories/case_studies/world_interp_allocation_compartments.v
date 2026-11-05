From iris.proofmode Require Import proofmode.
From griotte Require Export world_interp sts_multiple_updates.
From griotte Require Import logrel monotone interp_weakening.
From griotte Require Import compartment_layout mkregion_helpers disjoint_regions_tactics.
From griotte Require Import switcher_link.
From griotte Require Import world_ghost_theory world_interp_allocation.
From griotte Require Import stdpp_extra.

Section perm_extend.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Σ}
    {relg : relGS Σ}
    `{MP: MachineParameters}
    {th : Thread}
  .
  Notation Vg := (CmptName * LWord → iProp Σ).

  (* TODO: move to model/world_ghost_theory.v *)
  (** [world_interp_extend_perm_sepL2] on the map of Permanent regions alone. *)
  Lemma perm_extend_sepL2 {E : coPset} (C : CmptName) (la : list Addr) (lw : list LWord)
      (p : Perm) (φ : Vg) `{∀ Cv, Persistent (φ Cv)} :
    perm_region_map C ∅ -∗
    ([∗ list] a;v ∈ la;lw, PermRes C (LNonHeap a) p φ v)
    ={E}=∗
    perm_region_map C ∅ ∗
    ([∗ list] k ∈ la, LNonHeap k ↪ᵖ[C]{p} φ).
  Proof.
    revert lw. induction la as [|a la IH]; iIntros (lw) "Hm Hl".
    - iModIntro. by iFrame.
    - iDestruct (big_sepL2_cons_inv_l with "Hl") as (v lw' ->) "[(%HpO & Ha & Hφ) Hl]".
      iDestruct (key_pointsto_known with "Ha") as "#Hkn".
      iMod (perm_extend with "Hm Hkn Ha [Hφ]") as "[Hm $]"; [set_solver|done|by iNext|].
      iApply (IH with "Hm Hl").
  Qed.

  (* TODO: move to model/world_ghost_theory.v *)
  (** [world_interp_extend_perm_sepL2_open] on the map of Permanent regions
      alone. *)
  Lemma perm_extend_sepL2_open {E : coPset} (C : CmptName) (la : list Addr) (lw : list LWord)
      (p : Perm) (φ : Vg) `{∀ Cv, Persistent (φ Cv)} :
    NoDup la →
    isO p = false →
    perm_region_map C ∅ -∗
    ([∗ list] k;v ∈ la;lw, k ↦ₐ v) -∗
    (([∗ list] k ∈ la, LNonHeap k ↪ᵖ[C]{p} φ) -∗ ([∗ list] v ∈ lw, φ (C, v)))
    ={E}=∗
    perm_region_map C ∅ ∗
    ([∗ list] k ∈ la, LNonHeap k ↪ᵖ[C]{p} φ) ∗
    ([∗ list] v ∈ lw, φ (C, v)).
  Proof.
    iIntros (Hnd HpO) "(%M & Hm) Hcells Hφ".
    assert (NoDup (LNonHeap <$> la)) as Hnd'.
    { apply NoDup_fmap; [intros ?? [= ->]; done|done]. }
    iMod (perm_insert_open_list C M ∅ (LNonHeap <$> la) lw p φ with "Hm [Hcells]")
      as (M') "(Hm & #Hrels & Hcells)"; [done|set_solver|by rewrite big_sepL2_fmap_l|].
    iDestruct ("Hφ" with "[]") as "#Hφs"; [by rewrite big_sepL_fmap|].
    iModIntro. rewrite big_sepL_fmap. iFrame "Hrels Hφs".
    iExists M'. iApply (perm_close_list with "Hm [Hcells]"); [done|set_solver|done|done|].
    iDestruct (big_sepL2_length with "Hcells") as %Hlen.
    iApply (big_sepL2_impl with "Hcells"). iIntros "!>" (i k v Hk Hv) "Hc".
    iFrame "Hc". apply list_lookup_fmap_Some in Hk as (a & -> & Ha). iSplitR.
    - iNext. by iApply (big_sepL_lookup with "Hφs").
    - by iApply (big_sepL_lookup with "Hrels").
  Qed.

  (* TODO: move to model/world_ghost_theory.v *)
  (** [world_interp_extend_perm_sepL2_open_frame] on the map of Permanent
      regions alone. *)
  Lemma perm_extend_sepL2_open_frame {E : coPset} (C : CmptName) (la : list Addr)
      (lw : list LWord) (p : Perm) (φ : Vg) (R : iProp Σ) `{∀ Cv, Persistent (φ Cv)} :
    NoDup la →
    isO p = false →
    perm_region_map C ∅ -∗
    ([∗ list] k;v ∈ la;lw, k ↦ₐ v) -∗
    (([∗ list] k ∈ la, LNonHeap k ↪ᵖ[C]{p} φ) -∗ ([∗ list] v ∈ lw, φ (C, v)) ∗ R)
    ={E}=∗
    perm_region_map C ∅ ∗
    ([∗ list] k ∈ la, LNonHeap k ↪ᵖ[C]{p} φ) ∗
    ([∗ list] v ∈ lw, φ (C, v)) ∗
    R.
  Proof.
    iIntros (Hnd HpO) "(%M & Hm) Hcells Hφ".
    assert (NoDup (LNonHeap <$> la)) as Hnd'.
    { apply NoDup_fmap; [intros ?? [= ->]; done|done]. }
    iMod (perm_insert_open_list C M ∅ (LNonHeap <$> la) lw p φ with "Hm [Hcells]")
      as (M') "(Hm & #Hrels & Hcells)"; [done|set_solver|by rewrite big_sepL2_fmap_l|].
    iDestruct ("Hφ" with "[]") as "[#Hφs HR]"; [by rewrite big_sepL_fmap|].
    iModIntro. rewrite big_sepL_fmap. iFrame "Hrels Hφs HR".
    iExists M'. iApply (perm_close_list with "Hm [Hcells]"); [done|set_solver|done|done|].
    iDestruct (big_sepL2_length with "Hcells") as %Hlen.
    iApply (big_sepL2_impl with "Hcells"). iIntros "!>" (i k v Hk Hv) "Hc".
    iFrame "Hc". apply list_lookup_fmap_Some in Hk as (a & -> & Ha). iSplitR.
    - iNext. by iApply (big_sepL_lookup with "Hφs").
    - by iApply (big_sepL_lookup with "Hrels").
  Qed.
End perm_extend.

Section local_extend.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Σ}
    {relg : relGS Σ}
    `{MP: MachineParameters}
    {th : Thread}
  .
  Notation Vc := (WORLD * CmptName * LWord → iProp Σ).

  (* TODO: move to model/world_ghost_theory.v *)
  (** [world_interp_extend_temp] on the local map of [th] alone: the map of
      Permanent regions is not touched. *)
  Lemma local_extend_temp {E : coPset}
      (W : WORLD) (C : CmptName) (a : LAddr) (v : LWord) (p : Perm) (φ : Vc)
      `{∀ Wv, Persistent (φ Wv)} :
    a ∉ dom (std W) →
    local_region_map th W C ∅ -∗
    TmpRes W C a p φ v
    ={E}=∗
    local_region_map th (<s[a := Temporary ]s>W) C ∅ ∗
    a ↪ˡ[C]{p} φ.
  Proof.
    iIntros (Hfresh) "Hl (%HpO & Ha & Hφ & #Hmono)".
    iDestruct (key_pointsto_known with "Ha") as "#Hkn".
    iMod (l_extend th W C ∅ a Temporary p φ with "Hl Hkn [Ha Hφ]") as "[Hl Hr]";
      [done|set_solver| |by iFrame "Hl Hr"].
    rewrite /body_l /std_update /= lookup_insert_eq.
    iApply heap_key_resource_intro. iExists v. rewrite /TmpRes. iFrame "∗#%".
    iNext. iApply ("Hmono" with "[] Hφ"). iPureIntro. by apply related_sts_pub_world_fresh.
  Qed.

  (* TODO: move to model/world_ghost_theory.v *)
  (** [world_interp_extend_temp_sepL2] on the local map of [th] alone. *)
  Lemma local_extend_temp_sepL2 {E : coPset}
      (W : WORLD) (C : CmptName) (la : list Addr) (lw : list LWord) (p : Perm) (φ : Vc)
      `{∀ Wv, Persistent (φ Wv)} :
    isO p = false →
    Forall (λ k, std W !! LNonHeap k = None) la →
    local_region_map th W C ∅ -∗
    ([∗ list] a;v ∈ la;lw, TmpRes W C (LNonHeap a) p φ v)
    ={E}=∗
    local_region_map th (std_update_multiple W la Temporary) C ∅ ∗
    ([∗ list] k ∈ la, LNonHeap k ↪ˡ[C]{p} φ).
  Proof.
    revert lw. induction la as [|a la IH]; iIntros (lw HpO Hnone) "Hl Hres".
    - iModIntro. by iFrame.
    - iDestruct (big_sepL2_cons_inv_l with "Hres") as (v lw' ->) "[Ha Hres]".
      apply Forall_cons in Hnone as [Ha Hnone].
      destruct (decide (a ∈ la)) as [Hin|Hnin].
      { iExFalso. iDestruct "Ha" as "(_ & Ha & _)".
        iApply (sepL2_TmpRes_not_elem_of with "Ha Hres"). done. }
      iMod (IH with "Hl Hres") as "[Hl $]"; [done..|].
      assert (Forall (λ a, LNonHeap a ∉ dom (std W)) la) as Hnone2.
      { eapply Forall_impl; [exact Hnone|]. intros a' Ha'. by rewrite not_elem_of_dom. }
      iDestruct "Ha" as "(_ & Ha & Hφ & #Hmono)".
      iApply (local_extend_temp with "Hl [Ha Hφ]").
      { intros [Hin|Hdom]%elem_of_dom_std_multiple_update; [done|].
        rewrite elem_of_dom_std Ha in Hdom. by destruct Hdom. }
      rewrite /TmpRes. iFrame "Ha #%". iNext. iApply ("Hmono" with "[] Hφ"). iPureIntro.
      by apply related_sts_pub_update_multiple.
  Qed.

  (* TODO: move to model/world_ghost_theory.v *)
  (** [world_interp_extend_revoked] on the local map of [th] alone. *)
  Lemma local_extend_revoked {E : coPset}
      (W : WORLD) (C : CmptName) (a : LAddr) (p : Perm) (φ : Vc)
      `{∀ Wv, Persistent (φ Wv)} :
    a ∉ dom (std W) →
    heap_key_known a -∗
    local_region_map th W C ∅
    ={E}=∗
    local_region_map th (<s[a := Revoked ]s>W) C ∅ ∗
    a ↪ˡ[C]{p} φ.
  Proof.
    iIntros (Hfresh) "#Hkn Hl".
    iMod (l_extend th W C ∅ a Revoked p φ with "Hl Hkn []") as "[Hl Hr]";
      [done|set_solver| |by iFrame "Hl Hr"].
    by rewrite /body_l /std_update /= lookup_insert_eq.
  Qed.

  (* TODO: move to model/world_ghost_theory.v *)
  (** [world_interp_extend_revoked_sepL2] on the local map of [th] alone. *)
  Lemma local_extend_revoked_sepL2 {E : coPset}
      (W : WORLD) (C : CmptName) (la : list Addr) (p : Perm) (φ : Vc)
      `{∀ Wv, Persistent (φ Wv)} :
    Forall (λ k, std W !! LNonHeap k = None) la →
    local_region_map th W C ∅
    ={E}=∗
    local_region_map th (std_update_multiple W la Revoked) C ∅ ∗
    ([∗ list] k ∈ la, LNonHeap k ↪ˡ[C]{p} φ).
  Proof.
    induction la as [|a la IH]; iIntros (Hnone) "Hl".
    - iModIntro. by iFrame.
    - apply Forall_cons in Hnone as [Ha Hnone].
      iMod (IH with "Hl") as "[Hl #Hrels]"; [done|].
      destruct (decide (a ∈ la)) as [Hin|Hnin].
      + iModIntro. rewrite /= /std_update insert_id.
        2:{ by apply std_sta_update_multiple_lookup_in_i. }
        destruct (std_update_multiple W la Revoked). iFrame "Hl Hrels".
        by iApply (big_sepL_elem_of with "Hrels").
      + iMod (local_extend_revoked with "[] Hl") as "[$ $]"; [|done|done].
        intros [Hin|Hdom]%elem_of_dom_std_multiple_update; [done|].
        rewrite elem_of_dom_std Ha in Hdom. by destruct Hdom.
  Qed.
End local_extend.

Section region_alloc_cmpt.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    {cthreads : CmptThreads}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .
  #[local] Notation V := (interpO Σ).

  Definition exported_entries_sealable (C_cmpt : cmpt) : list Sealable :=
    let export_tbl_addrs := finz.seq_between (cmpt_exp_tbl_entries_start C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt) in
    let exported_word g a := (SCap true RO g (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt) a) in
    ((exported_word Global) <$> export_tbl_addrs) ++ ((exported_word Local) <$> export_tbl_addrs).

  Definition exported_entries_words (C_cmpt : cmpt) : gset LWord :=
    list_to_set ((λ sb, lword_of_word (WSealable sb)) <$> (exported_entries_sealable C_cmpt)).
  Definition exported_entries_sealed (C_cmpt : cmpt) : gset LWord :=
    list_to_set ((λ sb, lword_of_word (WSealed ot_switcher sb)) <$> (exported_entries_sealable C_cmpt)).

  (** The PCC and CGP of a compartment are valid in every world and at
      every thread, from the Permanent regions of their addresses. *)
  Lemma cmpt_caps_interp (W : WORLD) (C_cmpt : cmpt) (C : CmptName) :
    let imports_addrs := finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_a_code C_cmpt) in
    let code_addrs := finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt) in
    let data_addrs := finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) in
    let pcc_cap := (Cap RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_b_pcc C_cmpt)%a) in
    let cgp_cap := (Cap RW Global (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) (cmpt_b_cgp C_cmpt)%a) in
    ([∗ list] k ∈ (imports_addrs++code_addrs), LNonHeap k ↪ᵖ[C]{RX} safeGC interp_cmpt_threads) -∗
    ([∗ list] k ∈ data_addrs, LNonHeap k ↪ᵖ[C]{RW} safeGC interp_nonlocal) -∗
    interp W C pcc_cap ∗ interp W C cgp_cap.
  Proof.
    intros *.
    pose proof (cmpt_pcc_disjoint_from_mmio C_cmpt) as Hpcc_shadow.
    pose proof (cmpt_pcc_disjoint_from_heap C_cmpt) as Hpcc_heap.
    pose proof (cmpt_cgp_disjoint_from_mmio C_cmpt) as Hcgp_shadow.
    pose proof (cmpt_cgp_disjoint_from_heap C_cmpt) as Hcgp_heap.
    iIntros "#Hrel_pcc #Hrel_data".
    iSplit.
    - iEval (rewrite interp_unfold /=). iLeft.
      iSplitR; last (iSplit; [iPureIntro; exact Hpcc_shadow|iApply heap_cap_ok_disjoint; exact Hpcc_heap]).
      iApply big_sepL_intro; iModIntro.
      iIntros (ka a Ha).
      rewrite /addr_key.
      iExists RX, interp_cmpt_threads.
      iEval (cbn).
      iSplit; first done.
      iSplit; first (iPureIntro ; by apply persistent_cond_interp_cmpt_threads).
      iSplit.
      { apply list_elem_of_lookup_2 in Ha.
        iApply (big_sepL_elem_of with "Hrel_pcc"); eauto.
        rewrite -finz_seq_between_split;auto.
        pose proof (cmpt_import_size C_cmpt) as HC.
        pose proof (cmpt_code_size C_cmpt) as HC'.
        solve_addr.
      }
      iSplit; first (iNext ; by iApply zcond_interp_cmpt_threads).
      iSplit; first (iNext ; by iApply rcond_g_interp_cmpt_threads).
      done.
    - iEval (rewrite interp_unfold /=). iLeft.
      iSplitR; last (iSplit; [iPureIntro; exact Hcgp_shadow|iApply heap_cap_ok_disjoint; exact Hcgp_heap]).
      iApply big_sepL_intro; iModIntro.
      iIntros (ka a Ha).
      rewrite /addr_key.
      iExists RW, interp_nonlocal.
      iEval (cbn).
      iSplit; first done.
      iSplit; first (iPureIntro ; by apply persistent_cond_interp_nonlocal).
      iDestruct (big_sepL_lookup _ _ ka a Ha with "Hrel_data") as "Hrel_a".
      iSplit; first iExact "Hrel_a".
      iSplit; first (iNext ; by iApply zcond_interp_nonlocal).
      iSplit; first (iNext ; by iApply rcond_g_interp_nonlocal).
      iNext ; by iApply wcond_nwl_interp_nonlocal.
  Qed.

  (** [alloc_compartment_interp_rel] on the map of Permanent regions alone. *)
  Lemma alloc_compartment_interp_rel_perm {E : coPset} (W : WORLD) ( C_cmpt : cmpt ) (C : CmptName) :
    let imports_addrs := finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_a_code C_cmpt) in
    let code_addrs := finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt) in
    let data_addrs := finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) in
    let pcc_cap := (Cap RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_b_pcc C_cmpt)%a) in
    let cgp_cap := (Cap RW Global (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) (cmpt_b_cgp C_cmpt)%a) in

    Forall (λ w : Word, is_z w) (cmpt_code C_cmpt) ->
    Forall (is_initial_data_word C_cmpt) (cmpt_data C_cmpt) ->

    ([∗ list] k;v ∈ imports_addrs ; lword_of_word <$> cmpt_imports C_cmpt, k ↦ₐ v) -∗
    ([∗ list] k;v ∈ code_addrs ; lword_of_word <$> cmpt_code C_cmpt, k ↦ₐ v) -∗
    ([∗ list] k;v ∈ data_addrs ; lword_of_word <$> cmpt_data C_cmpt, k ↦ₐ v) -∗

    (
      (
        ([∗ list] k ∈ (imports_addrs++code_addrs), LNonHeap k ↪ᵖ[C]{RX} safeGC interp_cmpt_threads) ∗
        ([∗ list] k ∈ (data_addrs), LNonHeap k ↪ᵖ[C]{RW} safeGC interp_nonlocal)
      )
      -∗
      ([∗ list] v ∈ lword_of_word <$> cmpt_imports C_cmpt, safeGC interp_cmpt_threads (C, v)) ∗
      ([∗ set] v ∈ exported_entries_sealed C_cmpt, interp_in_mem RWL W C v)
    ) -∗

    thread_in th C -∗
    perm_region_map C ∅

    ={E}=∗

    perm_region_map C ∅ ∗
    interp W C pcc_cap ∗
    interp W C cgp_cap ∗
    ([∗ list] v ∈ lword_of_word <$> cmpt_imports C_cmpt, interp_in_mem RWL W C v) ∗
    ([∗ set] v ∈ exported_entries_sealed C_cmpt, interp_in_mem RWL W C v)
  .
  Proof.
    intros * C_code C_data.
    pose proof (cmpt_pcc_disjoint_from_mmio C_cmpt) as Hpcc_shadow.
    pose proof (cmpt_pcc_disjoint_from_heap C_cmpt) as Hpcc_heap.
    pose proof (cmpt_cgp_disjoint_from_mmio C_cmpt) as Hcgp_shadow.
    pose proof (cmpt_cgp_disjoint_from_heap C_cmpt) as Hcgp_heap.
    iIntros "HC_imports HC_code HC_data Himport_interp #Hth Hworld_C".

    iMod (perm_extend_sepL2 C
            code_addrs (lword_of_word <$> cmpt_code C_cmpt)
            RX (safeGC interp_cmpt_threads)
           with "Hworld_C [HC_code]") as "(Hworld_C & #HC_code)".
    {
      rewrite !big_sepL2_fmap_r.
      iApply (big_sepL2_mono with "HC_code").
      intros k v1 v2 Hv1 Hv2. cbn. iIntros "Hv".
      pose proof (Forall_lookup_1 _ _ _ _ C_code Hv2) as Hncap.
      destruct v2; [| by inversion Hncap..].
      rewrite /PermRes key_pointsto_nonheap.
      iFrame "Hv".
      iSplit; first done.
      iApply bi.later_intro. iApply interp_cmpt_threads_int.
    }

    iMod (perm_extend_sepL2_open C
            data_addrs
            (lword_of_word <$> cmpt_data C_cmpt)
            RW (safeGC interp_nonlocal)
           with "Hworld_C HC_data []") as "(Hworld_C & #HC_data & _)".
    { apply finz_seq_between_NoDup. }
    { done. }
    {
      iClear "#".
      rewrite big_sepL_fmap.
      clear -C_data Hcgp_shadow Hcgp_heap.
      generalize dependent (cmpt_data C_cmpt); iIntros (l Hl).
      iIntros "#Hrels".
      iInduction (l) as [| w l] "IH"; first done.
      cbn.
      apply Forall_cons in Hl; destruct Hl as [Hw Hl].
      iSplitL; last (iApply "IH"; eauto).
      destruct w as [| [|] | |] ; cbn in Hw; destruct Hw as [Hw|Hw]; cbn in Hw; try done
      ; [|destruct g ; last done].
      - iApply interp_nonlocal_int.
      - rewrite /interp_nonlocal /=. iSplit; first by destruct tag.
        destruct tag; last (iApply interp_untagged; done).
        rewrite interp_unfold interp1_eq.
        destruct Hw as (Hp & Hb & He).
        destruct (isO p) eqn:HpO.
        { assert (Hsub : finz.seq_between b e ⊆
              finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt)).
          { intros x Hx. apply elem_of_finz_seq_between in Hx.
            apply elem_of_finz_seq_between. solve_addr. }
          assert (Hdisjoint : disjoint_from_heap b e).
          { rewrite /disjoint_from_heap in Hcgp_heap |- *.
            set_solver+Hsub Hcgp_heap. }
          iSplit; first by iApply heap_cap_ok_disjoint.
          iApply big_sepL_intro. iIntros "!>" (i x Hx%list_elem_of_lookup_2 Hheap).
          rewrite /disjoint_from_heap elem_of_disjoint in Hdisjoint.
          exfalso. eapply Hdisjoint; first exact Hx.
          apply withinBounds_true_iff in Hheap.
          apply elem_of_finz_seq_between. solve_addr. }
        destruct (has_sreg_access p) eqn:HpXSR.
        { destruct p as [ [] w dl dro ]; cbn in *; done. }
        assert (isWL p = false) as Hwl.
        { destruct p as [ rx [] dl dro ]; cbn in *; auto.
          rewrite !andb_True in Hp.
          destruct Hp as [ [ [] ] ]; done.
        }
        rewrite Hwl. iLeft.
        iSplitR; cycle 1.
        { assert (finz.seq_between b e ⊆
            finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt)) as Hbounds.
          { intros a' Ha'. apply elem_of_finz_seq_between in Ha'.
            apply elem_of_finz_seq_between; solve_addr. }
          iSplit.
          - iPureIntro. split; first done.
            eapply disjoint_from_mmio_weaken; [| | exact Hcgp_shadow]; solve_addr.
          - iApply heap_cap_ok_disjoint.
            rewrite /disjoint_from_heap in Hcgp_heap |- *.
            set_solver+Hbounds Hcgp_heap.
        }
        iApply big_sepL_intro; iModIntro.
        iIntros (k a' Ha').
        apply list_elem_of_lookup_2, elem_of_finz_seq_between in Ha'.
        assert (a' ∈ₐ [(cmpt_b_cgp C_cmpt), (cmpt_e_cgp C_cmpt))) as Ha'' by solve_addr.
        apply elem_of_finz_seq_between in Ha''.
        rewrite /addr_key.
        iDestruct (big_sepL_elem_of with "Hrels") as "Hrel_a'"; eauto.
        iExists RW, interp_nonlocal; cbn.
        iSplit; first done.
        iSplit; first (iPureIntro; apply persistent_cond_interp_nonlocal).
        iSplit; first by rewrite /region_rel Hwl.
        iSplit; first iApply zcond_interp_nonlocal.
        iSplit; first by iApply rcond_g_interp_nonlocal.
        iApply wcond_nwl_interp_nonlocal.
    }

    iMod (perm_extend_sepL2_open_frame C
            imports_addrs
            (lword_of_word <$> cmpt_imports C_cmpt)
            RX (safeGC interp_cmpt_threads)
            ([∗ set] v ∈ exported_entries_sealed C_cmpt, interp_in_mem RWL W C v)
           with "Hworld_C HC_imports [Himport_interp]")
      as "(Hworld_C & #HC_imports & #Hinterp_imports & Hinterp_exports)".
    { apply finz_seq_between_NoDup. }
    { done. }
    {
      iIntros "#HC_imports".
      iApply "Himport_interp".
      iFrame "HC_data".
      rewrite big_sepL_app. iFrame "HC_imports HC_code".
    }
    iDestruct (big_sepL_app _ imports_addrs code_addrs with "[$HC_imports $HC_code]") as "HC_PCC".
    iDestruct (cmpt_caps_interp W C_cmpt C with "HC_PCC HC_data") as "[#Hpcc #Hcgp]".
    iModIntro. iFrame "Hworld_C Hpcc Hcgp Hinterp_exports".
    iApply (big_sepL_impl with "Hinterp_imports").
    iIntros "!>" (k v Hv) "Hv". iApply interp_to_in_mem.
    iEval (rewrite /interp_cmpt_threads /=) in "Hv". iDestruct "Hv" as "#Hv".
    iApply (interp_monotone with "[] (Hv Hth)").
    iPureIntro. apply related_sts_pub_world_empty.
  Qed.

  Lemma alloc_compartment_interp_rel {E : coPset} (W : WORLD) ( C_cmpt : cmpt ) (C : CmptName) :
    let imports_addrs := finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_a_code C_cmpt) in
    let code_addrs := finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt) in
    let data_addrs := finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) in
    let pcc_cap := (Cap RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_b_pcc C_cmpt)%a) in
    let cgp_cap := (Cap RW Global (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) (cmpt_b_cgp C_cmpt)%a) in

    Forall (λ w : Word, is_z w) (cmpt_code C_cmpt) ->
    Forall (is_initial_data_word C_cmpt) (cmpt_data C_cmpt) ->

    ([∗ list] k;v ∈ imports_addrs ; lword_of_word <$> cmpt_imports C_cmpt, k ↦ₐ v) -∗
    ([∗ list] k;v ∈ code_addrs ; lword_of_word <$> cmpt_code C_cmpt, k ↦ₐ v) -∗
    ([∗ list] k;v ∈ data_addrs ; lword_of_word <$> cmpt_data C_cmpt, k ↦ₐ v) -∗

    (
      (
        ([∗ list] k ∈ (imports_addrs++code_addrs), LNonHeap k ↪ᵖ[C]{RX} safeGC interp_cmpt_threads) ∗
        ([∗ list] k ∈ (data_addrs), LNonHeap k ↪ᵖ[C]{RW} safeGC interp_nonlocal)
      )
      -∗
      ([∗ list] v ∈ lword_of_word <$> cmpt_imports C_cmpt, safeGC interp_cmpt_threads (C, v)) ∗
      ([∗ set] v ∈ exported_entries_sealed C_cmpt, interp_in_mem RWL W C v)
    ) -∗

    thread_in th C -∗
    world_interp W C

    ={E}=∗

    world_interp W C ∗
    interp W C pcc_cap ∗
    interp W C cgp_cap ∗
    ([∗ list] v ∈ lword_of_word <$> cmpt_imports C_cmpt, interp_in_mem RWL W C v) ∗
    ([∗ set] v ∈ exported_entries_sealed C_cmpt, interp_in_mem RWL W C v)
  .
  Proof.
    intros * C_code C_data.
    iIntros "HC_imports HC_code HC_data Himport_interp #Hth Hworld_C".
    rewrite world_interp_eq. iDestruct "Hworld_C" as "[Hperm Hlocal]".
    iMod (alloc_compartment_interp_rel_perm W C_cmpt C C_code C_data
      with "HC_imports HC_code HC_data Himport_interp Hth Hperm") as "[Hperm $]".
    iModIntro. iFrame.
  Qed.

  (** [alloc_compartment_interp] on the map of Permanent regions alone. *)
  Lemma alloc_compartment_interp_perm (E : coPset) (W : WORLD) ( C_cmpt : cmpt ) (C : CmptName) :
    let imports_addrs := finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_a_code C_cmpt) in
    let code_addrs := finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt) in
    let data_addrs := finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) in
    let pcc_cap := (Cap RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_b_pcc C_cmpt)%a) in
    let cgp_cap := (Cap RW Global (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) (cmpt_b_cgp C_cmpt)%a) in

    Forall (λ w : Word, is_z w) (cmpt_code C_cmpt) ->
    Forall (is_initial_data_word C_cmpt) (cmpt_data C_cmpt) ->

    ([∗ list] k;v ∈ imports_addrs ; lword_of_word <$> cmpt_imports C_cmpt, k ↦ₐ v) -∗
    ([∗ list] k;v ∈ code_addrs ; lword_of_word <$> cmpt_code C_cmpt, k ↦ₐ v) -∗
    ([∗ list] k;v ∈ data_addrs ; lword_of_word <$> cmpt_data C_cmpt, k ↦ₐ v) -∗
    (
      (
        interp W C pcc_cap ∗
        interp W C cgp_cap
      )
      -∗
      ([∗ list] v ∈ lword_of_word <$> cmpt_imports C_cmpt, safeGC interp_cmpt_threads (C, v)) ∗
      ([∗ set] v ∈ exported_entries_sealed C_cmpt, interp_in_mem RWL W C v)
    )
    -∗

    thread_in th C -∗
    perm_region_map C ∅

    ={E}=∗

    perm_region_map C ∅ ∗
    interp W C pcc_cap ∗
    interp W C cgp_cap ∗
    ([∗ list] v ∈ lword_of_word <$> cmpt_imports C_cmpt, interp_in_mem RWL W C v) ∗
    ([∗ set] v ∈ exported_entries_sealed C_cmpt, interp_in_mem RWL W C v)
  .
  Proof.
    intros * C_code C_data.
    iIntros "HC_imports HC_code HC_data Himport_interp #Hth Hworld_C".
    iApply (alloc_compartment_interp_rel_perm W C_cmpt C C_code C_data
      with "HC_imports HC_code HC_data [Himport_interp] Hth Hworld_C").
    iIntros "(#Hrel_pcc & #Hrel_data)".
    iApply "Himport_interp".
    iApply (cmpt_caps_interp with "Hrel_pcc Hrel_data").
  Qed.

  Lemma alloc_compartment_interp (E : coPset) (W : WORLD) ( C_cmpt : cmpt ) (C : CmptName) :
    let imports_addrs := finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_a_code C_cmpt) in
    let code_addrs := finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt) in
    let data_addrs := finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) in
    let pcc_cap := (Cap RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_b_pcc C_cmpt)%a) in
    let cgp_cap := (Cap RW Global (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) (cmpt_b_cgp C_cmpt)%a) in

    Forall (λ w : Word, is_z w) (cmpt_code C_cmpt) ->
    Forall (is_initial_data_word C_cmpt) (cmpt_data C_cmpt) ->

    ([∗ list] k;v ∈ imports_addrs ; lword_of_word <$> cmpt_imports C_cmpt, k ↦ₐ v) -∗
    ([∗ list] k;v ∈ code_addrs ; lword_of_word <$> cmpt_code C_cmpt, k ↦ₐ v) -∗
    ([∗ list] k;v ∈ data_addrs ; lword_of_word <$> cmpt_data C_cmpt, k ↦ₐ v) -∗
    (
      (
        interp W C pcc_cap ∗
        interp W C cgp_cap
      )
      -∗
      ([∗ list] v ∈ lword_of_word <$> cmpt_imports C_cmpt, safeGC interp_cmpt_threads (C, v)) ∗
      ([∗ set] v ∈ exported_entries_sealed C_cmpt, interp_in_mem RWL W C v)
    )
    -∗

    thread_in th C -∗
    world_interp W C

    ={E}=∗

    world_interp W C ∗
    interp W C pcc_cap ∗
    interp W C cgp_cap ∗
    ([∗ list] v ∈ lword_of_word <$> cmpt_imports C_cmpt, interp_in_mem RWL W C v) ∗
    ([∗ set] v ∈ exported_entries_sealed C_cmpt, interp_in_mem RWL W C v)
  .
  Proof.
    intros * C_code C_data.
    iIntros "HC_imports HC_code HC_data Himport_interp #Hth Hworld_C".
    rewrite world_interp_eq. iDestruct "Hworld_C" as "[Hperm Hlocal]".
    iMod (alloc_compartment_interp_perm E W C_cmpt C C_code C_data
      with "HC_imports HC_code HC_data Himport_interp Hth Hperm") as "[Hperm $]".
    iModIntro. iFrame.
  Qed.

End region_alloc_cmpt.
