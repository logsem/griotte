From iris.proofmode Require Import proofmode.
From griotte Require Import rules_Load map_simpl register_tactics logrel.
From griotte Require Import rules_Allocator.
From griotte Require Export call_stack.

Section Switcher_Load.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} `{MP : MachineParameters}.

  Lemma switcher_load_stack E pc_p pc_g pc_b pc_e pc_a pc_a'
    dst src wi wd b e a raw :
    is_shadow_address a = false ->
    decodeInstrW wi = Load dst src 0 ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    withinBounds b e a = true ->
    (pc_a + 1)%a = Some pc_a' ->
    dst ≠ cnull -> src ≠ cnull ->
    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ wd ∗ src ↦ᵣ WCap true RWL Local b e a ∗ a ↦ₐ raw }}}
      Instr Executable @ E
    {{{ retv, RET retv; ⌜retv = FailedV⌝ ∨
        ∃ actual, ⌜retv = NextIV⌝ ∗ ⌜load_heap raw actual⌝ ∗
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ actual ∗ src ↦ᵣ WCap true RWL Local b e a ∗ a ↦ₐ raw }}}.
  Proof.
    iIntros (Hshadow Hinstr Hvpc Hbounds Hpc' Hdst Hsrc φ)
      "(HPC & Hi & Hdst & Hsrc & Ha) Hφ".
    destruct (is_heap_cap raw) eqn:Hheap; cycle 1.
    { iApply (wp_load_success_notinstr with "[$HPC $Hi $Hdst $Hsrc $Ha]"); eauto.
      iNext. iIntros "(HPC & Hdst & Hi & Hsrc & Ha)".
      iApply "Hφ". iRight. iExists raw. iFrame.
      iPureIntro. split; first done. by left. }
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%Hpc_src & %Hpc_dst & %Hsrc_dst)]".
    iDestruct (memMap_resource_2ne_apply with "Hi Ha") as "[Hmem %Hpc_a]".
    iApply (wp_load E pc_p pc_g pc_b pc_e pc_a dst src wi with "[$Hmap $Hmem]");
      eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { exists true, RWL, Local, b, e, a. split.
      - unfold read_reg_inr. by simplify_map_eq.
      - case_decide; last done. exists raw. by simplify_map_eq. }
    { intros p0 g0 b0 e0 a0 (Hsrc0 & _).
      simpl_map_regs by eauto. simplify_map_eq. done. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    destruct Hspec as [p0 g0 b0 e0 a0 loadv actual Hallow Hlookup Hactual Hinc|].
    2: { iApply "Hφ". by iLeft. }
    destruct Hallow as (Hsrc0 & _). simpl_map_regs by eauto. simplify_map_eq.
    unfold incrementPC, incrementPC_gen in Hinc. simplify_map_eq.
    rewrite (insert_insert_ne _ dst PC) // insert_insert_eq.
    rewrite (insert_insert_ne _ dst src) // insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(HPC & Hsrc & Hdst)"; eauto.
    iDestruct (memMap_resource_2ne with "Hmem") as "[Hi Ha]"; auto.
    iApply "Hφ". iRight. iExists actual. iFrame.
    iPureIntro. split; first done.
    destruct Hactual as [-> | ->]; [by left|right; done].
  Qed.

End Switcher_Load.

Section Switcher_Restore.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} `{!allocatorG Σ} `{MP : MachineParameters}.

  (** Restore one saved register, borrowing its shadow entry from the allocator
      for this instruction only. Success exposes [load_heap], so subsequent
      loads need not observe the same shadow bit, even for an aliased base. *)
  Lemma switcher_load_stack_restore E pc_p pc_g pc_b pc_e pc_a pc_a'
    dst src wi wd b e a raw :
    ↑Nallocator ⊆ E ->
    is_shadow_address a = false ->
    decodeInstrW wi = Load dst src 0 ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    withinBounds b e a = true ->
    (pc_a + 1)%a = Some pc_a' ->
    dst ≠ cnull -> src ≠ cnull ->
    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ wd ∗ src ↦ᵣ WCap true RWL Local b e a ∗ a ↦ₐ raw ∗
        allocator_ctx }}}
      Instr Executable @ E
    {{{ actual, RET NextIV; ⌜load_heap raw actual⌝ ∗
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ actual ∗ src ↦ᵣ WCap true RWL Local b e a ∗
        a ↦ₐ raw }}}.
  Proof.
    iIntros (HE Hshadow Hinstr Hvpc Hbounds Hpc Hdst Hsrc Φ)
      "(HPC & Hi & Hdst & Hsrc & Ha & #Halloc) HΦ".
    destruct (is_heap_cap raw) eqn:Hheap; cycle 1.
    { iApply (wp_load_success_notinstr with "[$HPC $Hi $Hdst $Hsrc $Ha]"); eauto.
      iNext. iIntros "(HPC & Hdst & Hi & Hsrc & Ha)".
      iApply ("HΦ" $! raw). iFrame. iPureIntro. by left. }
    unfold is_heap_cap in Hheap.
    destruct (heap_cap_base raw) as [base|] eqn:Hbase; last discriminate.
    (* Load dst src: the allocator invariant supplies the current shadow status. *)
    iApply (wp_load_heap_inv with "[$Halloc $HPC $Hi $Hdst $Hsrc $Ha]"); eauto.
    iNext. iIntros (status) "(HPC & Hdst & Hi & Hsrc & Ha)".
    iApply ("HΦ" $! (match status with ShadowLive => raw | ShadowQuarantined => clear_tag raw end)).
    destruct status; iFrame; iPureIntro.
    - left. reflexivity.
    - right. split; last reflexivity. unfold is_heap_cap. by rewrite Hbase.
  Qed.
End Switcher_Restore.

Section Switcher_Restore_Interp.
  Context
    {Σ : gFunctors} {ceriseg : ceriseG Σ} {sealsg : sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {cstackg : CSTACKG Σ}
    {allocatorg : allocatorG Σ} {relg : relGS Σ}
    `{MP : MachineParameters}.

  Lemma switcher_shadow_restore_retained Wworld Wval C opened raw actual alloc_map :
    Forall (heap_cell_live (heap_std Wworld)) opened ->
    heap_std Wworld = heap_std Wval ->
    dom alloc_map = heap_addresses ->
    load_memory_shadow_observation (shadow_status <$> alloc_map) RWL raw actual ->
    world_interp_open Wworld C opened -∗
    ([∗ map] a↦s ∈ alloc_map, allocator_entry a s) -∗
    ⌜filter_heap Wval actual = actual⌝ ∗
    world_interp_open Wworld C opened ∗
    ([∗ map] a↦s ∈ alloc_map, allocator_entry a s).
  Proof.
    iIntros (Hlive Hheap_eq Hdom Hobs) "Hworld Hentries".
    destruct (heap_cap_base raw) as [base|] eqn:Hbase; cycle 1.
    { rewrite /load_memory_shadow_observation Hbase in Hobs. subst actual.
      assert (heap_authority_base raw = None) as Hauth.
      { destruct (heap_authority_base raw) as [base'|] eqn:Hauth; last done.
        apply heap_authority_base_heap_cap_base_shared in Hauth.
        rewrite Hbase in Hauth. discriminate. }
      iFrame. iPureIntro. by apply filter_heap_nonheap. }
    assert (is_heap_address base = true) as Hheap.
    { unfold heap_cap_base in Hbase.
      destruct (memory_cap_base raw) as [b|] eqn:Hmemory; last discriminate.
      destruct (is_heap_address b) eqn:Hheap; last discriminate.
      by simplify_eq. }
    assert (is_Some (alloc_map !! base)) as [s Hlookup].
    { apply elem_of_dom. rewrite Hdom elem_of_heap_addresses. exact Hheap. }
    rewrite /load_memory_shadow_observation Hbase in Hobs.
    specialize (Hobs (shadow_status s)).
    assert ((shadow_status <$> alloc_map) !! base = Some (shadow_status s))
      as Hshadow_lookup by (rewrite lookup_fmap Hlookup; reflexivity).
    specialize (Hobs Hshadow_lookup).
    destruct s.
    - simpl in Hobs. subst actual.
      destruct (heap_authority_base raw) as [b|] eqn:Hauth; last first.
      { iFrame. iPureIntro. by apply filter_heap_nonheap. }
      pose proof (heap_authority_base_heap_cap_base_shared raw b Hauth) as Hcap.
      rewrite Hbase in Hcap. inversion Hcap; subst b.
      destruct (heap_lookup_addr (heap_std Wval) base) as [bo|] eqn:Hheaplookup;
        last (iFrame; iPureIntro; by rewrite /filter_heap Hauth Hheaplookup).
      destruct bo as [bb obj]. destruct (alloc_object_status obj) eqn:Hstatus.
      { iFrame. iPureIntro. by rewrite /filter_heap Hauth Hheaplookup /= Hstatus. }
      assert (heap_cell_status (heap_std Wworld) base = Some AllocObjectQuarantined)
        as Hqstatus by (rewrite Hheap_eq /heap_cell_status Hheap Hheaplookup /= Hstatus; reflexivity).
      assert (base ∉ opened) as Hnotpc.
      { intros Hbase_in. apply list_elem_of_In in Hbase_in.
        rewrite Forall_forall in Hlive.
        specialize (Hlive base Hbase_in). unfold heap_cell_live in Hlive.
        rewrite Hqstatus in Hlive. discriminate. }
      iDestruct (world_interp_open_quarantined_token with "Hworld")
        as "[Htoken Hrestore]"; [exact Hnotpc|exact Hqstatus|].
      iDestruct (big_sepM_lookup with "Hentries") as "Hentry"; first exact Hlookup.
      iDestruct (allocator_entry_token_quarantined with "Hentry Htoken")
        as %Himpossible. discriminate Himpossible.
    - simpl in Hobs. subst actual.
      destruct (heap_authority_base raw) as [b|] eqn:Hauth; last first.
      { iFrame. iPureIntro. by apply filter_heap_nonheap. }
      pose proof (heap_authority_base_heap_cap_base_shared raw b Hauth) as Hcap.
      rewrite Hbase in Hcap. inversion Hcap; subst b.
      destruct (heap_lookup_addr (heap_std Wval) base) as [bo|] eqn:Hheaplookup;
        last (iFrame; iPureIntro; by rewrite /filter_heap Hauth Hheaplookup).
      destruct bo as [bb obj]. destruct (alloc_object_status obj) eqn:Hstatus.
      { iFrame. iPureIntro. by rewrite /filter_heap Hauth Hheaplookup /= Hstatus. }
      assert (heap_cell_status (heap_std Wworld) base = Some AllocObjectQuarantined)
        as Hqstatus by (rewrite Hheap_eq /heap_cell_status Hheap Hheaplookup /= Hstatus; reflexivity).
      assert (base ∉ opened) as Hnotpc.
      { intros Hbase_in. apply list_elem_of_In in Hbase_in.
        rewrite Forall_forall in Hlive.
        specialize (Hlive base Hbase_in). unfold heap_cell_live in Hlive.
        rewrite Hqstatus in Hlive. discriminate. }
      iDestruct (world_interp_open_quarantined_token with "Hworld")
        as "[Htoken Hrestore]"; [exact Hnotpc|exact Hqstatus|].
      iDestruct (big_sepM_lookup with "Hentries") as "Hentry"; first exact Hlookup.
      iDestruct (allocator_entry_token_quarantined with "Hentry Htoken")
        as %Himpossible. discriminate Himpossible.
    - simpl in Hobs. subst actual.
      iFrame. iPureIntro. apply filter_heap_untagged, get_tag_clear_tag.
  Qed.

  Lemma switcher_load_stack_restore_world E Wworld Wval C opened
    pc_p pc_g pc_b pc_e pc_a pc_a' dst src wi wd b e a raw :
    heap_std Wworld = heap_std Wval ->
    Forall (heap_cell_live (heap_std Wworld)) opened ->
    ↑Nallocator ⊆ E ->
    is_shadow_address a = false ->
    decodeInstrW wi = Load dst src 0 ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    withinBounds b e a = true ->
    (pc_a + 1)%a = Some pc_a' ->
    dst ≠ cnull -> src ≠ cnull ->
    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ wd ∗ src ↦ᵣ WCap true RWL Local b e a ∗ a ↦ₐ raw ∗
        world_interp_open Wworld C opened ∗ allocator_ctx }}}
      Instr Executable @ E
    {{{ actual, RET NextIV;
        ⌜load_heap raw actual ∧ filter_heap Wval actual = actual⌝ ∗
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ actual ∗ src ↦ᵣ WCap true RWL Local b e a ∗
        a ↦ₐ raw ∗ world_interp_open Wworld C opened }}}.
  Proof.
    iIntros (Hheap_eq Hlive HE Hshadow Hinstr Hvpc Hbounds Hpc Hdst Hsrc Φ)
      "(HPC & Hi & Hdst & Hsrc & Ha & Hworld & #Halloc) HΦ".
    destruct (heap_cap_base raw) as [base|] eqn:Hbase.
    - iInv Nallocator as ">Halloc_body" "Halloc_close".
      iDestruct "Halloc_body" as (alloc_map Halloc_dom) "Halloc_entries".
      assert (is_Some (alloc_map !! base)) as [status Hlookup].
      { apply elem_of_dom. rewrite Halloc_dom elem_of_heap_addresses.
        unfold heap_cap_base in Hbase.
        destruct (memory_cap_base raw) as [base'|] eqn:Hmemory; last discriminate.
        destruct (is_heap_address base') eqn:Hheap; inversion Hbase; subst; done. }
      iDestruct (big_sepM_delete with "Halloc_entries") as "[Hentry Halloc_entries]";
        first exact Hlookup.
      iDestruct "Hentry" as "[Hstatus Hstatus_res]".
      destruct (shadow_status status) eqn:Hstatus_eq.
      + iApply (wp_load_success_heap_word with
          "[$HPC $Hi $Hdst $Hsrc $Ha $Hstatus]"); eauto.
        iNext. iIntros "(HPC & Hdst & Hi & Hsrc & Ha & Hstatus)".
        iAssert ([∗ map] x↦s ∈ alloc_map, allocator_entry x s)%I
          with "[Hstatus Hstatus_res Halloc_entries]" as "Halloc_entries".
        { iApply big_sepM_delete; first exact Hlookup.
          iFrame. rewrite /allocator_entry Hstatus_eq. iFrame. }
        iDestruct (switcher_shadow_restore_retained Wworld Wval C opened raw raw alloc_map
          with "Hworld Halloc_entries")
          as "(%Hretained & Hworld & Halloc_entries)";
          [exact Hlive|exact Hheap_eq|exact Halloc_dom| |].
        { unfold load_memory_shadow_observation. rewrite Hbase.
          intros observed Hobserved. rewrite lookup_fmap Hlookup in Hobserved.
          inversion Hobserved; subst. by rewrite Hstatus_eq. }
        iMod ("Halloc_close" with "[Halloc_entries]") as "_".
        { iNext. iExists alloc_map. iFrame. iPureIntro. exact Halloc_dom. }
        iModIntro. iApply "HΦ". iFrame.
        iPureIntro. split; first by left. exact Hretained.
      + iApply (wp_load_success_heap_word_revoked with
          "[$HPC $Hi $Hdst $Hsrc $Ha $Hstatus]"); eauto.
        iNext. iIntros "(HPC & Hdst & Hi & Hsrc & Ha & Hstatus)".
        iAssert ([∗ map] x↦s ∈ alloc_map, allocator_entry x s)%I
          with "[Hstatus Hstatus_res Halloc_entries]" as "Halloc_entries".
        { iApply big_sepM_delete; first exact Hlookup.
          iFrame. rewrite /allocator_entry Hstatus_eq. iFrame. }
        iDestruct (switcher_shadow_restore_retained Wworld Wval C opened raw
          (clear_tag raw) alloc_map with "Hworld Halloc_entries")
          as "(%Hretained & Hworld & Halloc_entries)";
          [exact Hlive|exact Hheap_eq|exact Halloc_dom| |].
        { unfold load_memory_shadow_observation. rewrite Hbase.
          intros observed Hobserved. rewrite lookup_fmap Hlookup in Hobserved.
          inversion Hobserved; subst. by rewrite Hstatus_eq. }
        iMod ("Halloc_close" with "[Halloc_entries]") as "_".
        { iNext. iExists alloc_map. iFrame. iPureIntro. exact Halloc_dom. }
        iModIntro. iApply "HΦ". iFrame.
        iPureIntro. split; last exact Hretained.
        right. split; last done. unfold is_heap_cap. by rewrite Hbase.
    - iApply (wp_load_success_notinstr with "[$HPC $Hi $Hdst $Hsrc $Ha]"); eauto.
      { unfold is_heap_cap. by rewrite Hbase. }
      iNext. iIntros "(HPC & Hdst & Hi & Hsrc & Ha)".
      iApply "HΦ". iFrame.
      iPureIntro. split; first by left.
      assert (heap_authority_base raw = None) as Hauth.
      { destruct (heap_authority_base raw) as [base'|] eqn:Hauth; last done.
        apply heap_authority_base_heap_cap_base_shared in Hauth.
        rewrite Hbase in Hauth. discriminate. }
      by apply filter_heap_nonheap.
  Qed.

  Lemma switcher_load_stack_restore_interp E Wworld Wval C opened
    pc_p pc_g pc_b pc_e pc_a pc_a' dst src wi wd b e a raw :
    heap_std Wworld = heap_std Wval ->
    Forall (heap_cell_live (heap_std Wworld)) opened ->
    ↑Nallocator ⊆ E ->
    is_shadow_address a = false ->
    decodeInstrW wi = Load dst src 0 ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    withinBounds b e a = true ->
    (pc_a + 1)%a = Some pc_a' ->
    dst ≠ cnull -> src ≠ cnull ->
    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ wd ∗ src ↦ᵣ WCap true RWL Local b e a ∗ a ↦ₐ raw ∗
        world_interp_open Wworld C opened ∗ interp_in_mem RWL Wval C raw ∗
        allocator_ctx }}}
      Instr Executable @ E
    {{{ actual, RET NextIV; ⌜load_heap raw actual⌝ ∗
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ actual ∗ src ↦ᵣ WCap true RWL Local b e a ∗
        a ↦ₐ raw ∗ world_interp_open Wworld C opened ∗ interp Wval C actual }}}.
  Proof.
    iIntros (Hheap_eq Hlive HE Hshadow Hinstr Hvpc Hbounds Hpc Hdst Hsrc Φ)
      "(HPC & Hi & Hdst & Hsrc & Ha & Hworld & #Hnormal & #Halloc) HΦ".
    destruct (heap_cap_base raw) as [base|] eqn:Hbase.
    - iInv Nallocator as ">Halloc_body" "Halloc_close".
      iDestruct "Halloc_body" as (alloc_map Halloc_dom) "Halloc_entries".
      assert (is_Some (alloc_map !! base)) as [status Hlookup].
      { apply elem_of_dom. rewrite Halloc_dom elem_of_heap_addresses.
        unfold heap_cap_base in Hbase.
        destruct (memory_cap_base raw) as [base'|] eqn:Hmemory; last discriminate.
        destruct (is_heap_address base') eqn:Hheap; inversion Hbase; subst; done. }
      iDestruct (big_sepM_delete with "Halloc_entries") as "[Hentry Halloc_entries]";
        first exact Hlookup.
      iDestruct "Hentry" as "[Hstatus Hstatus_res]".
      destruct (shadow_status status) eqn:Hstatus_eq.
      + iApply (wp_load_success_heap_word with
          "[$HPC $Hi $Hdst $Hsrc $Ha $Hstatus]"); eauto.
        iNext. iIntros "(HPC & Hdst & Hi & Hsrc & Ha & Hstatus)".
        iAssert ([∗ map] x↦s ∈ alloc_map, allocator_entry x s)%I
          with "[Hstatus Hstatus_res Halloc_entries]" as "Halloc_entries".
        { iApply big_sepM_delete; first exact Hlookup.
          iFrame. rewrite /allocator_entry Hstatus_eq. iFrame. }
        iDestruct (interp_in_mem_shadow_result_gen Wworld Wval C opened RWL raw raw alloc_map
          with "Hworld Halloc_entries Hnormal")
          as "(#Hactual & Hworld & Halloc_entries)";
          [exact Hlive|exact Hheap_eq|exact Halloc_dom| |].
        { unfold load_memory_shadow_observation. rewrite Hbase.
          intros observed Hobserved. rewrite lookup_fmap Hlookup in Hobserved.
          inversion Hobserved; subst. by rewrite Hstatus_eq. }
        iMod ("Halloc_close" with "[Halloc_entries]") as "_".
        { iNext. iExists alloc_map. iFrame. iPureIntro. exact Halloc_dom. }
        iModIntro. iApply "HΦ".
        iFrame "∗#". iPureIntro. by left.
      + iApply (wp_load_success_heap_word_revoked with
          "[$HPC $Hi $Hdst $Hsrc $Ha $Hstatus]"); eauto.
        iNext. iIntros "(HPC & Hdst & Hi & Hsrc & Ha & Hstatus)".
        iAssert ([∗ map] x↦s ∈ alloc_map, allocator_entry x s)%I
          with "[Hstatus Hstatus_res Halloc_entries]" as "Halloc_entries".
        { iApply big_sepM_delete; first exact Hlookup.
          iFrame. rewrite /allocator_entry Hstatus_eq. iFrame. }
        iDestruct (interp_in_mem_shadow_result_gen Wworld Wval C opened RWL raw
          (clear_tag raw) alloc_map with "Hworld Halloc_entries Hnormal")
          as "(#Hactual & Hworld & Halloc_entries)";
          [exact Hlive|exact Hheap_eq|exact Halloc_dom| |].
        { unfold load_memory_shadow_observation. rewrite Hbase.
          intros observed Hobserved. rewrite lookup_fmap Hlookup in Hobserved.
          inversion Hobserved; subst. by rewrite Hstatus_eq. }
        iMod ("Halloc_close" with "[Halloc_entries]") as "_".
        { iNext. iExists alloc_map. iFrame. iPureIntro. exact Halloc_dom. }
        iModIntro. iApply "HΦ".
        iFrame "∗#". iPureIntro. right. split; last done.
        unfold is_heap_cap. by rewrite Hbase.
    - iApply (wp_load_success_notinstr with "[$HPC $Hi $Hdst $Hsrc $Ha]"); eauto.
      { unfold is_heap_cap. by rewrite Hbase. }
      iNext. iIntros "(HPC & Hdst & Hi & Hsrc & Ha)".
      iApply "HΦ". iFrame "∗#".
      iSplit; first by iPureIntro; left.
      iApply (interp_in_mem_load_result with "Hnormal").
      right. split; first by rewrite /load_word.
      rewrite /load_word.
      assert (heap_authority_base raw = None) as Hauth.
      { destruct (heap_authority_base raw) as [base|] eqn:Hauth; last done.
        apply heap_authority_base_heap_cap_base_shared in Hauth.
        rewrite Hbase in Hauth. discriminate. }
      by apply filter_heap_nonheap.
  Qed.
End Switcher_Restore_Interp.
