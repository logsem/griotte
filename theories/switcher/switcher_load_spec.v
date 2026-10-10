From iris.proofmode Require Import proofmode.
From griotte Require Import rules_Load map_simpl register_tactics logrel.
From griotte Require Import world_ghost_theory wp_rules_interp.
From griotte Require Export call_stack.

Section Switcher_Restore.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} `{MP : MachineParameters}.

  (** Restore one saved register under a load witness. The load does not
      fail, and its result satisfies [load_post] for that witness. *)
  Lemma switcher_load_stack_restore_witness E pc_p pc_g pc_b pc_e pc_a pc_a'
    dst src (wi wd : LWord) b e a (raw : LWord) wit :
    is_shadow_address a = false ->
    decodeInstrW wi.(lw) = Load dst src 0 ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    withinBounds b e a = true ->
    (pc_a + 1)%a = Some pc_a' ->
    dst ≠ cnull -> src ≠ cnull ->
    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ wd ∗ src ↦ᵣ WCap true RWL Local b e a ∗ a ↦ₐ raw ∗
        load_witness_res wit }}}
      Instr Executable @ E
    {{{ actual, RET NextIV; ⌜load_post wit RWL raw actual⌝ ∗
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ actual ∗ src ↦ᵣ WCap true RWL Local b e a ∗
        a ↦ₐ raw ∗ load_witness_res wit }}}.
  Proof.
    iIntros (Hshadow Hinstr Hvpc Hbounds Hpc Hdst Hsrc Φ)
      "(HPC & Hi & Hdst & Hsrc & Ha & Hwit) HΦ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%Hpc_src & %Hpc_dst & %Hsrc_dst)]".
    iDestruct (memMap_resource_2ne_apply with "Hi Ha") as "[Hmem %Hpc_a]".
    iApply (wp_load_witness_imm with "[$Hmem $Hwit $Hmap]"); eauto.
    { by simplify_map_eq. }
    { by rewrite !dom_insert; set_solver+. }
    { by simplify_map_eq. }
    { intros p0 g0 b0 e0 ea0 Hallow.
      destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)].
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0').
      rewrite lookup_insert_ne // lookup_insert_eq in Hsrc0'. injection Hsrc0' as <- <- <- <- <- <-.
      rewrite addr_add_0 in Haddr. injection Haddr as <-.
      rewrite Hshadow.
      destruct (is_revoker_address a); first done.
      eexists. by simplify_map_eq. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hwit & Hmap)".
    destruct Hspec as [p0 g0 b0 e0 ea0 loadv loadv' Hallow Hsh Hl Hpost Hinc
                      |p0 g0 b0 e0 ea0 heap_a revoked Hallow Hsh
                      |p0 g0 b0 e0 ea0 Hallow Hrev Hl
                      |Hfail].
    2,3: exfalso;
      destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)];
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0');
      rewrite lookup_insert_ne // lookup_insert_eq in Hsrc0'; injection Hsrc0' as <- <- <- <- <- <-;
      rewrite addr_add_0 in Haddr; injection Haddr as <-;
      simplify_map_eq; congruence.
    2: { exfalso. eapply (load_failure_spec_impossible _ _ _ _ _ _ RWL Local b e a a);
         eauto; try by simplify_map_eq.
         all: try by rewrite addr_add_0.
         all: rewrite llookup_reg_not_cnull //; by simplify_map_eq. }
    destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)].
    destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0').
    rewrite lookup_insert_ne // lookup_insert_eq in Hsrc0'. injection Hsrc0' as <- <- <- <- <- <-.
    rewrite addr_add_0 in Haddr. injection Haddr as <-.
    rewrite lookup_insert_ne // lookup_insert_eq in Hl. injection Hl as <-.
    rewrite /linsert_reg in Hinc; try rewrite decide_False // in Hinc.
    apply incrementPC_Some_inv in Hinc
      as (tpc & ppc & gpc & bpc & epc & apc & apc'' & πpc & HPC & Hapc & ->).
    rewrite lookup_insert_ne // lookup_insert_eq in HPC.
    injection HPC as <- <- <- <- <- <- <-.
    rewrite Hpc in Hapc. injection Hapc as <-.
    rewrite (insert_insert_ne _ dst PC) // insert_insert_eq.
    rewrite (insert_insert_ne _ dst src) // insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(HPC & Hsrc & Hdst)"; eauto.
    iDestruct (memMap_resource_2ne with "Hmem") as "[Hi Ha]"; auto.
    iApply "HΦ". by iFrame.
  Qed.

  (** Restore one saved register without a witness. Success exposes
      [load_heap], so subsequent loads need not observe the same tag, even
      for an aliased base. *)
  Lemma switcher_load_stack_restore E pc_p pc_g pc_b pc_e pc_a pc_a'
    dst src (wi wd : LWord) b e a (raw : LWord) :
    is_shadow_address a = false ->
    decodeInstrW wi.(lw) = Load dst src 0 ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    withinBounds b e a = true ->
    (pc_a + 1)%a = Some pc_a' ->
    dst ≠ cnull -> src ≠ cnull ->
    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ wd ∗ src ↦ᵣ WCap true RWL Local b e a ∗ a ↦ₐ raw }}}
      Instr Executable @ E
    {{{ actual, RET NextIV; ⌜load_heap raw actual⌝ ∗
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ actual ∗ src ↦ᵣ WCap true RWL Local b e a ∗
        a ↦ₐ raw }}}.
  Proof.
    iIntros (Hshadow Hinstr Hvpc Hbounds Hpc Hdst Hsrc Φ)
      "(HPC & Hi & Hdst & Hsrc & Ha) HΦ".
    iApply (switcher_load_stack_restore_witness _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LoadPlain
             with "[$HPC $Hi $Hdst $Hsrc $Ha]"); eauto.
    iNext. iIntros (actual) "([%Hpost _] & HPC & Hi & Hdst & Hsrc & Ha & _)".
    rewrite lload_word_RWL in Hpost.
    iApply "HΦ". by iFrame.
  Qed.
End Switcher_Restore.

Section Switcher_Restore_Interp.
  Context
    {Σ : gFunctors} {ceriseg : ceriseG Σ} {sealsg : sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP : MachineParameters}.

  (** The witness of [Wval] for [raw], from the open world [Wworld]. *)
  Lemma world_interp_open_load_witness_eq Wworld Wval C opened raw :
    heap_std Wworld = heap_std Wval ->
    world_interp_open Wworld C opened -∗
    world_interp_open Wworld C opened ∗ load_witness_res (load_witness_of Wval raw).
  Proof.
    iIntros (Hheap_eq) "Hworld".
    iDestruct (world_interp_open_heap_provenance with "Hworld") as "[$ #Hprov]".
    rewrite Hheap_eq. by iApply heap_provenance_load_witness.
  Qed.

  Lemma switcher_load_stack_restore_world E Wworld Wval C opened
    pc_p pc_g pc_b pc_e pc_a pc_a' dst src (wi wd : LWord) b e a (raw : LWord) :
    heap_std Wworld = heap_std Wval ->
    is_shadow_address a = false ->
    decodeInstrW wi.(lw) = Load dst src 0 ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    withinBounds b e a = true ->
    (pc_a + 1)%a = Some pc_a' ->
    dst ≠ cnull -> src ≠ cnull ->
    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ wd ∗ src ↦ᵣ WCap true RWL Local b e a ∗ a ↦ₐ raw ∗
        world_interp_open Wworld C opened }}}
      Instr Executable @ E
    {{{ actual, RET NextIV;
        ⌜load_heap_in_world Wval raw actual⌝ ∗
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ actual ∗ src ↦ᵣ WCap true RWL Local b e a ∗
        a ↦ₐ raw ∗ world_interp_open Wworld C opened }}}.
  Proof.
    iIntros (Hheap_eq Hshadow Hinstr Hvpc Hbounds Hpc Hdst Hsrc Φ)
      "(HPC & Hi & Hdst & Hsrc & Ha & Hworld) HΦ".
    iDestruct (world_interp_open_load_witness_eq _ Wval _ _ raw Hheap_eq with "Hworld")
      as "[Hworld Hwit]".
    iApply (switcher_load_stack_restore_witness with "[$HPC $Hi $Hdst $Hsrc $Ha $Hwit]"); eauto.
    iNext. iIntros (actual) "(%Hpost & HPC & Hi & Hdst & Hsrc & Ha & _)".
    pose proof (load_post_world_load_heap_in_world Wval RWL raw actual Hpost) as Hloaded.
    rewrite lload_word_RWL in Hloaded.
    iApply "HΦ". by iFrame.
  Qed.

  Lemma switcher_load_stack_restore_interp E Wworld Wval C opened
    pc_p pc_g pc_b pc_e pc_a pc_a' dst src (wi wd : LWord) b e a (raw : LWord) :
    heap_std Wworld = heap_std Wval ->
    is_shadow_address a = false ->
    decodeInstrW wi.(lw) = Load dst src 0 ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    withinBounds b e a = true ->
    (pc_a + 1)%a = Some pc_a' ->
    dst ≠ cnull -> src ≠ cnull ->
    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ wd ∗ src ↦ᵣ WCap true RWL Local b e a ∗ a ↦ₐ raw ∗
        world_interp_open Wworld C opened ∗ interp_in_mem RWL Wval C raw }}}
      Instr Executable @ E
    {{{ actual, RET NextIV; ⌜load_heap_in_world Wval raw actual⌝ ∗
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ actual ∗ src ↦ᵣ WCap true RWL Local b e a ∗
        a ↦ₐ raw ∗ world_interp_open Wworld C opened ∗ interp Wval C actual }}}.
  Proof.
    iIntros (Hheap_eq Hshadow Hinstr Hvpc Hbounds Hpc Hdst Hsrc Φ)
      "(HPC & Hi & Hdst & Hsrc & Ha & Hworld & #Hnormal) HΦ".
    iDestruct (world_interp_open_load_witness_eq _ Wval _ _ raw Hheap_eq with "Hworld")
      as "[Hworld Hwit]".
    iApply (switcher_load_stack_restore_witness with "[$HPC $Hi $Hdst $Hsrc $Ha $Hwit]"); eauto.
    iNext. iIntros (actual) "(%Hpost & HPC & Hi & Hdst & Hsrc & Ha & _)".
    iDestruct (interp_in_mem_load_post with "Hnormal") as "#Hactual"; first exact Hpost.
    pose proof (load_post_world_load_heap_in_world Wval RWL raw actual Hpost) as Hloaded.
    rewrite lload_word_RWL in Hloaded.
    iApply "HΦ". by iFrame "∗#".
  Qed.
End Switcher_Restore_Interp.
