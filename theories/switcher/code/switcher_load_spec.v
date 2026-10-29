From iris.proofmode Require Import proofmode.
From griotte Require Import rules_Load map_simpl register_tactics logrel.
From griotte Require Import world_ghost_theory wp_rules_interp.
From griotte Require Export call_stack.

Section Switcher_Restore.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} `{MP : MachineParameters}.

  (** Restore one saved register, at the offset [off] from the stack
      pointer, under a load witness. The load does not fail, and its result
      satisfies [load_post] for that witness. *)
  Lemma switcher_load_stack_restore_witness {dq : dfrac} E pc_p pc_g pc_b pc_e pc_a pc_a'
    dst src (wi wd : LWord) b e a (off : Z) (ea : Addr) (raw : LWord) wit :
    (a + off)%a = Some ea ->
    is_shadow_address ea = false ->
    decodeInstrW wi.(lw) = CLoad dst src off ->
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) ->
    withinBounds b e ea = true ->
    (pc_a + 1)%a = Some pc_a' ->
    dst ≠ cnull -> src ≠ cnull ->
    {{{ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ wd ∗ src ↦ᵣ Cap RWL Local b e a ∗ ea ↦ₐ raw ∗
        load_witness_res wit }}}
      Instr Executable @ E
    {{{ actual, RET NextIV; ⌜load_post wit RWL raw actual⌝ ∗
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ actual ∗ src ↦ᵣ Cap RWL Local b e a ∗
        ea ↦ₐ raw ∗ load_witness_res wit }}}.
  Proof.
    iIntros (Hea Hshadow Hinstr Hvpc Hbounds Hpc Hdst Hsrc Φ)
      "(HPC & Hi & Hdst & Hsrc & Ha & Hwit) HΦ".
    iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %Hsrc_dst]".
    iDestruct (pointsto_ne with "Ha Hi") as %Hpc_a.
    iDestruct (memMap_resource_2ne_dq pc_a ea dq (DfracOwn 1) wi raw with "[$Hi $Ha]")
      as "Hmem"; first done.
    iAssert (▷ ([∗ map] k↦revoked ∈ (∅ : ShadowTbl), k ↦ₛ□ revoked))%I
      as "Hshadow".
    { by rewrite big_sepM_empty. }
    iApply (wp_load_general_shadow_imm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DerefNoId
              with "[$HPC $Hmem $Hshadow $Hwit $Hmap //]"); eauto.
    { by rewrite !dom_insert; set_solver+. }
    { by simplify_map_eq. }
    { intros p0 g0 b0 e0 ea0 Hallow.
      destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)].
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0').
      rewrite lookup_insert_eq in Hsrc0'. injection Hsrc0' as <- <- <- <- <- <-.
      rewrite Hea in Haddr. injection Haddr as <-.
      rewrite Hshadow.
      destruct (is_revoker_address ea); first done.
      eexists. by simplify_map_eq. }
    { by rewrite !dom_insert_L. }
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hmem & _ & Hwit & _ & Hmap)".
    destruct Hspec as [p0 g0 b0 e0 ea0 loadv loadv' Hallow Hsh Hl Hpost Hinc ->
                      |p0 g0 b0 e0 ea0 heap_a revoked Hallow Hsh
                      |p0 g0 b0 e0 ea0 Hallow Hrev Hl
                      |Hfail].
    2,3: exfalso;
      destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)];
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0');
      rewrite lookup_insert_eq in Hsrc0'; injection Hsrc0' as <- <- <- <- <- <-;
      rewrite Hea in Haddr; injection Haddr as <-;
      simplify_map_eq; congruence.
    2: { exfalso. eapply (load_failure_spec_impossible _ _ _ _ _ _ _ RWL Local b e a ea);
         eauto; try by simplify_map_eq.
         all: try (by intros ? Hv; rewrite llookup_reg_not_cnull // in Hv; simplify_map_eq).
         all: rewrite llookup_reg_not_cnull //; by simplify_map_eq. }
    destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)].
    destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0').
    rewrite lookup_insert_eq in Hsrc0'. injection Hsrc0' as <- <- <- <- <- <-.
    rewrite Hea in Haddr. injection Haddr as <-.
    rewrite lookup_insert_ne // lookup_insert_eq in Hl. injection Hl as <-.
    rewrite linsert_reg_not_cnull //.
    apply incrementPC_Some_inv in Hinc
      as (tpc & ppc & gpc & bpc & epc & apc & apc'' & πpc & HPC & Hapc & ->).
    injection HPC as <- <- <- <- <- <- <-.
    rewrite Hpc in Hapc. injection Hapc as <-.
    rewrite (insert_insert_ne _ dst src) // insert_insert_eq.
    iDestruct (regs_of_map_2 with "Hmap") as "(Hsrc & Hdst)"; eauto.
    iDestruct (memMap_resource_2ne_dq with "Hmem") as "[Hi Ha]"; first done.
    iApply "HΦ". by iFrame.
  Qed.

  (** Restore one saved register without a witness. Success exposes
      [load_heap], so subsequent loads need not observe the same tag, even
      for an aliased base. *)
  Lemma switcher_load_stack_restore {dq : dfrac} E pc_p pc_g pc_b pc_e pc_a pc_a'
    dst src (wi wd : LWord) b e a (off : Z) (ea : Addr) (raw : LWord) :
    (a + off)%a = Some ea ->
    is_shadow_address ea = false ->
    decodeInstrW wi.(lw) = CLoad dst src off ->
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) ->
    withinBounds b e ea = true ->
    (pc_a + 1)%a = Some pc_a' ->
    dst ≠ cnull -> src ≠ cnull ->
    {{{ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ wd ∗ src ↦ᵣ Cap RWL Local b e a ∗ ea ↦ₐ raw }}}
      Instr Executable @ E
    {{{ actual, RET NextIV; ⌜load_heap raw actual⌝ ∗
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ actual ∗ src ↦ᵣ Cap RWL Local b e a ∗
        ea ↦ₐ raw }}}.
  Proof.
    iIntros (Hea Hshadow Hinstr Hvpc Hbounds Hpc Hdst Hsrc Φ)
      "(HPC & Hi & Hdst & Hsrc & Ha) HΦ".
    iApply (switcher_load_stack_restore_witness _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LoadPlain
             with "[$HPC $Hi $Hdst $Hsrc $Ha]"); eauto.
    iNext. iIntros (actual) "([%Hpost _] & HPC & Hi & Hdst & Hsrc & Ha & _)".
    rewrite lload_word_RWL in Hpost.
    iApply "HΦ". by iFrame.
  Qed.
End Switcher_Restore.

Section Switcher_Restore_Interp.
  Context
    {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg : sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP : MachineParameters}.

  (** The witness of [Wval] for [raw], from the open world [Wworld]. *)
  Lemma world_interp_open_load_witness_eq Wworld Wval C opened raw :
    world_interp_open Wworld C opened -∗
    world_interp_open Wworld C opened ∗ load_witness_res (load_witness_of Wval raw).
  Proof.
    by iIntros "$".
  Qed.

  Lemma switcher_load_stack_restore_world {dq : dfrac} E Wworld Wval C opened
    pc_p pc_g pc_b pc_e pc_a pc_a' dst src (wi wd : LWord) b e a (off : Z) (ea : Addr)
    (raw : LWord) :
    (a + off)%a = Some ea ->
    is_shadow_address ea = false ->
    decodeInstrW wi.(lw) = CLoad dst src off ->
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) ->
    withinBounds b e ea = true ->
    (pc_a + 1)%a = Some pc_a' ->
    dst ≠ cnull -> src ≠ cnull ->
    {{{ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ[th] wd ∗ src ↦ᵣ[th] Cap RWL Local b e a ∗ ea ↦ₐ raw ∗
        world_interp_open Wworld C opened }}}
      Instr Executable @[th] E
    {{{ actual, RET NextIV;
        ⌜load_heap_in_world Wval raw actual⌝ ∗
        PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ[th] actual ∗ src ↦ᵣ[th] Cap RWL Local b e a ∗
        ea ↦ₐ raw ∗ world_interp_open Wworld C opened }}}.
  Proof.
    iIntros (Hea Hshadow Hinstr Hvpc Hbounds Hpc Hdst Hsrc Φ)
      "(HPC & Hi & Hdst & Hsrc & Ha & Hworld) HΦ".
    iDestruct (world_interp_open_load_witness_eq _ Wval _ _ raw with "Hworld")
      as "[Hworld Hwit]".
    iApply (switcher_load_stack_restore_witness with "[$HPC $Hi $Hdst $Hsrc $Ha $Hwit]"); eauto.
    iNext. iIntros (actual) "(%Hpost & HPC & Hi & Hdst & Hsrc & Ha & _)".
    pose proof (load_post_world_load_heap_in_world Wval RWL raw actual Hpost) as Hloaded.
    rewrite lload_word_RWL in Hloaded.
    iApply "HΦ". by iFrame.
  Qed.

  Lemma switcher_load_stack_restore_interp {dq : dfrac} E Wworld Wval C opened
    pc_p pc_g pc_b pc_e pc_a pc_a' dst src (wi wd : LWord) b e a (off : Z) (ea : Addr)
    (raw : LWord) :
    (a + off)%a = Some ea ->
    is_shadow_address ea = false ->
    decodeInstrW wi.(lw) = CLoad dst src off ->
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) ->
    withinBounds b e ea = true ->
    (pc_a + 1)%a = Some pc_a' ->
    dst ≠ cnull -> src ≠ cnull ->
    {{{ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ[th] wd ∗ src ↦ᵣ[th] Cap RWL Local b e a ∗ ea ↦ₐ raw ∗
        world_interp_open Wworld C opened ∗ interp_in_mem RWL Wval C raw }}}
      Instr Executable @[th] E
    {{{ actual, RET NextIV; ⌜load_heap_in_world Wval raw actual⌝ ∗
        PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ[th] actual ∗ src ↦ᵣ[th] Cap RWL Local b e a ∗
        ea ↦ₐ raw ∗ world_interp_open Wworld C opened ∗ interp Wval C actual }}}.
  Proof.
    iIntros (Hea Hshadow Hinstr Hvpc Hbounds Hpc Hdst Hsrc Φ)
      "(HPC & Hi & Hdst & Hsrc & Ha & Hworld & #Hnormal) HΦ".
    iDestruct (world_interp_open_load_witness_eq _ Wval _ _ raw with "Hworld")
      as "[Hworld Hwit]".
    iApply (switcher_load_stack_restore_witness with "[$HPC $Hi $Hdst $Hsrc $Ha $Hwit]"); eauto.
    iNext. iIntros (actual) "(%Hpost & HPC & Hi & Hdst & Hsrc & Ha & _)".
    iDestruct (interp_in_mem_load_post with "Hnormal") as "#Hactual"; first exact Hpost.
    pose proof (load_post_world_load_heap_in_world Wval RWL raw actual Hpost) as Hloaded.
    rewrite lload_word_RWL in Hloaded.
    iApply "HΦ". by iFrame "∗#".
  Qed.
End Switcher_Restore_Interp.
