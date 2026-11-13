From iris.proofmode Require Import proofmode.
From griotte Require Import instructions.memory_accesses map_simpl register_tactics logrel.
From griotte Require Import world_ghost_theory wp_rules_interp.
From griotte Require Export call_stack.
From griotte Require Import switcher_link.

Section Switcher_Restore.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {th : Thread} {CL : CritLink Σ th}
    `{MP : MachineParameters}.

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
    iIntros (Hea Hshadow Hinstr Hvpc Hbounds Hpc Hdst Hsrc Φ) "Hpre HΦ".
    iApply (wp_load_witness_imm_one_inbounds with "Hpre"); [done.. |].
    iIntros "!>" (actual) "Hpost". iApply ("HΦ" with "Hpost").
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
    {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg : sealStoreG Σ}
    {stsg : STSG Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP : MachineParameters} {swlayout : switcherLayout}.

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
    {{{ actual, RET NextIV; ⌜load_heap raw actual⌝ ∗
        PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ[th] actual ∗ src ↦ᵣ[th] Cap RWL Local b e a ∗
        ea ↦ₐ raw ∗ world_interp_open Wworld C opened ∗ interp Wval C actual }}}.
  Proof.
    iIntros (Hea Hshadow Hinstr Hvpc Hbounds Hpc Hdst Hsrc Φ)
      "(HPC & Hi & Hdst & Hsrc & Ha & Hworld & #Hnormal) HΦ".
    iPoseProof load_witness_plain_intro as "Hwit".
    iApply (switcher_load_stack_restore_witness with "[$HPC $Hi $Hdst $Hsrc $Ha $Hwit]"); eauto.
    iNext. iIntros (actual) "(%Hpost & HPC & Hi & Hdst & Hsrc & Ha & _)".
    iDestruct (interp_in_mem_load_post with "Hnormal") as "#Hactual"; first exact Hpost.
    pose proof (load_post_plain_load_heap RWL raw actual Hpost) as Hloaded.
    rewrite lload_word_RWL in Hloaded.
    iApply "HΦ". by iFrame "∗#".
  Qed.

  (** Restore one saved register beside the local map of [Wworld] and the
      part of the world premise that holds the map of Permanent regions,
      both unchanged. *)
  Lemma switcher_load_stack_restore_local {dq : dfrac} E Wworld C opened
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
        local_region_map th Wworld C (open_l Wworld opened) ∗
        perm_resources C }}}
      Instr Executable @[th] E
    {{{ actual, RET NextIV;
        ⌜load_heap raw actual⌝ ∗
        PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ[th] actual ∗ src ↦ᵣ[th] Cap RWL Local b e a ∗
        ea ↦ₐ raw ∗
        local_region_map th Wworld C (open_l Wworld opened) ∗
        perm_resources C }}}.
  Proof.
    iIntros (Hea Hshadow Hinstr Hvpc Hbounds Hpc Hdst Hsrc Φ)
      "(HPC & Hi & Hdst & Hsrc & Ha & Hlocal & Hperm) HΦ".
    iPoseProof load_witness_plain_intro as "Hwit".
    iApply (switcher_load_stack_restore_witness with "[$HPC $Hi $Hdst $Hsrc $Ha $Hwit]"); eauto.
    iNext. iIntros (actual) "(%Hpost & HPC & Hi & Hdst & Hsrc & Ha & _)".
    pose proof (load_post_plain_load_heap RWL raw actual Hpost) as Hloaded.
    rewrite lload_word_RWL in Hloaded.
    iApply "HΦ". by iFrame.
  Qed.

  (** [switcher_load_stack_restore_interp] over the local map of
      [Wworld]. *)
  Lemma switcher_load_stack_restore_local_interp {dq : dfrac} E Wworld Wval C opened
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
        local_region_map th Wworld C (open_l Wworld opened) ∗
        perm_resources C ∗
        interp_in_mem RWL Wval C raw }}}
      Instr Executable @[th] E
    {{{ actual, RET NextIV; ⌜load_heap raw actual⌝ ∗
        PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ[th] actual ∗ src ↦ᵣ[th] Cap RWL Local b e a ∗
        ea ↦ₐ raw ∗
        local_region_map th Wworld C (open_l Wworld opened) ∗
        perm_resources C ∗
        interp Wval C actual }}}.
  Proof.
    iIntros (Hea Hshadow Hinstr Hvpc Hbounds Hpc Hdst Hsrc Φ)
      "(HPC & Hi & Hdst & Hsrc & Ha & Hlocal & Hperm & #Hnormal) HΦ".
    iPoseProof load_witness_plain_intro as "Hwit".
    iApply (switcher_load_stack_restore_witness with "[$HPC $Hi $Hdst $Hsrc $Ha $Hwit]"); eauto.
    iNext. iIntros (actual) "(%Hpost & HPC & Hi & Hdst & Hsrc & Ha & _)".
    iDestruct (interp_in_mem_load_post with "Hnormal") as "#Hactual"; first exact Hpost.
    pose proof (load_post_plain_load_heap RWL raw actual Hpost) as Hloaded.
    rewrite lload_word_RWL in Hloaded.
    iApply "HΦ". by iFrame "∗#".
  Qed.
End Switcher_Restore_Interp.
