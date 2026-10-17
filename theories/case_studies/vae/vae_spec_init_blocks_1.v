From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode world_ghost_theory.
From griotte Require Import vae_spec_states.

(** * VAE, blocks 0-3: call to the adversary [B.adv]

    Block 0 sets the flag to [0], block 1 fetches the entry point of the
    switcher in [ct0], block 2 fetches the entry point of [B.adv] in [ct1],
    and the first instruction of block 3 jumps to the switcher. The group
    ends at the entry point of the switcher, with the return address of the
    call in [cra]. *)

Section VAE_Init_Blocks_1.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma vae_init_blocks_1_spec
    (pc_b pc_e pc_a : Addr) (C_f : Sealable)
    (cgp_b cgp_e : Addr) (W : WORLD) (C : CmptName) (i : positive) (N : namespace)
    (wct0 wct1 wcra : LWord) :
    vae_code_bounds pc_b pc_e pc_a C_f ->
    (cgp_b < cgp_e)%a ->
    is_shadow_address cgp_b = false ->
    is_heap_cap (WSealed ot_switcher C_f) = false ->
    loc W !! i = Some (encode false) ->
    inv N (awk_inv C i cgp_b) ∗
    world_interp W C ∗
    PC ↦ₚ WCap true RX Global pc_b pc_e pc_a ∗
    cgp ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_b ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    cra ↦ᵣ wcra ∗
    pc_b ↦ₐ□ vae_switcher_entry ∗
    (pc_b ^+ 2)%a ↦ₐ□ WSealed ot_switcher C_f ∗
    codefrag_pers pc_a vae_main_code ∗
    ▷ (world_interp W C ∗
        PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_call ∗
        cgp ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_b ∗
        ct0 ↦ᵣ vae_switcher_entry ∗
        ct1 ↦ᵣ WSealed ot_switcher C_f ∗
        cra ↦ᵣ WSentry true RX Global pc_b pc_e (pc_a ^+ vae_label_offset ".Lvae_init_halt")%a ∗
        pc_b ↦ₐ□ vae_switcher_entry ∗
        (pc_b ^+ 2)%a ↦ₐ□ WSealed ot_switcher C_f ∗
        codefrag_pers pc_a vae_main_code
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap) Hcgp_bounds
               Hcgp_shadow Hsealed_nonheap Hloc)
      "(#Hawk & Hworld & HPC & Hcgp & Hct0 & Hct1 & Hcra
      & Himport_switcher & Himport_C_f & Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    vae_unfold_code.
    rewrite /vae_switcher_entry.

    (* Block 0: set the flag to [0] *)
    focus_block_0 "Hcode_main" as "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Store cgp 0 0 *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iMod (inv_acc with "Hawk") as "(>(%b & Hst & Hflag) & Hclose)"; auto.
    iDestruct (world_interp_loc_valid with "Hworld Hst") as %Hloc'.
    rewrite Hloc in Hloc'; simplify_eq.
    iPoseProof deref_res_none as "Hdw".
    iApply (wp_store_success_z with "[$HPC $Hi $Hcgp $Hflag $Hdw]"); try solve_pure.
    { apply withinBounds_true_iff; solve_addr+Hcgp_bounds. }
    iIntros "!> (HPC & Hi & Hcgp & Hflag & _)".
    iMod ("Hclose" with "[$Hst $Hflag]") as "_".
    iModIntro.
    wp_pure.
    iClear "Hi".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 1: fetch the entry point of the switcher *)
    focus_block (vae_block ".Lvae_init_fetch_switcher") "Hcode_main" of vae_main_blocks at pc_a as a_fetch1 Ha_fetch1 "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (fetch_spec 0 _ _ _ _ _ _ _
      (WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call)
      with "[- $HPC $Hct0 $Hcode]"); eauto using switcher_call_sentry_not_heap; try done.
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff; solve_addr. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext; iIntros "(HPC & Hct0 & _ & Himport_switcher)".
    iEval (cbn) in "Hct0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 2: fetch the entry point of [B.adv] *)
    focus_block (vae_block ".Lvae_init_fetch_adv") "Hcode_main" of vae_main_blocks at pc_a as a_fetch2 Ha_fetch2 "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hct1 $Hcode $Himport_C_f]"); eauto; try done.
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff; solve_addr. }
    iNext; iIntros "(HPC & Hct1 & _ & Himport_C_f)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 3: jump to the switcher *)
    focus_block (vae_block ".Lvae_init_call") "Hcode_main" of vae_main_blocks at pc_a as a_call Ha_call "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Jalr cra ct0 *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    assert ((a_call ^+ 1)%a = (pc_a ^+ vae_label_offset ".Lvae_init_halt")%a) as ->
      by (offsets_compute; solve_addr).
    iApply "Hpost"; iFrame "∗ Hcode_main".
  Qed.

End VAE_Init_Blocks_1.
