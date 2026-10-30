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
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma vae_init_blocks_1_spec
    (pc_b pc_e pc_a : Addr) (C_f : Sealable)
    (cgp_b cgp_e : Addr) (W : WORLD) (C : CmptName) (i : positive)
    (wct0 wct1 wcs0 wcra : LWord) :
    vae_code_bounds pc_b pc_e pc_a C_f ->
    (cgp_b < cgp_e)%a ->
    is_shadow_address cgp_b = false ->
    is_heap_cap (WSealed ot_switcher C_f) = false ->
    loc W !! i = Some (encode false) ->
    inv Nawk (awk_inv C i cgp_b) ∗
    world_interp W C ∗
    PC ↦ₚ[th] Cap RX Global pc_b pc_e pc_a ∗
    cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e cgp_b ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cra ↦ᵣ[th] wcra ∗
    pc_b ↦ₐ□ switcher_entry_call ∗
    (pc_b ^+ 2) ↦ₐ□ WSealed ot_switcher C_f ∗
    codefrag_pers pc_a vae_main_code ∗
    ▷ (∀ mie, world_interp W C ∗
        PC ↦ₚ[th] Cap XSRW_ Local b_switcher e_switcher a_switcher_call ∗
        cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e cgp_b ∗
        ct0 ↦ᵣ[th] switcher_entry_call ∗
        ct1 ↦ᵣ[th] WSealed ot_switcher C_f ∗
        cs0 ↦ᵣ[th] wcra ∗
        cra ↦ᵣ[th] Sentry (ret_kind mie) RX Global pc_b pc_e
          (pc_a ^+ vae_label_offset ".Lvae_init_return")%a ∗
        pc_b ↦ₐ□ switcher_entry_call ∗
        (pc_b ^+ 2) ↦ₐ□ WSealed ot_switcher C_f ∗
        codefrag_pers pc_a vae_main_code
        -∗ safe[th])
    ⊢ safe[th].
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap) Hcgp_bounds
               Hcgp_shadow Hsealed_nonheap Hloc)
      "(#Hawk & Hworld & HPC & Hcgp & Hct0 & Hct1 & Hcs0 & Hcra
      & Himport_switcher & Himport_C_f & Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    vae_unfold_code.
    rewrite /switcher_entry_call.

    (* Block 0: set the flag to [0] *)
    focus_block_0 "Hcode_main" as "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Store cgp 0 0 *)
    iInstrStart "Hcode".
    iMod (inv_acc with "Hawk") as "(>(%b & Hst & Hflag) & Hclose)"; auto.
    iDestruct (world_interp_loc_valid with "Hworld Hst") as %Hloc'.
    rewrite Hloc in Hloc'; simplify_eq.
    iPoseProof deref_res_none as "-#Hdw".
    iInstrApply wp_store_success_z with "[$HPC $Hcgp $Hflag $Hdw]"
      as "(HPC & Hcgp & Hflag & _)".
    { apply withinBounds_true_iff; solve_addr+Hcgp_bounds. }
    iMod ("Hclose" with "[$Hst $Hflag]") as "_".
    iInstrEnd.
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 1: fetch the entry point of the switcher *)
    focus_block (vae_block ".Lvae_init_fetch_switcher") "Hcode_main" of vae_main_blocks at pc_a as a_fetch1 Ha_fetch1 "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (fetch_spec 0 _ _ _ _ _ _ _
      switcher_entry_call
      with "[- $HPC $Hct0 $Hcode]"); eauto using switcher_call_sentry_not_heap; try done.
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff; solve_addr. }
    replace (pc_b ^+ 0) with pc_b by solve_addr.
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

    (* Block 3: save the return address and jump to the switcher *)
    focus_block (vae_block ".Lvae_init_call") "Hcode_main" of vae_main_blocks at pc_a as a_call Ha_call "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Mov cs0 cra *)
    iInstr "Hcode".
    (* Jalr cra ct0 *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    assert (a_call ^+ 2 = (pc_a ^+ vae_label_offset ".Lvae_init_return")%a) as ->
      by (offsets_compute; solve_addr).
    iApply "Hpost"; iFrame "∗ Hcode_main".
  Qed.

End VAE_Init_Blocks_1.
