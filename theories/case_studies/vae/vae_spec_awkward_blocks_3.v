From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode world_ghost_theory.
From griotte Require Import vae_spec_states.

(** * VAE, blocks 9-11: assert that the flag is [1], return

    From the return of the second call to [g], the last two instructions of
    block 9 load the flag in [ct0], which is [1] since the custom location
    [i] of the flag is [true], and [1] in [ct1]. Block 10 asserts that
    [ct0] and [ct1] are equal. Block 11 restores the return address in
    [cra], clears the return values and jumps to the switcher, for the
    return. *)

Section VAE_Awkward_Blocks_3.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma vae_awkward_blocks_3_spec
    (pc_b pc_e pc_a : Addr) (C_f : Sealable)
    (cgp_b cgp_e : Addr) (W : WORLD) (C : CmptName) (i : positive) (N : namespace)
    (wret wcra wca0 wca1 wct0 wct1 wct2 wca2 wcnull : LWord) :
    vae_code_bounds pc_b pc_e pc_a C_f ->
    (cgp_b < cgp_e)%a ->
    is_shadow_address cgp_b = false ->
    loc W !! i = Some (encode true) ->
    inv N (awk_inv C i cgp_b) ∗
    world_interp W C ∗
    assert_static b_assert e_assert a_flag ∗
    PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ vae_label_offset ".Lvae_awkward_check")%a ∗
    cgp ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_b ∗
    cra ↦ᵣ wcra ∗
    cs0 ↦ᵣ wret ∗
    ca0 ↦ᵣ wca0 ∗
    ca1 ↦ᵣ wca1 ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    ca2 ↦ᵣ wca2 ∗
    cnull ↦ᵣ wcnull ∗
    (pc_b ^+ 1)%a ↦ₐ□ vae_assert_entry ∗
    codefrag_pers pc_a vae_main_code ∗
    ▷ (world_interp W C ∗
        PC ↦ₚ lupdatePcPerm wret ∗
        cgp ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_b ∗
        cra ↦ᵣ wret ∗
        cs0 ↦ᵣ wret ∗
        ca0 ↦ᵣ WInt 0 ∗
        ca1 ↦ᵣ WInt 0 ∗
        ct0 ↦ᵣ WInt 0 ∗
        ct1 ↦ᵣ WInt 0 ∗
        ct2 ↦ᵣ WInt 0 ∗
        ca2 ↦ᵣ WInt 0 ∗
        cnull ↦ᵣ WInt 0 ∗
        (pc_b ^+ 1)%a ↦ₐ□ vae_assert_entry ∗
        codefrag_pers pc_a vae_main_code
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap) Hcgp_bounds
               Hcgp_shadow Hloc)
      "(#Hawk & Hworld & #Hassert & HPC & Hcgp & Hcra & Hcs0 & Hca0 & Hca1
      & Hct0 & Hct1 & Hct2 & Hca2 & Hcnull
      & Himport_assert & Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    vae_unfold_code.
    rewrite /vae_assert_entry.

    (* Block 9: load the flag, which is [1] *)
    focus_block (vae_block ".Lvae_awkward_call_2") "Hcode_main" of vae_main_blocks at pc_a as a_load Ha_load "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    change_pc_to (a_load ^+ 4)%a.
    (* CLoad ct0 cgp 0 *)
    iInstrStart "Hcode".
    iMod (inv_acc with "Hawk") as "(>(%b & Hst & Hflag) & Hclose)"; auto.
    iDestruct (world_interp_loc_valid with "Hworld Hst") as %Hloc'.
    rewrite Hloc in Hloc'; simplify_eq.
    iPoseProof deref_res_none as "-#Hdw".
    iInstrApply wp_load_success_alt with "[$HPC $Hct0 $Hcgp $Hflag $Hdw]"
      as "(HPC & Hct0 & Hcgp & Hflag & _)".
    { done. }
    { split; last apply withinBounds_true_iff; solve_addr+Hcgp_bounds. }
    iMod ("Hclose" with "[$Hst $Hflag]") as "_".
    iInstrEnd.
    iEval (cbn) in "Hct0".
    (* Mov ct1 1 *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 10: assert that the flag is [1] *)
    focus_block (vae_block ".Lvae_awkward_assert") "Hcode_main" of vae_main_blocks at pc_a as a_assert Ha_assert "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (assert_success_spec 1 with
             "[- $Hassert $HPC $Hct2 $Hca2 $Hct0 $Hct1 $Hcnull $Hcra
              $Hcode $Himport_assert]"); auto.
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff; solve_addr. }
    iNext; iIntros "(HPC & Hct2 & Hca2 & Hcra & Hct0 & Hct1 & Hcnull
                    & _ & Himport_assert)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 11: restore the return address, clear the return values, and
       return *)
    focus_block (vae_block ".Lvae_awkward_return") "Hcode_main" of vae_main_blocks at pc_a as a_ret Ha_ret "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Mov cra cs0 *)
    iInstr "Hcode".
    (* Mov ca0 0 *)
    iInstr "Hcode".
    (* Mov ca1 0 *)
    iInstr "Hcode".
    destruct (jalr_target_ok wret.(lw)) eqn:Htgt; cycle 1.
    { (* Jalr cnull cra *)
      iInstr_fail "Hcode".
      wp_end; by iIntros (?). }
    (* Jalr cnull cra *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    iApply "Hpost"; iFrame "∗ Hcode_main".
  Qed.

End VAE_Awkward_Blocks_3.
