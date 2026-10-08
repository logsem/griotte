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
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma vae_awkward_blocks_3_spec
    (pc_b pc_e pc_a : Addr) (C_f : Sealable)
    (cgp_b cgp_e : Addr) (W : WORLD) (C : CmptName) (i : positive) (N : namespace)
    (Nassert : namespace) (E : coPset)
    (wret wcra wca0 wca1 wct0 wct1 wct2 wct3 wct4 wcnull : Word) :
    vae_code_bounds pc_b pc_e pc_a C_f ->
    (cgp_b < cgp_e)%a ->
    loc W !! i = Some (encode true) ->
    ↑Nassert ⊆ E ->
    inv N (awk_inv C i cgp_b) ∗
    world_interp W C ∗
    na_inv cerise_nais Nassert (assert_inv b_assert e_assert a_flag) ∗
    na_own cerise_nais E ∗
    PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ vae_instr_offset 9 4)%a ∗
    cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
    cra ↦ᵣ wcra ∗
    cs0 ↦ᵣ wret ∗
    ca0 ↦ᵣ wca0 ∗
    ca1 ↦ᵣ wca1 ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    ct3 ↦ᵣ wct3 ∗
    ct4 ↦ᵣ wct4 ∗
    cnull ↦ᵣ wcnull ∗
    (pc_b ^+ 1)%a ↦ₐ vae_assert_entry ∗
    codefrag pc_a vae_main_code ∗
    ▷ (world_interp W C ∗
        na_own cerise_nais E ∗
        PC ↦ᵣ updatePcPerm wret ∗
        cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
        cra ↦ᵣ wret ∗
        cs0 ↦ᵣ wret ∗
        ca0 ↦ᵣ WInt 0 ∗
        ca1 ↦ᵣ WInt 0 ∗
        ct0 ↦ᵣ WInt 0 ∗
        ct1 ↦ᵣ WInt 0 ∗
        ct2 ↦ᵣ WInt 0 ∗
        ct3 ↦ᵣ WInt 0 ∗
        ct4 ↦ᵣ WInt 0 ∗
        cnull ↦ᵣ WInt 0 ∗
        (pc_b ^+ 1)%a ↦ₐ vae_assert_entry ∗
        codefrag pc_a vae_main_code
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ([HsubBounds Himports_contiguous] Hcgp_bounds Hloc HNassert)
      "(#Hawk & Hworld & #Hassert & Hna & HPC & Hcgp & Hcra & Hcs0 & Hca0 & Hca1
      & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hcnull
      & Himport_assert & Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    vae_unfold_code.
    rewrite /vae_assert_entry.

    (* Block 9: load the flag, which is [1] *)
    focus_block 9 "Hcode_main" of vae_main_blocks at pc_a as a_load Ha_load "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    change_pc_to (a_load ^+ 4)%a.
    (* Load ct0 cgp *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iMod (inv_acc with "Hawk") as "(>(%b & Hst & Hflag) & Hclose)"; auto.
    iDestruct (world_interp_loc_valid with "Hworld Hst") as %Hloc'.
    rewrite Hloc in Hloc'; simplify_eq.
    iApply (wp_load_success_alt with "[$HPC $Hi $Hct0 $Hcgp $Hflag]"); try solve_pure.
    { split; last apply withinBounds_true_iff; solve_addr+Hcgp_bounds. }
    iIntros "!> (HPC & Hct0 & Hi & Hcgp & Hflag)".
    iMod ("Hclose" with "[$Hst $Hflag]") as "_".
    iModIntro.
    wp_pure.
    iSpecialize ("Hcode" with "[$]").
    iEval (cbn) in "Hct0".
    (* Mov ct1 1 *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 10: assert that the flag is [1] *)
    focus_block 10 "Hcode_main" of vae_main_blocks at pc_a as a_assert Ha_assert "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (assert_success_spec with
             "[- $Hassert $Hna $HPC $Hct2 $Hct3 $Hct4 $Hct0 $Hct1 $Hcnull $Hcra
              $Hcode $Himport_assert]"); auto.
    { apply withinBounds_true_iff; solve_addr. }
    iNext; iIntros "(Hna & HPC & Hct2 & Hct3 & Hct4 & Hcra & Hct0 & Hct1 & Hcnull
                    & Hcode & Himport_assert)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 11: restore the return address, clear the return values, and
       return *)
    focus_block 11 "Hcode_main" of vae_main_blocks at pc_a as a_ret Ha_ret "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Mov cra cs0 *)
    iInstr "Hcode".
    (* Mov ca0 0 *)
    iInstr "Hcode".
    (* Mov ca1 0 *)
    iInstr "Hcode".
    (* Jalr cnull cra *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    iApply "Hpost"; iFrame.
  Qed.

End VAE_Awkward_Blocks_3.
