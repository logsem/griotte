From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode world_ghost_theory.
From griotte Require Import vae_spec_states.

(** * VAE, blocks 7-9: second call to the callback [g]

    From the return of the first call to [g], block 7 sets the flag to [1],
    updates the custom location [i] of the flag to [true] accordingly, and
    restores the return address in [cra] and the callback [g] in [ct1].
    Block 8 fetches the entry point of the switcher in [ct0]. The first four
    instructions of block 9 save the return address in [cs0], clear the
    arguments and jump to the switcher. The group ends at the entry point
    of the switcher, with the return address of the call in [cra]. *)

Section VAE_Awkward_Blocks_2.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma vae_awkward_blocks_2_spec
    (pc_b pc_e pc_a : Addr) (C_f : Sealable)
    (cgp_b cgp_e : Addr) (W : WORLD) (C : CmptName) (i : positive) (N : namespace)
    (wret wg wcra wca0 wca1 wct0 wct1 : Word) :
    vae_code_bounds pc_b pc_e pc_a C_f ->
    (cgp_b < cgp_e)%a ->
    revoke_condition W ->
    related_sts_priv_world W (<l[i:=true]l>W) ->
    inv N (awk_inv C i cgp_b) ∗
    world_interp W C ∗
    PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ vae_block_offset 7)%a ∗
    cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
    cra ↦ᵣ wcra ∗
    ca0 ↦ᵣ wca0 ∗
    ca1 ↦ᵣ wca1 ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    cs0 ↦ᵣ wret ∗
    cs1 ↦ᵣ wg ∗
    pc_b ↦ₐ vae_switcher_entry ∗
    codefrag pc_a vae_main_code ∗
    ▷ (world_interp (<l[i:=true]l>W) C ∗
        PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call ∗
        cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
        cra ↦ᵣ WSentry RX Global pc_b pc_e (pc_a ^+ vae_instr_offset 9 4)%a ∗
        ca0 ↦ᵣ WInt 0 ∗
        ca1 ↦ᵣ WInt 0 ∗
        ct0 ↦ᵣ vae_switcher_entry ∗
        ct1 ↦ᵣ wg ∗
        cs0 ↦ᵣ wret ∗
        cs1 ↦ᵣ WInt 0 ∗
        pc_b ↦ₐ vae_switcher_entry ∗
        codefrag pc_a vae_main_code
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ([HsubBounds Himports_contiguous] Hcgp_bounds Hrevoke Hpriv)
      "(#Hawk & Hworld & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hct0 & Hct1 & Hcs0 & Hcs1
      & Himport_switcher & Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    vae_unfold_code.
    rewrite /vae_switcher_entry.

    (* Block 7: set the flag to [1], restore [cra] and [ct1] *)
    focus_block 7 "Hcode_main" of vae_main_blocks at pc_a as a_store Ha_store "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Store cgp 1 *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iMod (inv_acc with "Hawk") as "(>(%b & Hst & Hflag) & Hclose)"; auto.
    iAssert (cgp_b ↦ₐ (if b then WInt 1 else WInt 0))%I with "[Hflag]" as "Hflag".
    { destruct b; iFrame. }
    iApply (wp_store_success_z with "[$HPC $Hi $Hcgp $Hflag]"); try solve_pure.
    { apply withinBounds_true_iff; solve_addr+Hcgp_bounds. }
    iIntros "!> (HPC & Hi & Hcgp & Hflag)".
    iMod (world_interp_update_loc _ _ _ _ true with "Hworld Hst")
      as "[Hworld Hst]"; [done|done|].
    iMod ("Hclose" with "[$Hst $Hflag]") as "_".
    iModIntro.
    wp_pure.
    iSpecialize ("Hcode" with "[$]").
    (* Mov cra cs0 *)
    iInstr "Hcode".
    (* Mov ct1 cs1 *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 8: fetch the entry point of the switcher *)
    focus_block 8 "Hcode_main" of vae_main_blocks at pc_a as a_fetch Ha_fetch "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hct0 $Hcs0 $Hcs1 $Hcode]"); eauto.
    { apply withinBounds_true_iff; solve_addr. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext; iIntros "(HPC & Hct0 & Hcs0 & Hcs1 & Hcode & Himport_switcher)".
    iEval (cbn) in "Hct0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 9: save the return address, clear the arguments, jump to the
       switcher *)
    focus_block 9 "Hcode_main" of vae_main_blocks at pc_a as a_call Ha_call "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Mov cs0 cra *)
    iInstr "Hcode".
    (* Mov ca0 0 *)
    iInstr "Hcode".
    (* Mov ca1 0 *)
    iInstr "Hcode".
    (* Jalr cra ct0 *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    assert ((a_call ^+ 4)%a = (pc_a ^+ vae_instr_offset 9 4)%a) as ->
      by (offsets_compute; solve_addr).
    iApply "Hpost"; iFrame.
  Qed.

End VAE_Awkward_Blocks_2.
