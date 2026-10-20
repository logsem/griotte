From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import stack_object_spec_states.

(** * Stack object, blocks 7-9: call to the callback [g]

    Block 7 pushes the secret on the stack and allocates the one-cell stack
    object [z] (in [ca1]) right after it. Block 8 fetches the entry point of
    the switcher in [ct0], and block 9 jumps to the switcher. The group ends
    at the entry point of the switcher, with the return address of the call
    in [cra]. *)

Section SO_Call_Blocks_3.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma so_call_blocks_3_spec
    (pc_b pc_e pc_a : Addr) (C_f : Sealable)
    (csp_b csp_e : Addr) (stk_mem : list LWord)
    (wca1 wct0 wct1 wcs0 wcs1 wcra : LWord) :
    so_code_bounds pc_b pc_e pc_a C_f ->
    disjoint_from_shadow csp_b csp_e ->
    disjoint_from_heap csp_b csp_e ->
    (* The stack frame holds the secret and [z] *)
    (csp_b + 2 <= csp_e)%Z ->
    PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ so_label_offset ".Lso_f_alloc")%a ∗
    csp ↦ᵣ WCap true RWL Local csp_b csp_e csp_b ∗
    ca1 ↦ᵣ wca1 ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    cra ↦ᵣ wcra ∗
    [[csp_b, csp_e]] ↦ₐ [[stk_mem]] ∗
    pc_b ↦ₐ□ so_switcher_entry ∗
    codefrag_pers pc_a so_main_code ∗
    ▷ (∀ mie a_stk1 a_stk2 stk_mem',
        ⌜(csp_b + 1)%a = Some a_stk1⌝ ∗
        ⌜(a_stk1 + 1)%a = Some a_stk2⌝ ∗
        ⌜(a_stk2 <= csp_e)%a⌝ ∗
        PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_call ∗
        csp ↦ᵣ WCap true RWL Local csp_b csp_e a_stk2 ∗
        ca1 ↦ᵣ WCap true RWL Local a_stk1 a_stk2 a_stk1 ∗
        ct0 ↦ᵣ so_switcher_entry ∗
        ct1 ↦ᵣ wct1 ∗
        cs0 ↦ᵣ wcra ∗
        cs1 ↦ᵣ wct1 ∗
        cra ↦ᵣ WSentry (ret_kind mie) true RX Global pc_b pc_e (pc_a ^+ so_label_offset ".Lso_f_after_call")%a ∗
        csp_b ↦ₐ WInt so_secret ∗
        a_stk1 ↦ₐ WInt 0 ∗
        [[a_stk2, csp_e]] ↦ₐ [[stk_mem']] ∗
        pc_b ↦ₐ□ so_switcher_entry ∗
        codefrag_pers pc_a so_main_code
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap) Hstk_shadow Hstk_heap Hstk_size)
      "(HPC & Hcsp & Hca1 & Hct0 & Hct1 & Hcs0 & Hcs1 & Hcra & Hstk & Himport_switcher
      & Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    so_unfold_code.
    rewrite /so_switcher_entry.

    (* Block 7: push the secret and allocate the stack object [z] *)
    focus_block (so_block ".Lso_f_alloc") "Hcode_main" of so_main_blocks at pc_a as a_alloc Ha_alloc "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    assert (csp_b < csp_e)%a as Hcsp_size by solve_addr+Hstk_size.
    iDestruct (big_sepL2_length with "Hstk") as %Hstklen.
    rewrite finz_seq_between_length in Hstklen.
    rewrite finz_dist_S in Hstklen; last solve_addr+Hcsp_size.
    destruct stk_mem as [|w0 stk_mem]; simplify_eq.
    assert (is_Some (csp_b + 1)%a) as [a_stk1 Hastk1]; [solve_addr+Hcsp_size|].
    iDestruct (region_pointsto_cons with "Hstk") as "[Hastk0 Hstk]"; eauto.
    { solve_addr+Hcsp_size Hastk1. }
    (* Store csp so_secret 0 *)
    iInstr "Hcode".
    { eapply disjoint_from_shadow_not_in; [exact Hstk_shadow|rewrite /withinBounds; solve_addr+Hcsp_size]. }
    { rewrite /withinBounds; solve_addr+Hcsp_size. }
    (* Lea csp 1 *)
    iInstr "Hcode".
    (* Mov ca1 csp *)
    iInstr "Hcode".
    (* GetA cs0 ca1 *)
    iInstr "Hcode".
    (* Add cs1 cs0 1 *)
    iInstr "Hcode".
    assert (a_stk1 < csp_e)%a as Hcsp_size' by solve_addr+Hstk_size Hastk1.
    iDestruct (big_sepL2_length with "Hstk") as %Hstklen'.
    rewrite finz_seq_between_length in Hstklen'.
    rewrite finz_dist_S in Hstklen'; last solve_addr+Hcsp_size'.
    destruct stk_mem as [|w1 stk_mem]; simplify_eq.
    assert (is_Some (a_stk1 + 1)%a) as [a_stk2 Hastk2]; [solve_addr+Hcsp_size'|].
    iDestruct (region_pointsto_cons with "Hstk") as "[Hastk1 Hstk]"; eauto.
    { solve_addr+Hcsp_size Hastk1 Hcsp_size' Hastk2. }
    assert (is_heap_address a_stk1 = false) as Hastk1_nonheap.
    { eapply disjoint_from_heap_not_in; [exact Hstk_heap|].
      rewrite /withinBounds; solve_addr+Hcsp_size Hastk1 Hcsp_size' Hastk2. }
    (* Subseg ca1 cs0 cs1 *)
    iInstr "Hcode".
    { transitivity (Some a_stk2); auto. solve_addr+Hastk2. }
    { solve_addr+Hcsp_size Hastk1 Hcsp_size' Hastk2. }
    { solve_addr+Hastk2. }
    (* Store ca1 0%Z 0 *)
    iInstr "Hcode".
    { eapply disjoint_from_shadow_not_in; [exact Hstk_shadow|].
      rewrite /withinBounds; solve_addr+Hcsp_size Hastk1 Hcsp_size' Hastk2. }
    { solve_addr+Hcsp_size Hastk1 Hcsp_size' Hastk2. }
    (* Lea csp 1%Z *)
    iInstr "Hcode".
    replace (a_stk1 ^+ 1)%a with a_stk2 by solve_addr+Hastk2.
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 8: fetch the entry point of the switcher *)
    focus_block (so_block ".Lso_f_fetch_switcher") "Hcode_main" of so_main_blocks at pc_a as a_fetch Ha_fetch "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (fetch_spec 0 _ _ _ _ _ _ _
      (WSentry FwdDisable true XSRW_ Local b_switcher e_switcher a_switcher_call)
      with "[- $HPC $Hct0 $Hcode]"); eauto using switcher_call_sentry_not_heap; try done.
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff; solve_addr. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext; iIntros "(HPC & Hct0 & _ & Himport_switcher)".
    iEval (cbn) in "Hct0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 9: jump to the switcher *)
    focus_block (so_block ".Lso_f_call") "Hcode_main" of so_main_blocks at pc_a as a_call Ha_call "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Mov cs0 cra *)
    iInstr "Hcode".
    (* Mov cs1 ct1 *)
    iInstr "Hcode".
    (* Jalr cra ct0 *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    assert ((a_call ^+ 3)%a = (pc_a ^+ so_label_offset ".Lso_f_after_call")%a) as ->
      by (offsets_compute; solve_addr).
    iApply ("Hpost" $! mie a_stk1 a_stk2 stk_mem); iFrame "∗ Hcode_main".
    iPureIntro; repeat split; solve_addr.
  Qed.

End SO_Call_Blocks_3.
