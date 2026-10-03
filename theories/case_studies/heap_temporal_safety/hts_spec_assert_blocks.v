From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel.
From griotte Require Import assert_spec switcher_spec_call
  heap_temporal_safety heap_temporal_safety_preamble.
From griotte.allocator Require Import allocator allocator_preamble.
From griotte Require Import proofmode register_tactics map_simpl.
From griotte Require Import hts_spec_states.

(** * Segment (e): blocks 20-22

    Assert that [p] still holds [0], and halt. *)

Section HTS_Spec_Assert.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {FA : FreeAuth Σ}
    `{MP: MachineParameters}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .
  Context (C : CmptName).
  Context (pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e : Addr).
  Context (C_f : Sealable) (W_init_C : WORLD).
  Context (Nassert Nswitcher : namespace) (cstk : CSTK).

  Local Notation hts_ctx := (hts_main_ctx C C_f W_init_C Nassert Nswitcher).
  Local Notation adv2_ret := (hts_adv2_ret pc_b pc_e pc_a cgp_b cgp_e
    csp_b csp_e C_f cstk).

  Lemma hts_spec_assert :
    disjoint_from_shadow pc_b pc_e ->
    disjoint_from_shadow cgp_b cgp_e ->
    (cgp_b + length hts_main_data)%a = Some cgp_e ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_main_code)%a ->
    hts_ctx ∗
    adv2_ret
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hpc_shadow Hcgp_shadow Hcgp_contiguous HsubBounds) "(#Hctx & Hret)".
    iDestruct "Hctx" as "(#Hassert & _)".
    iDestruct "Hret" as (a_ret Ha_ret) "(Hframe & Hregs)".
    iDestruct "Hframe" as "(Hna & HPC & Hcra & Hcgp & Hcsp & _ & _ & _
      & Himports & Hcode & Hp)".
    iDestruct "Himports" as "(_ & Himport_assert & _)".
    iDestruct "Hregs" as (rmap Hdom_rmap) "Hrmap".
    rewrite /hts_main_data in Hcgp_contiguous.
    assert (cgp_b < cgp_e)%a as Hcgp_size by solve_addr.
    codefrag_facts "Hcode". clear H0.
    iEval (rewrite /hts_main_code /assembled_hts_main /assembled_hts_main') in "Hcode".
    iEval (cbv [fmap list_fmap concat]) in "Hcode".

    (* Block 20: load p and prepare zero for the assertion. *)
    hts_focus_entry_block 20 "Hcode" as a_prep Ha_prep "Hblock" "Hcont"
      from Ha_ret.
    iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ct0;ct1] as ["[Hct0 _]";"[Hct1 _]"].
    (* Load ct0 cgp 0. *)
    iInstr "Hblock".
    (* Mov ct1 0. *)
    iInstr "Hblock".
    subst hcont; unfocus_block "Hblock" "Hcont" as "Hcode".

    (* Block 21: fetch and call the assertion service. *)
    focus_block 21 "Hcode" as a_assert Ha_assert "Hblock" "Hcont";
      iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ct2;ct3;ct4;cnull] as
      ["[Hct2 _]";"[Hct3 _]";"[Hct4 _]";"[Hcnull _]"].
    iApply (assert_success_spec with
      "[- $Hassert $Hna $HPC $Hct2 $Hct3 $Hct4 $Hct0 $Hct1
        $Hcnull $Hcra $Hblock $Himport_assert]"); auto.
    { solve_addr. }
    iNext; iIntros "(Hna & HPC & Hct2 & Hct3 & Hct4 & Hcra & Hct0
      & Hct1 & Hcnull & Hblock & Himport_assert)".
    subst hcont; unfocus_block "Hblock" "Hcont" as "Hcode".

    (* Block 22: halt with the assertion service token restored. *)
    focus_block 22 "Hcode" as a_halt Ha_halt "Hblock" "Hcont";
      iHide "Hcont" as hcont.
    (* Halt. *)
    iInstr "Hblock".
    wp_end; iIntros "_"; iFrame.
  Qed.
End HTS_Spec_Assert.
