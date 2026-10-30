From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel.
From griotte Require Import assert_spec switcher_base.
From griotte.case_studies.hts_ownership Require Import heap_temporal_safety heap_temporal_safety_preamble.
From griotte.allocators.ownership Require Import allocator allocator_preamble.
From griotte Require Import proofmode register_tactics map_simpl.
From griotte.case_studies.hts_ownership Require Import hts_spec_states.

(** * Segment (e): blocks 21-23

    Assert that [p] still holds [0], and return: the thread exits. Block 23,
    the return, is also reached from the failed result checks of the
    segments (b) and (d) ([hts_return_spec]). *)

Section HTS_Return.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}
  .

  (** Block 23: return through the switcher's return sentry, saved in
      [cs0]: the thread exits. *)
  Lemma hts_return_spec
    (pc_b pc_e pc_a : Addr) (cstk : CSTK) (wcra wctp wct0 wct2 : LWord) :
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_main_code) ->
    cstk.(cstk_frames) = [] ->
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static ∗
    na_own (tpool th) ⊤ ∗
    PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ hts_label_offset ".Lhts_return")%a ∗
    cs0 ↦ᵣ[th] thread_return_sentry ∗
    cra ↦ᵣ[th] wcra ∗
    ctp ↦ᵣ[th] wctp ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    ◯(CSTK)[th] cstk ∗
    codefrag_pers pc_a hts_main_code
    ⊢ safe[th].
  Proof.
    iIntros (HsubBounds Hframes)
      "(#Hswitcher & #Hswitcher_static & Hna & HPC & Hcs0 & Hcra & Hctp & Hct0 & Hct2
        & Hcstk & Hcode_main)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    unfold_code hts_main_code "Hcode_main".
    focus_block (hts_block ".Lhts_return") "Hcode_main" of hts_main_blocks at pc_a
      as a_ret Ha_ret "Hcode" "Hcont".
    (* Mov cra cs0 *)
    iInstr "Hcode".
    (* Jalr cnull cra *)
    iInstr "Hcode".
    iEval (rewrite thread_return_sentry_pc) in "HPC".
    iApply (switcher_ret_thread_exit_specification _ _ _ _ Hframes with
             "[$Hswitcher $Hswitcher_static $Hna $HPC $Hctp $Hct0 $Hct2 $Hcstk]").
  Qed.
End HTS_Return.

Section HTS_Spec_Assert.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {allocator_ownerg : allocatorOwnerG Σ}
    `{MP: MachineParameters}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .
  Context (C : CmptName).
  Context (pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e : Addr).
  Context (C_f : Sealable) (owner_a : Addr) (W_init_C : WORLD).
  Context (cstk : CSTK).

  #[local] Notation hts_ctx := (hts_main_ctx C C_f W_init_C).
  #[local] Notation adv2_ret := (hts_adv2_ret pc_b pc_e pc_a cgp_b cgp_e
    csp_b csp_e C_f owner_a cstk).

  Lemma hts_spec_assert :
    cstk.(cstk_frames) = [] ->
    disjoint_from_shadow pc_b pc_e ->
    disjoint_from_shadow cgp_b cgp_e ->
    (cgp_b + length hts_main_data)%a = Some cgp_e ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_main_code) ->
    (pc_b + hts_label ".Lhts_main")%a = Some pc_a ->
    hts_ctx ∗
    adv2_ret
    ⊢ safe[th].
  Proof.
    iIntros (Hframes Hpc_shadow Hcgp_shadow Hcgp_contiguous HsubBounds Himports_contiguous)
      "(#Hctx & Hret)".
    iDestruct "Hctx" as "(#Hassert & _ & _ & #Hswitcher & #Hswitcher_static & _)".
    iDestruct "Hret" as "(Hframe & Hregs)".
    iDestruct "Hframe" as "(Hna & HPC & [%mie_ret Hcra] & Hcgp & Hcsp & Hcs0 & _ & Hcstk
      & Himports & Hcode_main & Hp & _)".
    iDestruct "Himports" as "(_ & Himport_assert & _)".
    iDestruct "Hregs" as (rmap Hdom_rmap) "Hrmap".
    rewrite /hts_main_data in Hcgp_contiguous.
    assert (cgp_b < cgp_e)%a as Hcgp_size by solve_addr.
    codefrag_facts "Hcode_main". clear H0.
    unfold_code hts_main_code "Hcode_main".

    (* Block 21: load p and prepare zero for the assertion. *)
    focus_block (hts_block ".Lhts_prep_assert") "Hcode_main" of hts_main_blocks at pc_a as a_prep Ha_prep "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ct0;ct1] as ["[Hct0 _]";"[Hct1 _]"].
    (* CLoad ct0 cgp 0. *)
    iInstr "Hcode".
    { eapply disjoint_from_shadow_not_in; [exact Hcgp_shadow|rewrite /withinBounds; solve_addr]. }
    { done. }
    { split; first done. apply withinBounds_true_iff; solve_addr. }
    (* Mov ct1 0. *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 22: fetch and call the assertion service. *)
    focus_block (hts_block ".Lhts_assert") "Hcode_main" of hts_main_blocks at pc_a as a_assert Ha_assert "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ctp;ct2;ca2] as
      ["[Hctp _]";"[Hct2 _]";"[Hca2 _]"].
    iApply (assert_success_spec 1 with
      "[- $Hassert $HPC $Hct2 $Hca2 $Hct0 $Hct1
        $Hcra $Hcode $Himport_assert]"); auto; try (by intros ?).
    { offsets_compute; solve_addr. }
    { solve_addr. }
    iNext; iIntros "(HPC & Hct2 & Hca2 & Hcra & Hct0
      & Hct1 & _ & Himport_assert)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 23: return, the thread exits *)
    assert (a_assert ^+ length (assert_instrs (-47) ct2 ca2) =
              (pc_a ^+ hts_label_offset ".Lhts_return")%a) as ->
      by (offsets_compute; solve_addr).
    iApply (hts_return_spec with
             "[$Hswitcher $Hswitcher_static $Hna $HPC $Hcs0 $Hcra $Hctp $Hct0 $Hct2
               $Hcstk $Hcode_main]"); [done | done].
  Qed.
End HTS_Spec_Assert.
