From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import fetch_spec assert_spec switcher_spec_call
  heap_temporal_safety heap_temporal_safety_preamble.
From griotte.allocator Require Import allocator allocator_preamble.
From griotte Require Import heap_temporal_safety_allocator_spec world_ghost_theory heap_region.
From griotte Require Import world_interp_stack region_invariants heap_ghost.
From griotte Require Import proofmode register_tactics map_simpl.
From griotte Require Import hts_spec_states hts_spec_world.

(** * Segment (d): blocks 15-19

    Check the free result (halting on failure), quarantine the buffer in the
    world, and call [adv(0)]: the saved alias of the buffer is dangling. *)

Section HTS_Spec_Dangling.
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
  Context (Ws : list WORLD) (Cs : list CmptName).
  Context (Nassert Nswitcher : namespace) (cstk : CSTK).

  Local Notation hts_ctx := (hts_main_ctx C C_f W_init_C Nassert Nswitcher).
  Local Notation free_ret := (hts_free_ret C pc_b pc_e pc_a cgp_b cgp_e
    csp_b csp_e C_f Ws Cs cstk).
  Local Notation adv2_ret := (hts_adv2_ret pc_b pc_e pc_a cgp_b cgp_e
    csp_b csp_e C_f cstk).

  Lemma hts_spec_dangling :
    disjoint_from_shadow pc_b pc_e ->
    is_heap_address pc_b = false ->
    is_heap_cap (WSealed ot_switcher C_f) = false ->
    not_heap_range cgp_b cgp_e ->
    disjoint_from_mmio csp_b csp_e ->
    disjoint_from_heap csp_b csp_e ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_main_code)%a ->
    hts_ctx ∗
    free_ret ∗
    (adv2_ret -∗
     WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hpc_shadow Hpc_nonheap Hadv_nonheap Hcgp_heap Hstk_shadow Hstk_heap
      HsubBounds) "(#Hctx & Hret & Hcontinue)".
    iDestruct "Hctx" as "(#Hassert & #Hservice & #Hswitcher
       & #Hexport_pcc & #Hexport_cgp & #Hexport_malloc & #Hexport_free
       & #Hadv & #Hentry)".
    iDestruct "Hret" as (a_ret Ha_ret) "[Herr|Hok]".
    { (* Block 15: halt when free failed. *)
      iDestruct "Herr" as (z) "(%Hz & Hna & HPC & Hca0 & _ & Hcode)".
      codefrag_facts "Hcode". clear H0.
      iEval (rewrite /hts_main_code /assembled_hts_main /assembled_hts_main') in "Hcode".
      iEval (cbv [fmap list_fmap concat]) in "Hcode".
      hts_focus_entry_block 15 "Hcode" as a_free_result Ha_free_result
        "Hblock" "Hcont" from Ha_ret.
      (* Jnz 2 ca0. *)
      iInstr "Hblock".
      (* Halt. *)
      iInstr "Hblock".
      wp_end. by iIntros (?). }
    iDestruct "Hok" as (ι b Wret) "(%Hbounds & %Hstk_nonempty
      & %Hb_lookup & %Hstd_rev & #Hrel_b & Hframe & Hca0 & Hca1 & Hregs
      & [%stk Hstk] & Hworld_open & Hstate_b & Hstack_revoked_ret
      & %Hstack_revoked_ret & HK & #Hquar)".
    iDestruct "Hframe" as "(Hna & HPC & Hcra & Hcgp & Hcsp & [%wcs0 Hcs0]
      & [%wcs1 Hcs1] & Hcstk & Himports & Hcode & Hp)".
    iDestruct "Himports" as
      "(Himport_switcher & Himport_assert & Himport_adv & Himport_malloc
       & Himport_free)".
    iDestruct "Hregs" as (rmap Hdom_rmap) "Hrmap".
    codefrag_facts "Hcode". clear H0.
    iEval (rewrite /hts_main_code /assembled_hts_main /assembled_hts_main') in "Hcode".
    iEval (cbv [fmap list_fmap concat]) in "Hcode".

    (* Block 15: the free result is ALLOC_OK. *)
    hts_focus_entry_block 15 "Hcode" as a_free_result Ha_free_result
      "Hblock" "Hcont" from Ha_ret.
    iHide "Hcont" as hcont.
    (* Jnz 2 ca0. *)
    iInstr "Hblock".
    (* Jmp 2. *)
    iInstr "Hblock".
    subst hcont; unfocus_block "Hblock" "Hcont" as "Hcode".

    (* Quarantine b in the world and close its world entry. The dangling
       saved alias remains private. *)
    iMod (hts_world_quarantine C _ ι b Wret Hbounds Hb_lookup Hstd_rev
      with "Hrel_b Hstate_b Hquar Hworld_open") as "Hworld".
    iDestruct (StackRevokedResources_mono_priv Wret (hts_Wfree Wret ι) C
      (finz.seq_between (csp_b ^+ 1)%a csp_e) (hts_Wfree_related Wret ι)
      with "Hstack_revoked_ret") as "Hstack_revoked_free".
    assert (revoked_addresses (hts_Wfree Wret ι)
      (finz.seq_between (csp_b ^+ 1)%a csp_e)) as Hstack_revoked_free.
    { rewrite /hts_Wfree /revoked_addresses /=. exact Hstack_revoked_ret. }
    iDestruct (hts_interp_adv_world C C_f W_init_C (hts_Wfree Wret ι)
      Hadv_nonheap with "Hadv") as "#Hinterp_adv_free".

    (* Block 16: clear the second adversary argument. *)
    focus_block 16 "Hcode" as a_zero Ha_zero "Hblock" "Hcont";
      iHide "Hcont" as hcont.
    (* Mov ca0 0. *)
    iInstr "Hblock".
    subst hcont; unfocus_block "Hblock" "Hcont" as "Hcode".

    (* Block 17: fetch the switcher entry. *)
    focus_block 17 "Hcode" as a_fetch17 Ha_fetch17 "Hfetch" "Hcont";
      iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ctp;ct2] as ["[Hctp _]";"[Hct2 _]"].
    iExtractList "Hrmap" [ct0] as ["[Hct0 _]"].
    iApply (fetch_spec hts_switcher_offset ctp ct0 ct2 RX Global
      pc_b pc_e a_fetch17
      (WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call)
      _ _ _ _ with "[- $HPC $Hctp $Hct0 $Hct2 $Hfetch]").
    { reflexivity. }
    { solve_addr. }
    { rewrite /hts_switcher_offset. apply withinBounds_true_iff. solve_addr. }
    { exact Hpc_shadow. }
    { apply switcher_call_sentry_not_heap. }
    { done. }
    { done. }
    { done. }
    replace (pc_b ^+ hts_switcher_offset)%a with pc_b
      by (rewrite /hts_switcher_offset; solve_addr).
    iFrame "Himport_switcher".
    iNext; iIntros "(HPC & Hctp & Hct0 & Hct2 & Hfetch & Himport_switcher)".
    iEval (cbn) in "Hctp".
    subst hcont; unfocus_block "Hfetch" "Hcont" as "Hcode".

    (* Block 18: fetch the adversary entry. *)
    focus_block 18 "Hcode" as a_fetch18 Ha_fetch18 "Hfetch" "Hcont";
      iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ct1] as ["[Hct1 _]"].
    iApply (fetch_spec hts_adv_offset ct1 ct0 ct2 RX Global
      pc_b pc_e a_fetch18 (WSealed ot_switcher C_f)
      _ _ _ _ with "[- $HPC $Hct1 $Hct0 $Hct2 $Hfetch]").
    { reflexivity. }
    { solve_addr. }
    { rewrite /hts_adv_offset. apply withinBounds_true_iff. solve_addr. }
    { exact Hpc_shadow. }
    { exact Hadv_nonheap. }
    { done. }
    { done. }
    { done. }
    replace (pc_b ^+ hts_adv_offset)%a with (pc_b ^+ 2)%a by reflexivity.
    iFrame "Himport_adv".
    iNext; iIntros "(HPC & Hct1 & Hct0 & Hct2 & Hfetch & Himport_adv)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hfetch" "Hcont" as "Hcode".

    (* Block 19: call the adversary with zero. *)
    focus_block 19 "Hcode" as a_advcall2 Ha_advcall2 "Hblock" "Hcont";
      iHide "Hcont" as hcont.
    (* Jalr cra ctp. *)
    iInstr_success "Hblock".
    subst hcont; unfocus_block "Hblock" "Hcont" as "Hcode".
    assert (hts_block_addr pc_a 20 (a_advcall2 ^+ 1)%a) as Ha_next.
    { rewrite /hts_block_addr. solve_addr. }
    clear Ha_free_result Ha_zero Ha_fetch17 Ha_fetch18.

    iAssert (interp (hts_Wfree Wret ι) C (WInt 0)) as "#Hinterp_zero".
    { iApply interp_int. }
    iExtractList "Hrmap" [ca2;ca3;ca4;ca5] as
      ["[Hca2 %Hwca2]";"[Hca3 %Hwca3]";"[Hca4 %Hwca4]";"[Hca5 %Hwca5]"].
    subst wca2 wca3 wca4 wca5.
    set (adv_arg := ({[ca0 := lword_of_word (WInt 0); ca1 := lword_of_word (WInt 0);
      ca2 := lword_of_word (WInt 0); ca3 := lword_of_word (WInt 0);
      ca4 := lword_of_word (WInt 0); ca5 := lword_of_word (WInt 0);
      ct0 := lword_of_word (WInt 0)]} : LReg)).
    iAssert ([∗ map] rarg↦warg ∈ adv_arg,
      rarg ↦ᵣ warg ∗ if decide (rarg ∈ dom_arg_rmap 1)
        then interp (hts_Wfree Wret ι) C warg else True)%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hadv_arg".
    { subst adv_arg.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done. }
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iInsertList "Hrmap" [ctp;ct2].
    set (adv_other := <[ct2:=lword_of_word (WInt 0)]>
      (<[ctp:=lword_of_word (WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call)]>
       (delete ca5 (delete ca4 (delete ca3 (delete ca2
         (delete ct1 (delete ct0 rmap)))))))).
    iApply (switcher_cc_specification Nswitcher (hts_Wfree Wret ι) C
      (WCap true RW Global cgp_b cgp_e cgp_b)
      (WSentry true RX Global pc_b pc_e (a_advcall2 ^+ 1)%a)
      wcs0 wcs1 csp_b csp_e (csp_b ^+ 1)%a C_f stk
      adv_arg adv_other cstk Ws Cs 1
      with "[- $Hswitcher $Hna $HPC $Hcgp $Hcra $Hcsp
        $Hct1 $Hentry $Hcs0 $Hcs1 $Hadv_arg $Hrmap $Hstk
        $Hworld $Hstack_revoked_free $Hcstk $HK $Hinterp_adv_free]").
    { exact Hstk_shadow. }
    { exact Hstk_heap. }
    { subst adv_other. repeat (rewrite dom_insert_L).
      repeat (rewrite dom_delete_L).
      rewrite Hdom_rmap /dom_arg_rmap /=. set_solver+. }
    { subst adv_arg. rewrite /is_arg_rmap /dom_arg_rmap /=. reflexivity. }
    iSplitR; first (iPureIntro; exact Hstack_revoked_free).
    iNext.
    iIntros (Wret2 rmap_after2 stk_after2 lret2 rcgp rcra rcs0 rcs1)
      "(_ & _ & _ & _ & _ & %Hdom_rmap_after2 & _ & _
       & Hna & _ & _ & Hcstk
       & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
       & _ & _ & Hrmap & _ & _ & %Hrestored)".
    destruct Hrestored as (Hgp_ret2 & Hra_ret2 & _ & _).
    apply load_heap_nonheap in Hgp_ret2.
    2: { destruct Hcgp_heap as [Hcgp_nonheap _].
         rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=
           Hcgp_nonheap /=. reflexivity. }
    apply load_heap_nonheap in Hra_ret2.
    2: { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=
           Hpc_nonheap /=. reflexivity. }
    subst rcgp rcra.
    iEval (cbn) in "HPC".
    iApply "Hcontinue".
    iExists (a_advcall2 ^+ 1)%a.
    iFrame "∗#%".
  Qed.
End HTS_Spec_Dangling.
