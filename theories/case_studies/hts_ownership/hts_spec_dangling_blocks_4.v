From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import fetch_spec assert_spec switcher_base.
From griotte.case_studies.hts_ownership Require Import heap_temporal_safety heap_temporal_safety_preamble.
From griotte.allocators.ownership Require Import allocator allocator_preamble.
From griotte.case_studies.hts_ownership Require Import heap_temporal_safety_allocator_spec.
From griotte Require Import world_ghost_theory heap_region.
From griotte Require Import world_interp_stack region_invariants.
From griotte Require Import proofmode register_tactics map_simpl.
From griotte.case_studies.hts_ownership Require Import hts_spec_states hts_spec_world.
From griotte.case_studies.hts_ownership Require Import hts_spec_assert_blocks_5.

(** * Segment (d): blocks 16-20

    Check the free result (returning on failure), quarantine the buffer in the
    world, and call [adv(0)]: the saved alias of the buffer is dangling. *)

Section HTS_Spec_Dangling.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
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
  Context (Ws : list WORLD) (Cs : list CmptName).
  Context (cstk : CSTK).

  #[local] Notation hts_ctx := (hts_main_ctx C C_f W_init_C).
  #[local] Notation free_ret := (hts_free_ret C pc_b pc_e pc_a cgp_b cgp_e
    csp_b csp_e C_f owner_a Ws Cs cstk).
  #[local] Notation adv2_ret := (hts_adv2_ret pc_b pc_e pc_a cgp_b cgp_e
    csp_b csp_e C_f owner_a cstk).

  Lemma hts_spec_dangling :
    disjoint_from_shadow pc_b pc_e ->
    is_heap_address pc_b = false ->
    is_heap_cap (WSealed ot_switcher C_f) = false ->
    not_heap_range cgp_b cgp_e ->
    disjoint_from_mmio csp_b csp_e ->
    disjoint_from_heap csp_b csp_e ->
    (csp_b + 1 + SpillSlot_size + 2 * StackEntry_reserved_space <= csp_e)%Z ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_main_code) ->
    (pc_b + hts_label ".Lhts_main")%a = Some pc_a ->
    hts_ctx ∗
    free_ret ∗
    (adv2_ret -∗
     safe[th])
    ⊢ safe[th].
  Proof.
    iIntros (Hpc_shadow Hpc_nonheap Hadv_nonheap Hcgp_heap Hstk_shadow Hstk_heap Hstk_min
      HsubBounds Himports_contiguous) "(#Hctx & Hret & Hcontinue)".
    iDestruct "Hctx" as "(#Hassert & #Hservice & #Hservice_static & #Hswitcher & #Hswitcher_static
       & #Hexport_pcc & #Hexport_cgp & #Hexport_malloc & #Hexport_free
       & #Hadv & #Hentry)".
    iDestruct "Hret" as "[Herr|Hok]".
    { (* Block 16: return when free failed. *)
      iDestruct "Herr" as (z) "(%Hz & Hna & HPC & Hca0 & [%wct0 Hct0] & Hcs0 & [%wcra Hcra]
        & [%wctp Hctp] & [%wct2 Hct2] & Hcstk & %Hframes & Hcode_main)".
      codefrag_facts "Hcode_main". clear H0.
      unfold_code hts_main_code "Hcode_main".
      focus_block (hts_block ".Lhts_free_result") "Hcode_main" of hts_main_blocks at pc_a as a_free_result Ha_free_result
        "Hcode" "Hcont".
      (* Jne 2 ca0 0. *)
      iInstr "Hcode".
      { apply nonZero_WInt. intros [= ->]. done. }
      (* Jmp .Lhts_return *)
      iInstr "Hcode".
      { jump_to (pc_a ^+ hts_label_offset ".Lhts_return")%a. }
      unfocus_block "Hcode" "Hcont" as "Hcode_main".
      iApply (hts_return_spec with
               "[$Hswitcher $Hswitcher_static $Hna $HPC $Hcs0 $Hcra $Hctp $Hct0 $Hct2
                 $Hcstk $Hcode_main]"); [done | done]. }
    iDestruct "Hok" as (ι b Wret) "(%Hbounds & %Hstk_nonempty
      & _ & %Hstd_rev & #Hrel_b & Hframe & Hca0 & Hca1 & Hregs
      & [%stk Hstk] & Hworld_open & Hstate_b & Hstack_revoked_ret
      & %Hstack_revoked_ret & HK & #Hquar)".
    iDestruct "Hframe" as "(Hna & HPC & [%mie_ret Hcra] & Hcgp & Hcsp & Hcs0
      & [%wcs1 Hcs1] & Hcstk & Himports & Hcode_main & Hp & Howner_word)".
    iDestruct "Himports" as
      "(Himport_switcher & Himport_assert & Himport_adv & Himport_malloc
       & Himport_free & Himport_alloc_cap)".
    iDestruct "Hregs" as (rmap Hdom_rmap) "Hrmap".
    codefrag_facts "Hcode_main". clear H0.
    unfold_code hts_main_code "Hcode_main".

    (* Block 16: the free result is ALLOC_OK. *)
    focus_block (hts_block ".Lhts_free_result") "Hcode_main" of hts_main_blocks at pc_a as a_free_result Ha_free_result
      "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Jne 2 ca0 0. *)
    iInstr "Hcode".
    (* Jmp 2. *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Quarantine b in the world and close its world entry. The dangling
       saved alias remains private. *)
    iMod (hts_world_quarantine C _ ι b Wret Hbounds Hstd_rev
      with "Hrel_b Hstate_b Hquar Hworld_open") as "Hworld".
    iDestruct (StackRevokedResources_mono_priv Wret (hts_Wfree Wret ι) C
      (stk_free csp_b csp_e (stk_start_a csp_b csp_e ^+ -1)) (hts_Wfree_related Wret ι)
      with "Hstack_revoked_ret") as "Hstack_revoked_free".
    assert (revoked_addresses (hts_Wfree Wret ι)
      (stk_free csp_b csp_e (stk_start_a csp_b csp_e ^+ -1))) as Hstack_revoked_free.
    { rewrite /hts_Wfree /revoked_addresses /=. exact Hstack_revoked_ret. }
    iDestruct (hts_interp_adv_world C C_f W_init_C (hts_Wfree Wret ι)
      Hadv_nonheap with "Hadv") as "#Hinterp_adv_free".

    (* Block 17: clear the second adversary argument. *)
    focus_block (hts_block ".Lhts_zero_arg") "Hcode_main" of hts_main_blocks at pc_a as a_zero Ha_zero "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Mov ca0 0. *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 18: fetch the switcher entry. *)
    focus_block (hts_block ".Lhts_fetch_switcher_adv_2") "Hcode_main" of hts_main_blocks at pc_a as a_fetch18 Ha_fetch18 "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ctp] as ["[Hctp _]"].
    iExtractList "Hrmap" [ct0] as ["[Hct0 %Hwct0]"].
    subst wct0.
    iApply (fetch_spec 0 _ ctp RX Global
      pc_b pc_e a_fetch18
      switcher_entry_call
      _ _ _ with "[- $HPC $Hctp $Hcode]").
    { reflexivity. }
    { solve_addr. }
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff. solve_addr. }
    { exact Hpc_shadow. }
    { apply switcher_call_sentry_not_heap. }
    { done. }
    replace (pc_b ^+ 0) with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext; iIntros "(HPC & Hctp & _ & Himport_switcher)".
    iEval (cbn) in "Hctp".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 19: fetch the adversary entry. *)
    focus_block (hts_block ".Lhts_fetch_adv_2") "Hcode_main" of hts_main_blocks at pc_a as a_fetch19 Ha_fetch19 "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ct1] as ["[Hct1 _]"].
    iApply (fetch_spec 2 _ ct1 RX Global
      pc_b pc_e a_fetch19 (WSealed ot_switcher C_f)
      _ _ _ with "[- $HPC $Hct1 $Hcode]").
    { reflexivity. }
    { solve_addr. }
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff. solve_addr. }
    { exact Hpc_shadow. }
    { exact Hadv_nonheap. }
    { done. }
    iFrame "Himport_adv".
    iNext; iIntros "(HPC & Hct1 & _ & Himport_adv)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 20: call the adversary with zero. *)
    focus_block (hts_block ".Lhts_call_adv_2") "Hcode_main" of hts_main_blocks at pc_a as a_advcall2 Ha_advcall2
      "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Jalr cra ctp. *)
    iInstr_success "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    assert (a_advcall2 ^+ 1 = (pc_a ^+ hts_label_offset ".Lhts_prep_assert")%a) as Ha_next
      by (offsets_compute; solve_addr).
    rewrite Ha_next.
    clear Ha_free_result Ha_zero Ha_fetch18 Ha_fetch19.

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
    iInsertList "Hrmap" [ctp].
    set (adv_other :=
      <[ctp:=lword_of_word switcher_entry_call]>
       (delete ca5 (delete ca4 (delete ca3 (delete ca2
         (delete ct1 (delete ct0 rmap))))))).
    assert (dom adv_other =
      all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8))
      as Hdom_other.
    { subst adv_other. repeat (rewrite dom_insert_L).
      repeat (rewrite dom_delete_L).
      rewrite Hdom_rmap /dom_arg_rmap /=. set_solver+. }
    assert (is_arg_rmap adv_arg 8) as Hargs_rmap.
    { subst adv_arg. rewrite /is_arg_rmap /dom_arg_rmap /=. reflexivity. }
    iApply (switcher_cc_specification (hts_Wfree Wret ι) C
      (Cap RW Global cgp_b cgp_e cgp_b)
      (Sentry (ret_kind mie) RX Global pc_b pc_e (pc_a ^+ hts_label_offset ".Lhts_prep_assert")%a)
      thread_return_sentry wcs1 csp_b csp_e (stk_start_a csp_b csp_e ^+ -1) C_f stk
      adv_arg adv_other cstk Ws Cs 1
      with "[- $Hswitcher $Hswitcher_static $Hna $HPC $Hcgp $Hcra $Hcsp
        $Hct1 $Hentry $Hcs0 $Hcs1 $Hadv_arg $Hrmap $Hstk
        $Hworld $Hstack_revoked_free $Hcstk $HK $Hinterp_adv_free]").
    { exact Hstk_shadow. }
    { exact Hstk_heap. }
    { stk_unfold; solve_addr. }
    { exact Hdom_other. }
    { exact Hargs_rmap. }
    { destruct mie; reflexivity. }
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=.
      reflexivity. }
    iSplitR; first (iPureIntro; exact Hstack_revoked_free).
    iSplit; last first.
    { (* The spill cannot fault: the stack holds it *)
      iApply switcher_cc_fault_stack_fits; stk_unfold; solve_addr+Hstk_min. }
    iNext.
    iIntros (Wret2 rmap_after2 stk_after2 lret2 rcgp rcra rcs0 rcs1)
      "(_ & _ & _ & _ & _ & %Hdom_rmap_after2 & _ & _
       & Hna & _ & _ & Hcstk
       & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
       & _ & _ & Hrmap & _ & _ & %Hrestored)".
    destruct Hrestored as (Hgp_ret2 & Hra_ret2 & Hs0_ret2 & _).
    apply load_heap_nonheap in Hs0_ret2; [|exact thread_return_sentry_not_heap].
    apply load_heap_nonheap in Hgp_ret2.
    2: { destruct Hcgp_heap as [Hcgp_nonheap _].
         rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=
           Hcgp_nonheap /=. reflexivity. }
    apply load_heap_nonheap in Hra_ret2.
    2: { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=
           Hpc_nonheap /=. reflexivity. }
    subst rcgp rcra rcs0.
    iEval (cbn) in "HPC".
    iApply "Hcontinue".
    iFrame "∗#%".
  Qed.
End HTS_Spec_Dangling.
