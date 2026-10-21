From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening wp_rules_interp.
From griotte Require Import fetch_spec assert_spec switcher_spec_call.
From griotte.case_studies.hts_ownership Require Import heap_temporal_safety heap_temporal_safety_preamble.
From griotte Require Import switcher_spec_KtK switcher_spec_KtK_call switcher_exception_stub.
From griotte.allocators.ownership Require Import allocator allocator_preamble.
From griotte.case_studies.hts_ownership Require Import heap_temporal_safety_allocator_spec.
From griotte Require Import world_ghost_theory heap_region.
From griotte Require Import world_interp_stack region_invariants heap_ghost.
From griotte Require Import proofmode register_tactics map_simpl.
From griotte.case_studies.hts_ownership Require Import hts_spec_states hts_spec_world.

(** * Segment (c): blocks 10-15

    Reload the saved buffer, store [&p] in it, fetch the allocator
    capability, the switcher and the free entry, and call free. *)

Section HTS_Reload.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    `{MP: MachineParameters}.

  Definition hts_reload_buffer_instrs : list Word :=
    hts_main_instrs_n 10.

  (** Reload of the saved buffer from the stack slot [s], just below the
      current stack pointer, with the load witness [wit]. HTS uses the
      tag-preserving post with [LoadLive ι]. *)
  Lemma hts_reload_retained_buffer_spec
    pc_b pc_e pc_a s e (raw w0 : LWord) wit :
    disjoint_from_shadow s e ->
    (s + 1)%a = Some (s ^+ 1)%a ->
    (s < e)%a ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_reload_buffer_instrs)%a ->
    (PC ↦ₚ WCap true RX Global pc_b pc_e pc_a ∗
     csp ↦ᵣ WCap true RWL Local s e (s ^+ 1)%a ∗
     ca0 ↦ᵣ w0 ∗
     s ↦ₐ raw ∗
     codefrag_pers pc_a hts_reload_buffer_instrs ∗
     load_witness_res wit ∗
     ▷ (∀ actual,
       ⌜load_post wit RWL raw actual⌝ -∗
       PC ↦ₚ WCap true RX Global pc_b pc_e
         (pc_a ^+ length hts_reload_buffer_instrs)%a ∗
       csp ↦ᵣ WCap true RWL Local s e (s ^+ 1)%a ∗
       ca0 ↦ᵣ actual ∗
       s ↦ₐ raw ∗
       codefrag_pers pc_a hts_reload_buffer_instrs ∗
       load_witness_res wit -∗
       WP Seq (Instr Executable)
         {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
     ⊢ WP Seq (Instr Executable)
         {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    iIntros (Hshadow Hs1 Hbounds Hsub)
      "(HPC & Hcsp & Hca0 & Ha & Hcode & Hwit & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /hts_reload_buffer_instrs.
    (* CLoad ca0 csp (-1). *)
    iInstrApply "Hcode" (wp_load_witness_imm_one_inbounds _ _ _ _ _ _ _ ca0 csp (-1))
      with "[$HPC $Hca0 $Hcsp $Ha $Hwit]"
      as (actual) "(%Hactual & HPC & Hca0 & Hcsp & Ha & Hwit)".
    { solve_addr. }
    { eapply disjoint_from_shadow_not_in; first exact Hshadow.
      apply withinBounds_true_iff; solve_addr. }
    { apply withinBounds_true_iff; solve_addr. }
    iApply ("Hpost" $! actual with "[//]"). iFrame "∗ Hcode".
  Qed.

End HTS_Reload.

Section HTS_Spec_Free.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {allocator_ownerg : allocatorOwnerG Σ}
    `{MP: MachineParameters}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  #[local] Instance free_auth_owner_inst : FreeAuth Σ := free_auth_owner.

  Context (C : CmptName).
  Context (pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e : Addr).
  Context (C_f : Sealable) (owner_a : Addr) (W_init_C : WORLD).
  Context (Ws : list WORLD) (Cs : list CmptName).
  Context (Nswitcher : namespace).

  #[local] Notation hts_ctx := (hts_main_ctx C C_f W_init_C Nswitcher).
  #[local] Notation adv1_ret := (hts_adv1_ret C pc_b pc_e pc_a cgp_b cgp_e
    csp_b csp_e C_f owner_a W_init_C Ws Cs []).
  #[local] Notation free_ret := (hts_free_ret C pc_b pc_e pc_a cgp_b cgp_e
    csp_b csp_e C_f owner_a Ws Cs []).

  Lemma hts_spec_free :
    Nswitcher ## Nallocator_service ->
    Nswitcher ## N_trap ->
    is_shadow_address owner_a = false ->
    withinBounds owner_a (owner_a ^+ 1)%a owner_a = true ->
    is_heap_address owner_a = false ->
    disjoint_from_shadow pc_b pc_e ->
    is_heap_address pc_b = false ->
    not_heap_range cgp_b cgp_e ->
    disjoint_from_mmio csp_b csp_e ->
    disjoint_from_heap csp_b csp_e ->
    (csp_b + 5 <= csp_e)%Z ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_main_code)%a ->
    (pc_b + hts_label ".Lhts_main")%a = Some pc_a ->
    hts_ctx ∗
    adv1_ret ∗
    (free_ret -∗
     WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hdisj HNtrap Howner_shadow Howner_bounds Howner_nonheap Hpc_shadow Hpc_nonheap Hcgp_heap Hstk_shadow Hstk_heap Hstk_min HsubBounds
      Himports_contiguous) "(#Hctx & Hret & Hcontinue)".
    iDestruct "Hctx" as "(#Hassert & #Hservice & #Hservice_static & #Hswitcher & #Hswitcher_static
       & #Hexport_pcc & #Hexport_cgp & #Hexport_malloc & #Hexport_free
       & #Hadv & #Hentry)".
    iDestruct "Hret" as (ι b Wret) "(%Hbounds & %Hstk_nonempty
      & %Hrelated_share_ret & #Hrel_b & Hframe & [%w0 Hca0] & [%w1 Hca1]
      & Hregs & Hslot & [%stk Hstk] & Hworld & Hstack_revoked_ret
      & %Hstack_revoked_ret & HK & Howner & #Hobj & Hright)".
    iDestruct "Hframe" as "(Hna & HPC & [%mie_ret Hcra] & Hcgp & Hcsp & [%wcs0 Hcs0]
      & [%wcs1 Hcs1] & Hcstk & Himports & Hcode_main & Hp & Howner_word)".
    iDestruct "Himports" as
      "(Himport_switcher & Himport_assert & Himport_adv & Himport_malloc
       & Himport_free & Himport_alloc_cap)".
    iDestruct "Hregs" as (rmap Hdom_rmap) "Hrmap".
    pose proof Hbounds as Hbnd; rewrite /hts_buffer_bounds in Hbnd.
    assert ((b + 1)%a = Some (b ^+ 1)%a) as Hsucc by solve_addr.
    pose proof (hts_buffer_heap_address b Hbounds) as Hb_heap.

    (* Main still holds the free right of ι: ι is live, open its world
       entry. *)
    iMod (hts_world_reopen_live C csp_b csp_e W_init_C _ ι b Wret
      Hbounds Hrelated_share_ret with "Hrel_b Hright Hworld")
      as (v_b) "(%Hι_ret & %Hstd_rev & Hworld_open & Hstate_b & Hright
        & [Hb Hb_share])".

    codefrag_facts "Hcode_main". clear H0.
    unfold_code hts_main_code "Hcode_main".

    (* Block 10: reload the saved buffer. Its tag is kept: the free right
       of ι is a live witness. *)
    focus_block (hts_block ".Lhts_reload") "Hcode_main" of hts_main_blocks at pc_a as a_reload Ha_reload "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* CLoad ca0 csp (-1). *)
    iApply (hts_reload_retained_buffer_spec pc_b pc_e a_reload
      csp_b csp_e (hts_buffer b @@ ι) _ (LoadLive ι (1/2)%Qp)
      with "[- $HPC $Hcsp $Hca0 $Hslot $Hcode $Hright]").
    { exact (disjoint_from_mmio_shadow _ _ Hstk_shadow). }
    { solve_addr. }
    { exact Hstk_nonempty. }
    { solve_addr. }
    iNext. iIntros (actual (_ & _ & _ & Hlivepost))
      "(HPC & Hcsp & Hca0 & Hslot & _ & Hright)".
    rewrite (Hlivepost eq_refl); last first.
    { intros _. left. cbn. split; first done. exists b.
      rewrite /heap_authority_base decide_True; last solve_addr.
      by rewrite /heap_cap_base /= Hb_heap. }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 11: store cgp, which covers exactly p, in live b, and move the
       buffer to the second argument register. *)
    focus_block (hts_block ".Lhts_store_private") "Hcode_main" of hts_main_blocks at pc_a as a_private Ha_private "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iEval (cbn) in "Hca0".
    iExtractList "Hrmap" [ct0;ct1] as ["[Hct0 %Hwct0]";"[Hct1 _]"].
    subst wct0.
    (* The share of the buffer cell is the dereference witness of [ι]. *)
    iDestruct (key_share_deref (Some ι) b with "Hb_share") as (dw Hdw) "[Hdw Hdw_close]".
    destruct dw as [|ι' q]; cbn in Hdw; [done|]. injection Hdw as <-.
    iSimpl in "Hdw".
    (* Store ca0 cgp 0. *)
    iInstr "Hcode".
    { apply hts_heap_not_shadow. solve_addr. }
    { apply withinBounds_true_iff; solve_addr. }
    iDestruct ("Hdw_close" with "Hdw") as "Hb_share".
    (* Mov ca1 ca0. *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 12: fetch the allocator capability for free. *)
    focus_block (hts_block ".Lhts_fetch_alloc_cap_free") "Hcode_main" of hts_main_blocks at pc_a as a_fetch12 Ha_fetch12 "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (fetch_spec 5 _ ca0 RX Global
      pc_b pc_e a_fetch12 (allocator_capability Global owner_a)
      _ _ _ with "[- $HPC $Hca0 $Hcode]").
    { reflexivity. }
    { solve_addr. }
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff. solve_addr. }
    { exact Hpc_shadow. }
    { apply sealed_cap_nonheap. exact Howner_nonheap. }
    { done. }
    iFrame "Himport_alloc_cap".
    iNext; iIntros "(HPC & Hca0 & _ & Himport_alloc_cap)".
    iEval (cbn) in "Hca0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 13: fetch the switcher entry for free. *)
    focus_block (hts_block ".Lhts_fetch_switcher_free") "Hcode_main" of hts_main_blocks at pc_a as a_fetch13 Ha_fetch13 "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ctp] as ["[Hctp _]"].
    iApply (fetch_spec 0 _ ctp RX Global
      pc_b pc_e a_fetch13
      (WSentry FwdDisable true XSRW_ Local b_switcher e_switcher a_switcher_call)
      _ _ _ with "[- $HPC $Hctp $Hcode]").
    { reflexivity. }
    { solve_addr. }
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff. solve_addr. }
    { exact Hpc_shadow. }
    { apply switcher_call_sentry_not_heap. }
    { done. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext; iIntros "(HPC & Hctp & _ & Himport_switcher)".
    iEval (cbn) in "Hctp".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 14: fetch the sealed free entry. *)
    focus_block (hts_block ".Lhts_fetch_free") "Hcode_main" of hts_main_blocks at pc_a as a_fetch14 Ha_fetch14 "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (fetch_spec 4 _ ct1 RX Global
      pc_b pc_e a_fetch14
      (WSealed ot_switcher (allocator_free Global))
      _ _ _ with "[- $HPC $Hct1 $Hcode]").
    { reflexivity. }
    { solve_addr. }
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff. solve_addr. }
    { exact Hpc_shadow. }
    { unfold allocator_free. apply sealed_cap_nonheap.
      exact hts_export_tbl_not_heap. }
    { done. }
    iFrame "Himport_free".
    iNext; iIntros "(HPC & Hct1 & _ & Himport_free)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 15: call the trusted free entry while the live world cell is open. *)
    focus_block (hts_block ".Lhts_call_free") "Hcode_main" of hts_main_blocks at pc_a as a_freecall Ha_freecall
      "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Jalr cra ctp. *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    assert ((a_freecall ^+ 1)%a = (pc_a ^+ hts_label_offset ".Lhts_free_result")%a) as Ha_next
      by (offsets_compute; solve_addr).
    rewrite Ha_next.
    clear Ha_reload Ha_private Ha_fetch12 Ha_fetch13 Ha_fetch14.

    iAssert ([[b,(b ^+ 1)%a]] ↦ₕ[ι]
      [[ [lword_of_word (WCap true RW Global cgp_b cgp_e cgp_b)] ]])%I
      with "[Hb Hb_share]" as "Hfree_mem".
    { rewrite /heap_region_pointsto
        (finz_seq_between_singleton b (b ^+ 1)%a Hsucc) big_sepL2_singleton.
      iFrame. }
    iExtractList "Hrmap" [ca2;ca3;ca4;ca5] as
      ["[Hca2 %Hca2]";"[Hca3 %Hca3]";"[Hca4 %Hca4]";"[Hca5 %Hca5]"].
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    subst wca2 wca3 wca4 wca5.
    set (free_arg := ({[ca0 := lword_of_word (allocator_capability Global owner_a);
      ca1 := hts_buffer b @@ ι;
      ca2 := lword_of_word (WInt 0); ca3 := lword_of_word (WInt 0);
      ca4 := lword_of_word (WInt 0); ca5 := lword_of_word (WInt 0);
      ct0 := lword_of_word (WInt 0)]} : LReg)).
    iAssert ([∗ map] rarg↦warg ∈ free_arg, rarg ↦ᵣ warg)%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hfree_arg".
    { subst free_arg.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]). done. }
    iInsertList "Hrmap" [ctp].
    set (free_other :=
      <[ctp:=lword_of_word (WSentry FwdDisable true XSRW_ Local b_switcher e_switcher a_switcher_call)]>
       (delete ca5 (delete ca4 (delete ca3 (delete ca2
         (delete ct1 (delete ct0 rmap))))))).
    iPoseProof (hts_free_known_function Nswitcher
      (WCap true RW Global cgp_b cgp_e cgp_b)
      (WSentry (ret_kind mie) true RX Global pc_b pc_e (pc_a ^+ hts_label_offset ".Lhts_free_result")%a)
      wcs0 wcs1 csp_b csp_e (csp_b ^+ 1)%a b (b ^+ 1)%a b
      free_arg [] RW Global ι
      [lword_of_word (WCap true RW Global cgp_b cgp_e cgp_b)]
      Global owner_a hts_main_owner_id {[ι]}
      with "[$Hservice $Hservice_static $Hswitcher]") as "Hfree_fun".
    { exact Hdisj. }
    { exact Howner_shadow. }
    { exact Howner_bounds. }
    { exact Hbounds. }
    { rewrite (finz_seq_between_singleton b (b ^+ 1)%a Hsucc).
      reflexivity. }
    { subst free_arg. reflexivity. }
    { subst free_arg. reflexivity. }
    assert (dom free_other =
      all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8))
      as Hdom_other.
    { subst free_other.
      repeat (rewrite dom_insert_L).
      repeat (rewrite dom_delete_L).
      rewrite Hdom_rmap /dom_arg_rmap /=. set_solver+. }
    assert (is_arg_rmap free_arg 8) as Hargs_rmap.
    { subst free_arg. rewrite /is_arg_rmap /dom_arg_rmap /=.
      reflexivity. }
    pose proof allocator_size_exports as Hsize.
    rewrite /allocator_export_table_entries in Hsize.
    iApply (switcher_cc_specification_known_to_known_end_to_end
      Nswitcher
      (WCap true RW Global cgp_b cgp_e cgp_b)
      (WSentry (ret_kind mie) true RX Global pc_b pc_e (pc_a ^+ hts_label_offset ".Lhts_free_result")%a)
      wcs0 wcs1 csp_b csp_e (csp_b ^+ 1)%a stk free_arg free_other []
      allocator_free_nargs allocator_free_min_stack ⊤
      allocator_exp_tbl_b
      (allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a
      allocator_exp_tbl_e allocator_pcc_b allocator_pcc_e
      allocator_cgp_b allocator_cgp_e allocator_free_pcc_off _ false
      with "[- $Hswitcher $Hswitcher_static $Hexport_pcc $Hexport_cgp $Hexport_free
        $Hna $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1
        $Hfree_arg $Hrmap $Hstk $Hcstk $Hfree_fun]").
    { exact Hstk_heap. }
    { exact Hstk_shadow. }
    { solve_addr. }
    { apply hts_export_tbl_not_shadow.
      rewrite /allocator_free_exp_tbl_off /allocator_entry_free. solve_addr. }
    { apply hts_export_tbl_not_shadow. solve_addr. }
    { apply hts_export_tbl_not_shadow. solve_addr. }
    { exact hts_export_tbl_disjoint_from_shadow. }
    { exact hts_allocator_pcc_not_heap. }
    { exact hts_allocator_cgp_not_heap. }
    { solve_ndisj. }
    { solve_ndisj. }
    { exact HNtrap. }
    { rewrite /allocator_free_exp_tbl_off /allocator_entry_free. solve_addr. }
    { solve_addr. }
    { rewrite /allocator_free_exp_tbl_off /allocator_entry_free. solve_addr. }
    { rewrite /allocator_free_nargs; lia. }
    { exists (allocator_code_b ^+ length allocator_malloc_instrs)%a.
      rewrite allocator_free_pcc_off_eq /allocator_malloc_pcc_off.
      pose proof allocator_size_imports as Himports_size.
      pose proof allocator_size_code as Hcode_size.
      rewrite /allocator_code length_app in Hcode_size.
      rewrite -allocator_imports_length.
      solve_addr+ Himports_size Hcode_size. }
    { rewrite /allocator_free_min_stack. solve_addr+Hstk_min. }
    { exact Hdom_other. }
    { exact Hargs_rmap. }
    { destruct mie; reflexivity. }
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=.
      reflexivity. }
    iFrame "Hobj Hright Hfree_mem Howner Howner_word".
    iSplitR; first (iPureIntro; set_solver+).
    iNext.
    iIntros "[Hcall|Hcall]".
    - iNamed "Hcall".
      destruct Hrestored as (Hgp_free & Hra_free & _ & _).
      apply load_heap_nonheap in Hgp_free.
      2: { destruct Hcgp_heap as [Hcgp_nonheap _].
           rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=
             Hcgp_nonheap /=. reflexivity. }
      apply load_heap_nonheap in Hra_free.
      2: { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=
             Hpc_nonheap /=. reflexivity. }
      subst rcgp rcra.
      iEval (cbn) in "HPC".
      iEval (rewrite /hts_free_result /allocator_free_result) in "HQ".
      iDestruct "HQ" as
        "(#Hquar & _ & Howner_word & %Hfree_values)".
      destruct Hfree_values as [-> ->].
      iApply "Hcontinue".
      iRight. iExists ι, b, Wret.
      iFrame "∗#%".
    - iNamed "Hcall".
      destruct Hrestored as (_ & Hra_free & _ & _).
      apply load_heap_nonheap in Hra_free.
      2: { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=
             Hpc_nonheap /=. reflexivity. }
      subst rcra.
      iEval (cbn) in "HPC".
      iApply "Hcontinue".
      iLeft. iExists _. iFrame "Hna HPC Hca0 Hcode_main".
      iSplit; first (iPureIntro; rewrite /ENOTENOUGHTRUSTEDSTACK; lia).
      iExtractList "Hrmap" [ct0] as ["[Hct0 _]"].
      by iExists _.
  Qed.
End HTS_Spec_Free.
