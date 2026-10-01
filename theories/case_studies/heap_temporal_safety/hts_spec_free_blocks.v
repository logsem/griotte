From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import fetch_spec assert_spec switcher_spec_call
  heap_temporal_safety heap_temporal_safety_preamble.
From griotte Require Import switcher_spec_KtK.
From griotte.allocator Require Import allocator allocator_preamble.
From griotte Require Import heap_temporal_safety_allocator_spec world_ghost_theory heap_region.
From griotte Require Import world_interp_stack region_invariants heap_ghost.
From griotte Require Import proofmode register_tactics map_simpl.
From griotte Require Import hts_spec_states hts_spec_world.

(** * Segment (c): blocks 10-15

    Reload the saved buffer, store [&p] in it, fetch the allocator
    capability, the switcher and the free entry, and call free. *)

Section HTS_Reload.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {allocatorg : allocatorG Σ}
    `{MP : MachineParameters}.

  Definition hts_reload_buffer_instrs : list Word :=
    hts_main_instrs_n 10.

  (** Physical ownership of the base address [b] shows that the allocator
      state of [b] is [Live]: the shadow table then keeps the tag of the
      loaded buffer. *)
  Lemma hts_reload_live_buffer_spec pc_b pc_e pc_a s e b (w0 v : Word) :
    disjoint_from_shadow s e ->
    (s + 1)%a = Some (s ^+ 1)%a ->
    (s < e)%a ->
    is_heap_address b = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_reload_buffer_instrs)%a ->
    allocator_ctx ∗
    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a ∗
    csp ↦ᵣ WCap true RWL Local s e (s ^+ 1)%a ∗
    ca0 ↦ᵣ w0 ∗
    s ↦ₐ hts_buffer b ∗
    b ↦ₐ v ∗
    codefrag pc_a hts_reload_buffer_instrs ∗
    ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ length hts_reload_buffer_instrs)%a ∗
       csp ↦ᵣ WCap true RWL Local s e (s ^+ 1)%a ∗
       ca0 ↦ᵣ hts_buffer b ∗
       s ↦ₐ hts_buffer b ∗
       b ↦ₐ v ∗
       codefrag pc_a hts_reload_buffer_instrs -∗
       WP Seq (Instr Executable)
         {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hshadow Hp1 Hbounds Hheap Hsub)
      "(#Halloc & HPC & Hcsp & Hca0 & Hsaved & Hb & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /hts_reload_buffer_instrs.
    (* Load ca0 csp (-1). *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iDestruct (map_of_regs_3 with "HPC Hcsp Hca0") as "[Hmap (%Hpc_csp & %Hpc_ca0 & %Hcsp_ca0)]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hsaved") as "[Hmem %Hpc_saved]".
    iInv Nallocator as ">Hbody" "Hclose".
    iDestruct (allocator_inv_lookup b with "Hbody") as (st) "[Hentry Hrestore]".
    { by apply elem_of_heap_addresses. }
    iDestruct (allocator_entry_memory_live with "Hentry Hb") as %->.
    iDestruct "Hentry" as "[Hs Hres]".
    iApply (wp_load_memory_shadow_imm _ _ _ _ _ _ _ _ _ _ _ _ _
      {[b := ShadowLive]} (DfracOwn 1) with "[$Hmem Hs $Hmap]");
      eauto; try solve_pure; try (by simplify_map_eq).
    { rewrite decode_encode_instrW_inv. reflexivity. }
    { unfold regs_of. rewrite !dom_insert. set_solver+. }
    { exists true, RWL, Local, s, e, (s ^+ 1)%a. split.
      - unfold read_reg_inr. by simplify_map_eq.
      - unfold reg_allows_load_imm.
        assert (((s ^+ 1)%a + -1)%a = Some s) as -> by solve_addr.
        case_decide; last done. exists (hts_buffer b). by simplify_map_eq. }
    { intros p0 g0 b0 e0 a0 ea (Hsrc & Hea & _).
      simpl_map_regs by eauto. simplify_map_eq.
      apply (disjoint_from_shadow_not_in _ _ _ Hshadow). apply withinBounds_true_iff. solve_addr. }
    { iNext. rewrite big_sepM_singleton. iExact "Hs". }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hs & Hmap)".
    rewrite big_sepM_singleton.
    iMod ("Hclose" with "[Hs Hres Hrestore]") as "_".
    { iNext. iApply "Hrestore". iFrame. }
    iModIntro.
    destruct retv; simpl in Hspec; [contradiction| |].
    { wp_pure. wp_end. by iIntros (?). }
    destruct Hspec as (p0 & g0 & b0 & e0 & a0 & ea & raw & actual &
      Hallow & Hlookup & _ & Hobserved & Hinc).
    destruct Hallow as (Hsrc & Hea & _).
    simpl_map_regs by eauto. simplify_map_eq.
    match type of Hea with ((?x ^+ 1) + _)%a = Some _ =>
      assert (ea = x) as -> by solve_addr end.
    simplify_map_eq.
    assert (actual = hts_buffer b) as ->.
    { rewrite /load_memory_shadow_observation /hts_buffer /heap_cap_base
        /memory_cap_base /= Hheap in Hobserved.
      rewrite (Hobserved ShadowLive); first reflexivity.
      by simplify_map_eq. }
    unfold incrementPC, incrementPC_gen in Hinc. simplify_map_eq.
    assert ((pc_a + 1)%a = Some (pc_a ^+ 1)%a) as Hpc by solve_addr.
    rewrite Hpc in Hinc. simplify_eq.
    rewrite (insert_insert_ne _ ca0 PC) // insert_insert_eq.
    rewrite (insert_insert_ne _ ca0 csp) // insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(HPC & Hcsp & Hca0)"; eauto.
    iDestruct (memMap_resource_2ne with "Hmem") as "[Hi Hsaved]"; auto.
    wp_pure.
    iSpecialize ("Hcode" with "Hi").
    iApply "Hpost". iFrame.
  Qed.
End HTS_Reload.

Section HTS_Spec_Free.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ}
    {allocator_ownerg : allocatorOwnerG Σ}
    `{MP: MachineParameters}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .
  Context (C : CmptName).
  Context (pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e : Addr).
  Context (C_f : Sealable) (owner_a : Addr) (W_init_C : WORLD).
  Context (Ws : list WORLD) (Cs : list CmptName).
  Context (Nassert Nswitcher : namespace) (cstk : CSTK).

  Local Notation hts_ctx := (hts_main_ctx C C_f W_init_C Nassert Nswitcher).
  Local Notation adv1_ret := (hts_adv1_ret C pc_b pc_e pc_a cgp_b cgp_e
    csp_b csp_e C_f owner_a W_init_C Ws Cs cstk).
  Local Notation free_ret := (hts_free_ret C pc_b pc_e pc_a cgp_b cgp_e
    csp_b csp_e C_f owner_a Ws Cs cstk).

  Lemma hts_spec_free :
    is_shadow_address owner_a = false ->
    withinBounds owner_a (owner_a ^+ 1)%a owner_a = true ->
    is_heap_address owner_a = false ->
    disjoint_from_shadow pc_b pc_e ->
    is_heap_address pc_b = false ->
    not_heap_range cgp_b cgp_e ->
    disjoint_from_shadow csp_b csp_e ->
    disjoint_from_heap csp_b csp_e ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_main_code)%a ->
    hts_ctx ∗
    adv1_ret ∗
    (free_ret -∗
     WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Howner_shadow Howner_bounds Howner_nonheap Hpc_shadow Hpc_nonheap
      Hcgp_heap Hstk_shadow Hstk_heap HsubBounds) "(#Hctx & Hret & Hcontinue)".
    iDestruct "Hctx" as "(#Hassert & #Halloc & #Hservice & #Hswitcher
       & #Hexport_pcc & #Hexport_cgp & #Hexport_malloc & #Hexport_free
       & #Hadv & #Hentry)".
    iDestruct "Hret" as (b a_ret Wret) "(%Ha_ret & %Hbounds & %Hstk_nonempty
      & %Hrelated_share_ret & #Hrel_b & Hframe & [%w0 Hca0] & [%w1 Hca1]
      & Hregs & Hslot & [%stk Hstk] & Hworld & Hstack_revoked_ret
      & %Hstack_revoked_ret & HK & Howner & Hright & #Hallocation)".
    iDestruct "Hframe" as "(Hna & HPC & Hcra & Hcgp & Hcsp & [%wcs0 Hcs0]
      & [%wcs1 Hcs1] & Hcstk & Himports & Hcode & Hp & Howner_word)".
    iDestruct "Himports" as
      "(Himport_switcher & Himport_assert & Himport_adv & Himport_malloc
       & Himport_free & Himport_alloc_cap)".
    iDestruct "Hregs" as (rmap Hdom_rmap) "Hrmap".
    pose proof Hbounds as Hbnd; rewrite /hts_buffer_bounds in Hbnd.
    assert ((b + 1)%a = Some (b ^+ 1)%a) as Hsucc by solve_addr.

    (* Main still holds the free right of b: open its world entry. *)
    iMod (hts_world_reopen_live C csp_b csp_e W_init_C _ b Wret
      Hbounds Hstk_heap Hrelated_share_ret with "Hrel_b Hright Hworld")
      as (v_b) "(%Hwf_rev & %Hb_lookup & %Hstd_rev & Hworld_open & Hstate_b
        & Hright & Hb)".

    codefrag_facts "Hcode". clear H0.
    iEval (rewrite /hts_main_code /assembled_hts_main /assembled_hts_main') in "Hcode".
    iEval (cbv [fmap list_fmap concat]) in "Hcode".

    (* Block 10: reload the saved buffer. Its tag is kept: main owns the
       memory of b, so the allocator state of b is live. *)
    hts_focus_entry_block 10 "Hcode" as a_reload Ha_reload "Hblock" "Hcont"
      from Ha_ret.
    iHide "Hcont" as hcont.
    (* Load ca0 csp (-1). *)
    iApply (hts_reload_live_buffer_spec pc_b pc_e a_reload
      csp_b csp_e b _ v_b
      with "[- $Halloc $HPC $Hcsp $Hca0 $Hslot $Hb $Hblock]").
    { exact Hstk_shadow. }
    { solve_addr. }
    { exact Hstk_nonempty. }
    { by apply hts_buffer_heap_address. }
    { solve_addr. }
    iNext. iIntros "(HPC & Hcsp & Hca0 & Hslot & Hb & Hblock)".
    subst hcont; unfocus_block "Hblock" "Hcont" as "Hcode".

    (* Block 11: store cgp, which covers exactly p, in live b, and move the
       buffer to the second argument register. *)
    focus_block 11 "Hcode" as a_private Ha_private "Hblock" "Hcont";
      iHide "Hcont" as hcont.
    iEval (rewrite /hts_buffer) in "Hca0".
    iExtractList "Hrmap" [ct0;ct1;ct2] as ["[Hct0 _]";"[Hct1 _]";"[Hct2 _]"].
    (* Store ca0 cgp 0. *)
    iInstr_success "Hblock".
    { apply hts_heap_not_shadow. solve_addr. }
    { apply withinBounds_true_iff; solve_addr. }
    (* Mov ca1 ca0. *)
    iInstr "Hblock".
    subst hcont; unfocus_block "Hblock" "Hcont" as "Hcode".

    (* Block 12: fetch the allocator capability for free. *)
    focus_block 12 "Hcode" as a_fetch12 Ha_fetch12 "Hfetch" "Hcont";
      iHide "Hcont" as hcont.
    iApply (fetch_spec hts_alloc_cap_offset ca0 ct0 ct2 RX Global
      pc_b pc_e a_fetch12 (allocator_capability Global owner_a)
      _ _ _ _ with "[- $HPC $Hca0 $Hct0 $Hct2 $Hfetch]").
    { reflexivity. }
    { solve_addr. }
    { rewrite /hts_alloc_cap_offset. apply withinBounds_true_iff. solve_addr. }
    { exact Hpc_shadow. }
    { apply sealed_cap_nonheap. exact Howner_nonheap. }
    { done. }
    { done. }
    { done. }
    replace (pc_b ^+ hts_alloc_cap_offset)%a with (pc_b ^+ 5)%a by reflexivity.
    iFrame "Himport_alloc_cap".
    iNext; iIntros "(HPC & Hca0 & Hct0 & Hct2 & Hfetch & Himport_alloc_cap)".
    iEval (cbn) in "Hca0".
    subst hcont; unfocus_block "Hfetch" "Hcont" as "Hcode".

    (* Block 13: fetch the switcher entry for free. *)
    focus_block 13 "Hcode" as a_fetch13 Ha_fetch13 "Hfetch" "Hcont";
      iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ctp] as ["[Hctp _]"].
    iApply (fetch_spec hts_switcher_offset ctp ct0 ct2 RX Global
      pc_b pc_e a_fetch13
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

    (* Block 14: fetch the sealed free entry. *)
    focus_block 14 "Hcode" as a_fetch14 Ha_fetch14 "Hfetch" "Hcont";
      iHide "Hcont" as hcont.
    iApply (fetch_spec hts_free_offset ct1 ct0 ct2 RX Global
      pc_b pc_e a_fetch14
      (WSealed ot_switcher (allocator_free Global))
      _ _ _ _ with "[- $HPC $Hct1 $Hct0 $Hct2 $Hfetch]").
    { reflexivity. }
    { solve_addr. }
    { rewrite /hts_free_offset. apply withinBounds_true_iff. solve_addr. }
    { exact Hpc_shadow. }
    { unfold allocator_free. apply sealed_cap_nonheap.
      exact hts_export_tbl_not_heap. }
    { done. }
    { done. }
    { done. }
    replace (pc_b ^+ hts_free_offset)%a with (pc_b ^+ 4)%a by reflexivity.
    iFrame "Himport_free".
    iNext; iIntros "(HPC & Hct1 & Hct0 & Hct2 & Hfetch & Himport_free)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hfetch" "Hcont" as "Hcode".

    (* Block 15: call the trusted free entry while the live world cell is open. *)
    focus_block 15 "Hcode" as a_freecall Ha_freecall "Hblock" "Hcont";
      iHide "Hcont" as hcont.
    (* Jalr cra ctp. *)
    iInstr "Hblock".
    subst hcont; unfocus_block "Hblock" "Hcont" as "Hcode".
    assert (hts_block_addr pc_a 16 (a_freecall ^+ 1)%a) as Ha_next.
    { rewrite /hts_block_addr. solve_addr. }
    clear Ha_reload Ha_private Ha_fetch12 Ha_fetch13 Ha_fetch14.

    iAssert ([[b,(b ^+ 1)%a]] ↦ₐ
      [[ [WCap true RW Global cgp_b cgp_e cgp_b] ]])%I
      with "[Hb]" as "Hfree_mem".
    { rewrite /region_pointsto
        (finz_seq_between_singleton b (b ^+ 1)%a Hsucc) /=.
      iFrame. }
    iExtractList "Hrmap" [ca2;ca3;ca4;ca5] as
      ["[Hca2 %Hca2]";"[Hca3 %Hca3]";"[Hca4 %Hca4]";"[Hca5 %Hca5]"].
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    subst wca2 wca3 wca4 wca5.
    set (free_arg := ({[ca0 := allocator_capability Global owner_a;
      ca1 := hts_buffer b;
      ca2 := WInt 0; ca3 := WInt 0; ca4 := WInt 0;
      ca5 := WInt 0; ct0 := WInt 0]} : Reg)).
    iAssert ([∗ map] rarg↦warg ∈ free_arg, rarg ↦ᵣ warg)%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hfree_arg".
    { subst free_arg.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]). done. }
    iInsertList "Hrmap" [ctp;ct2].
    set (free_other := <[ct2:=WInt 0]>
      (<[ctp:=WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call]>
       (delete ca5 (delete ca4 (delete ca3 (delete ca2
         (delete ct1 (delete ct0 rmap)))))))).
    iPoseProof (hts_free_known_function
      (WCap true RW Global cgp_b cgp_e cgp_b)
      (WSentry true RX Global pc_b pc_e (a_freecall ^+ 1)%a)
      wcs0 wcs1 csp_b csp_e (csp_b ^+ 1)%a b (b ^+ 1)%a b
      free_arg cstk RW Global 0%Z
      [WCap true RW Global cgp_b cgp_e cgp_b]
      Global owner_a hts_main_owner_id {[b]}
      with "Hservice") as "Hfree_fun".
    { exact Howner_shadow. }
    { exact Howner_bounds. }
    { exact Hbounds. }
    { rewrite (finz_seq_between_singleton b (b ^+ 1)%a Hsucc).
      reflexivity. }
    { subst free_arg. reflexivity. }
    { subst free_arg. reflexivity. }
    pose proof allocator_size_exports as Hsize.
    rewrite /allocator_export_table_entries in Hsize.
    iApply (switcher_cc_specification_known_to_known_end_to_end
      Nswitcher
      (WCap true RW Global cgp_b cgp_e cgp_b)
      (WSentry true RX Global pc_b pc_e (a_freecall ^+ 1)%a)
      wcs0 wcs1 csp_b csp_e (csp_b ^+ 1)%a stk free_arg free_other cstk
      allocator_free_nargs ⊤ hts_allocator_exp_tblN
      allocator_exp_tbl_b
      (allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a
      allocator_exp_tbl_e allocator_pcc_b allocator_pcc_e
      allocator_cgp_b allocator_cgp_e allocator_free_pcc_off
      with "[- $Halloc $Hswitcher $Hexport_pcc $Hexport_cgp $Hexport_free
        $Hna $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1
        $Hfree_arg $Hrmap $Hstk $Hcstk $Hfree_fun]").
    { exact Hstk_heap. }
    { exact Hstk_shadow. }
    { apply hts_export_tbl_not_shadow.
      rewrite /allocator_free_exp_tbl_off. solve_addr. }
    { apply hts_export_tbl_not_shadow. solve_addr. }
    { apply hts_export_tbl_not_shadow. solve_addr. }
    { exact hts_allocator_pcc_not_heap. }
    { exact hts_allocator_cgp_not_heap. }
    { solve_ndisj. }
    { rewrite /allocator_free_exp_tbl_off. solve_addr. }
    { solve_addr. }
    { rewrite /allocator_free_exp_tbl_off. solve_addr. }
    { rewrite /allocator_free_nargs; lia. }
    { exists (allocator_code_b ^+ length allocator_malloc_instrs)%a.
      rewrite /allocator_free_pcc_off /allocator_malloc_pcc_off.
      pose proof allocator_size_imports as Himports_size.
      pose proof allocator_size_code as Hcode_size.
      rewrite /allocator_code length_app in Hcode_size.
      solve_addr. }
    { subst free_other.
      repeat (rewrite dom_insert_L).
      repeat (rewrite dom_delete_L).
      rewrite Hdom_rmap /dom_arg_rmap /=. set_solver+. }
    { subst free_arg. rewrite /is_arg_rmap /dom_arg_rmap /=.
      reflexivity. }
    iFrame "Hallocation Hfree_mem Howner Howner_word".
    iNext.
    iIntros "[Hcall|Hcall]".
    - iDestruct "Hcall" as
        (rcgp rcra rcs0 rcs1 wca0_ret wca1_ret free_rmap_ret
          Hdom_free_rmap_ret)
        "(Hna & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
          & Hca0 & Hca1 & Hrmap & Hstk & Hcstk & %Hrestored & Hfree_post)".
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
      iEval (rewrite /hts_free_result) in "Hfree_post".
      iDestruct "Hfree_post" as
        "(_ & Hreclaimed & _ & Howner_word & %Hfree_values)".
      destruct Hfree_values as [-> ->].
      iApply "Hcontinue".
      iExists (a_freecall ^+ 1)%a.
      iSplit; first done.
      iRight. iExists b, Wret.
      iFrame "∗#%".
    - iDestruct "Hcall" as
        (free_rmap_exhaust stk_mem_exhaust rcgp rcra rcs0 rcs1
          Hdom_free_rmap_exhaust)
        "(Hna & HPC & Hcgp & Hcra & Hcsp & Hcs0 & Hcs1
          & Hca0 & Hca1 & Hrmap & Hstk & Hcstk & %Hrestored & _)".
      destruct Hrestored as (_ & Hra_free & _ & _).
      apply load_heap_nonheap in Hra_free.
      2: { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=
             Hpc_nonheap /=. reflexivity. }
      subst rcra.
      iEval (cbn) in "HPC".
      iApply "Hcontinue".
      iExists (a_freecall ^+ 1)%a.
      iSplit; first done.
      iLeft. iExists _. iFrame "Hna HPC Hca0 Hcode".
      iSplit; first (iPureIntro; rewrite /ENOTENOUGHTRUSTEDSTACK; lia).
      iExtractList "Hrmap" [ct0] as ["[Hct0 _]"].
      by iExists _.
  Qed.
End HTS_Spec_Free.
