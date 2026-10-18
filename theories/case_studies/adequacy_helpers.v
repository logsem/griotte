From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From griotte Require Import switcher_preamble assert_spec.
From griotte Require Import rules call_stack.
From griotte Require Import mkregion_helpers memory_region disjoint_regions_tactics.
From griotte Require Import switcher_adequacy compartment_layout.
From griotte Require Import allocator_resources.


Section adequacy_helpers.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters} .

    Lemma initialise_assert_compartment
      {E : coPset} (assert_cmpt : cmptAssert) (flagN : namespace) :
      ([∗ map] a↦v ∈ mk_initial_assert assert_cmpt, a ↦ₐ lword_of_word v)
      ={E}=∗
      inv flagN (flag_assert assert_cmpt ↦ₐ WInt 0) ∗
      assert_static (b_assert assert_cmpt) (e_assert assert_cmpt) (flag_assert assert_cmpt).
    Proof.
      iIntros "Hcmpt_assert".
      rewrite /mk_initial_assert.
      iDestruct (big_sepM_union with "Hcmpt_assert") as "[Hassert Hassert_flag]".
      { eapply cmpt_assert_flag_mregion_disjoint ; eauto. }
      iDestruct (big_sepM_union with "Hassert") as "[Hassert Hassert_cap]".
      { eapply cmpt_assert_cap_mregion_disjoint ; eauto. }
      rewrite /cmpt_assert_flag_mregion.
      rewrite /mkregion.
      rewrite finz_seq_between_singleton.
      2: { pose proof (assert_flag_size assert_cmpt) as H; solve_addr+H. }
      cbn.
      iDestruct (big_sepM_insert with "Hassert_flag") as "[Hassert_flag _]"; first done.
      iMod (inv_alloc flagN E (flag_assert assert_cmpt ↦ₐ WInt 0%Z) with "Hassert_flag")%I
        as "#Hinv_assert_flag".
      rewrite /cmpt_assert_cap_mregion.
      rewrite /mkregion.
      rewrite finz_seq_between_singleton.
      2: { pose proof (assert_cap_size assert_cmpt) as H; solve_addr+H. }
      cbn.
      iDestruct (big_sepM_insert with "Hassert_cap") as "[Hassert_cap _]"; first done.

      rewrite /cmpt_assert_code_mregion.
      iDestruct (mkregion_prepare with "[Hassert]") as ">Hassert"; auto.
      { apply (assert_code_size assert_cmpt). }
      iAssert (codefrag (b_assert assert_cmpt) assert_subroutine_instrs)
        with "[Hassert]" as "Hassert".
      { rewrite /codefrag /region_pointsto big_sepL2_fmap_r.
        replace (b_assert assert_cmpt ^+ length assert_subroutine_instrs)%a
          with (cap_assert assert_cmpt).
        2: { pose proof (assert_code_size assert_cmpt); solve_addr+H. }
        iFrame.
      }
      iMod (codefrag_persist with "Hassert") as "#Hassert".
      iMod (pointsto_persist with "Hassert_cap") as "#Hassert_cap".
      iModIntro. iFrame "Hinv_assert_flag".
      rewrite /assert_static.
      iSplit; first (iPureIntro; apply (assert_code_nonheap assert_cmpt)).
      iExists (cap_assert assert_cmpt).
      iFrame "Hassert Hassert_cap".
      iSplit; first (iPureIntro ; apply (assert_code_size assert_cmpt)).
      iSplit; iPureIntro.
      + apply (assert_cap_size assert_cmpt).
      + by rewrite (assert_flag_size assert_cmpt).
    Qed.

    Lemma initialise_switcher_compartment
      {E : coPset} (switcher_cmpt : cmptSwitcher) (switcherN : namespace) :
      let swlayout :=  (cmptSwitcher_switcherLayout switcher_cmpt) in
      ([∗ map] k↦y ∈ mk_initial_switcher switcher_cmpt, k ↦ₐ lword_of_word y) -∗
      can_alloc_pred (ot_switcher switcher_cmpt) -∗
      cstack_full [] -∗
      mtdc ↦ₛᵣ WCap true RWL Local (b_trusted_stack switcher_cmpt) (e_trusted_stack switcher_cmpt) (b_trusted_stack switcher_cmpt)
      ={E}=∗
      seal_pred (ot_switcher switcher_cmpt) ot_switcher_propC ∗
      na_inv cerise_nais switcherN switcher_inv ∗
      switcher_static ∗
      [[ (b_stack switcher_cmpt), (e_stack switcher_cmpt) ]] ↦ₐ [[ lword_of_word <$> stack_content switcher_cmpt ]].
    Proof.
      intros.
      iIntros "Hcmpt_switcher Hseal_store Hcstk_full Hmtdc".
      rewrite /mk_initial_switcher.
      iDestruct (big_sepM_union with "Hcmpt_switcher") as "[Hswitcher Hstack]".
      { eapply cmpt_switcher_stack_mregion_disjoint ; eauto. }
      iDestruct (big_sepM_union with "Hswitcher") as "[Hswitcher Htrusted_stack]".
      { eapply cmpt_switcher_trusted_stack_mregion_disjoint ; eauto. }

      rewrite /cmpt_switcher_code_mregion.
      iDestruct (big_sepM_union with "Hswitcher") as "[Hswitcher_sealing Hswitcher]".
      { eapply cmpt_switcher_code_stack_mregion_disjoint ; eauto. }
      iEval (rewrite /mkregion) in "Hswitcher_sealing".
      rewrite finz_seq_between_singleton.
      2: { apply switcher_call_entry_point. }
      iEval (cbn) in "Hswitcher_sealing".
      iDestruct (big_sepM_insert with "Hswitcher_sealing") as "[Hswitcher_sealing _]"; first done.
      iDestruct (mkregion_prepare with "[Hswitcher]") as ">Hswitcher"; auto.
      { apply switcher_size. }
      rewrite /cmpt_switcher_trusted_stack_mregion.
      iDestruct (mkregion_prepare with "[Htrusted_stack]") as ">Htrusted_stack"; auto.
      { apply (trusted_stack_size switcher_cmpt). }
      iMod (seal_store_update_alloc _ ( ot_switcher_propC ) with "Hseal_store") as "#Hsealed_pred_ot_switcher".
      iAssert (codefrag (a_switcher_call switcher_cmpt) switcher_instrs)
        with "[Hswitcher]" as "Hswitcher_code".
      {
        rewrite /codefrag /region_pointsto.
        setoid_rewrite big_sepL2_fmap_r.
        replace ((a_switcher_call switcher_cmpt) ^+ length switcher_instrs)%a
          with (e_switcher switcher_cmpt).
        2: { pose proof (switcher_size switcher_cmpt) as H.
             solve_addr+H.
        }
        iFrame.
      }
      iAssert ( switcher_preamble.switcher_inv )
        with "[Htrusted_stack Hcstk_full Hmtdc]" as "Hswitcher".
      {
        rewrite /switcher_inv /region_pointsto.
        iFrame "∗#".
        iExists (lword_of_word <$> tl (trusted_stack_content switcher_cmpt)).
        iSplitR; first (iPureIntro; apply (ot_switcher_size switcher_cmpt)).
        pose proof (trusted_stack_content_base_zeroed switcher_cmpt) as Htstk_head.
        pose proof (trusted_stack_size switcher_cmpt) as Htstk_size.
        destruct (trusted_stack_content switcher_cmpt); cbn in Htstk_head; simplify_eq.
        rewrite finz_seq_between_cons; last solve_addr+Htstk_size.
        iDestruct "Htrusted_stack" as "[Hbase_stack Htrusted_stack]".
        rewrite big_sepL2_fmap_r.
        iFrame.
        iSplitL; last (iPureIntro ; by rewrite finz_add_0).
        iPureIntro; subst swlayout; cbn; solve_addr.
      }
      iMod (na_inv_alloc cerise_nais _ switcherN _ with "Hswitcher") as "#Hswitcher".
      iMod (codefrag_persist with "Hswitcher_code") as "#Hswitcher_code".
      iMod (pointsto_persist with "Hswitcher_sealing") as "#Hswitcher_sealing".
      iAssert switcher_static as "#Hswitcher_static".
      { rewrite /switcher_static. iFrame "Hswitcher_code Hswitcher_sealing". }
      iClear "Hswitcher_code Hswitcher_sealing".

      iDestruct (mkregion_prepare with "[Hstack]") as ">Hstack"; auto.
      { apply (stack_size switcher_cmpt). }
      rewrite /region_pointsto big_sepL2_fmap_r.
      iFrame "∗ Hsealed_pred_ot_switcher Hswitcher Hswitcher_static".
      done.
    Qed.

    Lemma initialise_compartment ( C_cmpt : cmpt ) :
      let PCC := WCap true RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_b_pcc C_cmpt) in
      let CGP := WCap true RW Global (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) (cmpt_b_cgp C_cmpt) in
      ([∗ map] k↦y ∈ mk_initial_cmpt C_cmpt, k ↦ₐ lword_of_word y)
      ==∗
      [[ (cmpt_b_pcc C_cmpt), (cmpt_a_code C_cmpt) ]] ↦ₐ [[ lword_of_word <$> cmpt_imports C_cmpt ]] ∗
      [[ (cmpt_a_code C_cmpt), (cmpt_e_pcc C_cmpt) ]] ↦ₐ [[ lword_of_word <$> cmpt_code C_cmpt ]] ∗
      [[ (cmpt_b_cgp C_cmpt), (cmpt_e_cgp C_cmpt) ]] ↦ₐ [[ lword_of_word <$> cmpt_data C_cmpt ]] ∗
      [[ (cmpt_b_static_sealed C_cmpt), (cmpt_e_static_sealed C_cmpt) ]] ↦ₐ [[ lword_of_word <$> cmpt_static_sealed C_cmpt ]] ∗
      cmpt_exp_tbl_pcc C_cmpt ↦ₐ PCC ∗
      cmpt_exp_tbl_cgp C_cmpt ↦ₐ CGP ∗
      [[ (cmpt_exp_tbl_entries_start C_cmpt), (cmpt_exp_tbl_entries_end C_cmpt) ]] ↦ₐ [[ lword_of_word <$> cmpt_exp_tbl_entries C_cmpt ]].
    Proof.
      intros PCC CGP.
      iIntros "Hcmpt_C".
      iEval (rewrite /mk_initial_cmpt) in "Hcmpt_C".
      iDestruct (big_sepM_union with "Hcmpt_C") as "[HC HC_etbl]".
      { eapply cmpt_exp_tbl_disjoint ; eauto. }
      iDestruct (big_sepM_union with "HC") as "[HC HC_static_sealed]".
      { eapply cmpt_static_sealed_disjoint ; eauto. }
      rewrite /cmpt_static_sealed_mregion.
      iDestruct (big_sepM_union with "HC") as "[HC_code HC_data]".
      { eapply cmpt_cgp_disjoint ; eauto. }
      rewrite /cmpt_pcc_mregion.
      iDestruct (big_sepM_union with "HC_code") as "[HC_imports HC_code]".
      { eapply cmpt_code_disjoint ; eauto. }
      iEval (rewrite /mkregion) in "HC_imports".
      rewrite /cmpt_cgp_mregion.
      iDestruct (mkregion_prepare with "[HC_code]") as ">HC_code"; auto.
      { apply (cmpt_code_size C_cmpt). }
      iDestruct (mkregion_prepare with "[HC_data]") as ">HC_data"; auto.
      { apply (cmpt_data_size C_cmpt). }
      iDestruct (mkregion_prepare with "[HC_static_sealed]") as ">HC_static_sealed"; auto.
      { apply (cmpt_static_sealed_size C_cmpt). }
      iDestruct (mkregion_prepare with "[HC_imports]") as ">HC_imports"; auto.
      { by pose proof (cmpt_import_size C_cmpt) as H ; cbn in *. }

      iEval (rewrite /cmpt_exp_tbl_mregion) in "HC_etbl".
      iDestruct (big_sepM_union with "HC_etbl") as "[HC_etbl HC_etbl_entries]".
      { eapply cmpt_exp_tbl_entries_disjoint. }
      iDestruct (big_sepM_union with "HC_etbl") as "[HC_etbl_pcc HC_etbl_cgp]".
      { eapply cmpt_exp_tbl_pcc_cgp_disjoint. }
      iDestruct (mkregion_prepare with "[HC_etbl_entries]") as ">HC_etbl_entries"; auto.
      { apply cmpt_exp_tbl_entries_size. }
      iDestruct (mkregion_prepare with "[HC_etbl_pcc]") as ">HC_etbl_pcc"; auto.
      { cbn; apply cmpt_exp_tbl_pcc_size. }
      iDestruct (mkregion_prepare with "[HC_etbl_cgp]") as ">HC_etbl_cgp"; auto.
      { cbn; apply cmpt_exp_tbl_cgp_size. }
      rewrite (finz_seq_between_singleton (cmpt_exp_tbl_pcc C_cmpt))
      ; last (apply cmpt_exp_tbl_pcc_size).
      rewrite (finz_seq_between_singleton (cmpt_exp_tbl_cgp C_cmpt))
      ; last (apply cmpt_exp_tbl_cgp_size).
      rewrite !big_sepL2_singleton.
      rewrite /region_pointsto !big_sepL2_fmap_r.
      iFrame.
      done.
    Qed.

    (** The memory of a compartment, with its read-only parts persistent:
        its import table, its code and its export table. *)
    Lemma initialise_compartment_pers ( C_cmpt : cmpt ) :
      let PCC := WCap true RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_b_pcc C_cmpt) in
      let CGP := WCap true RW Global (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) (cmpt_b_cgp C_cmpt) in
      ([∗ map] k↦y ∈ mk_initial_cmpt C_cmpt, k ↦ₐ lword_of_word y)
      ==∗
      [[ (cmpt_b_pcc C_cmpt), (cmpt_a_code C_cmpt) ]] ↦ₐ□ [[ lword_of_word <$> cmpt_imports C_cmpt ]] ∗
      codefrag_pers (cmpt_a_code C_cmpt) (cmpt_code C_cmpt) ∗
      [[ (cmpt_b_cgp C_cmpt), (cmpt_e_cgp C_cmpt) ]] ↦ₐ [[ lword_of_word <$> cmpt_data C_cmpt ]] ∗
      [[ (cmpt_b_static_sealed C_cmpt), (cmpt_e_static_sealed C_cmpt) ]] ↦ₐ [[ lword_of_word <$> cmpt_static_sealed C_cmpt ]] ∗
      cmpt_exp_tbl_pcc C_cmpt ↦ₐ□ PCC ∗
      cmpt_exp_tbl_cgp C_cmpt ↦ₐ□ CGP ∗
      [[ (cmpt_exp_tbl_entries_start C_cmpt), (cmpt_exp_tbl_entries_end C_cmpt) ]] ↦ₐ□ [[ lword_of_word <$> cmpt_exp_tbl_entries C_cmpt ]].
    Proof.
      intros PCC CGP.
      iIntros "Hcmpt_C".
      iMod (initialise_compartment with "Hcmpt_C")
        as "(HC_imports & HC_code & $ & $ & HC_etbl_pcc & HC_etbl_cgp & HC_etbl_entries)".
      iMod (region_pointsto_persist with "HC_imports") as "$".
      iMod (pointsto_persist with "HC_etbl_pcc") as "$".
      iMod (pointsto_persist with "HC_etbl_cgp") as "$".
      iMod (region_pointsto_persist with "HC_etbl_entries") as "$".
      iApply codefrag_persist.
      rewrite /codefrag.
      replace (cmpt_a_code C_cmpt ^+ length (cmpt_code C_cmpt))%a with (cmpt_e_pcc C_cmpt).
      { iExact "HC_code". }
      pose proof (cmpt_code_size C_cmpt); solve_addr.
    Qed.

    Lemma initialise_adversary_compartment ( C_cmpt : cmpt ) :
      let PCC := WCap true RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_b_pcc C_cmpt) in
      let CGP := WCap true RW Global (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) (cmpt_b_cgp C_cmpt) in
      let exp_tbl_addrs := (finz.seq_between (cmpt_exp_tbl_entries_start C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt)) in
      ([∗ map] k↦y ∈ mk_initial_cmpt C_cmpt, k ↦ₐ lword_of_word y)
      ==∗
      [[ (cmpt_b_pcc C_cmpt), (cmpt_a_code C_cmpt) ]] ↦ₐ [[ lword_of_word <$> cmpt_imports C_cmpt ]] ∗
      [[ (cmpt_a_code C_cmpt), (cmpt_e_pcc C_cmpt) ]] ↦ₐ [[ lword_of_word <$> cmpt_code C_cmpt ]] ∗
      [[ (cmpt_b_cgp C_cmpt), (cmpt_e_cgp C_cmpt) ]] ↦ₐ [[ lword_of_word <$> cmpt_data C_cmpt ]] ∗
      [[ (cmpt_b_static_sealed C_cmpt), (cmpt_e_static_sealed C_cmpt) ]] ↦ₐ [[ lword_of_word <$> cmpt_static_sealed C_cmpt ]] ∗
      cmpt_exp_tbl_pcc C_cmpt ↦ₐ□ PCC ∗
      cmpt_exp_tbl_cgp C_cmpt ↦ₐ□ CGP ∗
      ([∗ list] a;v ∈ exp_tbl_addrs ; cmpt_exp_tbl_entries C_cmpt, a ↦ₐ□ lword_of_word v).
    Proof.
      intros PCC CGP exp_tbl_addrs.
      iIntros "Hcmpt_C".
      iMod (initialise_compartment with "Hcmpt_C")
        as "($ & $ & $ & $ & HC_etbl_pcc & HC_etbl_cgp & HC_etbl_entries)".
      iMod (pointsto_persist with "HC_etbl_pcc") as "$".
      iMod (pointsto_persist with "HC_etbl_cgp") as "$".
      iMod (region_pointsto_persist with "HC_etbl_entries") as "HC_etbl_entries".
      subst exp_tbl_addrs.
      rewrite /region_pointsto_pers big_sepL2_fmap_r.
      by iFrame "HC_etbl_entries".
    Qed.

End adequacy_helpers.

(** ** Ghost initialisation *)
Section adequacy_ghost_init.
  Context `{MP : MachineParameters}.

  (** With zero in [cnull], the initial logical registers are the physical
      ones without identifiers. *)
  Lemma init_lregs_cnull (reg : Reg) :
    reg !! cnull = Some (WInt 0) → init_lregs reg = lword_of_word <$> reg.
  Proof.
    intros Hnull. rewrite /init_lregs Hnull insert_id //.
    by rewrite lookup_fmap Hnull.
  Qed.

  (** The initial condition without heap roots, for a system without an
      allocator: no initial word carries heap authority, and every tagged
      executable word has closed bounds that avoid the heap. *)
  Lemma ghost_init_cond_no_roots (pc : Word) (reg : Reg) (sreg : SReg) (m : Mem) :
    mem_rooted ∅ m →
    word_rooted ∅ pc →
    (∀ r w, reg !! r = Some w → word_rooted ∅ w) →
    (∀ sr w, sreg !! sr = Some w → word_rooted ∅ w) →
    mem_avoids_mmio m →
    reg !! cnull = Some (WInt 0) →
    mem_exec_ok m →
    word_exec_ok pc →
    (∀ r w, reg !! r = Some w → word_exec_ok w) →
    (∀ sr w, sreg !! sr = Some w → word_exec_ok w) →
    pc_ok pc →
    (∀ sr w, is_pc_sreg sr = true → sreg !! sr = Some w → pc_ok w) →
    (∀ sr, sr ∈ reserved_sregs → is_Some (sreg !! sr)) →
    (∀ w, sreg !! MTCC = Some w → get_tag w = false) →
    ghost_init_cond (pc, reg, sreg, m, initial_heap_shadow) ∅.
  Proof.
    intros Hm Hpc Hreg Hsreg Hmmio Hnull Hmx Hpcx Hregx Hsregx Hpcok Hsregok Hreserved Hmtcc.
    constructor; cbn.
    - set_solver.
    - set_solver.
    - intros a Ha. eexists.
      rewrite /initial_heap_shadow lookup_fmap /initial_heap_memory
        lookup_gset_to_gmap option_guard_True //.
      by apply elem_of_heap_addresses.
    - intros a w b Ha. by eapply Hm.
    - intros b. by eapply Hpc.
    - intros r w b _ Hw. by eapply Hreg.
    - intros sr w b Hw. by eapply Hsreg.
    - exact Hmmio.
    - intros w Hw. rewrite Hnull in Hw. by injection Hw as <-.
    - exact Hmx.
    - exact Hpcx.
    - exact Hregx.
    - exact Hsregx.
    - exact Hpcok.
    - exact Hsregok.
    - exact Hreserved.
    - exact Hmtcc.
  Qed.

  (** Program memory disjoint from the initial heap holds no heap address. *)
  Lemma not_heap_of_disjoint_dom (pm : Mem) a :
    initial_heap_memory ##ₘ pm → a ∈ dom pm → is_heap_address a = false.
  Proof.
    intros Hdisj Ha. apply not_true_is_false. intros Hheap.
    apply elem_of_dom in Ha as [w Hw].
    eapply map_disjoint_spec; [exact Hdisj| |exact Hw].
    rewrite /initial_heap_memory lookup_gset_to_gmap option_guard_True //.
    by apply elem_of_heap_addresses.
  Qed.

  Lemma disjoint_from_heap_of_disjoint_dom (pm : Mem) b e :
    initial_heap_memory ##ₘ pm →
    list_to_set (finz.seq_between b e) ⊆ dom pm →
    disjoint_from_heap b e.
  Proof.
    intros Hdisj Hdom. rewrite /disjoint_from_heap elem_of_disjoint.
    intros x Hx Hheap.
    assert (x ∈ dom pm) as Hx_dom by (apply Hdom; set_solver).
    pose proof (not_heap_of_disjoint_dom pm x Hdisj Hx_dom) as Hnot.
    apply elem_of_finz_seq_between in Hheap.
    assert (is_heap_address x = true) as Hyes by (apply withinBounds_true_iff; solve_addr).
    congruence.
  Qed.

  (** The switcher's trusted stack lies outside the heap. *)
  Lemma trusted_stack_disjoint_from_heap_of_disjoint_dom
    (Cswitcher : cmptSwitcher) (pm : Mem) :
    initial_heap_memory ##ₘ pm →
    dom (mk_initial_switcher Cswitcher) ⊆ dom pm →
    disjoint_from_heap (b_trusted_stack Cswitcher) (e_trusted_stack Cswitcher).
  Proof.
    intros Hdisj Hdom. apply (disjoint_from_heap_of_disjoint_dom pm); first done.
    etrans; last exact Hdom.
    rewrite /mk_initial_switcher !dom_union_L dom_switcher_trusted_stack_mregion.
    set_solver.
  Qed.

  (** The assert code lies outside the heap. *)
  Lemma assert_disjoint_from_heap_of_disjoint_dom (Cassert : cmptAssert) (pm : Mem) :
    initial_heap_memory ##ₘ pm →
    dom (mk_initial_assert Cassert) ⊆ dom pm →
    disjoint_from_heap (b_assert Cassert) (e_assert Cassert).
  Proof.
    intros Hdisj Hdom. apply (disjoint_from_heap_of_disjoint_dom pm); first done.
    etrans; last exact Hdom.
    rewrite /mk_initial_assert !dom_union_L dom_assert_code_mregion dom_assert_cap_mregion
      /cmpt_assert_code_region /cmpt_assert_cap_region.
    pose proof (assert_code_size Cassert). pose proof (assert_cap_size Cassert).
    rewrite (finz_seq_between_split (b_assert Cassert) (cap_assert Cassert) (e_assert Cassert));
      last solve_addr.
    rewrite list_to_set_app_L. set_solver.
  Qed.

  (** The assert flag lies outside the heap. *)
  Lemma assert_flag_not_heap_of_disjoint_dom (Cassert : cmptAssert) (pm : Mem) :
    initial_heap_memory ##ₘ pm →
    dom (mk_initial_assert Cassert) ⊆ dom pm →
    is_heap_address (flag_assert Cassert) = false.
  Proof.
    intros Hdisj Hdom. apply (not_heap_of_disjoint_dom pm); first done.
    apply Hdom.
    rewrite /mk_initial_assert !dom_union_L dom_assert_flag_mregion
      /cmpt_assert_flag_region.
    pose proof (assert_flag_size Cassert).
    rewrite (finz_seq_between_singleton (flag_assert Cassert)); last solve_addr.
    set_solver.
  Qed.
End adequacy_ghost_init.
