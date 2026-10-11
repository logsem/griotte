From iris.program_logic Require Import adequacy.
From iris.proofmode Require Import proofmode.
From griotte Require Import griotte_lang logrel interp_weakening monotone.
From griotte Require Import compartment_layout adequacy_helpers adequacy_common switcher assert assert_spec.
From griotte.case_studies.hts_no_ownership Require Import heap_temporal_safety heap_temporal_safety_preamble heap_temporal_safety_spec.
From griotte.allocators.no_ownership Require Import allocator_malloc_safe allocator_free_safe.
From griotte Require Import mkregion_helpers disjoint_regions_tactics
  region_invariants_revocation region_invariants_allocation
  world_interp_allocation_compartments switcher_preamble
  interp_switcher_call interp_switcher_return switcher_adequacy.
From griotte.allocators.no_ownership Require Import allocator allocator_preamble allocator_resource_spec.

(** The allocator is an ordinary switcher compartment. Its special authority
    is in its imports (shadow) and data (heap root), not a new calling ABI. *)
Definition hts_cmpt_allocator_layout `{MP : MachineParameters} (C : cmpt)
    (otype : OType)
    : allocatorLayout :=
  {| AllocOtype := otype;
     allocator_pcc_b := cmpt_b_pcc C;
     allocator_code_b := cmpt_a_code C;
     allocator_pcc_e := cmpt_e_pcc C;
     allocator_cgp_b := cmpt_b_cgp C;
     allocator_cgp_e := cmpt_e_cgp C;
     allocator_exp_tbl_b := cmpt_exp_tbl_pcc C;
     allocator_exp_tbl_e := cmpt_exp_tbl_entries_end C |}.

Class hts_memory_layout `{MP : MachineParameters} := {
    hts_switcher_cmpt : cmptSwitcher;
    hts_assert_cmpt : cmptAssert;
    hts_main_cmpt : cmpt;
    hts_adv_cmpt : cmpt;
    hts_allocator_cmpt : cmpt;
    hts_allocator_otype : OType;
    hts_adv_entry_offset : nat;
    hts_adv_entry_valid :
      is_Some (cmpt_b_pcc hts_adv_cmpt + hts_adv_entry_offset)%a;
    hts_allocator_wf :
      @allocatorLayoutWf MP (hts_cmpt_allocator_layout hts_allocator_cmpt hts_allocator_otype);
    hts_regions_disjoint :
      ## [cmpt_region hts_main_cmpt; cmpt_region hts_adv_cmpt;
          cmpt_region hts_allocator_cmpt; cmpt_switcher_region hts_switcher_cmpt;
          cmpt_assert_region hts_assert_cmpt;
          finz.seq_between heap_b heap_e; finz.seq_between shadow_b shadow_e]
  }.

#[local] Instance hts_memory_switcher_layout `{hts_memory_layout} : switcherLayout :=
  cmptSwitcher_switcherLayout hts_switcher_cmpt.
#[local] Instance hts_memory_assert_layout `{hts_memory_layout} : assertLayout :=
  cmptAssert_assertLayout hts_assert_cmpt.
#[local] Instance hts_memory_allocator_layout `{hts_memory_layout} : allocatorLayout :=
  hts_cmpt_allocator_layout hts_allocator_cmpt hts_allocator_otype.

#[local] Instance hts_memory_allocator_wf `{hts_memory_layout} : allocatorLayoutWf :=
  hts_allocator_wf.

#[local] Instance hts_memory_switcher_wf `{hts_memory_layout} : switcherLayoutWf.
Proof.
  pose proof (compartment_layout.ot_switcher_size hts_switcher_cmpt).
  pose proof (compartment_layout.switcher_size hts_switcher_cmpt).
  pose proof (compartment_layout.switcher_call_entry_point hts_switcher_cmpt).
  pose proof (compartment_layout.switcher_return_entry_point hts_switcher_cmpt).
  pose proof (compartment_layout.trusted_stack_disjoint_from_shadow hts_switcher_cmpt).
  pose proof (compartment_layout.switcher_base_not_shadow hts_switcher_cmpt).
  pose proof (compartment_layout.switcher_not_heap_range hts_switcher_cmpt).
  refine (mkSwitcherLayoutWf _ _ _ _ _ _ _ _); cbn in *; auto.
Defined.

Definition hts_initial_program_memory `{hts_memory_layout} : Mem :=
  mk_initial_switcher hts_switcher_cmpt ∪
  mk_initial_assert hts_assert_cmpt ∪
  mk_initial_cmpt hts_main_cmpt ∪
  mk_initial_cmpt hts_allocator_cmpt ∪
  mk_initial_cmpt hts_adv_cmpt.

Definition hts_initial_memory `{hts_memory_layout} : Mem :=
  initial_heap_memory ∪ hts_initial_program_memory.

Definition hts_is_initial_registers `{hts_memory_layout} (reg : Reg) :=
  reg !! PC = Some (WCap true RX Global
    (cmpt_b_pcc hts_main_cmpt) (cmpt_e_pcc hts_main_cmpt) (cmpt_a_code hts_main_cmpt)) ∧
  reg !! cgp = Some (WCap true RW Global
    (cmpt_b_cgp hts_main_cmpt) (cmpt_e_cgp hts_main_cmpt) (cmpt_b_cgp hts_main_cmpt)) ∧
  reg !! csp = Some (WCap true RWL Local
    (b_stack hts_switcher_cmpt) (e_stack hts_switcher_cmpt) (b_stack hts_switcher_cmpt)) ∧
  (∀ r, r ∉ ({[PC; cgp; csp]} : gset RegName) -> reg !! r = Some (WInt 0)).

Definition hts_is_initial_sregisters `{hts_memory_layout} (sreg : SReg) :=
  sreg !! MTDC = Some (WCap true RWL Local
    (compartment_layout.b_trusted_stack hts_switcher_cmpt)
    (compartment_layout.e_trusted_stack hts_switcher_cmpt)
    (compartment_layout.b_trusted_stack hts_switcher_cmpt)).

Definition hts_is_initial_memory `{hts_memory_layout} (mem : Mem) :=
  let adv_f := SCap true RO Global
    (cmpt_exp_tbl_pcc hts_adv_cmpt) (cmpt_exp_tbl_entries_end hts_adv_cmpt)
    (cmpt_exp_tbl_entries_start hts_adv_cmpt) in
  mem = hts_initial_memory ∧
  cmpt_imports hts_main_cmpt = hts_main_imports adv_f ∧
  cmpt_code hts_main_cmpt = hts_main_code ∧
  cmpt_data hts_main_cmpt = hts_main_data ∧
  cmpt_static_sealed hts_main_cmpt = [] ∧
  cmpt_exp_tbl_entries hts_main_cmpt = [] ∧
  cmpt_imports hts_allocator_cmpt = allocator_imports ∧
  cmpt_code hts_allocator_cmpt = allocator_code ∧
  cmpt_data hts_allocator_cmpt = allocator_data ∧
  cmpt_static_sealed hts_allocator_cmpt = [] ∧
  cmpt_exp_tbl_entries hts_allocator_cmpt = allocator_export_table_entries ∧
  (* The adversary is arbitrary and may call malloc and free. In particular,
     it may quarantine the buffer during the first call. *)
  cmpt_imports hts_adv_cmpt =
    [WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call;
     WSealed ot_switcher (allocator_malloc Global);
     WSealed ot_switcher (allocator_free Global)] ∧
  Forall is_z (cmpt_code hts_adv_cmpt) ∧
  Forall (is_initial_data_word hts_adv_cmpt) (cmpt_data hts_adv_cmpt) ∧
  cmpt_static_sealed hts_adv_cmpt = [] ∧
  cmpt_exp_tbl_entries hts_adv_cmpt =
    [WInt (encode_entry_point 1 hts_adv_entry_offset)] ∧
  Forall is_z (stack_content hts_switcher_cmpt).

Lemma hts_initial_adv_disjoint `{hts_memory_layout} :
  mk_initial_switcher hts_switcher_cmpt ∪
  mk_initial_assert hts_assert_cmpt ∪
  mk_initial_cmpt hts_main_cmpt ∪
  mk_initial_cmpt hts_allocator_cmpt ##ₘ
  mk_initial_cmpt hts_adv_cmpt.
Proof.
  do 3 rewrite map_disjoint_union_l.
  repeat split.
  - symmetry. apply disjoint_switcher_cmpts_mkinitial.
    unfold switcher_cmpt_disjoint.
    eapply (addr_disjoint_list_lookup _ 3 1); [exact hts_regions_disjoint|reflexivity..|lia].
  - symmetry. apply disjoint_assert_cmpts_mkinitial.
    unfold assert_cmpt_disjoint.
    eapply (addr_disjoint_list_lookup _ 4 1); [exact hts_regions_disjoint|reflexivity..|lia].
  - apply disjoint_cmpts_mkinitial.
    eapply (addr_disjoint_list_lookup _ 0 1); [exact hts_regions_disjoint|reflexivity..|lia].
  - apply disjoint_cmpts_mkinitial.
    eapply (addr_disjoint_list_lookup _ 2 1); [exact hts_regions_disjoint|reflexivity..|lia].
Qed.

Lemma hts_initial_allocator_disjoint `{hts_memory_layout} :
  mk_initial_switcher hts_switcher_cmpt ∪
  mk_initial_assert hts_assert_cmpt ∪
  mk_initial_cmpt hts_main_cmpt ##ₘ
  mk_initial_cmpt hts_allocator_cmpt.
Proof.
  do 2 rewrite map_disjoint_union_l.
  repeat split.
  - symmetry. apply disjoint_switcher_cmpts_mkinitial.
    unfold switcher_cmpt_disjoint.
    eapply (addr_disjoint_list_lookup _ 3 2); [exact hts_regions_disjoint|reflexivity..|lia].
  - symmetry. apply disjoint_assert_cmpts_mkinitial.
    unfold assert_cmpt_disjoint.
    eapply (addr_disjoint_list_lookup _ 4 2); [exact hts_regions_disjoint|reflexivity..|lia].
  - apply disjoint_cmpts_mkinitial.
    eapply (addr_disjoint_list_lookup _ 0 2); [exact hts_regions_disjoint|reflexivity..|lia].
Qed.

Lemma hts_initial_main_disjoint `{hts_memory_layout} :
  mk_initial_switcher hts_switcher_cmpt ∪
  mk_initial_assert hts_assert_cmpt ##ₘ
  mk_initial_cmpt hts_main_cmpt.
Proof.
  rewrite map_disjoint_union_l. split.
  - symmetry. apply disjoint_switcher_cmpts_mkinitial.
    unfold switcher_cmpt_disjoint.
    eapply (addr_disjoint_list_lookup _ 3 0); [exact hts_regions_disjoint|reflexivity..|lia].
  - symmetry. apply disjoint_assert_cmpts_mkinitial.
    unfold assert_cmpt_disjoint.
    eapply (addr_disjoint_list_lookup _ 4 0); [exact hts_regions_disjoint|reflexivity..|lia].
Qed.

Lemma hts_initial_assert_switcher_disjoint `{hts_memory_layout} :
  mk_initial_switcher hts_switcher_cmpt ##ₘ
  mk_initial_assert hts_assert_cmpt.
Proof.
  symmetry. apply disjoint_assert_switcher_mkinitial.
  unfold assert_switcher_disjoint.
  eapply (addr_disjoint_list_lookup _ 4 3); [exact hts_regions_disjoint|reflexivity..|lia].
Qed.

(** ** Initialisation of the allocator compartment *)
Section hts_allocator_init.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {FA : FreeAuth Σ}
    `{MP : MachineParameters} {Layout : hts_memory_layout}.

  (** The imports, code and data of the allocator, together with the heap
      (its memory, unpainted shadow entries and claims), form the allocator
      service invariant. *)
  Lemma hts_allocator_service_init (E : coPset) :
    cmpt_imports hts_allocator_cmpt = allocator_imports →
    cmpt_code hts_allocator_cmpt = allocator_code →
    cmpt_data hts_allocator_cmpt = allocator_data →
    [[ cmpt_b_pcc hts_allocator_cmpt, cmpt_a_code hts_allocator_cmpt ]]
      ↦ₐ [[ lword_of_word <$> cmpt_imports hts_allocator_cmpt ]] -∗
    [[ cmpt_a_code hts_allocator_cmpt, cmpt_e_pcc hts_allocator_cmpt ]]
      ↦ₐ [[ lword_of_word <$> cmpt_code hts_allocator_cmpt ]] -∗
    [[ cmpt_b_cgp hts_allocator_cmpt, cmpt_e_cgp hts_allocator_cmpt ]]
      ↦ₐ [[ lword_of_word <$> cmpt_data hts_allocator_cmpt ]] -∗
    ([∗ map] a↦w ∈ initial_heap_memory, a ↦ₐ lword_of_word w) -∗
    ([∗ map] a↦s ∈ initial_heap_shadow, a ↦ₛ s) -∗
    ([∗ map] a↦c ∈ init_claims {[heap_b]}, addr_alloc a c)
    ={E}=∗
    allocator_service_ctx.
  Proof.
    intros Himports Hcode Hdata.
    iIntros "Himports Hcode Hdata Hheap Hshadow Hclaims".
    iEval (rewrite cmpt_code_codefrag) in "Hcode".
    rewrite Himports Hcode Hdata.
    iDestruct (initial_heap_resources with "Hheap Hshadow") as "Hheap".
    iApply (allocator_service_init_correct E (lword_of_word <$> initial_heap_memory)
             with "[$Himports $Hcode $Hdata] Hheap Hclaims").
    by rewrite dom_fmap_L /initial_heap_memory dom_gset_to_gmap.
  Qed.

  (** The export table of the allocator becomes invariant. *)
  Lemma hts_allocator_exports_init (E : coPset) :
    cmpt_exp_tbl_entries hts_allocator_cmpt = allocator_export_table_entries →
    cmpt_exp_tbl_pcc hts_allocator_cmpt ↦ₐ cmpt_pcc_cap hts_allocator_cmpt -∗
    cmpt_exp_tbl_cgp hts_allocator_cmpt ↦ₐ cmpt_cgp_cap hts_allocator_cmpt -∗
    [[ cmpt_exp_tbl_entries_start hts_allocator_cmpt, cmpt_exp_tbl_entries_end hts_allocator_cmpt ]]
      ↦ₐ [[ lword_of_word <$> cmpt_exp_tbl_entries hts_allocator_cmpt ]]
    ={E}=∗
    inv (export_table_PCCN allocator_exp_tblN)
      (allocator_exp_tbl_b ↦ₐ WCap true RX Global allocator_pcc_b allocator_pcc_e allocator_pcc_b) ∗
    inv (export_table_CGPN allocator_exp_tblN)
      ((allocator_exp_tbl_b ^+ 1)%a ↦ₐ WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b) ∗
    inv (export_table_entryN allocator_exp_tblN (allocator_exp_tbl_b ^+ allocator_malloc_exp_tbl_off)%a)
      ((allocator_exp_tbl_b ^+ allocator_malloc_exp_tbl_off)%a ↦ₐ
         WInt (encode_entry_point allocator_malloc_nargs allocator_malloc_pcc_off)) ∗
    inv (export_table_entryN allocator_exp_tblN (allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a)
      ((allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a ↦ₐ
         WInt (encode_entry_point allocator_free_nargs allocator_free_pcc_off)).
  Proof.
    intros Hexports.
    iIntros "Hpcc Hcgp Hentries".
    pose proof (cmpt_exp_tbl_entries_size hts_allocator_cmpt) as Hsize.
    rewrite Hexports in Hsize.
    rewrite Hexports /region_pointsto
      (finz_seq_between_cons (cmpt_exp_tbl_entries_start hts_allocator_cmpt));
      last solve_addr+Hsize.
    rewrite (finz_seq_between_cons (cmpt_exp_tbl_entries_start hts_allocator_cmpt ^+ 1)%a);
      last solve_addr+Hsize.
    iDestruct "Hentries" as "(Hmalloc & Hfree & _)".
    rewrite cmpt_exp_tbl_cgp_eq cmpt_exp_tbl_entries_start_eq.
    replace (cmpt_exp_tbl_pcc hts_allocator_cmpt ^+ 2 ^+ 1)%a
      with (cmpt_exp_tbl_pcc hts_allocator_cmpt ^+ 3)%a by solve_addr+Hsize.
    iMod (inv_alloc (export_table_PCCN allocator_exp_tblN) E _ with "Hpcc") as "$".
    iMod (inv_alloc (export_table_CGPN allocator_exp_tblN) E _ with "Hcgp") as "$".
    iMod (inv_alloc (export_table_entryN allocator_exp_tblN _) E _ with "Hmalloc") as "$".
    iMod (inv_alloc (export_table_entryN allocator_exp_tblN _) E _ with "Hfree") as "$".
    done.
  Qed.

End hts_allocator_init.

Section Adequacy.
  Context (Σ : gFunctors).
  Context {cname : CmptNameG} {Adv : CmptName}.
  Context {inv_preg : invGpreS Σ}.
  Context {cerise_preg : ceriseGpreS Σ}.
  Context {entry_preg : entryGpreS Σ}.
  Context {seal_store_preg : sealStorePreG Σ}.
  Context {na_invg : na_invariants.na_invG Σ}.
  Context {sts_preg : STS_preG LAddr region_type OType LWord Σ}.
  Context {cstack_preg : CSTACK_preG Σ}.
  Context {relpreg : relGpreS Σ}.
  Context `{MP : MachineParameters} {Layout : hts_memory_layout}.

  Lemma hts_adequacy'
      (reg reg' : Reg) (sreg sreg' : SReg) (mem mem' : Mem)
      (sh sh' : ShadowTbl) (es : list griotte_lang.expr) :
    CNames = list_to_set [Adv] ->
    hts_is_initial_registers reg ->
    hts_is_initial_sregisters sreg ->
    hts_is_initial_memory mem ->
    sh = initial_heap_shadow ->
    initial_heap_memory ##ₘ hts_initial_program_memory ->
    rtc erased_step ([Seq (Instr Executable)], (reg, sreg, mem, sh))
      (es, (reg', sreg', mem', sh')) ->
    mem' !! flag_assert hts_assert_cmpt = Some (WInt 0).
  Proof.
    intros HCNames Hreg Hsreg Hmem Hshadow Hheap_disjoint Hstep.
    destruct Hmem as (Hmem & Hmain_imports & Hmain_code & Hmain_data
      & Hmain_static & Hmain_exports & Halloc_imports & Halloc_code
      & Halloc_data & Halloc_static & Halloc_exports & Hadv_imports
      & Hadv_code & Hadv_data & Hadv_static & Hadv_exports & Hstack).
    pose proof hts_regions_disjoint as Hdisj.
    assert (hts_adv_cmpt ## hts_allocator_cmpt) as Hadv_alloc.
    { eapply (addr_disjoint_list_lookup _ 1 2); [exact Hdisj|reflexivity..|lia]. }
    set (adv_f := cmpt_export hts_adv_cmpt (cmpt_exp_tbl_entries_start hts_adv_cmpt)).
    set (malloc_f := allocator_malloc Global).
    set (free_f := allocator_free Global).

    (* Iris adequacy: the program-logic resources of the initial state *)
    eapply (cerise_flag_adequacy Σ ot_switcher
              [(adv_f, 1); (malloc_f, allocator_malloc_nargs); (free_f, allocator_free_nargs)]
              (htsN .@ "flag") (flag_assert hts_assert_cmpt) {[heap_b]});
      [| by repeat constructor | | | | exact Hstep].
    { assert (adv_f ≠ malloc_f) by apply cmpt_export_disjoint, Hadv_alloc.
      assert (adv_f ≠ free_f) by apply cmpt_export_disjoint, Hadv_alloc.
      assert (malloc_f ≠ free_f).
      { pose proof (cmpt_exp_tbl_entries_size hts_allocator_cmpt) as Hsize.
        pose proof (cmpt_exp_tbl_pcc_size hts_allocator_cmpt).
        pose proof (cmpt_exp_tbl_cgp_size hts_allocator_cmpt).
        rewrite Halloc_exports in Hsize.
        rewrite /malloc_f /free_f /allocator_malloc /allocator_free
          /allocator_malloc_exp_tbl_off /allocator_free_exp_tbl_off.
        cbn in *. intros Heq; simplify_eq; solve_addr. }
      cbn; repeat (apply NoDup_cons; split); try apply NoDup_nil; set_solver. }
    { (* The allocator holds the root of the heap. *)
      subst sh mem.
      apply (ghost_init_cond_initial_layout_roots {[heap_b]} hts_switcher_cmpt hts_assert_cmpt
             hts_main_cmpt [hts_main_cmpt; hts_allocator_cmpt; hts_adv_cmpt]);
        [| done | exact Hheap_disjoint | exact Hreg | exact Hsreg | exact Hstack |].
      { intros a ->%elem_of_singleton. apply withinBounds_true_iff.
        pose proof heap_valid. solve_addr. }
      repeat constructor.
      - apply mem_rooted_initial_cmpt.
        + rewrite Hmain_imports /hts_main_imports.
          repeat constructor; try apply word_rooted_int.
          all: apply word_rooted_not_heap_cap.
          all: first [ apply switcher_call_sentry_not_heap
                     | apply sealed_cap_nonheap, cmpt_exp_tbl_base_not_heap
                     | rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=;
                       by rewrite (assert_code_nonheap hts_assert_cmpt) ].
        + rewrite Hmain_code hts_main_code_assembled. apply word_rooted_code.
        + rewrite Hmain_data. repeat constructor. apply word_rooted_int.
        + by rewrite Hmain_static.
        + by rewrite Hmain_exports.
      - apply mem_rooted_initial_cmpt.
        + rewrite Halloc_imports /allocator_imports.
          repeat constructor.
          * apply word_rooted_cap_disjoint. rewrite /disjoint_from_heap.
            symmetry. apply heap_shadow_disjoint.
          * by apply word_rooted_nonheap.
          * apply word_rooted_cap_nonheap, revoker_not_heap_address.
        + rewrite Halloc_code /allocator_code. apply Forall_app.
          split; apply word_rooted_code.
        + (* The heap root, based at [heap_b]. *)
          rewrite Halloc_data /allocator_data. repeat constructor.
          intros b _ Hb. rewrite /heap_authority_base decide_True in Hb;
            last (pose proof heap_valid; solve_addr).
          rewrite /heap_cap_base /= in Hb.
          destruct (is_heap_address heap_b); simplify_eq; set_solver.
        + by rewrite Halloc_static.
        + rewrite Halloc_exports /allocator_export_table_entries.
          repeat constructor; apply word_rooted_int.
      - apply mem_rooted_initial_cmpt.
        + rewrite Hadv_imports.
          repeat constructor; apply word_rooted_not_heap_cap.
          all: first [ apply switcher_call_sentry_not_heap
                     | apply sealed_cap_nonheap, (cmpt_exp_tbl_base_not_heap hts_allocator_cmpt) ].
        + by apply word_rooted_ints.
        + eapply Forall_impl; first exact Hadv_data.
          intros w. apply word_rooted_initial_data.
        + by rewrite Hadv_static.
        + rewrite Hadv_exports. repeat constructor. apply word_rooted_int. }
    { destruct Hreg as (_&_&_&Hr). apply Hr. set_solver. }
    subst sh.
    iIntros (ceriseg) "Hreg Hsreg Hmem Hshadow Hclaims Hna
      ([#Hentry_adv #Hentry_adv'] & [#Hentry_malloc #Hentry_malloc']
       & [#Hentry_free #Hentry_free'] & _)".
    pose FA := @free_auth_core Σ _.
    iMod (initialise_world [Adv] {[ ot_switcher ]})
      as (seal_storeg relg stsg cstackg) "(Hseal_store & Hcstk_full & Hcstk_frag & [Hworld_adv _])";
      [done | apply NoDup_singleton |].

    (* Get initial sregister mtdc *)
    iDestruct (big_sepM_lookup with "Hsreg") as "Hmtdc"; first exact Hsreg.

    (* Separate the initial heap from the compartments *)
    rewrite Hmem /hts_initial_memory.
    iDestruct (big_sepM_union with "Hmem") as "[Hheap Hmem]"; first exact Hheap_disjoint.

    (* Separate all compartments *)
    rewrite /hts_initial_program_memory.
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hcmpt_adv]";
      first exact hts_initial_adv_disjoint.
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hcmpt_allocator]";
      first exact hts_initial_allocator_disjoint.
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hcmpt_main]";
      first exact hts_initial_main_disjoint.
    iDestruct (big_sepM_union with "Hmem") as "[Hcmpt_switcher Hcmpt_assert]";
      first exact hts_initial_assert_switcher_disjoint.

    (* Assert *)
    iMod (initialise_assert_compartment (Σ := Σ) _ hts_assertN (htsN .@ "flag")
           with "Hcmpt_assert")
      as "[#Hassert_flag #Hassert]".

    (* Switcher *)
    rewrite big_sepS_singleton.
    iMod (initialise_switcher_compartment (Σ := Σ) _ hts_switcherN
           with "Hcmpt_switcher Hseal_store Hcstk_full Hmtdc")
      as "(#Hsealed_pred_ot_switcher & #Hswitcher & Hstack)".

    (* Allocator: its service invariant owns the heap *)
    iMod (initialise_compartment (Σ := Σ) with "Hcmpt_allocator")
      as "(Halloc_imports & Halloc_code & Halloc_data & _
           & Halloc_etbl_pcc & Halloc_etbl_cgp & Halloc_etbl_entries)".
    iMod (hts_allocator_service_init with
           "Halloc_imports Halloc_code Halloc_data Hheap Hshadow Hclaims")
      as "#Hservice"; [done..|].
    iMod (hts_allocator_exports_init with
           "Halloc_etbl_pcc Halloc_etbl_cgp Halloc_etbl_entries")
      as "#(Hexport_pcc & Hexport_cgp & Hexport_malloc & Hexport_free)"; first done.

    (* CMPT Adv *)
    iMod (initialise_adversary_compartment (Σ := Σ) _ Adv with "Hcmpt_adv")
      as "(Hadv_imports & Hadv_code & Hadv_data & _
           & #Hadv_etbl_pcc & #Hadv_etbl_cgp & #Hadv_etbl_entries)".

    (* CMPT MAIN *)
    iMod (initialise_compartment (Σ := Σ) with "Hcmpt_main")
      as "(Hmain_imports & Hmain_code & Hmain_data & _ & _ & _ & _)".
    iEval (rewrite cmpt_code_codefrag) in "Hmain_code".
    rewrite Hmain_imports Hmain_code Hmain_data.

    (* Seal the exported entries of the allocator in the world of Adv *)
    iMod (seal_service_exports _ Adv [malloc_f; free_f]
           with "Hsealed_pred_ot_switcher [] Hworld_adv")
      as "(Hworld_adv & #Hseal_alloc)"; [by repeat constructor | done | |].
    { iModIntro. iSplit; last iSplit; last done.
      - iApply (malloc_entry_point_spec Global _ Adv hts_switcherN); iFrame "#".
      - iApply (free_entry_point_spec Global _ Adv hts_switcherN); iFrame "#". }
    set (W1 := <o[ ot_switcher := exports_words [malloc_f; free_f] ]o> (∅, (∅, ∅), ∅, ∅)).

    (* Initialise the world of Adv *)
    assert (switcher_cmpt_disjoint hts_adv_cmpt hts_switcher_cmpt) as Hsw_adv.
    { eapply (addr_disjoint_list_lookup _ 3 1); [exact Hdisj|reflexivity..|lia]. }
    iMod (initialise_adversary_world W1 hts_switcher_cmpt _ Adv
           with "Hsealed_pred_ot_switcher Hadv_imports Hadv_code Hadv_data Hstack [] [] Hworld_adv")
      as "(Hworld_adv & #Hinterp_pcc_adv & #Hinterp_cgp_adv & #Hinterp_stack & #Hadv_exports)";
      [auto..| | |].
    { (* The exported entry Adv.f satisfies the sealing predicate of the switcher *)
      iApply (adversary_exports_prop _ _ _ _ [(1, hts_adv_entry_offset)]
               with "Hswitcher Hadv_etbl_pcc Hadv_etbl_cgp Hadv_etbl_entries");
        [by rewrite Hadv_exports | by repeat constructor |
         by apply Forall_singleton, hts_adv_entry_valid |].
      rewrite /= finz_add_0_default; iFrame "Hentry_adv Hentry_adv'". }
    { (* The imports of Adv: the switcher, malloc and free *)
      rewrite Hadv_imports.
      iIntros "_".
      iSplit; first by iApply switcher_call_import_safe.
      iSplit.
      { iApply (sealed_import_safe with "Hseal_alloc"); [done | |].
        - apply exports_words_elem_of; set_solver.
        - intros ? ? ? ? ? Heq; injection Heq; intros; subst.
          apply cmpt_exp_tbl_disjoint_from_heap. }
      iSplit; last done.
      iApply (sealed_import_safe with "Hseal_alloc"); [done | |].
      - apply exports_words_elem_of; set_solver.
      - intros ? ? ? ? ? Heq; injection Heq; intros; subst.
        apply cmpt_exp_tbl_disjoint_from_heap. }
    iAssert (interp (adv_world W1 hts_switcher_cmpt hts_adv_cmpt) Adv
               (WSealed ot_switcher adv_f)) as "#Hinterp_adv".
    { iApply (adversary_export_interp _ _ _ 0 with "Hadv_exports").
      - solve_addr.
      - rewrite Hadv_exports /=; lia. }

    (* Extract registers *)
    iDestruct (initial_registers_split with "Hreg")
      as (rmap) "(HPC & Hcgp & Hcsp & Hrmap & %Hrmap_dom & %Hrmap_zero)"; first exact Hreg.
    pose proof (main_spec_size_obligations _ _ _ _ Hmain_imports Hmain_code Hmain_data)
      as (Hmain_bounds & Hmain_data_size & Hmain_imports_size).

    iPoseProof (hts_main_spec _ _ _ _ _ _ _ _ adv_f (adv_world W1 hts_switcher_cmpt hts_adv_cmpt)
                  [] [] hts_assertN hts_switcherN []
                 with "[$Hassert $Hservice $Hswitcher
                        $Hexport_pcc $Hexport_cgp $Hexport_malloc $Hexport_free
                        $Hna $HPC $Hcgp $Hcsp $Hrmap
                        $Hmain_imports $Hmain_code $Hmain_data
                        $Hworld_adv $Hcstk_frag
                        $Hinterp_adv $Hentry_adv $Hinterp_stack]")
      as "Hspec".
    { exact (cmpt_pcc_disjoint_from_shadow hts_main_cmpt). }
    { exact (cmpt_pcc_base_not_heap hts_main_cmpt). }
    { apply sealed_cap_nonheap, cmpt_exp_tbl_base_not_heap. }
    { exact (cmpt_cgp_disjoint_from_shadow hts_main_cmpt). }
    { exact (cmpt_cgp_not_heap_range hts_main_cmpt). }
    { solve_ndisj. }
    { solve_ndisj. }
    { solve_ndisj. }
    { exact Hrmap_dom. }
    { intros r Hr. rewrite (Hrmap_zero r Hr). by eexists. }
    { exact Hmain_bounds. }
    { exact Hmain_data_size. }
    { exact Hmain_imports_size. }
    { apply (main_cgp_not_in_adv_world _ _ _ hts_main_cmpt).
      - eapply (addr_disjoint_list_lookup _ 0 1); [exact Hdisj|reflexivity..|lia].
      - eapply (addr_disjoint_list_lookup _ 3 0); [exact Hdisj|reflexivity..|lia].
      - rewrite /= dom_empty_L; set_solver+.
      - rewrite elem_of_finz_seq_between; solve_addr+Hmain_data_size. }
    { by rewrite adv_world_with_heap. }
    { done. }

    iModIntro; iFrame "Hassert_flag".
    iApply (wp_mono with "Hspec"); auto.
  Qed.
End Adequacy.

Inductive CmptNames_hts := | B .
Local Instance CmptNames_hts_eq_dec : EqDecision CmptNames_hts.
Proof. intros C C'; destruct C,C'; solve_decision. Qed.
Local Instance CmptNames_hts_finite : finite.Finite CmptNames_hts.
Proof.
  refine {| finite.enum := [B] |}.
  + apply NoDup_singleton.
  + intros []; left.
Defined.

Local Program Instance CmptNames_hts_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_hts; |}.

(** END-TO-END THEOREM *)
Theorem hts_adequacy `{hts_memory_layout}
    (reg reg' : Reg) (sreg sreg' : SReg) (mem mem' : Mem)
    (sh sh' : ShadowTbl) (es : list griotte_lang.expr) :
  hts_is_initial_registers reg ->
  hts_is_initial_sregisters sreg ->
  hts_is_initial_memory mem ->
  sh = initial_heap_shadow ->
  initial_heap_memory ##ₘ hts_initial_program_memory ->
  rtc erased_step ([Seq (Instr Executable)], (reg, sreg, mem, sh))
    (es, (reg', sreg', mem', sh')) ->
  mem' !! flag_assert hts_assert_cmpt = Some (WInt 0).
Proof.
  intros ? ? ? ? ? ?.
  set (cnames := CmptNames_hts_CmptNameG).
  set (Σ := #[invΣ; ceriseGpreΣ
              ; entryPreΣ; CSTACK_preΣ
              ; na_invΣ; sealStorePreΣ
              ; STS_preΣ LAddr region_type OType LWord; relPreΣ
              ; savedPredΣ (WorldT * CmptName * LWord)
      ]).
  eapply (@hts_adequacy' Σ cnames B); eauto; try typeclasses eauto.
Qed.
