From iris.program_logic Require Import adequacy.
From iris.proofmode Require Import proofmode.
From griotte Require Import griotte_lang logrel interp_weakening monotone.
From griotte Require Import compartment_layout adequacy_helpers switcher assert
  assert_spec heap_temporal_safety heap_temporal_safety_preamble
  heap_temporal_safety_spec.
From griotte.allocator Require Import allocator_malloc_safe allocator_free_safe.
From griotte Require Import mkregion_helpers disjoint_regions_tactics
  region_invariants_revocation region_invariants_allocation
  world_interp_allocation_compartments switcher_preamble
  interp_switcher_call interp_switcher_return switcher_adequacy.
From griotte.allocator Require Import allocator allocator_preamble allocator_resource_spec.

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

Section Adequacy.
  Context (Σ : gFunctors).
  Context {cname : CmptNameG} {Adv : CmptName}.
  Context {inv_preg : invGpreS Σ}.
  Context {shadow_preg : gen_heapGpreS Addr AllocStatus Σ}.
  Context {allocator_preg : allocator_preG Σ}.
  Context {mem_preg : gen_heapGpreS Addr Word Σ}.
  Context {reg_preg : gen_heapGpreS RegName Word Σ}.
  Context {sreg_preg : gen_heapGpreS SRegName Word Σ}.
  Context {entry_preg : entryGpreS Σ}.
  Context {seal_store_preg : sealStorePreG Σ}.
  Context {na_invg : na_invariants.na_invG Σ}.
  Context {sts_preg : STS_preG Addr region_type OType Word Σ}.
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
    pose proof (@wp_invariance Σ griotte_lang _ NotStuck) as WPI.
    cbn in WPI.
    pose (fun (c : ExecConf) =>
      griotte_opsem.mem c !! flag_assert hts_assert_cmpt = Some (WInt 0))
      as state_is_good.
    specialize (WPI (Seq (Instr Executable)) (reg, sreg, mem, sh)
      es (reg', sreg', mem', sh')
      (state_is_good (reg', sreg', mem', sh'))).
    eapply WPI. 2: exact Hstep.
    intros Hinv κs. clear WPI.

    destruct Hmem as (Hmem & Hmain_imports & Hmain_code & Hmain_data
      & Hmain_static & Hmain_exports & Halloc_imports & Halloc_code
      & Halloc_data & Halloc_static & Halloc_exports & Hadv_imports
      & Hadv_code & Hadv_data & Hadv_static & Hadv_exports & Hstack).
    set (adv_f := SCap true RO Global
      (cmpt_exp_tbl_pcc hts_adv_cmpt)
      (cmpt_exp_tbl_entries_end hts_adv_cmpt)
      (cmpt_exp_tbl_entries_start hts_adv_cmpt)).
    set (malloc_f := allocator_malloc Global).
    set (free_f := allocator_free Global).
    iMod (gen_heap_init (reg : Reg)) as (reg_heapg) "(Hreg_ctx & Hreg & _)".
    iMod (gen_heap_init (sreg : SReg)) as (sreg_heapg) "(Hsreg_ctx & Hsreg & _)".
    iMod (gen_heap_init sh) as (shadow_heapg) "(Hshadow_ctx & Hshadow & _)".
    iMod (gen_heap_init (mem : Mem)) as (mem_heapg) "(Hmem_ctx & Hmem & _)".
    set (entry_keys :=
      {[ seal_capability (WSealable adv_f) ot_switcher;
         borrow (seal_capability (WSealable adv_f) ot_switcher);
         seal_capability (WSealable malloc_f) ot_switcher;
         borrow (seal_capability (WSealable malloc_f) ot_switcher);
         seal_capability (WSealable free_f) ot_switcher;
         borrow (seal_capability (WSealable free_f) ot_switcher) ]}
      : gset Word).
    iMod (entry_init (gset_to_gmap 1 entry_keys)) as (entry_g) "Hentries".
    iMod (@na_alloc Σ na_invg) as (cerise_nais) "Hna".
    pose cerise_na_invs := Build_cerise_na_invs _ na_invg cerise_nais.
    pose ceriseg := CeriseG Σ Hinv cerise_na_invs mem_heapg
      shadow_heapg reg_heapg sreg_heapg entry_g.

    iEval (rewrite Hmem /hts_initial_memory) in "Hmem".
    iDestruct (big_sepM_union with "Hmem") as "[Hheap Hprogram]";
      first exact Hheap_disjoint.
    iEval (rewrite Hshadow) in "Hshadow".
    rewrite /hts_initial_program_memory.
    iDestruct (big_sepM_union with "Hprogram") as "[Hprogram Hcmpt_adv]";
      first exact hts_initial_adv_disjoint.
    iDestruct (big_sepM_union with "Hprogram") as "[Hprogram Hcmpt_allocator]";
      first exact hts_initial_allocator_disjoint.
    iDestruct (big_sepM_union with "Hprogram") as "[Hprogram Hcmpt_main]";
      first exact hts_initial_main_disjoint.
    iDestruct (big_sepM_union with "Hprogram") as "[Hcmpt_switcher Hcmpt_assert]";
      first exact hts_initial_assert_switcher_disjoint.

    (* Split the allocator service body before the world instances exist. *)
    iEval (rewrite /mk_initial_cmpt) in "Hcmpt_allocator".
    iDestruct (big_sepM_union with "Hcmpt_allocator")
      as "[Hallocator Halloc_etbl]"; first apply cmpt_exp_tbl_disjoint.
    iDestruct (big_sepM_union with "Hallocator")
      as "[Hallocator Halloc_static]"; first apply cmpt_static_sealed_disjoint.
    iDestruct (big_sepM_union with "Hallocator")
      as "[Halloc_pcc Halloc_data]"; first apply cmpt_cgp_disjoint.
    iEval (rewrite /cmpt_pcc_mregion) in "Halloc_pcc".
    iDestruct (big_sepM_union with "Halloc_pcc")
      as "[Halloc_imports_mem Halloc_code_mem]"; first apply cmpt_code_disjoint.
    iDestruct (mkregion_prepare with "[Halloc_imports_mem]")
      as ">Halloc_imports_mem"; auto.
    { apply cmpt_import_size. }
    iDestruct (mkregion_prepare with "[Halloc_code_mem]")
      as ">Halloc_code_mem"; auto.
    { apply cmpt_code_size. }
    iEval (rewrite /cmpt_cgp_mregion) in "Halloc_data".
    iDestruct (mkregion_prepare with "[Halloc_data]") as ">Halloc_data"; auto.
    { apply cmpt_data_size. }
    iEval (rewrite Halloc_imports) in "Halloc_imports_mem".
    iEval (rewrite Halloc_code) in "Halloc_code_mem".
    iEval (rewrite Halloc_data) in "Halloc_data".
    iAssert (allocator_service_initial_resources)
      with "[Halloc_imports_mem Halloc_code_mem Halloc_data]"
      as "Hservice_initial".
    { rewrite /allocator_service_initial_resources /allocator_service_static /codefrag.
      replace (allocator_code_b ^+ length allocator_code)%a with allocator_pcc_e.
      2: { pose proof allocator_size_code; solve_addr. }
      iFrame "Halloc_imports_mem Halloc_code_mem Halloc_data". }
    iEval (rewrite /initial_heap_shadow big_sepM_fmap) in "Hshadow".
    iCombine "Hheap Hshadow" as "Hheap".
    iDestruct (big_sepM_sep with "Hheap") as "Hheap".
    iMod (allocator_service_init_correct ⊤ initial_heap_memory
      with "Hservice_initial Hheap")
      as (allocatorg) "[#Halloc #Hservice]".
    { split; first exact hts_allocator_wf.
      by rewrite /initial_heap_memory dom_gset_to_gmap. }

    iMod (gen_cstack_init []) as (cstackg) "[Hcstk_full Hcstk_frag]".
    iMod (world_interp_init ({[ ot_switcher ]} : gset OType))
      as (relg stsg seal_storeg) "(Hworld & Hseal_store)".
    iDestruct (big_sepS_elements with "Hworld") as "Hworld_adv".
    rewrite HCNames.
    pose proof (NoDup_singleton Adv) as HCNoDup.
    setoid_rewrite elements_list_to_set; auto.
    rewrite !big_sepL_singleton.
    set (W0 := (∅, (∅, ∅), ∅, ∅)).

    iDestruct (big_sepM_lookup with "Hsreg") as "Hmtdc"; first exact Hsreg.
    iMod (initialise_assert_compartment (Σ := Σ) hts_assert_cmpt
      hts_assertN (htsN .@ "flag") with "Hcmpt_assert")
      as "[#Hassert_flag #Hassert]".
    rewrite big_sepS_singleton.
    iMod (initialise_switcher_compartment (Σ := Σ) hts_switcher_cmpt
      hts_switcherN with "Hcmpt_switcher Hseal_store Hcstk_full Hmtdc")
      as "(#Hsealed_pred_ot_switcher & #Hswitcher & Hstack_mem)".

    (* Keep the allocator export cells outside the service invariant. *)
    iEval (rewrite /cmpt_exp_tbl_mregion) in "Halloc_etbl".
    iDestruct (big_sepM_union with "Halloc_etbl")
      as "[Halloc_etbl Halloc_etbl_entries]";
      first apply cmpt_exp_tbl_entries_disjoint.
    iDestruct (big_sepM_union with "Halloc_etbl")
      as "[Halloc_etbl_pcc Halloc_etbl_cgp]";
      first apply cmpt_exp_tbl_pcc_cgp_disjoint.
    iDestruct (mkregion_prepare with "[Halloc_etbl_entries]")
      as ">Halloc_etbl_entries"; auto.
    { apply cmpt_exp_tbl_entries_size. }
    iDestruct (mkregion_prepare with "[Halloc_etbl_pcc]")
      as ">Halloc_etbl_pcc"; auto.
    { apply cmpt_exp_tbl_pcc_size. }
    iDestruct (mkregion_prepare with "[Halloc_etbl_cgp]")
      as ">Halloc_etbl_cgp"; auto.
    { apply cmpt_exp_tbl_cgp_size. }
    rewrite (finz_seq_between_singleton (cmpt_exp_tbl_pcc hts_allocator_cmpt));
      last apply cmpt_exp_tbl_pcc_size.
    rewrite (finz_seq_between_singleton (cmpt_exp_tbl_cgp hts_allocator_cmpt));
      last apply cmpt_exp_tbl_cgp_size.
    rewrite !big_sepL2_singleton.
    iEval (rewrite Halloc_exports) in "Halloc_etbl_entries".
    rewrite (finz_seq_between_cons (cmpt_exp_tbl_entries_start hts_allocator_cmpt)).
    2: { pose proof (cmpt_exp_tbl_entries_size hts_allocator_cmpt) as Hsize.
         rewrite Halloc_exports in Hsize. solve_addr+Hsize. }
    rewrite (finz_seq_between_cons (cmpt_exp_tbl_entries_start hts_allocator_cmpt ^+ 1)%a).
    2: { pose proof (cmpt_exp_tbl_entries_size hts_allocator_cmpt) as Hsize.
         rewrite Halloc_exports in Hsize. solve_addr+Hsize. }
    rewrite big_sepL2_cons big_sepL2_cons.
    iDestruct "Halloc_etbl_entries"
      as "(Hmalloc_entry_cell & Hfree_entry_cell & _)".

    assert (Hcgp_addr : cmpt_exp_tbl_cgp hts_allocator_cmpt =
      (allocator_exp_tbl_b ^+ 1)%a).
    { cbn [allocator_exp_tbl_b hts_memory_allocator_layout
        hts_cmpt_allocator_layout] in *.
      pose proof (cmpt_exp_tbl_pcc_size hts_allocator_cmpt); solve_addr. }
    assert (Hmalloc_addr : cmpt_exp_tbl_entries_start hts_allocator_cmpt =
      (allocator_exp_tbl_b ^+ allocator_malloc_exp_tbl_off)%a).
    { cbn [allocator_exp_tbl_b hts_memory_allocator_layout
        hts_cmpt_allocator_layout] in *.
      pose proof (cmpt_exp_tbl_pcc_size hts_allocator_cmpt).
      pose proof (cmpt_exp_tbl_cgp_size hts_allocator_cmpt).
      unfold allocator_malloc_exp_tbl_off in *; solve_addr. }
    assert (Hfree_addr :
      (cmpt_exp_tbl_entries_start hts_allocator_cmpt ^+ 1)%a =
      (allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a).
    { cbn [allocator_exp_tbl_b hts_memory_allocator_layout
        hts_cmpt_allocator_layout] in *.
      unfold allocator_free_exp_tbl_off, allocator_malloc_exp_tbl_off.
      pose proof (cmpt_exp_tbl_pcc_size hts_allocator_cmpt).
      pose proof (cmpt_exp_tbl_cgp_size hts_allocator_cmpt).
      solve_addr. }
    iEval (rewrite Hcgp_addr) in "Halloc_etbl_cgp".
    iEval (rewrite Hmalloc_addr) in "Hmalloc_entry_cell".
    iEval (rewrite Hfree_addr) in "Hfree_entry_cell".
    iMod (inv_alloc (export_table_PCCN hts_allocator_exp_tblN) ⊤ _
      with "Halloc_etbl_pcc") as "#Hexport_pcc".
    iMod (inv_alloc (export_table_CGPN hts_allocator_exp_tblN) ⊤ _
      with "Halloc_etbl_cgp") as "#Hexport_cgp".
    iMod (inv_alloc
      (export_table_entryN hts_allocator_exp_tblN
        (allocator_exp_tbl_b ^+ allocator_malloc_exp_tbl_off)%a) ⊤ _
      with "Hmalloc_entry_cell") as "#Hexport_malloc".
    iMod (inv_alloc
      (export_table_entryN hts_allocator_exp_tblN
        (allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a) ⊤ _
      with "Hfree_entry_cell") as "#Hexport_free".

    iMod (initialise_adversary_compartment (Σ := Σ) hts_adv_cmpt Adv
      with "Hcmpt_adv") as
      "(Hadv_imports_mem & Hadv_code_mem & Hadv_data_mem & Hadv_static_mem
        & #Hadv_etbl_pcc & #Hadv_etbl_cgp & #Hadv_etbl_entries)".
    iMod (initialise_compartment (Σ := Σ) hts_main_cmpt
      with "Hcmpt_main") as
      "(Hmain_imports_mem & Hmain_code_mem & Hmain_data_mem
        & Hmain_static_mem & Hmain_etbl_pcc & Hmain_etbl_cgp
        & Hmain_etbl_entries)".
    iEval (rewrite Hadv_exports) in "Hadv_etbl_entries".
    rewrite (finz_seq_between_singleton
      (cmpt_exp_tbl_entries_start hts_adv_cmpt)).
    2: { pose proof (cmpt_exp_tbl_entries_size hts_adv_cmpt) as Hsize.
         rewrite Hadv_exports in Hsize. solve_addr+Hsize. }
    iDestruct "Hadv_etbl_entries" as "/= [Hadv_entry_cell _]".
    iAssert (codefrag (cmpt_a_code hts_main_cmpt)
      (cmpt_code hts_main_cmpt)) with "[Hmain_code_mem]"
      as "Hmain_codefrag".
    { rewrite /codefrag.
      replace (cmpt_a_code hts_main_cmpt ^+
        length (cmpt_code hts_main_cmpt))%a
        with (cmpt_e_pcc hts_main_cmpt).
      2: { pose proof (cmpt_code_size hts_main_cmpt) as Hsize;
           solve_addr+Hsize. }
      iExact "Hmain_code_mem". }
    iEval (rewrite Hmain_imports) in "Hmain_imports_mem".
    iEval (rewrite Hmain_code) in "Hmain_codefrag".
    iEval (rewrite Hmain_data) in "Hmain_data_mem".

    iDestruct (big_sepM_lookup _ _
      (seal_capability (WSealable adv_f) ot_switcher) with "Hentries")
      as "#Hentry_adv".
    { apply lookup_gset_to_gmap_Some. split; last reflexivity.
      subst entry_keys; set_solver. }
    iDestruct (big_sepM_lookup _ _
      (borrow (seal_capability (WSealable adv_f) ot_switcher))
      with "Hentries") as "#Hentry_adv_borrow".
    { apply lookup_gset_to_gmap_Some. split; last reflexivity.
      subst entry_keys; set_solver. }
    iDestruct (big_sepM_lookup _ _
      (seal_capability (WSealable malloc_f) ot_switcher) with "Hentries")
      as "#Hentry_malloc".
    { apply lookup_gset_to_gmap_Some. split; last reflexivity.
      subst entry_keys; set_solver. }
    iDestruct (big_sepM_lookup _ _
      (borrow (seal_capability (WSealable malloc_f) ot_switcher))
      with "Hentries") as "#Hentry_malloc_borrow".
    { apply lookup_gset_to_gmap_Some. split; last reflexivity.
      subst entry_keys; set_solver. }
    iDestruct (big_sepM_lookup _ _
      (seal_capability (WSealable free_f) ot_switcher) with "Hentries")
      as "#Hentry_free".
    { apply lookup_gset_to_gmap_Some. split; last reflexivity.
      subst entry_keys; set_solver. }
    iDestruct (big_sepM_lookup _ _
      (borrow (seal_capability (WSealable free_f) ot_switcher))
      with "Hentries") as "#Hentry_free_borrow".
    { apply lookup_gset_to_gmap_Some. split; last reflexivity.
      subst entry_keys; set_solver. }

    set (alloc_import_words :=
      ({[WSealable malloc_f; borrow (WSealable malloc_f)]} ∪
       {[WSealable free_f; borrow (WSealable free_f)]} : gset Word)).
    set (W1 := <o[ot_switcher := alloc_import_words]o> W0).
    iAssert (ot_switcher_prop W1 Adv (WSealable malloc_f))
      as "#Hmalloc_prop".
    { iApply (malloc_entry_point_spec Global W1 Adv hts_switcherN).
      iFrame "#". }
    iAssert (ot_switcher_prop W1 Adv (WSealable free_f))
      as "#Hfree_prop".
    { iApply (free_entry_point_spec Global W1 Adv hts_switcherN).
      iFrame "#". }
    assert (ot_switcher ∉ dom (seal_std W0)) as Hot_fresh
      by (subst W0; done).
    iMod (world_interp_salloc W0 Adv ot_switcher_propC ot_switcher
      alloc_import_words
      with "[$Hsealed_pred_ot_switcher] [] [] [$Hworld_adv]")
      as "(Hworld_adv & Hseal_alloc)"; first exact Hot_fresh.
    { iIntros (w); iApply mono_priv_ot_switcher. }
    { rewrite /alloc_import_words normalise_sealed_words_union
        !normalise_sealed_words_borrow.
      iApply big_sepS_insert_2; first iExact "Hmalloc_prop".
      rewrite big_sepS_singleton; iExact "Hfree_prop". }

    iAssert (interp W1 Adv (WSealed ot_switcher malloc_f))
      as "#Hinterp_malloc".
    { iEval (rewrite fixpoint_interp1_eq /= /interp_sb).
      iSplit; first (iApply (sts_seals_std_weaken with "Hseal_alloc");
        last set_solver+).
      iPureIntro; cbn.
      apply heap_cap_valid_disjoint, cmpt_exp_tbl_disjoint_from_heap. }
    iAssert (interp W1 Adv (WSealed ot_switcher free_f))
      as "#Hinterp_free".
    { iEval (rewrite fixpoint_interp1_eq /= /interp_sb).
      iSplit; first (iApply (sts_seals_std_weaken with "Hseal_alloc");
        last set_solver+).
      iPureIntro; cbn.
      apply heap_cap_valid_disjoint, cmpt_exp_tbl_disjoint_from_heap. }

    assert (exported_entries_sealable hts_adv_cmpt ≡ₚ
      [adv_f; borrow_sb adv_f]) as Hexported_entries_sealable.
    { rewrite /exported_entries_sealable /adv_f.
      pose proof (cmpt_exp_tbl_entries_size hts_adv_cmpt) as Hsize.
      rewrite Hadv_exports in Hsize.
      rewrite finz_seq_between_singleton; last solve_addr+Hsize.
      done. }
    assert (exported_entries_words hts_adv_cmpt =
      {[WSealable adv_f; borrow (WSealable adv_f)]})
      as Hexported_entries_words.
    { rewrite /exported_entries_words Hexported_entries_sealable.
      cbn; set_solver+. }
    assert (exported_entries_sealed hts_adv_cmpt =
      {[WSealed ot_switcher adv_f;
        WSealed ot_switcher (borrow_sb adv_f)]})
      as Hexported_entries_sealed.
    { rewrite /exported_entries_sealed Hexported_entries_sealable.
      cbn; set_solver+. }

    iMod (alloc_compartment_interp with
      "Hadv_imports_mem Hadv_code_mem Hadv_data_mem [] Hworld_adv")
      as "(Hworld_adv & #Hadv_code & #Hadv_data & _ & #Hadv_exports)";
      eauto.
    { apply Forall_true; intros; done. }
    { apply Forall_true; intros; done. }
    { apply Forall_true; intros; done. }
    { rewrite Hadv_imports.
      iIntros "(#Hadv_code & #Hadv_data & Hworld_adv)".
      match goal with
      | H : _ |- context [world_interp_open ?W Adv] => set (Wpre := W)
      end.
      set (Winter := std_update_compartment W1 hts_adv_cmpt).
      iAssert (ot_switcher_prop Winter Adv (WSealable adv_f))
        as "#Hadv_prop".
      { iApply (ot_switcher_interp _ _ _ _ _ 1 hts_adv_entry_offset
          hts_switcherN (nroot .@ Adv)).
        { pose proof (cmpt_exp_tbl_entries_size hts_adv_cmpt) as Hsize.
          rewrite Hadv_exports in Hsize; solve_addr+Hsize. }
        { lia. }
        { exact hts_adv_entry_valid. }
        all: try (iApply "Hadv_etbl_pcc").
        all: try (iApply "Hadv_etbl_cgp").
        all: try (iApply "Hadv_entry_cell").
        all: try (iApply "Hadv_code").
        all: try (iApply "Hadv_data").
        all: try (iApply "Hentry_adv").
        all: try (iApply "Hentry_adv_borrow").
        all: try (iApply "Hswitcher"). }
      assert (Winter =
        <o[ot_switcher := exported_entries_words hts_adv_cmpt]o> Wpre)
        as HWinter.
      { rewrite /Winter /Wpre /std_update_compartment
          Hexported_entries_words; done. }
      iMod (world_interp_open_sealing_update' Wpre Adv _
        ot_switcher_propC ot_switcher
        (exported_entries_words hts_adv_cmpt)
        with "[$Hsealed_pred_ot_switcher] [] [] [$Hworld_adv]")
        as "(Hworld_adv & #Hseal_adv)".
      { iIntros (w); iApply mono_priv_ot_switcher. }
      { rewrite -HWinter Hexported_entries_words.
        rewrite normalise_sealed_words_borrow big_sepS_singleton.
        iExact "Hadv_prop". }
      rewrite -HWinter.
      iFrame.
      iModIntro.
      rewrite Hexported_entries_sealed Hexported_entries_words.
      assert (related_sts_priv_world W1 Winter) as Hrelated_W1_Winter.
      { apply related_sts_pub_priv_world.
        subst Winter.
        eapply std_update_compartment_pub; eauto;
          apply Forall_true; intros; done. }
      iSplitR "Hseal_adv".
      - iApply big_sepL_cons; iSplitL.
        { assert (heap_authority_base
            (WSentry true XSRW_ Local b_switcher e_switcher
              a_switcher_call) = None) as Hcall_nonheap.
          { destruct (heap_authority_base _) as [b|] eqn:Hauth;
              last done.
            apply heap_authority_base_heap_cap_base in Hauth.
            pose proof switcher_call_sentry_not_heap as Hnonheap.
            unfold is_heap_cap in Hnonheap;
              rewrite Hauth in Hnonheap; discriminate. }
          iEval (cbn); iSplit.
          { iEval (rewrite /interp_in_mem_pre /=).
            iEval (rewrite (filter_heap_nonheap _ _ Hcall_nonheap) /=).
            iApply interp_switcher_call; done. }
          { iIntros "!>" (W2 W3 Hrel Hwf) "H".
            iEval (rewrite /interp_in_mem_pre /=).
            iEval (rewrite (filter_heap_nonheap _ _ Hcall_nonheap) /=).
            iApply interp_switcher_call; done. } }
        iApply big_sepL_cons; iSplitL.
        { iSplit.
          - iApply interp_to_in_mem.
            iApply (interp_monotone_sd_same_heap W1 Winter with "[]").
            { subst Winter. by rewrite std_update_compartment_heap. }
            { iPureIntro; exact Hrelated_W1_Winter. }
            iFrame "Hinterp_malloc".
          - iIntros (W2 W3) "!> %Hrelated %Hwf Hinterp".
            iEval (cbn) in "Hinterp".
            iApply (interp_in_mem_monotone_nl W2 W3 Adv RWL
              (WSealed ot_switcher malloc_f) with "Hinterp");
              [exact Hwf|exact Hrelated|by unfold malloc_f; cbn]. }
        iApply big_sepL_cons; iSplitL.
        { iSplit.
          - iApply interp_to_in_mem.
            iApply (interp_monotone_sd_same_heap W1 Winter with "[]").
            { subst Winter. by rewrite std_update_compartment_heap. }
            { iPureIntro; exact Hrelated_W1_Winter. }
            iFrame "Hinterp_free".
          - iIntros (W2 W3) "!> %Hrelated %Hwf Hinterp".
            iEval (cbn) in "Hinterp".
            iApply (interp_in_mem_monotone_nl W2 W3 Adv RWL
              (WSealed ot_switcher free_f) with "Hinterp");
              [exact Hwf|exact Hrelated|by unfold free_f; cbn]. }
        done.
      - iEval (rewrite union_comm_L).
        iApply big_sepS_insert_2.
        { iApply interp_to_in_mem.
          iEval (rewrite fixpoint_interp1_eq /= /interp_sb).
          iSplit; first (iApply (sts_seals_std_weaken with "Hseal_adv");
            set_solver+).
          iPureIntro; cbn; apply heap_cap_valid_disjoint,
            cmpt_exp_tbl_disjoint_from_heap. }
        rewrite big_sepS_singleton.
        iApply interp_to_in_mem.
        iEval (rewrite fixpoint_interp1_eq /= /interp_sb).
        iSplit; first (iApply (sts_seals_std_weaken with "Hseal_adv");
          set_solver+).
        iPureIntro; cbn; apply heap_cap_valid_disjoint,
          cmpt_exp_tbl_disjoint_from_heap. }

    match goal with
    | H : _ |- context [world_interp ?W Adv] => set (W2 := W)
    end.
    assert (switcher_cmpt_disjoint hts_adv_cmpt hts_switcher_cmpt)
      as Hadv_switcher.
    { unfold switcher_cmpt_disjoint.
      eapply (addr_disjoint_list_lookup _ 3 1);
        [exact hts_regions_disjoint|reflexivity..|lia]. }
    assert (Forall (fun a => a ∉ dom (std W2))
      (finz.seq_between (b_stack hts_switcher_cmpt)
        (e_stack hts_switcher_cmpt))) as Hstack_fresh.
    { apply Forall_forall; intros a Ha.
      rewrite not_elem_of_dom.
      subst W2;
        eapply switcher_cmpt_disjoint_std_update_compartment; eauto. }
    iMod (world_interp_extend_temp_sepL2 _ _
      (finz.seq_between (b_stack hts_switcher_cmpt)
        (e_stack hts_switcher_cmpt))
      (stack_content hts_switcher_cmpt) RWL interp_in_memC
      with "Hworld_adv [Hstack_mem]")
      as "(Hworld_adv & #Hrel_stack)".
    { apply Forall_forall; intros a Ha.
      apply heap_addr_live_nonheap.
      apply not_true_is_false; intros Hheap.
      apply withinBounds_true_iff in Hheap.
      pose proof (stack_disjoint_from_heap hts_switcher_cmpt) as Hdisj.
      rewrite /disjoint_from_heap elem_of_disjoint in Hdisj.
      eapply (Hdisj a);
        [exact Ha|apply elem_of_finz_seq_between; exact Hheap]. }
    { done. }
    { eapply Forall_impl; eauto.
      intros a Ha. by rewrite -not_elem_of_dom. }
    { iApply (big_sepL2_mono
        ((fun (_ : nat) (k : finz.finz MemNum) (v : Word) =>
          pointsto k (DfracOwn (pos_to_Qp 1)) v))
        with "Hstack_mem").
      intros k v1 v2 Hv1 Hv2. cbn. iIntros; iFrame.
      pose proof (Forall_lookup_1 _ _ _ _ Hstack Hv2) as Hncap.
      destruct v2; [| by inversion Hncap..].
      iSplit; first done.
      iSplit.
      { iEval (rewrite /interp_in_mem_pre /=). iApply interp_int. }
      rewrite mono_temporary_eq; cbn;
        iApply future_pub_mono_interp_in_mem_z. }

    match goal with
    | H : _ |- context [world_interp ?W Adv] => set (Winit := W)
    end.
    assert (related_sts_priv_world W2 Winit) as Hrelated_W2_Winit.
    { apply related_sts_pub_priv_world.
      apply related_sts_pub_update_multiple; auto. }
    iAssert (interp Winit Adv
      (WCap true RWL Local (b_stack hts_switcher_cmpt)
        (e_stack hts_switcher_cmpt) (b_stack hts_switcher_cmpt)))
      as "#Hinterp_stack".
    { iEval (rewrite fixpoint_interp1_eq /=).
      iSplit.
      { iApply big_sepL_intro; iModIntro.
        iIntros (k a Ha).
        iExists RWL, (interp_in_mem RWL).
        iEval (cbn).
        iSplit; first done.
        iSplit; first (iPureIntro;
          by apply persistent_cond_interp_in_mem).
        rewrite (big_sepL_lookup _
          (finz.seq_between (b_stack hts_switcher_cmpt)
            (e_stack hts_switcher_cmpt)) k a); eauto.
        iFrame "Hrel_stack".
        iSplit; first (iNext; by iApply zcond_interp_in_mem).
        iSplit; first (iNext; by iApply rcond_interp_in_mem).
        iSplit; first (iNext; by iApply wcond_interp_in_mem).
        assert (std Winit !! a = Some Temporary).
        { subst Winit.
          apply list_elem_of_lookup_2 in Ha.
          rewrite std_sta_update_multiple_lookup_in_i; auto. }
        iSplit; last done.
        iApply (monoReq_interp_in_mem _ _ _ _ Temporary); done. }
      iPureIntro; split.
      { apply stack_disjoint_from_shadow. }
      apply heap_cap_valid_disjoint, stack_disjoint_from_heap. }

    assert (is_heap_cap (WSealed ot_switcher adv_f) = false)
      as Hadv_nonheap.
    { unfold adv_f. apply sealed_cap_nonheap.
      exact (cmpt_exp_tbl_base_not_heap hts_adv_cmpt). }
    assert (heap_authority_base (WSealed ot_switcher adv_f) = None)
      as Hadv_base.
    { destruct (heap_authority_base _) as [b|] eqn:Hauth; last done.
      apply heap_authority_base_heap_cap_base in Hauth.
      unfold is_heap_cap in Hadv_nonheap;
        rewrite Hauth in Hadv_nonheap; discriminate. }
    iAssert (interp Winit Adv (WSealed ot_switcher adv_f))
      as "Hinterp_adv".
    { rewrite Hexported_entries_sealed.
      iDestruct (big_sepS_elem_of_acc _ _ (WSealed ot_switcher adv_f)
        with "Hadv_exports") as "[Hinterp_adv _]"; first set_solver+.
      iApply (interp_monotone_sd_same_heap W2 Winit Adv
        with "[] [Hinterp_adv]").
      { subst Winit. by rewrite std_update_multiple_heap. }
      { iPureIntro. exact Hrelated_W2_Winit. }
      iApply (interp_in_mem_load_result with "Hinterp_adv").
      right; split; [reflexivity|].
      apply filter_heap_nonheap; exact Hadv_base. }

    destruct Hreg as (HPC & Hcgp & Hcsp & Hreg).
    iDestruct (big_sepM_delete _ _ PC with "Hreg")
      as "[HPC Hreg]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cgp with "Hreg")
      as "[Hcgp Hreg]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ csp with "Hreg")
      as "[Hcsp Hreg]"; first by simplify_map_eq.
    assert (cmpt_region hts_main_cmpt ## cmpt_region hts_adv_cmpt)
      as Hmain_adv.
    { eapply (addr_disjoint_list_lookup _ 0 1);
        [exact hts_regions_disjoint|reflexivity..|lia]. }
    assert (cmpt_region hts_main_cmpt ##
      cmpt_switcher_region hts_switcher_cmpt) as Hmain_switcher.
    { eapply (addr_disjoint_list_lookup _ 0 3);
        [exact hts_regions_disjoint|reflexivity..|lia]. }
    assert (forall a, a ∈ cmpt_cgp_region hts_main_cmpt ->
      a ∈ cmpt_region hts_main_cmpt) as Hcgp_sub_main.
    { intros a Ha. unfold cmpt_region; set_solver. }
    assert (forall a, a ∈ cmpt_cgp_region hts_main_cmpt ->
      a ∉ cmpt_region hts_adv_cmpt /\
      a ∉ cmpt_switcher_region hts_switcher_cmpt) as Hcgp_outside.
    { intros a Ha; split; intros Hin.
      - pose proof Hmain_adv as Hdis.
        rewrite elem_of_disjoint in Hdis.
        eapply Hdis; eauto.
      - pose proof Hmain_switcher as Hdis.
        rewrite elem_of_disjoint in Hdis.
        eapply Hdis; eauto. }
    assert (forall a, a ∈ cmpt_cgp_region hts_main_cmpt ->
      std Winit !! a = None) as Hcgp_fresh.
    { intros a Ha.
      destruct (Hcgp_outside a Ha) as [Hnotadv Hnotsw].
      subst Winit W2 W1 W0.
      unfold std_update_compartment; cbn [std].
      assert (a ∉ finz.seq_between (cmpt_a_code hts_adv_cmpt)
        (cmpt_e_pcc hts_adv_cmpt)) as Hnotcode.
      { intros Hin; apply Hnotadv.
        unfold cmpt_region, cmpt_pcc_region.
        apply elem_of_union; left.
        apply elem_of_union; left.
        apply elem_of_union; left.
        apply elem_of_finz_seq_between.
        apply elem_of_finz_seq_between in Hin.
        destruct Hin as [Hlo Hhi]. split; last exact Hhi.
        pose proof (cmpt_import_size hts_adv_cmpt) as Hsize.
        solve_addr+Hsize Hlo. }
      assert (a ∉ finz.seq_between (cmpt_b_cgp hts_adv_cmpt)
        (cmpt_e_cgp hts_adv_cmpt)) as Hnotdata.
      { intros Hin; apply Hnotadv.
        unfold cmpt_region, cmpt_cgp_region.
        apply elem_of_union; left.
        apply elem_of_union; left.
        apply elem_of_union; right.
        exact Hin. }
      assert (a ∉ finz.seq_between (cmpt_b_pcc hts_adv_cmpt)
        (cmpt_a_code hts_adv_cmpt)) as Hnotimports.
      { intros Hin; apply Hnotadv.
        unfold cmpt_region, cmpt_pcc_region.
        apply elem_of_union; left.
        apply elem_of_union; left.
        apply elem_of_union; left.
        apply elem_of_finz_seq_between.
        apply elem_of_finz_seq_between in Hin.
        destruct Hin as [Hlo Hhi]. split; first exact Hlo.
        pose proof (cmpt_code_size hts_adv_cmpt) as Hsize.
        solve_addr+Hsize Hhi. }
      assert (a ∉ finz.seq_between (b_stack hts_switcher_cmpt)
        (e_stack hts_switcher_cmpt)) as Hnotstack.
      { intros Hin; apply Hnotsw.
        unfold cmpt_switcher_region, cmpt_switcher_stack_region.
        apply elem_of_union; right. exact Hin. }
      rewrite std_sta_update_multiple_lookup_same_i; [|exact Hnotstack].
      rewrite std_sta_update_multiple_lookup_same_i; [|exact Hnotimports].
      rewrite std_sta_update_multiple_lookup_same_i; [|exact Hnotdata].
      rewrite std_sta_update_multiple_lookup_same_i; [|exact Hnotcode].
      reflexivity. }

    iPoseProof (hts_main_spec _ _ _ _ _ _ _ _ adv_f Winit
      [] [] hts_assertN hts_switcherN []
      with "[$Hassert $Halloc $Hservice $Hswitcher
             $Hexport_pcc $Hexport_cgp $Hexport_malloc $Hexport_free
             $Hna $HPC $Hcgp $Hcsp $Hreg
             $Hmain_imports_mem $Hmain_codefrag $Hmain_data_mem
             $Hworld_adv $Hcstk_frag
             $Hinterp_adv $Hentry_adv $Hinterp_stack]")
      as "Hspec"; eauto.
    { exact (cmpt_pcc_disjoint_from_shadow hts_main_cmpt). }
    { exact (cmpt_pcc_base_not_heap hts_main_cmpt). }
    { exact (cmpt_cgp_disjoint_from_shadow hts_main_cmpt). }
    { exact (cmpt_cgp_not_heap_range hts_main_cmpt). }
    { solve_ndisj. }
    { solve_ndisj. }
    { solve_ndisj. }
    { rewrite !dom_delete_L.
      rewrite regmap_full_dom; first done.
      intros r.
      destruct (decide (r = PC)); simplify_eq.
      { eexists; eapply HPC. }
      destruct (decide (r = cgp)); simplify_eq.
      { eexists; eapply Hcgp. }
      destruct (decide (r = csp)); simplify_eq.
      { eexists; eapply Hcsp. }
      eexists (WInt 0). apply Hreg.
      clear -n n0 n1; set_solver. }
    { intros r Hdom.
      rewrite !dom_delete_L in Hdom.
      destruct (decide (r = PC)); simplify_eq.
      { set_solver+Hdom. }
      destruct (decide (r = cgp)); simplify_eq.
      { set_solver+Hdom. }
      destruct (decide (r = csp)); simplify_eq.
      { set_solver+Hdom. }
      rewrite !lookup_delete_ne //.
      exists (WInt 0). apply Hreg.
      clear -n n0 n1; set_solver. }
    { rewrite /SubBounds.
      pose proof (cmpt_import_size hts_main_cmpt) as Hsize_imports.
      pose proof (cmpt_code_size hts_main_cmpt) as Hsize_code.
      rewrite Hmain_code in Hsize_code.
      solve_addr+Hsize_imports Hsize_code. }
    { pose proof (cmpt_data_size hts_main_cmpt) as Hsize.
      by rewrite Hmain_data in Hsize. }
    { pose proof (cmpt_import_size hts_main_cmpt) as Hsize.
      by rewrite Hmain_imports in Hsize. }
    { rewrite not_elem_of_dom.
      apply Hcgp_fresh.
      apply elem_of_finz_seq_between.
      pose proof (cmpt_data_size hts_main_cmpt) as Hsize.
      rewrite Hmain_data in Hsize.
      solve_addr+Hsize. }
    { subst Winit W2 W1 W0.
      rewrite std_update_multiple_heap std_update_compartment_heap.
      done. }
    { done. }

    iModIntro.
    iExists (fun σ _ _ => (((gen_heap_interp (griotte_opsem.reg σ) ∗
      gen_heap_interp (griotte_opsem.sreg σ)) ∗
      gen_heap_interp (griotte_opsem.mem σ)) ∗
      gen_heap_interp (shadowtbl σ)))%I.
    iExists (fun _ => True)%I. cbn. iFrame.
    iSplitL "Hspec".
    { iApply (wp_mono with "Hspec"); iIntros (?) "?"; done. }
    iIntros "[[[Hreg' Hsreg'] Hmem'] Hshadow']".
    iExists (⊤ ∖ ↑(htsN .@ "flag")).
    iInv (htsN .@ "flag") as ">Hflag" "Hclose".
    iDestruct (gen_heap_valid with "Hmem' Hflag") as %Hm_flag.
    iModIntro. iPureIntro. rewrite /state_is_good //=.
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
  set (Σ := #[invΣ
              ; gen_heapΣ Addr Word; gen_heapΣ Addr AllocStatus
              ; gen_heapΣ RegName Word; gen_heapΣ SRegName Word
              ; entryPreΣ; CSTACK_preΣ; allocator_preΣ
              ; ghost_mapΣ Addr (Addr * (Z * Z))
              ; na_invΣ; sealStorePreΣ
              ; STS_preΣ Addr region_type OType Word; relPreΣ
              ; savedPredΣ (WorldT * CmptName * Word)
      ]).
  eapply (@hts_adequacy' Σ cnames B); eauto; try typeclasses eauto.
Qed.
