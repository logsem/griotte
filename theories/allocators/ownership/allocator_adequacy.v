From iris.proofmode Require Import proofmode.
From griotte Require Import logrel memory_region disjoint_regions_tactics.
From griotte Require Import switcher switcher_preamble compartment_layout adequacy_common allocator_resources.
From griotte.allocators.ownership Require Import allocator allocator_preamble allocator_resource_spec.
From griotte Require Import firmware_ok firmware_adequacy firmware_obligations.
(* Imported last: the fields of the image records shadow the fields of the
   layout records of [compartment_layout]. *)
From griotte Require Import image firmware.

(** * The initialisation of the allocator compartment of a firmware

    The allocator is an ordinary trusted compartment of a firmware with
    the heap root [heap_b]: it imports the shadow table, the unsealing key
    of its sealing type and the revoker, and its global is the capability
    on the whole heap. [allocator_init] turns its resources in
    [fw_init_res] (its imports, code and globals, its persistent export
    table, the heap, its shadow and its claims) into the allocator service
    invariant and the export table that the allocator's specifications
    take. *)

(** The allocator layout of a compartment of an image, with the sealing
    type [ot]. *)
Definition img_allocator_layout `{MP : MachineParameters} (c : img_cmpt) (ot : OType)
    : allocatorLayout :=
  {| AllocOtype := ot;
     allocator_pcc_b := cmpt_b_pcc c;
     allocator_code_b := cmpt_a_code c;
     allocator_pcc_e := cmpt_e_pcc c;
     allocator_cgp_b := cmpt_b_cgp c;
     allocator_cgp_e := cmpt_e_cgp c;
     allocator_exp_tbl_b := cmpt_exp_tbl_pcc c;
     allocator_exp_tbl_e := cmpt_exp_tbl_entries_end c |}.

(** The imports of the allocator, with the sealing type [ot]. *)
Definition img_allocator_imports `{MP : MachineParameters} (ot : OType) : list Word :=
  [WCap true RW Global shadow_b shadow_e shadow_b;
   WSealRange true (false, true) Global ot (ot ^+ 1)%ot ot;
   WCap true RW Global revoker_addr (revoker_addr ^+ 1)%a revoker_addr].

(** A compartment of an image holding the allocator is a well-formed
    allocator layout, given the conditions on the machine of a firmware
    with heap roots ([fw_heap_machine]) and a valid sealing type. *)
Lemma img_allocator_layout_wf `{MP : MachineParameters} (c : img_cmpt) (ot : OType) :
  img_cmpt_layout c →
  (ot < ot ^+ 1)%ot →
  (∀ a, heap_to_shadow a = translate_region heap_b heap_e shadow_b a) →
  (revoker_addr < revoker_addr ^+ 1)%a →
  cmpt_imports c = img_allocator_imports ot →
  cmpt_code c = allocator_code →
  cmpt_data c = allocator_data →
  cmpt_exp_tbl_entries c = allocator_export_table_entries →
  @allocatorLayoutWf MP (img_allocator_layout c ot).
Proof.
  intros Hc Hot Haffine Hrevoker Himports Hcode Hdata Hexports.
  pose proof (icl_import_size _ Hc) as Hi.
  pose proof (icl_code_size _ Hc) as Hcs.
  pose proof (icl_data_size _ Hc) as Hd.
  pose proof (icl_exp_tbl_pcc_size _ Hc) as He1.
  pose proof (icl_exp_tbl_header_size _ Hc) as He2.
  pose proof (icl_exp_tbl_entries_size _ Hc) as He3.
  pose proof (icl_disjointness _ Hc) as Hdisj.
  pose proof (icl_pcc_not_heap _ Hc) as [_ Hpcc_heap].
  pose proof (icl_cgp_not_heap _ Hc) as [_ Hcgp_heap].
  pose proof (icl_exp_tbl_not_heap _ Hc) as [_ Hetbl_heap].
  pose proof (icl_pcc_mmio _ Hc) as [Hpcc_sh _].
  pose proof (icl_cgp_mmio _ Hc) as [Hcgp_sh _].
  pose proof (icl_exp_tbl_mmio _ Hc) as [Hetbl_sh _].
  pose proof heap_shadow_disjoint as Hhs.
  rewrite Himports in Hi. rewrite Hcode in Hcs. rewrite Hdata in Hd.
  rewrite Hexports in He3.
  rewrite /disjoint_from_heap /disjoint_from_shadow in Hpcc_heap Hcgp_heap Hetbl_heap
    Hpcc_sh Hcgp_sh Hetbl_sh.
  constructor; cbn; try done.
  - rewrite /allocator_export_table_entries /= in He3 |- *. solve_addr+He1 He2 He3.
  - rewrite !disjoint_list_cons in Hdisj |- *.
    destruct Hdisj as (H0 & H1 & H2 & _).
    cbn [union_list foldr] in *.
    split_and!.
    + apply disjoint_union_r; split; first set_solver+H0.
      apply disjoint_union_r; split; first set_solver+H0.
      apply disjoint_union_r; split; first done.
      apply disjoint_union_r; split; first done.
      set_solver+.
    + apply disjoint_union_r; split; first set_solver+H1.
      apply disjoint_union_r; split; first done.
      apply disjoint_union_r; split; first done.
      set_solver+.
    + apply disjoint_union_r; split; first done.
      apply disjoint_union_r; split; first done.
      set_solver+.
    + apply disjoint_union_r; split; first done.
      set_solver+.
    + set_solver+.
    + apply addr_disjoint_list_empty.
Qed.

Section allocator_init.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {FA : FreeAuth Σ}
    {allocator_ownerg : allocatorOwnerG Σ}
    {sealsg : sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP : MachineParameters}.

  (** The allocator compartment [fc] of a firmware, with the sealing type
      [ot]: its imports, code and globals, together with the heap (its
      memory, unpainted shadow entries and claims from the heap root
      [heap_b]) and the owner map of the owner identifiers [ids], form the
      allocator service invariant; its export table gives the capabilities
      and the entries of [malloc] and [free]; it is a trusted compartment
      ([tb]) that declares no error handler. *)
  Lemma allocator_init {E : coPset} (img : fw_image) (fc : fw_cmpt) (ot : OType) (ids : gset Z)
      (tb : fw_trusted) :
    let c := cmpt_of img (fc_name fc) in
    let alloclayout := img_allocator_layout c ot in
    let a_alloc_exp_tbl_cgp := (cmpt_exp_tbl_pcc c ^+ ExportTable_offset_cgp)%a in
    let a_alloc_entry_malloc := (cmpt_exp_tbl_pcc c ^+ allocator_malloc_exp_tbl_off)%a in
    let a_alloc_entry_free := (cmpt_exp_tbl_pcc c ^+ allocator_free_exp_tbl_off)%a in
    img_cmpt_layout c →
    @allocatorLayoutWf MP alloclayout →
    cmpt_imports c = img_allocator_imports ot →
    cmpt_code c = allocator_code →
    cmpt_data c = allocator_data →
    cmpt_exp_tbl_entries c = allocator_export_table_entries →
    fc_body fc = TrustedBody tb →
    tb_error_handler tb = None →
    tb_error_handler_stackless tb = None →
    fw_cmpt_mem_res c -∗
    fw_cmpt_pers_res img fc -∗
    allocator_owners (gset_to_gmap ∅ ids) -∗
    ([∗ map] a↦w ∈ initial_heap_memory, a ↦ₐ lword_of_word w) -∗
    ([∗ map] a↦s ∈ initial_heap_shadow, a ↦ₛ s) -∗
    ([∗ map] a↦c ∈ init_claims {[heap_b]}, addr_alloc a c)
    ={E}=∗
    allocator_service_ctx (layout := alloclayout) ∗
    allocator_service_static (layout := alloclayout) ∗
    cmpt_exp_tbl_pcc c ↦ₐ□ WCap true RX Global (cmpt_b_pcc c) (cmpt_e_pcc c) (cmpt_b_pcc c) ∗
    a_alloc_exp_tbl_cgp ↦ₐ□ WCap true RW Global (cmpt_b_cgp c) (cmpt_e_cgp c) (cmpt_b_cgp c) ∗
    no_handler (cmpt_exp_tbl_pcc c) ∗
    a_alloc_entry_malloc ↦ₐ□
      WInt (encode_entry_point InterruptEnabled allocator_malloc_nargs allocator_malloc_min_stack
        allocator_malloc_pcc_off) ∗
    a_alloc_entry_free ↦ₐ□
      WInt (encode_entry_point InterruptEnabled allocator_free_nargs allocator_free_min_stack
        allocator_free_pcc_off).
  Proof.
    intros c alloclayout a_alloc_exp_tbl_cgp a_alloc_entry_malloc a_alloc_entry_free
      Hc Hwf Himports Hcode Hdata Hexports Hbody Hnh Hnhs.
    subst a_alloc_exp_tbl_cgp a_alloc_entry_malloc a_alloc_entry_free.
    iIntros "(Himports & Hcode & Hdata) (#Hpcc & #Hcgp & #Hh & #Hetbl) Howners Hheap Hshadow Hclaims".
    subst c. set (c := cmpt_of img (fc_name fc)) in *.
    pose proof (allocator_size_code (allocatorLayoutWf := Hwf)) as Hcode_size.
    pose proof (allocator_size_exports (allocatorLayoutWf := Hwf)) as Hexp_size.
    cbn in Hcode_size, Hexp_size.
    rewrite /allocator_export_table_entries /= in Hexp_size.
    pose proof (icl_exp_tbl_pcc_size _ Hc) as Hpcc_size.
    pose proof (icl_exp_tbl_header_size _ Hc) as Hcgp_size.
    iDestruct (initial_heap_resources with "Hheap Hshadow") as "Hheap".
    iMod (allocator_service_init_correct (layout := alloclayout) E
            (lword_of_word <$> initial_heap_memory) ids Hwf
           with "[Himports Hcode Hdata] Howners Hheap Hclaims") as "[$ $]".
    { by rewrite dom_fmap_L /initial_heap_memory dom_gset_to_gmap. }
    { rewrite /allocator_service_initial_resources /codefrag /=.
      rewrite Himports Hcode Hdata.
      replace (cmpt_a_code c ^+ length allocator_code)%a with (cmpt_e_pcc c)
        by solve_addr+Hcode_size.
      iFrame. }
    iModIntro. iFrame "Hpcc".
    replace (cmpt_exp_tbl_cgp c) with (cmpt_exp_tbl_pcc c ^+ ExportTable_offset_cgp)%a by solve_addr+Hpcc_size.
    rewrite /fw_handler_res Hbody Hnh Hnhs.
    iFrame "Hcgp Hh".
    rewrite Hexports /allocator_export_table_entries.
    iEval (rewrite !big_sepL_cons) in "Hetbl".
    iDestruct "Hetbl" as "(Hmalloc & Hfree & _)".
    iFrame "Hmalloc Hfree".
  Qed.
End allocator_init.
