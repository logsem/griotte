From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode memory_region region_keys.
From griotte.allocator Require Import allocator_preamble
  allocator_macros_spec allocator_header_spec.
From griotte.allocator Require Import allocator_free_spec_blocks.

(** The top-level specifications of [free]. The block specifications are in
    [allocator_free_spec_blocks]. *)

Section AllocatorFree.
  Context {Σ : gFunctors}
    {ceriseg : ceriseG Σ} {FA : FreeAuth Σ} {allocator_ownerg : allocatorOwnerG Σ}
    {MP : MachineParameters}
    {layout : allocatorLayout}.
  Context {layout_wf : allocatorLayoutWf}.

  (** Common call boundary for rejection. [P] carries the evidence for the
      particular rejection and is returned unchanged; the rejection itself
      may observe the request in [ca1] against the cells, the entries and the
      owner map of the service. The owner word of the allocator capability in
      [ca0] is only read. Other client resources can be framed. *)

  Local Lemma allocator_free_reject_correct
    (E : coPset) (g_owner : Locality) (a_owner : Addr) (o : Z)
    (wreq wret : LWord) (P : iProp Σ)
    (φ : language.val griotte_lang → iPropI Σ) :
    (∀ next allocations live issued Cs,
      (heap_b < next /\ next <= heap_e)%a ->
      allocator_chain (heap_b ^+ 1)%a next allocations ->
      allocator_entries_wf allocations ->
      allocator_cells_wf next allocations live issued Cs ->
      P -∗
      ca1 ↦ᵣ wreq -∗
      allocator_entries_res live allocations -∗
      allocator_service_owners allocations -∗
      allocator_cells Cs -∗
      |~{E}~>
        P ∗
        ca1 ↦ᵣ wreq ∗
        allocator_entries_res live allocations ∗
        allocator_service_owners allocations ∗
        allocator_cells Cs ∗
        ⌜¬ allocator_free_valid next allocations o wreq.(lw)⌝) ->
    ↑Nallocator_service ⊆ E ->
    is_shadow_address a_owner = false ->
    withinBounds a_owner (a_owner ^+ 1)%a a_owner = true ->
    ⊢ (
       allocator_service_ctx ∗
       na_own cerise_nais E ∗
       P ∗
       a_owner ↦ₐ WInt o ∗
       PC ↦ᵣ WCap true RX Global allocator_pcc_b allocator_pcc_e
         allocator_free_pcc_addr ∗
       cgp ↦ᵣ WCap true RW Global
         allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ allocator_capability g_owner a_owner ∗
       ca1 ↦ᵣ wreq ∗
       ca2 ↦ᵣ - ∗
       ct0 ↦ᵣ - ∗
       ct1 ↦ᵣ - ∗
       ct2 ↦ᵣ - ∗
       ct3 ↦ᵣ - ∗
       ct4 ↦ᵣ - ∗
       ctp ↦ᵣ - ∗
       cnull ↦ᵣ - ∗
       ▷ (na_own cerise_nais E ∗
          P ∗
          a_owner ↦ₐ WInt o ∗
          PC ↦ᵣ lupdatePcPerm wret ∗
          cgp ↦ᵣ WCap true RW Global
            allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
          cra ↦ᵣ wret ∗
          ca0 ↦ᵣ WInt ALLOC_INVALID ∗
          ca1 ↦ᵣ WInt 0 ∗
          ca2 ↦ᵣ - ∗
          ct0 ↦ᵣ - ∗
          ct1 ↦ᵣ - ∗
          ct2 ↦ᵣ - ∗
          ct3 ↦ᵣ - ∗
          ct4 ↦ᵣ - ∗
          ctp ↦ᵣ - ∗
          cnull ↦ᵣ WInt 0
          -∗ WP Seq (Instr Executable) @ E {{ φ }})
       -∗ WP Seq (Instr Executable) @ E {{ φ }})%I.
  Proof.
    intros Hreject_request HEservice Hshadow_a Hbounds_a.
    iIntros "(#Hservice & Hna & HP & Howner & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 &
      Hct2 & Hct3 & Hct4 & Hctp & Hcnull & Hpost)".
    (* Open the service invariant and recover the allocator code and state. *)
    iMod (na_inv_acc with "Hservice Hna") as "(Hinv & Hna & Hclose)"; try exact HEservice.
    iDestruct "Hinv" as ">[Hstatic Hdata]".
    iDestruct "Hstatic" as "[Himports Hcode]".
    iDestruct "Hdata" as (next allocations live issued Cs)
      "(%Hnext & Hslot & Hheaders & %Hwf & %Hcwf & Htoks & Howners & Hcells)".
    iDestruct (allocator_headers_chain_spec with "Hheaders") as %Hchain.
    (* The request is invalid. *)
    iMod (Hreject_request next allocations live issued Cs Hnext Hchain Hwf Hcwf
      with "HP Hca1 Htoks Howners Hcells")
      as "(HP & Hca1 & Htoks & Howners & Hcells & %Hinvalid)".
    iEval (rewrite /allocator_code) in "Hcode".
    focus_block_nochangePC 1 "Hcode" as a_free Ha_free "Hfreecode" "Hcode_cont".
    assert (Ha_eq : a_free = allocator_free_pcc_addr).
    { pose proof allocator_size_imports as Himports_size.
      rewrite allocator_imports_length in Himports_size.
      unfold allocator_free_pcc_addr, allocator_free_pcc_off, allocator_malloc_pcc_off in *.
      solve_addr. }
    subst a_free.
    (* The owner block: load the owner identifier of the allocator capability. *)
    iEval (rewrite allocator_free_instrs_owner_body) in "Hfreecode".
    iDestruct "Hctp" as (wtp) "Hctp".
    iDestruct "Hct3" as (w3o) "Hct3".
    iDestruct "Hct4" as (w4o) "Hct4".
    iApply (allocator_owner_entry_spec with
      "[- $HPC $Hctp $Hct3 $Hct4 $Hca0 $Himports $Howner $Hfreecode]"); try done.
    { pose proof allocator_size_code as Hsize_code.
      pose proof allocator_size_imports as Himports_size.
      rewrite /allocator_code length_app allocator_free_instrs_owner_body in Hsize_code.
      rewrite allocator_imports_length in Himports_size.
      unfold allocator_free_pcc_addr, allocator_free_pcc_off, allocator_malloc_pcc_off in *.
      solve_addr. }
    { by apply withinBounds_true_iff in Hbounds_a as [_ ?]. }
    iNext. iIntros "(HPC & Hctp & Hct3 & Hct4 & Hca0 & Himports & Howner & Hfreecode &
      Hbody_close)".
    change (allocator_free_pcc_addr ^+ length (allocator_owner_instrs ctp ca0 ct3 ct4))%a
      with allocator_free_body_addr.
    clear H. iDestruct (codefrag_contiguous_region with "Hfreecode") as %H.
    (* Check the capability and its bounds. *)
    assert (Hsplit : allocator_free_body_instrs =
      (allocator_free_body_instrs_n 0 ++ allocator_free_body_instrs_n 1) ++
      concat (encodeInstrsW <$> drop 2 assembled_allocator_free_body)) by reflexivity.
    iEval (rewrite Hsplit) in "Hfreecode".
    focus_block_0 "Hfreecode" as "Hprepare_code" "Hfree_cont".
    assert (Hpc : SubBounds allocator_pcc_b allocator_pcc_e
      allocator_free_body_addr (allocator_free_body_addr ^+ length allocator_free_body_instrs)%a).
    { pose proof allocator_size_code as Hsize_code.
      pose proof allocator_size_imports as Himports_size.
      rewrite /allocator_code length_app allocator_free_instrs_owner_body length_app
        in Hsize_code.
      rewrite allocator_imports_length in Himports_size.
      unfold allocator_free_body_addr, allocator_free_pcc_addr, allocator_free_pcc_off,
        allocator_malloc_pcc_off in *.
      assert (length (allocator_owner_instrs ctp ca0 ct3 ct4) = 11) as Hown_len
        by reflexivity.
      rewrite Hown_len in Hsize_code |- *.
      solve_addr. }
    assert (Hdisjoint : disjoint_from_shadow allocator_pcc_b allocator_pcc_e).
    { pose proof allocator_regions_disjoint as Hregions.
      unfold disjoint_from_shadow.
      rewrite !disjoint_list_cons in Hregions.
      cbn [union_list] in Hregions.
      set_solver. }
    assert (Hcgp_pc : allocator_cgp_b ∉ finz.seq_between allocator_pcc_b allocator_pcc_e).
    { pose proof allocator_regions_disjoint as Hregions.
      rewrite !disjoint_list_cons in Hregions. cbn [union_list] in Hregions.
      pose proof allocator_size_data as Hsize. cbn in Hsize.
      assert (allocator_cgp_b ∈ finz.seq_between allocator_cgp_b allocator_cgp_e)
        by (apply elem_of_finz_seq_between; solve_addr).
      set_solver. }
    iDestruct "Hct0" as (w0) "Hct0".
    iDestruct "Hct1" as (w1) "Hct1".
    iDestruct "Hct2" as (w2) "Hct2".
    iAssert ((allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
      allocator_headers (heap_b ^+ 1)%a next allocations ∗
      [[allocator_pcc_b, allocator_code_b]] ↦ₐ [[lword_of_word <$> allocator_imports]] ∗
      allocator_cells Cs ∗
      PC ↦ᵣ WCap true RX Global allocator_pcc_b allocator_pcc_e
        (allocator_free_block_addr allocator_free_body_addr 10) ∗
      cgp ↦ᵣ WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
      ca0 ↦ᵣ WInt o ∗
      ca1 ↦ᵣ wreq ∗
      ctp ↦ᵣ - ∗
      ct0 ↦ᵣ - ∗
      ct1 ↦ᵣ - ∗
      ct2 ↦ᵣ - ∗
      ct3 ↦ᵣ - ∗
      ct4 ↦ᵣ - ∗
      ca2 ↦ᵣ - ∗
      codefrag allocator_free_body_addr allocator_free_body_instrs) -∗
      WP Seq (Instr Executable) @ E {{ φ }})%I
      with "[- Hslot Hheaders Himports Hcells HPC Hcgp Hca0 Hca1 Hctp Hct0 Hct1 Hct2 Hct3 Hct4 Hca2
               Hprepare_code Hfree_cont]"
      as "Hreject".
    { iIntros "(Hslot & Hheaders & Himports & Hcells & HPC & Hcgp & Hca0 & Hca1 & Hctp & Hct0 & Hct1 &
        Hct2 & Hct3 & Hct4 & Hca2 & Hfreecode)".
      (* The validity check rejects the request; set ALLOC_INVALID. *)
      assert (Hsplit6 : allocator_free_body_instrs =
        concat (encodeInstrsW <$> take 10 assembled_allocator_free_body) ++
        (allocator_free_body_instrs_n 10 ++ allocator_free_body_instrs_n 11)) by reflexivity.
      iEval (rewrite Hsplit6) in "Hfreecode".
      focus_block_nochangePC 1 "Hfreecode" as a_invalid Ha_invalid "Hinvalid_code" "Hfreecode_cont".
      assert (Haddr : a_invalid = allocator_free_block_addr allocator_free_body_addr 10).
      { unfold allocator_free_block_addr in *. solve_addr. }
      subst a_invalid.
      (* Mov ca0 ALLOC_INVALID. *)
      unfold lword_of_word.
      iInstr_lookup "Hinvalid_code" as "Hi" "Hinvalid_code".
      wp_instr.
      iApply (wp_move_success_z with "[$HPC $Hi $Hca0]"); try solve_pure.
      iIntros "!> (HPC & Hi & Hca0)". wp_pure.
      iSpecialize ("Hinvalid_code" with "Hi").
      assert (Hstep : (allocator_free_body_addr ^+ 77)%a =
        (allocator_free_block_addr allocator_free_body_addr 10 ^+ 1)%a)
        by (unfold allocator_free_block_addr; solve_addr).
      iEval (rewrite Hstep) in "HPC".
      (* Mov ca1 0. *)
      iInstr "Hinvalid_code".
      iDestruct ("Hfreecode_cont" with "Hinvalid_code") as "Hfreecode".
      iEval (rewrite -Hsplit6) in "Hfreecode".
      (* Return to the caller and restore the service invariant. *)
      assert (Hsplit7 : allocator_free_body_instrs =
        concat (encodeInstrsW <$> take 11 assembled_allocator_free_body) ++
        allocator_free_body_instrs_n 11) by reflexivity.
      iEval (rewrite Hsplit7) in "Hfreecode".
      focus_block_nochangePC 1 "Hfreecode" as a_ret Ha_ret "Hret_code" "Hfreecode_cont".
      assert (Haddr : a_ret = allocator_free_block_addr allocator_free_body_addr 11).
      { unfold allocator_free_block_addr in *. solve_addr. }
      subst a_ret.
      assert (Hret : (allocator_free_block_addr allocator_free_body_addr 10 ^+ 2)%a =
        allocator_free_block_addr allocator_free_body_addr 11)
        by (unfold allocator_free_block_addr; solve_addr).
      iEval (rewrite Hret) in "HPC".
      assert (Hret_eq : allocator_free_body_instrs_n 11 =
        encodeInstrsW [Jalr cnull cra]) by reflexivity.
      iEval (rewrite Hret_eq) in "Hret_code".
      iDestruct "Hcnull" as (wnull) "Hcnull".
      iApply (allocator_return_spec with
        "[- $HPC $Hcra $Hcnull $Hret_code]").
      { clear -Hpc. unfold allocator_free_block_addr in *; cbn in *; solve_addr. }
      { exact Hdisjoint. }
      iNext. iIntros "(HPC & Hcra & Hcnull & Hret_code & _)".
      iEval (rewrite -Hret_eq) in "Hret_code".
      iDestruct ("Hfreecode_cont" with "Hret_code") as "Hfreecode".
      iEval (rewrite -Hsplit7) in "Hfreecode".
      iDestruct ("Hbody_close" with "Hfreecode") as "Hfreecode".
      iEval (rewrite -allocator_free_instrs_owner_body) in "Hfreecode".
      iDestruct ("Hcode_cont" with "Hfreecode") as "Hcode".
      iEval (rewrite -/allocator_code) in "Hcode".
      iMod ("Hclose" with "[Himports Hcode Hslot Hheaders Htoks Howners Hcells Hna]") as "Hna".
      { iFrame "Hna". iNext. iSplitL "Himports Hcode"; first iFrame.
        iExists next, allocations, live, issued, Cs. iFrame. done. }
      iApply "Hpost". iFrame. }
    destruct (decide (allocator_free_in_prefix next wreq.(lw))) as [Hprefix|Hprefix].
    - iApply (allocator_free_prepare_valid_spec with
        "[- $Hslot $HPC $Hcgp $Hca0 $Hca1 $Hctp $Hct0 $Hct1 $Hct2 $Hct3 $Hprepare_code]"); eauto.
      iNext. iIntros "(Hslot & Hcgp & Hca0 & Hca1 & Hctp & Hprepare_code & Hvalid)".
      iDestruct "Hvalid" as (p g b e a) "(%Hvalid & HPC & Hct0 & Hct1 & Hct2 & Hct3)".
      destruct Hvalid as [Heq Hbounds].
      assert (Hmissing : ¬ allocator_owned_bounds allocations o b e).
      { intros Hmember. apply Hinvalid. exists p, g, b, e, a. auto. }
      iDestruct ("Hfree_cont" with "Hprepare_code") as "Hfreecode".
      iEval (rewrite -Hsplit) in "Hfreecode".
      (* Fetch the shadow capability. *)
      assert (Hsplit2 : allocator_free_body_instrs =
        concat (encodeInstrsW <$> take 2 assembled_allocator_free_body) ++
        (allocator_free_body_instrs_n 2 ++
         concat (encodeInstrsW <$> drop 3 assembled_allocator_free_body))) by reflexivity.
      iEval (rewrite Hsplit2) in "Hfreecode".
      focus_block_nochangePC 1 "Hfreecode" as a_fetch Ha_fetch
        "Hfetch_code" "Hfreecode_cont".
      assert (Haddr : a_fetch = allocator_free_block_addr allocator_free_body_addr 2).
      { clear -Ha_fetch. unfold allocator_free_block_addr in *. solve_addr. }
      subst a_fetch.
      iEval (rewrite allocator_imports_split) in "Himports".
      iDestruct "Himports" as "(Hshadow_import & Hseal_import & Hrevoker_import)".
      assert (Hfetch_eq : allocator_free_body_instrs_n 2 =
        fetch.fetch_instrs allocator_shadow_import_off ctp ct3 ca2)
        by reflexivity.
      iEval (rewrite Hfetch_eq) in "Hfetch_code".
      iDestruct "Hca2" as (wa2) "Hca2".
      pose proof allocator_size_imports as Himports_size.
      rewrite allocator_imports_length in Himports_size.
      iApply (allocator_fetch_spec with
        "[- $HPC $Hctp $Hct3 $Hca2 $Hfetch_code $Hshadow_import]").
      { reflexivity. }
      { rewrite -Hfetch_eq; unfold allocator_free_block_addr; cbn; solve_addr. }
      { apply withinBounds_true_iff. unfold allocator_shadow_import_off. solve_addr. }
      { exact Hdisjoint. }
      { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=.
        destruct (is_heap_address shadow_b) eqn:Hheap; last reflexivity.
        exfalso. unfold is_heap_address in Hheap.
        apply withinBounds_true_iff in Hheap;
        pose proof heap_shadow_disjoint as Hd;
        rewrite /disjoint_from_shadow elem_of_disjoint in Hd;
        apply (Hd shadow_b); apply elem_of_finz_seq_between; try exact Hheap;
        pose proof shadow_valid; solve_addr. }
      { discriminate. }
      { discriminate. }
      { discriminate. }
      iNext. iIntros "(HPC & Hctp & Hct3 & Hca2 & Hshadow_import & Hfetch_code)".
      iEval (rewrite /lload_word /lift_word /=) in "Hctp".
      iEval (cbn [load_word]) in "Hctp".
      iEval (rewrite -Hfetch_eq) in "Hfetch_code".
      iDestruct ("Hfreecode_cont" with "Hfetch_code") as "Hfreecode".
      iEval (rewrite -Hsplit2) in "Hfreecode".
      (* The local header check finds no entry with these bounds. *)
      assert (Hsplit3 : allocator_free_body_instrs =
        concat (encodeInstrsW <$> take 3 assembled_allocator_free_body) ++
        (allocator_free_body_instrs_n 3 ++
         concat (encodeInstrsW <$> drop 4 assembled_allocator_free_body))) by reflexivity.
      iEval (rewrite Hsplit3) in "Hfreecode".
      focus_block_nochangePC 1 "Hfreecode" as a_check Ha_check
        "Hcheck_code" "Hfreecode_cont".
      assert (Haddr3 : a_check = allocator_free_block_addr allocator_free_body_addr 3).
      { clear -Ha_check. unfold allocator_free_block_addr in *. solve_addr. }
      subst a_check.
      assert (Hpc3 : (allocator_free_block_addr allocator_free_body_addr 2 ^+
        length (fetch.fetch_instrs allocator_shadow_import_off ctp ct3 ca2))%a =
        allocator_free_block_addr allocator_free_body_addr 3).
      { clear -Hpc. unfold allocator_free_block_addr in *. solve_addr. }
      iEval (rewrite Hpc3) in "HPC".
      iApply (allocator_free_local_check_spec _ _ _ _ next b e o allocations live issued Cs with
        "[- $Hcells $Hheaders $HPC $Hca0 $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hca2 $Hctp $Hcheck_code]");
        try done; first solve_addr.
      iNext. iIntros "(Hcells & Hheaders & Hca0 & Hct0 & Hct1 & Hct2 & Hct4 & Hcheck_code & Hout)".
      iDestruct "Hout" as "[(%Hhas & _)|(_ & HPC & Hct3 & Hca2 & Hctp)]"; first done.
      iDestruct ("Hfreecode_cont" with "Hcheck_code") as "Hfreecode".
      iEval (rewrite -Hsplit3) in "Hfreecode".
      iAssert ([[allocator_pcc_b, allocator_code_b]] ↦ₐ [[lword_of_word <$> allocator_imports]])%I
        with "[Hshadow_import Hseal_import Hrevoker_import]" as "Himports".
      { iApply allocator_imports_split. iFrame. }
      iApply "Hreject". iFrame.
    - iApply (allocator_free_prepare_invalid_spec with
        "[- $Hslot $HPC $Hcgp $Hca0 $Hca1 $Hctp $Hct0 $Hct1 $Hct2 $Hct3 $Hprepare_code]"); eauto.
      iNext. iIntros "(Hslot & Hcgp & Hca0 & Hca1 & Hctp & Hprepare_code & HPC & Hct0 & Hct1 & Hct2 &
        Hct3)".
      iDestruct ("Hfree_cont" with "Hprepare_code") as "Hfreecode".
      iEval (rewrite -Hsplit) in "Hfreecode".
      iApply "Hreject". iFrame.
  Qed.

  (** A strict subrange cannot be another allocation in the header chain.
      Observing the capability in [ca1] at its base finds the cell claimed by
      [ι], hence the header entry of [ι], whose bounds are [b] and [e]. *)

  Lemma allocator_free_narrowed_spec
    (E : coPset) (g_owner : Locality) (a_owner : Addr) (o : Z)
    (p : Perm) (g : Locality)
    (ι : AId) (b e b' e' a : Addr) (wret : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    (b <= b' /\ b' < e' /\ e' <= e)%a ->
    (b', e') ≠ (b, e) ->
    ↑Nallocator_service ⊆ E ->
    is_shadow_address a_owner = false ->
    withinBounds a_owner (a_owner ^+ 1)%a a_owner = true ->
    ⊢ (
       allocator_service_ctx ∗
       na_own cerise_nais E ∗
       alloc_obj ι b e ∗
       a_owner ↦ₐ WInt o ∗
       PC ↦ᵣ WCap true RX Global allocator_pcc_b allocator_pcc_e
         allocator_free_pcc_addr ∗
       cgp ↦ᵣ WCap true RW Global
         allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ allocator_capability g_owner a_owner ∗
       ca1 ↦ᵣ (WCap true p g b' e' a) @@ ι ∗
       ca2 ↦ᵣ - ∗
       ct0 ↦ᵣ - ∗
       ct1 ↦ᵣ - ∗
       ct2 ↦ᵣ - ∗
       ct3 ↦ᵣ - ∗
       ct4 ↦ᵣ - ∗
       ctp ↦ᵣ - ∗
       cnull ↦ᵣ - ∗
       ▷ (na_own cerise_nais E ∗
          a_owner ↦ₐ WInt o ∗
          PC ↦ᵣ lupdatePcPerm wret ∗
          cgp ↦ᵣ WCap true RW Global
            allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
          cra ↦ᵣ wret ∗
          ca0 ↦ᵣ WInt ALLOC_INVALID ∗
          ca1 ↦ᵣ WInt 0 ∗
          ca2 ↦ᵣ - ∗
          ct0 ↦ᵣ - ∗
          ct1 ↦ᵣ - ∗
          ct2 ↦ᵣ - ∗
          ct3 ↦ᵣ - ∗
          ct4 ↦ᵣ - ∗
          ctp ↦ᵣ - ∗
          cnull ↦ᵣ WInt 0
          -∗ WP Seq (Instr Executable) @ E {{ φ }})
       -∗ WP Seq (Instr Executable) @ E {{ φ }})%I.

  Proof.
    intros Hbounds Hneq HEservice Hshadow_a Hbounds_a.
    iIntros "(#Hservice & Hna & #Hobj & Howner & Hrest)".
    iDestruct "Hrest" as "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 &
      Hct3 & Hct4 & Hctp & Hcnull & Hpost)".
    iApply (allocator_free_reject_correct E g_owner a_owner o ((WCap true p g b' e' a) @@ ι) wret
      (alloc_obj ι b e) φ with "[-]"); [|exact HEservice|exact Hshadow_a|exact Hbounds_a|].
    { intros next allocations live issued Cs Hnext Hchain Hwf Hcwf.
      iIntros "#Hobj Hca1 Htoks Howners Hcells".
      destruct (decide (heap_b < b' /\ b' < e' /\ e' <= next)%a) as [Hin|Hout]; last first.
      { iApply si_upd_intro. iFrame "∗ #". iPureIntro.
        intros (p0 & g0 & b0 & e0 & a0 & Heq & Hprefix & _). inversion Heq; subst. done. }
      (* Observe the capability at its base: the cell is claimed by [ι]. *)
      destruct (acw_dom _ _ _ _ _ Hcwf b') as [ [ [c s] hdr] Hc]; first solve_addr.
      iDestruct (allocator_cells_acc _ _ _ Hc with "Hcells") as "[Hcell Hcells_close]".
      iDestruct "Hcell" as "(Hclaim & Hcell)".
      iMod (observe_claim E ca1 _ b' c with "Hca1 Hclaim") as "(Hca1 & Hclaim & %Hclaim)".
      { done. }
      { cbn. rewrite decide_True; last solve_addr.
        assert (is_heap_address b' = true) as -> by (apply withinBounds_true_iff; solve_addr).
        done. }
      cbn in Hclaim. subst c.
      iDestruct ("Hcells_close" $! (Claimed ι, s, hdr) with "[$Hclaim $Hcell]") as "Hcells".
      rewrite insert_id; last exact Hc.
      (* The claim/header clause names the header entry of [ι]. *)
      destruct (acw_claimed _ _ _ _ _ Hcwf _ _ _ _ Hc) as (b0 & e0 & r0 & Hentry & _ & _).
      iDestruct (allocator_entries_res_acc _ _ _ _ _ _ (proj2 Hwf) Hentry with "Htoks")
        as "(#Hobj0 & Htok & Htoks_close)".
      iDestruct (alloc_obj_agree with "Hobj Hobj0") as %[<- <-].
      iDestruct ("Htoks_close" $! live with "[//] Htok") as "Htoks".
      iModIntro. iFrame "∗ #". iPureIntro.
      intros (p0 & g0 & b1 & e1 & a1 & Heq & _ & r1 & ι1 & Hmember). inversion Heq; subst.
      apply (allocator_chain_subrange_spec _ _ _ _ _ _ _ Hchain
        (ex_intro _ r0 (ex_intro _ ι Hentry)) Hbounds Hneq
        (ex_intro _ (o, r1) (ex_intro _ ι1 Hmember))). }
    iFrame "Hservice Hna Hobj Howner HPC Hcgp Hcra Hca0 Hca1 Hca2 Hct0 Hct1 Hct2 Hct3 Hct4 Hctp
      Hcnull".
    iNext. iIntros "(Hna & _ & Hrest)". iApply "Hpost". iFrame.
  Qed.

  (** An allocation of another owner is rejected: [ι] is not in the owner set
      of [id], the owner of the allocator capability in [ca0], so the header
      entry of [ι], found by observing [ca1] at its base, records another
      owner. *)

  Lemma allocator_free_wrong_owner_spec
    (E : coPset) (g_owner : Locality) (a_owner : Addr) (id : Z) (Ω : gset AId)
    (p : Perm) (g : Locality)
    (ι : AId) (b e a : Addr) (wret : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    ↑Nallocator_service ⊆ E ->
    is_shadow_address a_owner = false ->
    withinBounds a_owner (a_owner ^+ 1)%a a_owner = true ->
    ι ∉ Ω ->
    ⊢ (
       allocator_service_ctx ∗
       na_own cerise_nais E ∗
       allocator_owner_id id Ω ∗
       alloc_obj ι b e ∗
       a_owner ↦ₐ WInt id ∗
       PC ↦ᵣ WCap true RX Global allocator_pcc_b allocator_pcc_e
         allocator_free_pcc_addr ∗
       cgp ↦ᵣ WCap true RW Global
         allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ allocator_capability g_owner a_owner ∗
       ca1 ↦ᵣ (WCap true p g b e a) @@ ι ∗
       ca2 ↦ᵣ - ∗
       ct0 ↦ᵣ - ∗
       ct1 ↦ᵣ - ∗
       ct2 ↦ᵣ - ∗
       ct3 ↦ᵣ - ∗
       ct4 ↦ᵣ - ∗
       ctp ↦ᵣ - ∗
       cnull ↦ᵣ - ∗
       ▷ (na_own cerise_nais E ∗
          allocator_owner_id id Ω ∗
          a_owner ↦ₐ WInt id ∗
          PC ↦ᵣ lupdatePcPerm wret ∗
          cgp ↦ᵣ WCap true RW Global
            allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
          cra ↦ᵣ wret ∗
          ca0 ↦ᵣ WInt ALLOC_INVALID ∗
          ca1 ↦ᵣ WInt 0 ∗
          ca2 ↦ᵣ - ∗
          ct0 ↦ᵣ - ∗
          ct1 ↦ᵣ - ∗
          ct2 ↦ᵣ - ∗
          ct3 ↦ᵣ - ∗
          ct4 ↦ᵣ - ∗
          ctp ↦ᵣ - ∗
          cnull ↦ᵣ WInt 0
          -∗ WP Seq (Instr Executable) @ E {{ φ }})
       -∗ WP Seq (Instr Executable) @ E {{ φ }})%I.

  Proof.
    intros HEservice Hshadow_a Hbounds_a HιΩ.
    iIntros "(#Hservice & Hna & Hid & #Hobj & Howner & Hrest)".
    iDestruct "Hrest" as "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 &
      Hct3 & Hct4 & Hctp & Hcnull & Hpost)".
    iApply (allocator_free_reject_correct E g_owner a_owner id ((WCap true p g b e a) @@ ι) wret
      (allocator_owner_id id Ω ∗ alloc_obj ι b e) φ with "[-]");
      [|exact HEservice|exact Hshadow_a|exact Hbounds_a|].
    { intros next allocations live issued Cs Hnext Hchain Hwf Hcwf.
      iIntros "[Hid #Hobj] Hca1 Htoks Howners Hcells".
      destruct (decide (heap_b < b /\ b < e /\ e <= next)%a) as [Hin|Hout]; last first.
      { iApply si_upd_intro. iFrame "∗ #". iPureIntro.
        intros (p0 & g0 & b0 & e0 & a0 & Heq & Hprefix & _). inversion Heq; subst. done. }
      (* Observe the capability at its base: the cell is claimed by [ι]. *)
      destruct (acw_dom _ _ _ _ _ Hcwf b) as [ [ [c s] hdr] Hc]; first solve_addr.
      iDestruct (allocator_cells_acc _ _ _ Hc with "Hcells") as "[Hcell Hcells_close]".
      iDestruct "Hcell" as "(Hclaim & Hcell)".
      iMod (observe_claim E ca1 _ b c with "Hca1 Hclaim") as "(Hca1 & Hclaim & %Hclaim)".
      { done. }
      { cbn. rewrite decide_True; last solve_addr.
        assert (is_heap_address b = true) as -> by (apply withinBounds_true_iff; solve_addr).
        done. }
      cbn in Hclaim. subst c.
      iDestruct ("Hcells_close" $! (Claimed ι, s, hdr) with "[$Hclaim $Hcell]") as "Hcells".
      rewrite insert_id; last exact Hc.
      (* The claim/header clause names the header entry of [ι]. *)
      destruct (acw_claimed _ _ _ _ _ Hcwf _ _ _ _ Hc) as (b0 & e0 & r0 & Hentry & _ & _).
      iDestruct (allocator_entries_res_acc _ _ _ _ _ _ (proj2 Hwf) Hentry with "Htoks")
        as "(#Hobj0 & Htok & Htoks_close)".
      iDestruct (alloc_obj_agree with "Hobj Hobj0") as %[<- <-].
      iDestruct ("Htoks_close" $! live with "[//] Htok") as "Htoks".
      (* The owner set of [id] is an exact view of the header list. *)
      iDestruct "Howners" as (O) "[Howners %Hown_wf]".
      iDestruct (allocator_owners_agree with "Howners Hid") as %HOid.
      iModIntro. iFrame "∗ #". iSplit; first done. iPureIntro.
      intros (p0 & g0 & b1 & e1 & a1 & Heq & _ & r1 & ι1 & Hmember). inversion Heq; subst.
      destruct (allocator_chain_base_unique _ _ _ _ _ _ _ _ _ _ Hchain Hentry Hmember)
        as (_ & -> & <-).
      by apply HιΩ, (allocator_owners_wf_lookup _ _ _ _ _ _ _ _ Hown_wf Hentry HOid). }
    iFrame "Hservice Hna Hid Hobj Howner HPC Hcgp Hcra Hca0 Hca1 Hca2 Hct0 Hct1 Hct2 Hct3 Hct4
      Hctp Hcnull".
    iNext. iIntros "(Hna & [Hid _] & Hrest)". iApply "Hpost". iFrame.
  Qed.

  (** A call with an invalid request leaves client memory untouched and returns
      [ALLOC_INVALID]. Other registers and resources can be framed. *)

  Lemma allocator_free_invalid_correct
    (E : coPset) (g_owner : Locality) (a_owner : Addr) (o : Z) (wreq wret : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    (∀ (next : Addr) (allocations : list allocator_header_entry),
      (heap_b < next /\ next <= heap_e)%a ->
      allocator_chain (heap_b ^+ 1)%a next allocations ->
      ¬ allocator_free_valid next allocations o wreq.(lw)) ->
    ↑Nallocator_service ⊆ E ->
    is_shadow_address a_owner = false ->
    withinBounds a_owner (a_owner ^+ 1)%a a_owner = true ->

    ⊢ (
       allocator_service_ctx ∗
       na_own cerise_nais E ∗
       a_owner ↦ₐ WInt o ∗

       (* Initial register file. *)
       PC ↦ᵣ WCap true RX Global allocator_pcc_b allocator_pcc_e
         allocator_free_pcc_addr ∗
       cgp ↦ᵣ WCap true RW Global
         allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ allocator_capability g_owner a_owner ∗
       ca1 ↦ᵣ wreq ∗
       ca2 ↦ᵣ - ∗
       ct0 ↦ᵣ - ∗
       ct1 ↦ᵣ - ∗
       ct2 ↦ᵣ - ∗
       ct3 ↦ᵣ - ∗
       ct4 ↦ᵣ - ∗
       ctp ↦ᵣ - ∗
       cnull ↦ᵣ - ∗

       ▷ (na_own cerise_nais E ∗
          a_owner ↦ₐ WInt o ∗
          PC ↦ᵣ lupdatePcPerm wret ∗
          cgp ↦ᵣ WCap true RW Global
            allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
          cra ↦ᵣ wret ∗
          ca0 ↦ᵣ WInt ALLOC_INVALID ∗
          ca1 ↦ᵣ WInt 0 ∗
          ca2 ↦ᵣ - ∗
          ct0 ↦ᵣ - ∗
          ct1 ↦ᵣ - ∗
          ct2 ↦ᵣ - ∗
          ct3 ↦ᵣ - ∗
          ct4 ↦ᵣ - ∗
          ctp ↦ᵣ - ∗
          cnull ↦ᵣ WInt 0

          -∗ WP Seq (Instr Executable) @ E {{ φ }})
       -∗ WP Seq (Instr Executable) @ E {{ φ }})%I.
  Proof.
    intros Hinvalid HEservice Hshadow_a Hbounds_a.
    iIntros "(#Hservice & Hna & Howner & Hrest)".
    iDestruct "Hrest" as "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 &
      Hct3 & Hct4 & Hctp & Hcnull & Hpost)".
    iApply (allocator_free_reject_correct E g_owner a_owner o wreq wret emp%I φ with "[-]");
      [|exact HEservice|exact Hshadow_a|exact Hbounds_a|].
    { intros next allocations live issued Cs Hnext Hchain _ _.
      iIntros "_ Hca1 Htoks Howners Hcells". iApply si_upd_intro. iFrame.
      iPureIntro. exact (Hinvalid next allocations Hnext Hchain). }
    iFrame "Hservice Hna Howner HPC Hcgp Hcra Hca0 Hca1 Hca2 Hct0 Hct1 Hct2 Hct3 Hct4 Hctp Hcnull".
    iNext. iIntros "(Hna & _ & Hrest)". iApply "Hpost". iFrame.
  Qed.

  (** The functional [free]. The capability in [ca1] carries [ι]: observing
      it at its base finds the cell claimed by [ι], hence the header entry of
      [ι] (the claim/header clause). Its recorded owner is [id], the owner of
      the allocator capability in [ca0], since [ι ∈ Ω] and the owner sets are
      an exact view of the header list (D22). The cells of [ι], with their
      shares, and
      the client's [free_auth_held ι] rebuild the whole status token, which
      moves to [APainting] before the paint loop and to [AQuar] after it. The
      revoker store then kills [ι]: no register holds a word with authority
      over [ι] there, since [ca0] holds [ALLOC_OK], [ca1] is zeroed and the
      framed registers are identifier-free. The payload is unpainted and
      returns to the service as unclaimed cells. A successful call
      relinquishes the memory and returns [ι ⊒ AQuar]. *)

  Lemma allocator_free_valid_correct
    (E : coPset) (g_owner : Locality) (a_owner : Addr) (id : Z) (Ω : gset AId)
    (p : Perm) (g : Locality) (ι : AId) (b e a : Addr)
    (ws : list LWord) (wret : LWord) (rmap : LReg)
    (φ : language.val griotte_lang → iPropI Σ) :

    ↑Nallocator_service ⊆ E ->
    is_shadow_address a_owner = false ->
    withinBounds a_owner (a_owner ^+ 1)%a a_owner = true ->
    ι ∈ Ω ->
    (heap_b < b /\ b < e /\ e <= heap_e)%a ->
    length ws = length (finz.seq_between b e) ->
    dom rmap = all_registers_s ∖
      {[PC; cgp; cra; ca0; ca1; ca2; ct0; ct1; ct2; ct3; ct4; ctp; cnull]} ->
    (∀ r w, rmap !! r = Some w -> has_authority w.(lw) -> w.(lprov) = None) ->
    (has_authority wret.(lw) -> wret.(lprov) = None) ->

    ⊢ (

       allocator_service_ctx ∗
       na_own cerise_nais E ∗
       allocator_owner_id id Ω ∗
       a_owner ↦ₐ WInt id ∗
       alloc_obj ι b e ∗
       free_auth_held ι ∗

       (* Initial register file. *)
       PC ↦ᵣ WCap true RX Global allocator_pcc_b allocator_pcc_e
         allocator_free_pcc_addr ∗
       cgp ↦ᵣ WCap true RW Global
         allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ allocator_capability g_owner a_owner ∗
       ca1 ↦ᵣ (WCap true p g b e a) @@ ι ∗
       ca2 ↦ᵣ - ∗
       ct0 ↦ᵣ - ∗
       ct1 ↦ᵣ - ∗
       ct2 ↦ᵣ - ∗
       ct3 ↦ᵣ - ∗
       ct4 ↦ᵣ - ∗
       ctp ↦ᵣ - ∗
       cnull ↦ᵣ - ∗
       ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) ∗
       [[b, e]] ↦ₕ[ι] [[ws]] ∗

       ▷ (na_own cerise_nais E ∗
          allocator_owner_id id Ω ∗
          a_owner ↦ₐ WInt id ∗
          PC ↦ᵣ lupdatePcPerm wret ∗
          cgp ↦ᵣ WCap true RW Global
            allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
          cra ↦ᵣ wret ∗
          ca0 ↦ᵣ WInt ALLOC_OK ∗
          ca1 ↦ᵣ WInt 0 ∗
          ca2 ↦ᵣ - ∗
          ct0 ↦ᵣ - ∗
          ct1 ↦ᵣ - ∗
          ct2 ↦ᵣ - ∗
          ct3 ↦ᵣ - ∗
          ct4 ↦ᵣ - ∗
          ctp ↦ᵣ - ∗
          cnull ↦ᵣ WInt 0 ∗
          ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) ∗
          ι ⊒ AQuar ∗
          £ 1

          -∗ WP Seq (Instr Executable) @ E {{ φ }})
       -∗ WP Seq (Instr Executable) @ E {{ φ }})%I.
  Proof.
    intros HEservice Hshadow_a Hbounds_a HιΩ Hbounds Hlen Hdom Hclean Hclean_ret.
    iIntros "(#Hservice & Hna & Hid & Howner & #Hobj & Hheld & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 &
      Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hcnull & Hrmap & Hheap & Hpost)".
    (* Split the cells into their memory and their status shares. *)
    iDestruct (heap_region_pointsto_split with "Hobj") as "[Hto _]".
    iDestruct ("Hto" with "Hheap") as "[Hmem Hshares]".
    (* Open the service invariant and recover the allocator code and state. *)
    iMod (na_inv_acc with "Hservice Hna") as "(Hinv & Hna & Hclose)"; try exact HEservice.
    iDestruct "Hinv" as ">[Hstatic Hdata]".
    iDestruct "Hstatic" as "[Himports Hcode]".
    iDestruct "Hdata" as (next allocations live issued Cs)
      "(%Hnext & Hslot & Hheaders & %Hwf & %Hcwf & Htoks & Howners & Hcells)".
    iDestruct "Howners" as (O) "[Howners %Hown_wf]".
    iDestruct (allocator_owners_agree with "Howners Hid") as %HOid.
    iDestruct (allocator_headers_chain_spec with "Hheaders") as %Hchain.
    (* Observe [ca1] at the payload base: the cell is claimed by [ι], so the
       claim/header clause names the header entry of [ι]. *)
    destruct (acw_dom _ _ _ _ _ Hcwf b) as [ [ [c s] hdr] Hc]; first solve_addr.
    iDestruct (allocator_cells_acc _ _ _ Hc with "Hcells") as "[Hcell Hcells_close]".
    iDestruct "Hcell" as "(Hclaim & Hcell)".
    iMod (observe_claim E ca1 _ b c with "Hca1 Hclaim") as "(Hca1 & Hclaim & %Hclaim)".
    { done. }
    { cbn. rewrite decide_True; last solve_addr.
      assert (is_heap_address b = true) as -> by (apply withinBounds_true_iff; solve_addr).
      done. }
    cbn in Hclaim. subst c.
    iDestruct ("Hcells_close" $! (Claimed ι, s, hdr) with "[$Hclaim $Hcell]") as "Hcells".
    rewrite insert_id; last exact Hc.
    destruct (acw_claimed _ _ _ _ _ Hcwf _ _ _ _ Hc) as (b0 & e0 & r0 & Hentry & Hlive & _).
    iDestruct (allocator_entries_res_acc _ _ _ _ _ _ (proj2 Hwf) Hentry with "Htoks")
      as "(#Hobj0 & Htok & Htoks_close)".
    iDestruct (alloc_obj_agree with "Hobj Hobj0") as %[<- <-].
    iClear "Hobj0".
    pose proof (allocator_chain_member_bounds _ _ _ _ _ _ _ Hchain Hentry) as Hentry_bounds.
    (* The owner link (D22): the entry of [ι] records [id]. *)
    destruct r0 as [o0 r0].
    pose proof (allocator_owners_wf_member _ _ _ _ _ _ _ _ _ Hown_wf (proj2 Hwf) Hentry HOid HιΩ)
      as <-.
    rewrite /allocator_tok decide_True //.
    iDestruct "Htok" as "[Hshare Hkept]".
    (* Rebuild the whole status token of [ι]. *)
    iAssert (ι ↦st{1} ALive)%I with "[Hkept Hheld Hshare Hshares]" as "Hfull".
    { rewrite (st_own_split_alloc ι (finz.seq_between b e))
        finz_seq_between_length -free_auth_split.
      iFrame. }
    iEval (rewrite /allocator_code) in "Hcode".
    focus_block_nochangePC 1 "Hcode" as a_free Ha_free "Hfreecode" "Hcode_cont".
    assert (Ha_eq : a_free = allocator_free_pcc_addr).
    { pose proof allocator_size_imports as Himports_size.
      rewrite allocator_imports_length in Himports_size.
      unfold allocator_free_pcc_addr, allocator_free_pcc_off, allocator_malloc_pcc_off in *.
      solve_addr. }
    subst a_free.
    (* The owner block: load the owner identifier of the allocator capability. *)
    iEval (rewrite allocator_free_instrs_owner_body) in "Hfreecode".
    iDestruct "Hctp" as (wtp) "Hctp".
    iDestruct "Hct3" as (w3o) "Hct3".
    iDestruct "Hct4" as (w4o) "Hct4".
    iApply (allocator_owner_entry_spec with
      "[- $HPC $Hctp $Hct3 $Hct4 $Hca0 $Himports $Howner $Hfreecode]"); try done.
    { pose proof allocator_size_code as Hsize_code.
      pose proof allocator_size_imports as Himports_size.
      rewrite /allocator_code length_app allocator_free_instrs_owner_body in Hsize_code.
      rewrite allocator_imports_length in Himports_size.
      unfold allocator_free_pcc_addr, allocator_free_pcc_off, allocator_malloc_pcc_off in *.
      solve_addr. }
    { by apply withinBounds_true_iff in Hbounds_a as [_ ?]. }
    iNext. iIntros "(HPC & Hctp & Hct3 & Hct4 & Hca0 & Himports & Howner & Hfreecode &
      Hbody_close)".
    change (allocator_free_pcc_addr ^+ length (allocator_owner_instrs ctp ca0 ct3 ct4))%a
      with allocator_free_body_addr.
    clear H. iDestruct (codefrag_contiguous_region with "Hfreecode") as %H.
    (* Check the capability and its bounds. *)
    assert (Hsplit : allocator_free_body_instrs =
      (allocator_free_body_instrs_n 0 ++ allocator_free_body_instrs_n 1) ++
      concat (encodeInstrsW <$> drop 2 assembled_allocator_free_body)) by reflexivity.
    iEval (rewrite Hsplit) in "Hfreecode".
    focus_block_0 "Hfreecode" as "Hprepare_code" "Hfree_cont".
    assert (Hpc : SubBounds allocator_pcc_b allocator_pcc_e
      allocator_free_body_addr (allocator_free_body_addr ^+ length allocator_free_body_instrs)%a).
    { pose proof allocator_size_code as Hsize_code.
      pose proof allocator_size_imports as Himports_size.
      rewrite /allocator_code length_app allocator_free_instrs_owner_body length_app
        in Hsize_code.
      rewrite allocator_imports_length in Himports_size.
      unfold allocator_free_body_addr, allocator_free_pcc_addr, allocator_free_pcc_off,
        allocator_malloc_pcc_off in *.
      assert (length (allocator_owner_instrs ctp ca0 ct3 ct4) = 11) as Hown_len
        by reflexivity.
      rewrite Hown_len in Hsize_code |- *.
      solve_addr. }
    assert (Hdisjoint : disjoint_from_shadow allocator_pcc_b allocator_pcc_e).
    { pose proof allocator_regions_disjoint as Hregions.
      unfold disjoint_from_shadow.
      rewrite !disjoint_list_cons in Hregions.
      cbn [union_list] in Hregions.
      set_solver. }
    assert (Hcgp_pc : allocator_cgp_b ∉ finz.seq_between allocator_pcc_b allocator_pcc_e).
    { pose proof allocator_regions_disjoint as Hregions.
      rewrite !disjoint_list_cons in Hregions. cbn [union_list] in Hregions.
      pose proof allocator_size_data as Hsize. cbn in Hsize.
      assert (allocator_cgp_b ∈ finz.seq_between allocator_cgp_b allocator_cgp_e)
        by (apply elem_of_finz_seq_between; solve_addr).
      set_solver. }
    iDestruct "Hct0" as (w0) "Hct0".
    iDestruct "Hct1" as (w1) "Hct1".
    iDestruct "Hct2" as (w2) "Hct2".
    assert (Hrequest : allocator_free_in_prefix next (WCap true p g b e a)).
    { exists p, g, b, e, a. split; first reflexivity. solve_addr. }
    iApply (allocator_free_prepare_valid_spec _ _ _ _ _ o0 ((WCap true p g b e a) @@ ι) with
      "[- $Hslot $HPC $Hcgp $Hca0 $Hca1 $Hctp $Hct0 $Hct1 $Hct2 $Hct3 $Hprepare_code]"); eauto.
    iNext. iIntros "(Hslot & Hcgp & Hca0 & Hca1 & Hctp & Hprepare_code & Hvalid)".
    iDestruct "Hvalid" as (p0 g0 b0 e0 a0)
      "(%Hvalid & HPC & Hct0 & Hct1 & Hct2 & Hct3)".
    destruct Hvalid as [Heq Hvalid]. cbn in Heq.
    injection Heq as <- <- <- <- <-.
    iDestruct ("Hfree_cont" with "Hprepare_code") as "Hfreecode".
    iEval (rewrite -Hsplit) in "Hfreecode".
    (* Fetch the shadow capability. *)
    assert (Hsplit2 : allocator_free_body_instrs =
      concat (encodeInstrsW <$> take 2 assembled_allocator_free_body) ++
      (allocator_free_body_instrs_n 2 ++
       concat (encodeInstrsW <$> drop 3 assembled_allocator_free_body))) by reflexivity.
    iEval (rewrite Hsplit2) in "Hfreecode".
    focus_block_nochangePC 1 "Hfreecode" as a_fetch Ha_fetch
      "Hfetch_code" "Hfreecode_cont".
    assert (Haddr : a_fetch = allocator_free_block_addr allocator_free_body_addr 2).
    { clear -Ha_fetch. unfold allocator_free_block_addr in *. solve_addr. }
    subst a_fetch.
    iEval (rewrite allocator_imports_split) in "Himports".
    iDestruct "Himports" as "(Hshadow_import & Hseal_import & Hrevoker_import)".
    assert (Hfetch_eq : allocator_free_body_instrs_n 2 =
      fetch.fetch_instrs allocator_shadow_import_off ctp ct3 ca2)
      by reflexivity.
    iEval (rewrite Hfetch_eq) in "Hfetch_code".
    iDestruct "Hca2" as (wa2) "Hca2".
    pose proof allocator_size_imports as Himports_size.
    rewrite allocator_imports_length in Himports_size.
    iApply (allocator_fetch_spec with
      "[- $HPC $Hctp $Hct3 $Hca2 $Hfetch_code $Hshadow_import]").
    { reflexivity. }
    { rewrite -Hfetch_eq; unfold allocator_free_block_addr; cbn; solve_addr. }
    { apply withinBounds_true_iff. unfold allocator_shadow_import_off. solve_addr. }
    { exact Hdisjoint. }
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=.
      destruct (is_heap_address shadow_b) eqn:Hheap; last reflexivity.
      exfalso. unfold is_heap_address in Hheap.
      apply withinBounds_true_iff in Hheap;
      pose proof heap_shadow_disjoint as Hd;
      rewrite /disjoint_from_shadow elem_of_disjoint in Hd;
      apply (Hd shadow_b); apply elem_of_finz_seq_between; try exact Hheap;
      pose proof shadow_valid; solve_addr. }
    { discriminate. }
    { discriminate. }
    { discriminate. }
    iNext. iIntros "(HPC & Hctp & Hct3 & Hca2 & Hshadow_import & Hfetch_code)".
    iEval (rewrite /lload_word /lift_word /=) in "Hctp".
    iEval (cbn [load_word]) in "Hctp".
    iEval (rewrite -Hfetch_eq) in "Hfetch_code".
    iDestruct ("Hfreecode_cont" with "Hfetch_code") as "Hfreecode".
    iEval (rewrite -Hsplit2) in "Hfreecode".
    (* The local header check finds the entry of [ι] (D11). *)
    assert (Hmember : allocator_owned_bounds allocations o0 b e) by (exists r0, ι; done).
    assert (Hsplit3 : allocator_free_body_instrs =
      concat (encodeInstrsW <$> take 3 assembled_allocator_free_body) ++
      (allocator_free_body_instrs_n 3 ++
       concat (encodeInstrsW <$> drop 4 assembled_allocator_free_body))) by reflexivity.
    iEval (rewrite Hsplit3) in "Hfreecode".
    focus_block_nochangePC 1 "Hfreecode" as a_check Ha_check
      "Hcheck_code" "Hfreecode_cont".
    assert (Haddr3 : a_check = allocator_free_block_addr allocator_free_body_addr 3).
    { clear -Ha_check. unfold allocator_free_block_addr in *. solve_addr. }
    subst a_check.
    assert (Hpc3 : (allocator_free_block_addr allocator_free_body_addr 2 ^+
      length (fetch.fetch_instrs allocator_shadow_import_off ctp ct3 ca2))%a =
      allocator_free_block_addr allocator_free_body_addr 3).
    { clear -Hpc. unfold allocator_free_block_addr in *. solve_addr. }
    iEval (rewrite Hpc3) in "HPC".
    iApply (allocator_free_local_check_spec _ _ _ _ next b e o0 allocations live issued Cs with
      "[- $Hcells $Hheaders $HPC $Hca0 $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hca2 $Hctp $Hcheck_code]");
      try done; first solve_addr.
    iNext. iIntros "(Hcells & Hheaders & Hca0 & Hct0 & Hct1 & Hct2 & Hct4 & Hcheck_code & Hout)".
    iDestruct "Hout" as "[(_ & HPC & Hct3 & Hca2 & Hctp)|(%Hmiss & _)]"; last done.
    iDestruct "Hct4" as (w4') "Hct4".
    iDestruct ("Hfreecode_cont" with "Hcheck_code") as "Hfreecode".
    iEval (rewrite -Hsplit3) in "Hfreecode".
    (* Take the cells of [ι]: they are claimed and unpainted. *)
    iDestruct (allocator_cells_range_acc (finz.seq_between b e)
                 (λ _, (Claimed ι, ShadowLive, false)) with "Hcells")
      as "[Hrange Hcells_close]".
    { apply finz_seq_between_NoDup. }
    { intros x Hx. apply elem_of_finz_seq_between in Hx.
      by apply (acw_live _ _ _ _ _ Hcwf b e (o0, r0) ι). }
    iEval (rewrite /cell_res' /cell_res /=) in "Hrange".
    iDestruct (big_sepL_sep with "Hrange") as "[Hclaims Hrange]".
    iDestruct (big_sepL_sep with "Hrange") as "[Hshadows _]".
    pose proof heap_shadow_same_size as Hss.
    pose proof heap_valid as Hheap_valid.
    pose (sb := (shadow_b ^+ (b - heap_b))%a).
    pose (se := (shadow_b ^+ (e - heap_b))%a).
    assert (Hshadow : (shadow_b <= sb /\ sb < se /\ se <= shadow_e)%a).
    { unfold sb, se. clear -Hss Hvalid Hnext Hheap_valid. solve_addr. }
    assert (Hlen_shadow : (se - sb = e - b)%Z).
    { unfold sb, se. clear -Hss Hvalid Hnext Hheap_valid. solve_addr. }
    assert (Hrewind : (se + (b - e))%a = Some sb).
    { unfold sb, se. clear -Hss Hvalid Hnext Hheap_valid. solve_addr. }
    assert (Htranslation : ∀ x, (b <= x /\ x < e)%a ->
      heap_to_shadow x = Some (sb ^+ (x - b))%a).
    { intros x Hx. rewrite allocator_translation_affine.
      unfold translate_region.
      assert (Hxheap : withinBounds heap_b heap_e x = true).
      { apply withinBounds_true_iff. clear -Hx Hvalid Hnext. solve_addr. }
      rewrite Hxheap. unfold sb. clear -Hx Hvalid Hnext Hheap_valid Hss. solve_addr. }
    (* Paint the payload quarantined: the status token moves to [APainting]. *)
    iMod (reg_painting E ι with "Hfull") as "Hpainting".
    assert (Hsplit4 : allocator_free_body_instrs =
      concat (encodeInstrsW <$> take 4 assembled_allocator_free_body) ++
      (allocator_free_body_instrs_n 4 ++
       concat (encodeInstrsW <$> drop 5 assembled_allocator_free_body))) by reflexivity.
    iEval (rewrite Hsplit4) in "Hfreecode".
    focus_block_nochangePC 1 "Hfreecode" as a_paint Ha_paint
      "Hpaint_code" "Hfreecode_cont".
    assert (Haddr4 : a_paint =
      allocator_free_block_addr allocator_free_body_addr 4).
    { clear -Ha_paint. unfold allocator_free_block_addr in *. solve_addr. }
    subst a_paint.
    assert (Hpaint_eq : allocator_free_body_instrs_n 4 =
      allocator_paint_instrs ctp ca2 ShadowQuarantined) by reflexivity.
    iEval (rewrite Hpaint_eq) in "Hpaint_code".
    iCombine "Hshadows Hclaims" as "Hpayload".
    rewrite -big_sepL_sep.
    iApply (allocator_paint_spec ShadowLive ShadowQuarantined ctp ca2 E RX Global
      allocator_pcc_b allocator_pcc_e
      (allocator_free_block_addr allocator_free_body_addr 4) b e sb se
      (ι ↦st{1} APainting) (λ a, addr_alloc a (Claimed ι))
      with "[- $HPC $Hctp $Hca2 $Hpaint_code $Hpainting $Hpayload]").
    { reflexivity. }
    { rewrite -Hpaint_eq. clear -Hpc.
      unfold allocator_free_block_addr in *; cbn in *; solve_addr. }
    { exact Hdisjoint. }
    { clear -Hvalid Hnext. solve_addr. }
    { exact Hshadow. }
    { exact Hlen_shadow. }
    { exact Htranslation. }
    { apply (bool_decide_unpack _). by vm_compute. }
    { right. apply allocator_free_paint_ok. }
    iNext. iIntros "(HPC & Hctp & Hca2 & Hpainting & Hpayload & Hpaint_code)".
    iEval (rewrite -Hpaint_eq) in "Hpaint_code".
    iDestruct ("Hfreecode_cont" with "Hpaint_code") as "Hfreecode".
    iEval (rewrite -Hsplit4) in "Hfreecode".
    (* Every cell is quarantined: the status token moves to [AQuar]. *)
    iDestruct (big_sepL_sep with "Hpayload") as "[Hshadows Hclaims]".
    iMod (reg_quarantine E ι b e with "Hobj Hpainting Hshadows")
      as "(Hquar & #Hq & Hshadows)".
    (* Set ALLOC_OK. *)
    assert (Hsplit5 : allocator_free_body_instrs =
      concat (encodeInstrsW <$> take 5 assembled_allocator_free_body) ++
      (allocator_free_body_instrs_n 5 ++
       concat (encodeInstrsW <$> drop 6 assembled_allocator_free_body))) by reflexivity.
    iEval (rewrite Hsplit5) in "Hfreecode".
    focus_block_nochangePC 1 "Hfreecode" as a_success Ha_success
      "Hsuccess_code" "Hfreecode_cont".
    assert (Haddr5 : a_success =
      allocator_free_block_addr allocator_free_body_addr 5).
    { clear -Ha_success. unfold allocator_free_block_addr in *. solve_addr. }
    subst a_success.
    assert (Hpc5 : (allocator_free_block_addr allocator_free_body_addr 4 ^+
       length (allocator_paint_instrs ctp ca2 ShadowQuarantined))%a =
       allocator_free_block_addr allocator_free_body_addr 5).
    { clear -Hpc. unfold allocator_free_block_addr in *; cbn in *; solve_addr. }
    iEval (rewrite Hpc5) in "HPC".
    iApply (allocator_free_success_block_spec with
      "[- $HPC $Hca0 $Hca1 $Hsuccess_code]"); eauto.
    iNext. iIntros "(HPC & Hca0 & Hca1 & Hsuccess_code)".
    iDestruct ("Hfreecode_cont" with "Hsuccess_code") as "Hfreecode".
    iEval (rewrite -Hsplit5) in "Hfreecode".
    (* Fetch the revoker capability. *)
    assert (Hsplit6 : allocator_free_body_instrs =
      concat (encodeInstrsW <$> take 6 assembled_allocator_free_body) ++
      (allocator_free_body_instrs_n 6 ++
       concat (encodeInstrsW <$> drop 7 assembled_allocator_free_body))) by reflexivity.
    iEval (rewrite Hsplit6) in "Hfreecode".
    focus_block_nochangePC 1 "Hfreecode" as a_rfetch Ha_rfetch
      "Hrfetch_code" "Hfreecode_cont".
    assert (Haddr6 : a_rfetch =
      allocator_free_block_addr allocator_free_body_addr 6).
    { clear -Ha_rfetch. unfold allocator_free_block_addr in *. solve_addr. }
    subst a_rfetch.
    assert (Hrfetch_eq : allocator_free_body_instrs_n 6 =
      fetch.fetch_instrs allocator_revoker_import_off ct3 ct4 ca2)
      by reflexivity.
    iEval (rewrite Hrfetch_eq) in "Hrfetch_code".
    iApply (allocator_fetch_spec with
      "[- $HPC $Hct3 $Hct4 $Hca2 $Hrfetch_code $Hrevoker_import]").
    { reflexivity. }
    { rewrite -Hrfetch_eq; unfold allocator_free_block_addr; cbn; solve_addr. }
    { apply withinBounds_true_iff. unfold allocator_revoker_import_off. solve_addr. }
    { exact Hdisjoint. }
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=.
      by rewrite revoker_not_heap_address. }
    { discriminate. }
    { discriminate. }
    { discriminate. }
    iNext. iIntros "(HPC & Hct3 & Hct4 & Hca2 & Hrevoker_import & Hrfetch_code)".
    iEval (rewrite /lload_word /lift_word /=) in "Hct3".
    iEval (cbn [load_word]) in "Hct3".
    iEval (rewrite -Hrfetch_eq) in "Hrfetch_code".
    iDestruct ("Hfreecode_cont" with "Hrfetch_code") as "Hfreecode".
    iEval (rewrite -Hsplit6) in "Hfreecode".
    (* Store to the revoker: the sweep kills [ι]. *)
    assert (Hsplit7 : allocator_free_body_instrs =
      concat (encodeInstrsW <$> take 7 assembled_allocator_free_body) ++
      (allocator_free_body_instrs_n 7 ++
       concat (encodeInstrsW <$> drop 8 assembled_allocator_free_body))) by reflexivity.
    iEval (rewrite Hsplit7) in "Hfreecode".
    focus_block_nochangePC 1 "Hfreecode" as a_revoke Ha_revoke
      "Hrevoke_code" "Hfreecode_cont".
    assert (Haddr7 : a_revoke =
      allocator_free_block_addr allocator_free_body_addr 7).
    { clear -Ha_revoke. unfold allocator_free_block_addr in *. solve_addr. }
    subst a_revoke.
    assert (Hpc7 : (allocator_free_block_addr allocator_free_body_addr 6 ^+
      length (fetch.fetch_instrs allocator_revoker_import_off ct3 ct4 ca2))%a =
      allocator_free_block_addr allocator_free_body_addr 7).
    { clear -Hpc. unfold allocator_free_block_addr in *. solve_addr. }
    iEval (rewrite Hpc7) in "HPC".
    iDestruct "Hcnull" as (wnull) "Hcnull".
    (* The rest of the register file: the frame, and the registers that hold
       no word with authority over [ι]. *)
    assert (Hrmap_none : ∀ r, r ∈ ({[PC; cgp; cra; ca0; ca1; ca2; ct0; ct1; ct2; ct3; ct4;
                                     ctp; cnull]} : gset RegName) -> rmap !! r = None).
    { intros r Hr. apply not_elem_of_dom. rewrite Hdom. set_solver. }
    iDestruct (big_sepM_insert with "[$Hrmap $Hcnull]") as "Hregs";
      first (apply Hrmap_none; set_solver).
    iDestruct (big_sepM_insert with "[$Hregs $Hct0]") as "Hregs";
      first (simplify_map_eq; apply Hrmap_none; set_solver).
    iDestruct (big_sepM_insert with "[$Hregs $Hca1]") as "Hregs";
      first (simplify_map_eq; apply Hrmap_none; set_solver).
    iDestruct (big_sepM_insert with "[$Hregs $Hca0]") as "Hregs";
      first (simplify_map_eq; apply Hrmap_none; set_solver).
    iDestruct (big_sepM_insert with "[$Hregs $Hcra]") as "Hregs";
      first (simplify_map_eq; apply Hrmap_none; set_solver).
    iDestruct (big_sepM_insert with "[$Hregs $Hcgp]") as "Hregs";
      first (simplify_map_eq; apply Hrmap_none; set_solver).
    iApply (allocator_free_revoke_spec _ _ _ _ b e sb se ι with
      "[- $HPC $Hct1 $Hct2 $Hct3 $Hct4 $Hctp $Hca2 $Hregs $Hrevoke_code]").
    { assumption. }
    { assumption. }
    { exact Hdisjoint. }
    { exact Hrewind. }
    { rewrite !dom_insert_L Hdom.
      apply set_eq. intros x. pose proof (all_registers_s_correct x).
      destruct (decide (x ∈ ({[PC; cgp; cra; ca0; ca1; ca2; ct0; ct1; ct2; ct3; ct4; ctp;
                               cnull]} : gset RegName))) as [Hx|Hx]; set_solver. }
    { intros x lv Hx Hlookup Hauth.
      destruct (decide (x = cgp)); [subst; simplify_map_eq; done|].
      destruct (decide (x = cra)); [subst; simplify_map_eq; by rewrite Hclean_ret|].
      destruct (decide (x = ca0)); [subst; simplify_map_eq; done|].
      destruct (decide (x = ca1)); [subst; simplify_map_eq; done|].
      destruct (decide (x = ct0)); [subst; simplify_map_eq; done|].
      rewrite !lookup_insert_ne // in Hlookup.
      by rewrite (Hclean _ _ Hlookup Hauth). }
    iSplitL "Hquar Hshadows Hclaims".
    { iExists b, e. iFrame "Hobj Hquar". iApply big_sepL_sep. iFrame. }
    iNext. iIntros "(HPC & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hca2 & Hregs & Hdead &
      Hrevoke_code)".
    iDestruct ("Hfreecode_cont" with "Hrevoke_code") as "Hfreecode".
    iEval (rewrite -Hsplit7) in "Hfreecode".
    iDestruct "Hdead" as (b1 e1) "(#Hobj1 & Hdead & _ & Hcells_dead)".
    iDestruct (alloc_obj_agree with "Hobj Hobj1") as %[<- <-].
    (* Unpaint the revoked payload. *)
    assert (Hsplit8 : allocator_free_body_instrs =
      concat (encodeInstrsW <$> take 8 assembled_allocator_free_body) ++
      (allocator_free_body_instrs_n 8 ++
       concat (encodeInstrsW <$> drop 9 assembled_allocator_free_body))) by reflexivity.
    iEval (rewrite Hsplit8) in "Hfreecode".
    focus_block_nochangePC 1 "Hfreecode" as a_unpaint Ha_unpaint
      "Hunpaint_code" "Hfreecode_cont".
    assert (Haddr8 : a_unpaint =
      allocator_free_block_addr allocator_free_body_addr 8).
    { clear -Ha_unpaint. unfold allocator_free_block_addr in *. solve_addr. }
    subst a_unpaint.
    assert (Hunpaint_eq : allocator_free_body_instrs_n 8 =
      allocator_paint_instrs ctp ca2 ShadowLive) by reflexivity.
    iEval (rewrite Hunpaint_eq) in "Hunpaint_code".
    iApply (allocator_paint_spec ShadowQuarantined ShadowLive ctp ca2 E RX Global
      allocator_pcc_b allocator_pcc_e
      (allocator_free_block_addr allocator_free_body_addr 8) b e sb se
      emp (λ a, addr_alloc a Unclaimed)
      with "[- $HPC $Hctp $Hca2 $Hunpaint_code $Hcells_dead]").
    { reflexivity. }
    { rewrite -Hunpaint_eq. clear -Hpc.
      unfold allocator_free_block_addr in *; cbn in *; solve_addr. }
    { exact Hdisjoint. }
    { clear -Hvalid Hnext. solve_addr. }
    { exact Hshadow. }
    { exact Hlen_shadow. }
    { exact Htranslation. }
    { apply (bool_decide_unpack _). by vm_compute. }
    { right. apply allocator_free_unpaint_ok. }
    iNext. iIntros "(HPC & Hctp & Hca2 & _ & Hcells_free & Hunpaint_code)".
    iEval (rewrite -Hunpaint_eq) in "Hunpaint_code".
    iDestruct ("Hfreecode_cont" with "Hunpaint_code") as "Hfreecode".
    iEval (rewrite -Hsplit8) in "Hfreecode".
    (* Jump to the return. *)
    assert (Hsplit9 : allocator_free_body_instrs =
      concat (encodeInstrsW <$> take 9 assembled_allocator_free_body) ++
      (allocator_free_body_instrs_n 9 ++
       concat (encodeInstrsW <$> drop 10 assembled_allocator_free_body))) by reflexivity.
    iEval (rewrite Hsplit9) in "Hfreecode".
    focus_block_nochangePC 1 "Hfreecode" as a_jmp Ha_jmp
      "Hjmp_code" "Hfreecode_cont".
    assert (Haddr9 : a_jmp =
      allocator_free_block_addr allocator_free_body_addr 9).
    { clear -Ha_jmp. unfold allocator_free_block_addr in *. solve_addr. }
    subst a_jmp.
    assert (Hpc9 : (allocator_free_block_addr allocator_free_body_addr 8 ^+
       length (allocator_paint_instrs ctp ca2 ShadowLive))%a =
       allocator_free_block_addr allocator_free_body_addr 9).
    { clear -Hpc. unfold allocator_free_block_addr in *; cbn in *; solve_addr. }
    iEval (rewrite Hpc9) in "HPC".
    codefrag_facts "Hjmp_code".
    (* Jmp .free_return. *)
    iInstr "Hjmp_code".
    iDestruct ("Hfreecode_cont" with "Hjmp_code") as "Hfreecode".
    iEval (rewrite -Hsplit9) in "Hfreecode".
    (* Return and restore the service invariant. *)
    assert (Hsplit11 : allocator_free_body_instrs =
      concat (encodeInstrsW <$> take 11 assembled_allocator_free_body) ++
      allocator_free_body_instrs_n 11) by reflexivity.
    iEval (rewrite Hsplit11) in "Hfreecode".
    focus_block_nochangePC 1 "Hfreecode" as a_ret Ha_ret
      "Hret_code" "Hfreecode_cont".
    assert (Haddr11 : a_ret =
      allocator_free_block_addr allocator_free_body_addr 11).
    { unfold allocator_free_block_addr. clear -Ha_ret.
      cbn [take concat fmap] in *. solve_addr. }
    subst a_ret.
    match goal with
    | |- context [ WCap true RX Global allocator_pcc_b allocator_pcc_e ?x ] =>
        assert (Hpc11 : x = allocator_free_block_addr allocator_free_body_addr 11)
          by (clear -Hpc; unfold allocator_free_block_addr in *; cbn in *; solve_addr);
        rewrite Hpc11
    end.
    (* Take the registers back from the register file. *)
    iDestruct (big_sepM_insert with "Hregs") as "[Hcgp Hregs]";
      first (simplify_map_eq; apply Hrmap_none; set_solver).
    iDestruct (big_sepM_insert with "Hregs") as "[Hcra Hregs]";
      first (simplify_map_eq; apply Hrmap_none; set_solver).
    iDestruct (big_sepM_insert with "Hregs") as "[Hca0 Hregs]";
      first (simplify_map_eq; apply Hrmap_none; set_solver).
    iDestruct (big_sepM_insert with "Hregs") as "[Hca1 Hregs]";
      first (simplify_map_eq; apply Hrmap_none; set_solver).
    iDestruct (big_sepM_insert with "Hregs") as "[Hct0 Hregs]";
      first (simplify_map_eq; apply Hrmap_none; set_solver).
    iDestruct (big_sepM_insert with "Hregs") as "[Hcnull Hrmap]";
      first (apply Hrmap_none; set_solver).
    assert (Hret_eq : allocator_free_body_instrs_n 11 =
      encodeInstrsW [Jalr cnull cra]) by reflexivity.
    iEval (rewrite Hret_eq) in "Hret_code".
    iApply (allocator_return_spec with
      "[- $HPC $Hcra $Hcnull $Hret_code]").
    { clear -Hpc. unfold allocator_free_block_addr in *; cbn in *; solve_addr. }
    { exact Hdisjoint. }
    iNext. iIntros "(HPC & Hcra & Hcnull & Hret_code & Hlc)".
    iEval (rewrite -Hret_eq) in "Hret_code".
    iDestruct ("Hfreecode_cont" with "Hret_code") as "Hfreecode".
    iEval (rewrite -Hsplit11) in "Hfreecode".
    iDestruct ("Hbody_close" with "Hfreecode") as "Hfreecode".
    iEval (rewrite -allocator_free_instrs_owner_body) in "Hfreecode".
    iDestruct ("Hcode_cont" with "Hfreecode") as "Hcode".
    iEval (rewrite -/allocator_code) in "Hcode".
    iAssert ([[allocator_pcc_b, allocator_code_b]] ↦ₐ [[lword_of_word <$> allocator_imports]])%I
      with "[Hshadow_import Hseal_import Hrevoker_import]" as "Himports".
    { iApply allocator_imports_split. iFrame.
      rewrite /allocator_shadow_import_off.
      assert ((allocator_pcc_b ^+ 0)%a = allocator_pcc_b) as -> by (clear; solve_addr).
      iFrame. }
    (* Return the payload cells as unclaimed, unpainted cells. *)
    iDestruct ("Hcells_close" $! allocator_free_cell
                 with "[Hcells_free Hmem]") as "Hcells".
    { iDestruct (big_sepL2_mono _ (λ _ a _, a ↦ₐ -)%I with "Hmem") as "Hmem".
      { iIntros (k a0 w Ha Hw) "H". by iExists _. }
      iDestruct (big_sepL2_const_sepL_l with "Hmem") as "[_ Hmem]".
      iCombine "Hcells_free Hmem" as "Hcells".
      rewrite -big_sepL_sep.
      iApply (big_sepL_mono with "Hcells").
      iIntros (k x _) "[[Hs Hc] Hm]".
      rewrite /cell_res' /allocator_free_cell /cell_res /=. iFrame. done. }
    iAssert (allocator_service_owners allocations) with "[Howners]" as "Howners".
    { iExists O. by iFrame. }
    iMod ("Hclose" with "[Himports Hcode Hslot Hheaders Htoks_close Hdead Hcells Howners Hna]")
      as "Hna".
    { iFrame "Hna". iNext. iSplitL "Himports Hcode"; first iFrame.
      iExists next, allocations, (live ∖ {[ι]}), issued, _.
      iFrame "Hslot Hheaders Hcells Howners".
      iSplit; first done.
      iSplit; first done.
      iSplit.
      { iPureIntro. eapply allocator_cells_wf_free; eauto. }
      iApply ("Htoks_close" with "[] [Hdead]").
      { iPureIntro. intros ι' Hι'. clear -Hι'. set_solver. }
      rewrite decide_False; last (clear; set_solver).
      iExists ADead. iFrame "Hdead Hq". }
    iApply "Hpost". iFrame "Hna Hid Howner HPC Hcgp Hcra Hca0 Hca1 Hcnull Hrmap Hq Hlc".
    iSplitL "Hca2"; first by iExists _.
    iSplitL "Hct0"; first by iExists _.
    iSplitL "Hct1"; first by iExists _.
    iSplitL "Hct2"; first by iExists _.
    iSplitL "Hct3"; first by iExists _.
    iSplitL "Hct4"; first by iExists _.
    by iExists _.
  Qed.

End AllocatorFree.
