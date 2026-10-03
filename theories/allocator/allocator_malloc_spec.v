From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode memory_region region_keys.
From griotte.allocator Require Import allocator_preamble
  allocator_macros_spec allocator_resource_spec allocator_header_spec.
From griotte.allocator Require Import allocator_malloc_spec_blocks.

(** The top-level specifications of [malloc]. The block specifications are
    in [allocator_malloc_spec_blocks]. *)

Section AllocatorMalloc.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {FA : FreeAuth Σ}
    {MP : MachineParameters} {layout : allocatorLayout}.
  Context {layout_wf : allocatorLayoutWf}.

  (** A noninteger or nonpositive size is rejected before the heap is read.
      Other registers and resources can be framed. *)

  Lemma allocator_malloc_invalid_correct
    (E : coPset) (wreq wret : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    ↑Nallocator_service ⊆ E ->
    ¬ allocator_positive_size wreq.(lw) ->

    ⊢ (

       allocator_service_ctx ∗
       na_own cerise_nais E ∗

       (* Initial register file. *)
       PC ↦ᵣ WCap true RX Global allocator_pcc_b allocator_pcc_e
         allocator_malloc_pcc_addr ∗
       cgp ↦ᵣ WCap true RW Global
         allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ wreq ∗
       ca1 ↦ᵣ - ∗
       ca2 ↦ᵣ - ∗
       ct0 ↦ᵣ - ∗
       ct1 ↦ᵣ - ∗
       ct2 ↦ᵣ - ∗
       ct3 ↦ᵣ - ∗
       ct4 ↦ᵣ - ∗
       ctp ↦ᵣ - ∗
       cnull ↦ᵣ - ∗

       ▷ (na_own cerise_nais E ∗
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
    intros HEservice Hinvalid.
    iIntros "(#Hservice & Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hcnull & Hpost)".
    (* Open the service invariant and recover the allocator code and state. *)
    iMod (na_inv_acc with "Hservice Hna") as "(Hinv & Hna & Hclose)"; try exact HEservice.
    iDestruct "Hinv" as ">[Hstatic Hdata]".
    iDestruct "Hstatic" as "[Himports Hcode]".
    iDestruct "Hdata" as (next) "Hdata".
    iEval (rewrite /allocator_code) in "Hcode".
    focus_block_0 "Hcode" as "Hmalloc_code" "Hcode_cont".
    (* Check the requested size. *)
    assert (Hsplit : allocator_malloc_instrs =
      allocator_malloc_instrs_n 0 ++
      concat (encodeInstrsW <$> drop 1 assembled_allocator_malloc)) by reflexivity.
    iEval (rewrite Hsplit) in "Hmalloc_code".
    focus_block_0 "Hmalloc_code" as "Hcheck_code" "Hmalloc_cont".
    assert (Hpc : SubBounds allocator_pcc_b allocator_pcc_e
      allocator_malloc_pcc_addr (allocator_malloc_pcc_addr ^+ length allocator_malloc_instrs)%a).
    { pose proof allocator_size_code as Hsize_code.
      pose proof allocator_size_imports as Himports_size.
      rewrite /allocator_code length_app in Hsize_code.
      rewrite allocator_imports_length in Himports_size.
      unfold allocator_malloc_pcc_addr, allocator_malloc_pcc_off in *.
      solve_addr. }
    assert (Hdisjoint : disjoint_from_shadow allocator_pcc_b allocator_pcc_e).
    { pose proof allocator_regions_disjoint as Hregions.
      unfold disjoint_from_shadow.
      rewrite !disjoint_list_cons in Hregions.
      cbn [union_list] in Hregions.
      set_solver. }
    assert (Hstart : allocator_code_b = allocator_malloc_pcc_addr).
    { pose proof allocator_size_imports as Hsize.
      rewrite allocator_imports_length in Hsize.
      unfold allocator_malloc_pcc_addr, allocator_malloc_pcc_off in *.
      solve_addr. }
    iDestruct "Hct3" as (w3) "Hct3".
    rewrite Hstart in H0.
    iEval (rewrite Hstart) in "Hcheck_code".
    iApply (allocator_malloc_size_check_invalid_spec with
      "[- $HPC $Hca0 $Hct3 $Hcheck_code]"); eauto.
    { rewrite -Hstart. exact H. }
    iNext. iIntros "(Hca0 & Hct3 & Hcheck_code & HPC)".
    iEval (rewrite -Hstart) in "Hcheck_code".
    iDestruct ("Hmalloc_cont" with "Hcheck_code") as "Hmalloc_code".
    iEval (rewrite -Hsplit) in "Hmalloc_code".
    (* The size check rejects the request; set ALLOC_INVALID. *)
    assert (Hsplit7 : allocator_malloc_instrs =
      concat (encodeInstrsW <$> take 7 assembled_allocator_malloc) ++
      (allocator_malloc_instrs_n 7 ++
       concat (encodeInstrsW <$> drop 8 assembled_allocator_malloc)))
      by reflexivity.
    iEval (rewrite Hsplit7) in "Hmalloc_code".
    focus_block_nochangePC 1 "Hmalloc_code" as a_reject Ha_reject
      "Hreject_code" "Hmalloc_cont".
    assert (Haddr7 : a_reject =
      allocator_malloc_block_addr allocator_malloc_pcc_addr 7).
    { rewrite -Hstart. unfold allocator_malloc_block_addr. solve_addr. }
    subst a_reject.
    iDestruct "Hca1" as (wca1) "Hca1".
    iApply (allocator_malloc_reject_block_spec with
      "[- $HPC $Hca0 $Hca1 $Hreject_code]"); eauto.
    { rewrite -Hstart. exact H. }
    iNext. iIntros "(HPC & Hca0 & Hca1 & Hreject_code)".
    iDestruct ("Hmalloc_cont" with "Hreject_code") as "Hmalloc_code".
    iEval (rewrite -Hsplit7) in "Hmalloc_code".
    (* Return to the caller and restore the service invariant. *)
    assert (Hsplit9 : allocator_malloc_instrs =
      concat (encodeInstrsW <$> take 9 assembled_allocator_malloc) ++
      allocator_malloc_instrs_n 9) by reflexivity.
    iEval (rewrite Hsplit9) in "Hmalloc_code".
    focus_block_nochangePC 1 "Hmalloc_code" as a_ret Ha_ret
      "Hret_code" "Hmalloc_cont".
    assert (Haddr9 : a_ret =
      allocator_malloc_block_addr allocator_malloc_pcc_addr 9).
    { rewrite -Hstart. unfold allocator_malloc_block_addr. solve_addr. }
    subst a_ret.
    assert (Hret_eq : allocator_malloc_instrs_n 9 =
      encodeInstrsW [Jalr cnull cra]) by reflexivity.
    iEval (rewrite Hret_eq) in "Hret_code".
    iDestruct "Hcnull" as (wnull) "Hcnull".
    iApply (allocator_return_spec with
      "[- $HPC $Hcra $Hcnull $Hret_code]"); eauto.
    { unfold allocator_malloc_block_addr in *. cbn. solve_addr. }
    iNext. iIntros "(HPC & Hcra & Hcnull & Hret_code & _)".
    iEval (rewrite -Hret_eq) in "Hret_code".
    iDestruct ("Hmalloc_cont" with "Hret_code") as "Hmalloc_code".
    iEval (rewrite -Hsplit9) in "Hmalloc_code".
    iDestruct ("Hcode_cont" with "Hmalloc_code") as "Hcode".
    iEval (rewrite -/allocator_code) in "Hcode".
    iMod ("Hclose" with "[Himports Hcode Hdata Hna]") as "Hna".
    { iSplitR "Hna"; last iFrame.
      iNext. iSplitL "Himports Hcode"; first iFrame.
      iExists next. iFrame. }
    iApply "Hpost". iFrame "∗".
  Qed.


  (** A positive integer size either exceeds the remaining suffix or obtains
      a fresh, exactly bounded, zeroed allocation [ι ∉ S]. The client gets the
      capability with [ι], [alloc_obj ι b e], [free_auth_held ι] and the cells
      of [ι] with their shares; no receipt. The bump cursor stays hidden in
      the service invariant. *)

  Lemma allocator_malloc_valid_correct
    (S : gset AId) (E : coPset) (n : Z) (wret : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    ↑Nallocator_service ⊆ E ->
    (0 < n)%Z ->

    ⊢ (

       allocator_service_ctx ∗
       na_own cerise_nais E ∗

       (* Initial register file. *)
       PC ↦ᵣ WCap true RX Global allocator_pcc_b allocator_pcc_e
         allocator_malloc_pcc_addr ∗
       cgp ↦ᵣ WCap true RW Global
         allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ WInt n ∗
       ca1 ↦ᵣ - ∗
       ca2 ↦ᵣ - ∗
       ct0 ↦ᵣ - ∗
       ct1 ↦ᵣ - ∗
       ct2 ↦ᵣ - ∗
       ct3 ↦ᵣ - ∗
       ct4 ↦ᵣ - ∗
       ctp ↦ᵣ - ∗
       cnull ↦ᵣ - ∗

       ▷ (na_own cerise_nais E ∗
          PC ↦ᵣ lupdatePcPerm wret ∗
          cgp ↦ᵣ WCap true RW Global
            allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
          cra ↦ᵣ wret ∗
          ca2 ↦ᵣ - ∗
          ct0 ↦ᵣ - ∗
          ct1 ↦ᵣ - ∗
          ct2 ↦ᵣ - ∗
          ct3 ↦ᵣ - ∗
          ct4 ↦ᵣ - ∗
          ctp ↦ᵣ - ∗
          cnull ↦ᵣ WInt 0 ∗

          ((ca0 ↦ᵣ WInt ALLOC_NO_MEMORY ∗
            ca1 ↦ᵣ WInt 0)
           ∨ (∃ (ι : AId) (b e : Addr),
                ⌜(heap_b < b /\ b < e /\ e <= heap_e)%a ∧
                  (e - b = n)%Z⌝ ∗
                ⌜ι ∉ S⌝ ∗
                ca0 ↦ᵣ (WCap true RW Global b e b) @@ ι ∗
                ca1 ↦ᵣ WInt 0 ∗
                alloc_obj ι b e ∗
                free_auth_held ι ∗
                [[b, e]] ↦ₕ[ι] [[region_addrs_zeroes b e]]))

          -∗ WP Seq (Instr Executable) @ E {{ φ }})
       -∗ WP Seq (Instr Executable) @ E {{ φ }})%I.
  Proof.
    intros HEservice Hpositive.
    iIntros "(#Hservice & Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 &
      Hct3 & Hct4 & Hctp & Hcnull & Hpost)".
    (* Open the service invariant and recover the allocator code and state. *)
    iMod (na_inv_acc with "Hservice Hna") as "(Hinv & Hna & Hclose)"; try exact HEservice.
    iDestruct "Hinv" as ">[Hstatic Hdata]".
    iDestruct "Hstatic" as "[Himports Hcode]".
    iDestruct "Hdata" as (next allocations live issued Cs)
      "(%Hnext & Hslot & Hheaders & %Hwf & %Hcwf & Htoks & Hcells)".
    iEval (rewrite /allocator_code) in "Hcode".
    focus_block_0 "Hcode" as "Hmalloc_code" "Hcode_cont".
    (* Check the requested size. *)
    assert (Hsplit : allocator_malloc_instrs =
      allocator_malloc_instrs_n 0 ++
      concat (encodeInstrsW <$> drop 1 assembled_allocator_malloc)) by reflexivity.
    iEval (rewrite Hsplit) in "Hmalloc_code".
    focus_block_0 "Hmalloc_code" as "Hcheck_code" "Hmalloc_cont".
    assert (Hpc : SubBounds allocator_pcc_b allocator_pcc_e
      allocator_malloc_pcc_addr
      (allocator_malloc_pcc_addr ^+ length allocator_malloc_instrs)%a).
    { pose proof allocator_size_code as Hsize_code.
      pose proof allocator_size_imports as Himports_size.
      rewrite /allocator_code length_app in Hsize_code.
      rewrite allocator_imports_length in Himports_size.
      unfold allocator_malloc_pcc_addr, allocator_malloc_pcc_off in *.
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
    assert (Hstart : allocator_code_b = allocator_malloc_pcc_addr).
    { pose proof allocator_size_imports as Hsize.
      rewrite allocator_imports_length in Hsize.
      unfold allocator_malloc_pcc_addr, allocator_malloc_pcc_off in *.
      solve_addr. }
    iDestruct "Hct3" as (w3) "Hct3".
    rewrite Hstart in H0.
    iEval (rewrite Hstart) in "Hcheck_code".
    assert (Hsize : allocator_positive_size (WInt n)).
    { exists n. split; [reflexivity|exact Hpositive]. }
    iApply (allocator_malloc_size_check_valid_spec with
      "[- $HPC $Hca0 $Hct3 $Hcheck_code]"); eauto.
    { rewrite -Hstart. exact H. }
    iNext. iIntros "(Hca0 & Hct3 & Hcheck_code & HPC)".
    iEval (rewrite -Hstart) in "Hcheck_code".
    iDestruct ("Hmalloc_cont" with "Hcheck_code") as "Hmalloc_code".
    iEval (rewrite -Hsplit) in "Hmalloc_code".
    (* Prepare the allocation, branching on the remaining capacity. *)
    assert (Hsplit1 : allocator_malloc_instrs =
      concat (encodeInstrsW <$> take 1 assembled_allocator_malloc) ++
      (allocator_malloc_instrs_n 1 ++
       concat (encodeInstrsW <$> drop 2 assembled_allocator_malloc)))
      by reflexivity.
    iEval (rewrite Hsplit1) in "Hmalloc_code".
    focus_block_nochangePC 1 "Hmalloc_code" as a_prepare Ha_prepare
      "Hprepare_code" "Hmalloc_cont".
    assert (Haddr1 : a_prepare =
      allocator_malloc_block_addr allocator_malloc_pcc_addr 1).
    { rewrite -Hstart. unfold allocator_malloc_block_addr. solve_addr. }
    subst a_prepare.
    iDestruct "Hct0" as (w0) "Hct0".
    iDestruct "Hct1" as (w1) "Hct1".
    iDestruct "Hct2" as (w2) "Hct2".
    iDestruct "Hct3" as (w3b) "Hct3".
    iDestruct "Hct4" as (w4) "Hct4".
    iDestruct "Hca2" as (wa2) "Hca2".
    iDestruct (allocator_headers_chain_spec with "Hheaders") as %Hchain.
    destruct (decide (n + allocator_header_words <= heap_e - next)%Z) as [Hroom|Hoom].
    - unfold allocator_header_words in Hroom.
      pose proof heap_valid as Hheap_valid.
      assert (Hbase : (next + allocator_header_words)%a = Some (next ^+ 3)%a)
        by (unfold allocator_header_words; solve_addr).
      assert (Hfinish : ((next ^+ 3)%a + n)%a = Some ((next ^+ 3)%a ^+ n)%a) by solve_addr.
      assert (Hrange : (next < (next ^+ 3) /\ (next ^+ 3) < ((next ^+ 3) ^+ n)
                        /\ ((next ^+ 3) ^+ n) <= heap_e)%a) by solve_addr.
      set (b := (next ^+ 3)%a) in *.
      set (finish := (b ^+ n)%a) in *.
      clearbody b finish.
      (* Take the cells of the new chunk: the cursor clause says they are
         unclaimed, unpainted and not headers. *)
      iDestruct (allocator_cells_range_acc (finz.seq_between next finish)
                   (λ _, (Unclaimed, ShadowLive, false)) with "Hcells")
        as "[Hchunk Hcells_close]".
      { apply finz_seq_between_NoDup. }
      { intros a Ha. apply elem_of_finz_seq_between in Ha.
        apply (acw_cursor _ _ _ _ _ Hcwf). solve_addr. }
      assert (Hsplit_range : (next <= b /\ b <= finish)%a) by solve_addr.
      iEval (rewrite (finz_seq_between_split next b finish Hsplit_range) big_sepL_app)
        in "Hchunk".
      iDestruct "Hchunk" as "[Hhdr_cells Hpay_cells]".
      iEval (rewrite /cell_res' /cell_res /=) in "Hhdr_cells Hpay_cells".
      iDestruct (big_sepL_sep with "Hhdr_cells") as "[Hhdr_claims Hhdr_cells]".
      iDestruct (big_sepL_sep with "Hhdr_cells") as "[Hhdr_shadow Hhdr_mem]".
      iDestruct (big_sepL_sep with "Hpay_cells") as "[Hpay_claims Hpay_cells]".
      iDestruct (big_sepL_sep with "Hpay_cells") as "[Hpay_shadow Hpay_mem]".
      iAssert (allocator_range_memory next b) with "[Hhdr_mem]" as "Hhdr_mem".
      { iApply (big_sepL_mono with "Hhdr_mem"). iIntros (k a _) "[_ $]". }
      iAssert (allocator_range_memory b finish) with "[Hpay_mem]" as "Hpay_mem".
      { iApply (big_sepL_mono with "Hpay_mem"). iIntros (k a _) "[_ $]". }
      iCombine "Hpay_shadow Hpay_claims" as "Hpayload".
      rewrite -big_sepL_sep.
      (* Allocate a fresh [ι ∉ S ∪ issued] and write the header. *)
      iApply (allocator_malloc_prepare_success_spec _ _ _ _ next b finish n (S ∪ issued) with
        "[- $HPC $Hcgp $Hca0 $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hca2 $Hslot $Hhdr_mem $Hpayload
            $Hprepare_code]"); eauto.
      { rewrite -Hstart. exact H. }
      { solve_addr. }
      { solve_addr. }
      iNext. iIntros (ι) "(%Hι & #Hobj & Htok & Hpayload & Hhead & Hslot & Hcgp & Hca0 & Hct0 &
        Hct1 & Hct2 & Hct3 & Hct4 & Hca2 & HPC & Hprepare_code)".
      apply not_elem_of_union in Hι as [HιS Hιissued].
      iDestruct ("Hmalloc_cont" with "Hprepare_code") as "Hmalloc_code".
      iEval (rewrite -Hsplit1) in "Hmalloc_code".
      (* Zero the newly allocated addresses. *)
      assert (Hsplit2 : allocator_malloc_instrs =
        concat (encodeInstrsW <$> take 2 assembled_allocator_malloc) ++
        (allocator_malloc_instrs_n 2 ++
         concat (encodeInstrsW <$> drop 3 assembled_allocator_malloc)))
        by reflexivity.
      iEval (rewrite Hsplit2) in "Hmalloc_code".
      focus_block_nochangePC 1 "Hmalloc_code" as a_zero Ha_zero
        "Hzero_code" "Hmalloc_cont".
      assert (Haddr2 : a_zero =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 2).
      { rewrite -Hstart. unfold allocator_malloc_block_addr.
        clear -Ha_zero. cbn [take concat fmap] in *. solve_addr. }
      subst a_zero.
      assert (Hzero_eq : allocator_malloc_instrs_n 2 =
        allocator_zero_instrs ca2 ct2 ct3) by reflexivity.
      iEval (rewrite Hzero_eq) in "Hzero_code".
      iApply (allocator_zero_spec ca2 ct2 ct3 E RX Global
        allocator_pcc_b allocator_pcc_e
        (allocator_malloc_block_addr allocator_malloc_pcc_addr 2)
        RW Global b finish (Some ι) (WInt 0)
        with "[- $HPC $Hca2 $Hct2 $Hct3 $Hzero_code $Hpay_mem]").
      { reflexivity. }
      { unfold allocator_malloc_block_addr; cbn; solve_addr. }
      { exact Hdisjoint. }
      { reflexivity. }
      { solve_addr. }
      { vm_compute;
        repeat (constructor;
          [rewrite !elem_of_cons elem_of_nil; intuition congruence|]);
        constructor.
        { apply not_elem_of_nil. }
        { constructor. } }
      iNext. iIntros "(HPC & Hca2 & Hct2 & Hct3 & Hzeros & Hzero_code)".
      iEval (rewrite -Hzero_eq) in "Hzero_code".
      iDestruct ("Hmalloc_cont" with "Hzero_code") as "Hmalloc_code".
      iEval (rewrite -Hsplit2) in "Hmalloc_code".
      (* Fetch the shadow capability and translate the allocated bounds. *)
      assert (Hsplit3 : allocator_malloc_instrs =
        concat (encodeInstrsW <$> take 3 assembled_allocator_malloc) ++
        (allocator_malloc_instrs_n 3 ++
         concat (encodeInstrsW <$> drop 4 assembled_allocator_malloc)))
        by reflexivity.
      iEval (rewrite Hsplit3) in "Hmalloc_code".
      focus_block_nochangePC 1 "Hmalloc_code" as a_fetch Ha_fetch
        "Hfetch_code" "Hmalloc_cont".
      assert (Haddr3 : a_fetch =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 3).
      { rewrite -Hstart. unfold allocator_malloc_block_addr.
        clear -Ha_fetch. cbn [take concat fmap] in *. solve_addr. }
      subst a_fetch.
      assert (Hpc3 : (allocator_malloc_block_addr allocator_malloc_pcc_addr 2 ^+
        length (allocator_zero_instrs ca2 ct2 ct3))%a =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 3).
      { unfold allocator_malloc_block_addr. clear -Hpc. solve_addr. }
      iEval (rewrite Hpc3) in "HPC".
      pose proof allocator_size_imports as Himports_size.
      rewrite allocator_imports_length in Himports_size.
      assert (Himpnext : (allocator_pcc_b + 1)%a = Some (allocator_pcc_b ^+ 1)%a) by solve_addr.
      assert (Himpend : (allocator_pcc_b ^+ 1 <= allocator_code_b)%a) by solve_addr.
      iEval (rewrite /allocator_imports fmap_cons
        (region_pointsto_cons allocator_pcc_b (allocator_pcc_b ^+ 1)%a
          allocator_code_b _ _ Himpnext Himpend)) in "Himports".
      iDestruct "Himports" as "[Himport Hkey]".
      assert (Hfetch_eq : allocator_malloc_instrs_n 3 =
        fetch.fetch_instrs allocator_shadow_import_off ctp ct3 ca2)
        by reflexivity.
      iEval (rewrite Hfetch_eq) in "Hfetch_code".
      iDestruct "Hctp" as (wctp) "Hctp".
      assert (Himpaddr : (allocator_pcc_b ^+ allocator_shadow_import_off)%a =
        allocator_pcc_b)
        by (unfold allocator_shadow_import_off; solve_addr).
      iEval (rewrite -Himpaddr) in "Himport".
      iApply (allocator_fetch_spec with
        "[- $HPC $Hctp $Hct3 $Hca2 $Hfetch_code $Himport]").
      { reflexivity. }
      { rewrite -Hfetch_eq;
        unfold allocator_malloc_block_addr; cbn; solve_addr. }
      { apply withinBounds_true_iff; solve_addr. }
      { exact Hdisjoint. }
      { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=.
        destruct (is_heap_address shadow_b) eqn:Hheap; last reflexivity.
        exfalso. unfold is_heap_address in Hheap.
        apply withinBounds_true_iff in Hheap;
        pose proof heap_shadow_disjoint as Hd;
        rewrite /disjoint_from_shadow elem_of_disjoint in Hd;
        apply (Hd shadow_b); apply elem_of_finz_seq_between;
        try exact Hheap;
        pose proof shadow_valid; solve_addr. }
      { discriminate. }
      { discriminate. }
      { discriminate. }
      iNext. iIntros "(HPC & Hctp & Hct3 & Hca2 & Himport & Hfetch_code)".
      iEval (cbn) in "Hctp".
      iEval (rewrite Himpaddr) in "Himport".
      iAssert ([[allocator_pcc_b,allocator_code_b]] ↦ₐ
                 [[lword_of_word <$> allocator_imports]])%I
        with "[Himport Hkey]" as "Himports".
      { rewrite /allocator_imports fmap_cons
          (region_pointsto_cons allocator_pcc_b (allocator_pcc_b ^+ 1)%a
            allocator_code_b _ _ Himpnext Himpend).
        iFrame. }
      iEval (rewrite -Hfetch_eq) in "Hfetch_code".
      iDestruct ("Hmalloc_cont" with "Hfetch_code") as "Hmalloc_code".
      iEval (rewrite -Hsplit3) in "Hmalloc_code".
      assert (Hsplit4 : allocator_malloc_instrs =
        concat (encodeInstrsW <$> take 4 assembled_allocator_malloc) ++
        (allocator_malloc_instrs_n 4 ++
         concat (encodeInstrsW <$> drop 5 assembled_allocator_malloc)))
        by reflexivity.
      iEval (rewrite Hsplit4) in "Hmalloc_code".
      focus_block_nochangePC 1 "Hmalloc_code" as a_translate Ha_translate
        "Htranslate_code" "Hmalloc_cont".
      assert (Haddr4 : a_translate =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 4).
      { rewrite -Hstart. unfold allocator_malloc_block_addr.
        clear -Ha_translate. cbn [take concat fmap] in *. solve_addr. }
      subst a_translate.
      assert (Hpc4 : (allocator_malloc_block_addr allocator_malloc_pcc_addr 3 ^+
        length (fetch.fetch_instrs allocator_shadow_import_off ctp ct3 ca2))%a =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 4).
      { unfold allocator_malloc_block_addr. solve_addr. }
      iEval (rewrite Hpc4) in "HPC".
      iApply (allocator_translate_spec E allocator_pcc_b allocator_pcc_e
        (allocator_malloc_block_addr allocator_malloc_pcc_addr 4) next b finish with
        "[- $HPC $Hct0 $Hct1 $Hct2 $Hct3 $Hctp $Hca2 $Htranslate_code]").
      { unfold allocator_malloc_block_addr; cbn; solve_addr. }
      { exact Hdisjoint. }
      { solve_addr. }
      iNext. iIntros
        "(HPC & Hct0 & Hct1 & Hct2 & Hct3 & Hctp & Hca2 & Htranslate_code)".
      iDestruct ("Hmalloc_cont" with "Htranslate_code") as "Hmalloc_code".
      iEval (rewrite -Hsplit4) in "Hmalloc_code".
      (* The same-value shadow store over the cells claimed by [ι]. *)
      assert (Hsplit5 : allocator_malloc_instrs =
        concat (encodeInstrsW <$> take 5 assembled_allocator_malloc) ++
        (allocator_malloc_instrs_n 5 ++
         concat (encodeInstrsW <$> drop 6 assembled_allocator_malloc)))
        by reflexivity.
      iEval (rewrite Hsplit5) in "Hmalloc_code".
      focus_block_nochangePC 1 "Hmalloc_code" as a_paint Ha_paint
        "Hpaint_code" "Hmalloc_cont".
      assert (Haddr5 : a_paint =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 5).
      { rewrite -Hstart. unfold allocator_malloc_block_addr.
        clear -Ha_paint. cbn [take concat fmap] in *. solve_addr. }
      subst a_paint.
      assert (Hpc5 : (allocator_malloc_block_addr allocator_malloc_pcc_addr 4 ^+
        length (allocator_malloc_instrs_n 4))%a =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 5).
      { unfold allocator_malloc_block_addr. solve_addr. }
      iEval (rewrite Hpc5) in "HPC".
      pose (sb := (shadow_b ^+ (b - heap_b))%a).
      pose (se := (shadow_b ^+ (finish - heap_b))%a).
      pose proof heap_shadow_same_size as Hss.
      assert (Hshadow : (shadow_b <= sb /\ sb < se /\ se <= shadow_e)%a).
      { unfold sb, se. clear -Hss Hrange Hnext Hheap_valid. solve_addr. }
      assert (Hlen_shadow : (se - sb = finish - b)%Z).
      { unfold sb, se. clear -Hss Hrange Hnext Hheap_valid. solve_addr. }
      assert (Htranslation : ∀ x, (b <= x /\ x < finish)%a ->
        heap_to_shadow x = Some (sb ^+ (x - b))%a).
      { intros x Hx. rewrite allocator_translation_affine.
        unfold translate_region.
        assert (Hxheap : withinBounds heap_b heap_e x = true).
        { apply withinBounds_true_iff. clear -Hx Hrange Hnext. solve_addr. }
        rewrite Hxheap. unfold sb.
        clear -Hx Hrange Hnext Hheap_valid Hss. solve_addr. }
      assert (Hpaint_eq : allocator_malloc_instrs_n 5 =
        allocator_paint_instrs ctp ca2 ShadowLive) by reflexivity.
      iEval (rewrite Hpaint_eq) in "Hpaint_code".
      iApply (allocator_paint_spec ShadowLive ShadowLive ctp ca2 E RX Global
        allocator_pcc_b allocator_pcc_e
        (allocator_malloc_block_addr allocator_malloc_pcc_addr 5)
        b finish sb se emp (λ a, addr_alloc a (Claimed ι))
        with "[- $HPC $Hctp $Hca2 $Hpaint_code $Hpayload]").
      { reflexivity. }
      { rewrite -Hpaint_eq. clear -Hpc.
        unfold allocator_malloc_block_addr in *; cbn in *; solve_addr. }
      { exact Hdisjoint. }
      { clear -Hrange Hnext. solve_addr. }
      { exact Hshadow. }
      { exact Hlen_shadow. }
      { exact Htranslation. }
      { vm_compute;
        repeat (constructor;
          [rewrite !elem_of_cons elem_of_nil; intuition congruence|]);
        try apply not_elem_of_nil; constructor.
        { apply not_elem_of_nil. }
        { constructor. } }
      { by left. }
      iNext. iIntros "(HPC & Hctp & Hca2 & _ & Hpayload & Hpaint_code)".
      iEval (rewrite -Hpaint_eq) in "Hpaint_code".
      iDestruct ("Hmalloc_cont" with "Hpaint_code") as "Hmalloc_code".
      iEval (rewrite -Hsplit5) in "Hmalloc_code".
      clear Hsplit Hsplit1 Hsplit2 Hsplit3 Hsplit4 H0 H1 H2 H3 H4 H5 Ha_prepare Ha_zero
        Ha_fetch Ha_translate Ha_paint Hpc3 Hpc4 Hpc5 Hzero_eq Hfetch_eq Hpaint_eq.
      (* Publish the new bump cursor and return the capability. *)
      assert (Hsplit6 : allocator_malloc_instrs =
        concat (encodeInstrsW <$> take 6 assembled_allocator_malloc) ++
        (allocator_malloc_instrs_n 6 ++
         concat (encodeInstrsW <$> drop 7 assembled_allocator_malloc)))
        by reflexivity.
      iEval (rewrite Hsplit6) in "Hmalloc_code".
      focus_block_nochangePC 1 "Hmalloc_code" as a_publish Ha_publish
        "Hpublish_code" "Hmalloc_cont".
      assert (Haddr6 : a_publish =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 6).
      { rewrite -Hstart. unfold allocator_malloc_block_addr.
        clear -Ha_publish. cbn [take concat fmap] in *. solve_addr. }
      subst a_publish.
      assert (Hpc6 : (allocator_malloc_block_addr allocator_malloc_pcc_addr 5 ^+
        length (allocator_paint_instrs ctp ca2 ShadowLive))%a =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 6).
      { clear -Hpc. unfold allocator_malloc_block_addr in *. cbn in *. solve_addr. }
      iEval (rewrite Hpc6) in "HPC".
      iDestruct "Hca1" as (wca1) "Hca1".
      iApply (allocator_malloc_publish_spec with
        "[- $HPC $Hcgp $Hct0 $Hct4 $Hca0 $Hca1 $Hslot $Hpublish_code]").
      { rewrite -Hstart; exact H. }
      { exact Hpc. }
      { exact Hdisjoint. }
      { exact Hbase. }
      { exact Hfinish. }
      { clear -Hnext Hrange. solve_addr. }
      iNext. iIntros
        "(HPC & Hcgp & Hct0 & Hct4 & Hca0 & Hca1 & Hslot & Hpublish_code)".
      iDestruct ("Hmalloc_cont" with "Hpublish_code") as "Hmalloc_code".
      iEval (rewrite -Hsplit6) in "Hmalloc_code".
      assert (Hsplit9 : allocator_malloc_instrs =
        concat (encodeInstrsW <$> take 9 assembled_allocator_malloc) ++
        allocator_malloc_instrs_n 9) by reflexivity.
      iEval (rewrite Hsplit9) in "Hmalloc_code".
      focus_block_nochangePC 1 "Hmalloc_code" as a_ret Ha_ret
        "Hret_code" "Hmalloc_cont".
      assert (Haddr9 : a_ret =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 9).
      { rewrite -Hstart. unfold allocator_malloc_block_addr.
        clear -Ha_ret. cbn [take concat fmap] in *. solve_addr. }
      subst a_ret.
      assert (Hret_eq : allocator_malloc_instrs_n 9 =
        encodeInstrsW [Jalr cnull cra]) by reflexivity.
      iEval (rewrite Hret_eq) in "Hret_code".
      iDestruct "Hcnull" as (wnull) "Hcnull".
      iApply (allocator_return_spec with
        "[- $HPC $Hcra $Hcnull $Hret_code]").
      { clear -Hpc. unfold allocator_malloc_block_addr in *; cbn in *; solve_addr. }
      { exact Hdisjoint. }
      iNext. iIntros "(HPC & Hcra & Hcnull & Hret_code & _)".
      iEval (rewrite -Hret_eq) in "Hret_code".
      iDestruct ("Hmalloc_cont" with "Hret_code") as "Hmalloc_code".
      iEval (rewrite -Hsplit9) in "Hmalloc_code".
      iDestruct ("Hcode_cont" with "Hmalloc_code") as "Hcode".
      iEval (rewrite -/allocator_code) in "Hcode".
      (* Put the chunk's cells back: header words, then cells claimed by [ι]. *)
      iDestruct ("Hcells_close" $! (allocator_malloc_cell b ι)
                   with "[Hhdr_claims Hhdr_shadow Hpayload]") as "Hcells".
      { iEval (rewrite (finz_seq_between_split next b finish Hsplit_range) big_sepL_app).
        iSplitL "Hhdr_claims Hhdr_shadow".
        - iCombine "Hhdr_claims Hhdr_shadow" as "Hhdr". rewrite -big_sepL_sep.
          iApply (big_sepL_mono with "Hhdr"). iIntros (k a Hk) "[Hc Hs]".
          apply list_elem_of_lookup_2, elem_of_finz_seq_between in Hk.
          rewrite /cell_res' /allocator_malloc_cell decide_True; last solve_addr.
          rewrite /cell_res /=. iFrame.
        - iApply (big_sepL_mono with "Hpayload"). iIntros (k a Hk) "[Hs Hc]".
          apply list_elem_of_lookup_2, elem_of_finz_seq_between in Hk.
          rewrite /cell_res' /allocator_malloc_cell decide_False; last solve_addr.
          rewrite /cell_res /=. iFrame. done. }
      (* Split the status token of [ι] between the allocator, the client half
         and the cells (D17, D35). *)
      iEval (rewrite (st_own_split_alloc ι (finz.seq_between b finish))
        finz_seq_between_length -free_auth_split) in "Htok".
      iDestruct "Htok" as "[[Hkept Hheld] [Hshare Hshares]]".
      assert (Hιids : ι ∉ allocator_entry_ids allocations).
      { intros Hin. apply Hιissued, (acw_issued _ _ _ _ _ Hcwf).
        by apply elem_of_list_to_set. }
      (* Publish the entry of [ι] and restore the service invariant. *)
      iMod ("Hclose" with "[Himports Hcode Hslot Hheaders Hhead Htoks Hkept Hshare Hcells Hna]")
        as "Hna".
      { iFrame "Hna". iNext. iSplitL "Himports Hcode"; first iFrame.
        iExists finish, (allocations ++ [(b, finish, (0%Z, 0%Z), ι)]), (live ∪ {[ι]}),
          (issued ∪ {[ι]}), _.
        iFrame "Hslot Hcells".
        iSplit; first (iPureIntro; clear -Hnext Hrange; solve_addr).
        iSplitL "Hheaders Hhead".
        { iApply (allocator_headers_snoc_spec with "Hheaders Hhead").
          split; [exact Hbase|clear -Hrange; solve_addr]. }
        iSplit; first (iPureIntro; by apply allocator_entries_wf_snoc).
        iSplit.
        { iPureIntro. apply allocator_cells_wf_malloc; try done.
          - exact (proj1 Hnext).
          - clear -Hrange; solve_addr. }
        rewrite allocator_entries_res_app.
        iSplitL "Htoks".
        { iApply (allocator_entries_res_live_ext with "Htoks").
          intros ι' Hι'. assert (ι' ≠ ι) by (intros ->; done). set_solver. }
        rewrite /allocator_entries_res /= /allocator_tok decide_True; last set_solver.
        iFrame "Hobj Hshare Hkept". }
      iApply "Hpost". iFrame "Hna HPC Hcgp Hcra Hcnull".
      iSplitL "Hca2"; first by iExists _.
      iSplitL "Hct0"; first by iExists _.
      iSplitL "Hct1"; first by iExists _.
      iSplitL "Hct2"; first by iExists _.
      iSplitL "Hct3"; first by iExists _.
      iSplitL "Hct4"; first by iExists _.
      iSplitL "Hctp"; first by iExists _.
      iRight. iExists ι, b, finish. iFrame "Hca0 Hca1 Hobj Hheld".
      iSplit.
      { iPureIntro. split; [clear -Hnext Hrange; solve_addr|clear -Hfinish; solve_addr]. }
      iSplit; first done.
      iApply (heap_region_pointsto_split with "Hobj"). iFrame "Hshares".
      rewrite /region_addrs_zeroes /region_pointsto
        -(finz_seq_between_length b finish) big_sepL2_replicate_r;
        last reflexivity.
      iFrame.
    - assert (Hcapacity : (heap_e - next - allocator_header_words < n)%Z) by lia.
      iApply (allocator_malloc_prepare_oom_spec with
        "[- $HPC $Hcgp $Hca0 $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hca2 $Hslot $Hprepare_code]");
        eauto.
      { rewrite -Hstart. exact H. }
      iNext. iIntros
        "(Hslot & Hcgp & Hca0 & Hct0 & Hct1 & Hprepare_code & HPC & Hct2 & Hct3 & Hct4 & Hca2)".
      iDestruct ("Hmalloc_cont" with "Hprepare_code") as "Hmalloc_code".
      iEval (rewrite -Hsplit1) in "Hmalloc_code".
      (* Capacity is exhausted; return ALLOC_NO_MEMORY without changing the state. *)
      assert (Hsplit8 : allocator_malloc_instrs =
        concat (encodeInstrsW <$> take 8 assembled_allocator_malloc) ++
        (allocator_malloc_instrs_n 8 ++ allocator_malloc_instrs_n 9))
        by reflexivity.
      iEval (rewrite Hsplit8) in "Hmalloc_code".
      focus_block_nochangePC 1 "Hmalloc_code" as a_oom Ha_oom
        "Hoom_code" "Hmalloc_cont".
      assert (Haddr8 : a_oom =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 8).
      { rewrite -Hstart. unfold allocator_malloc_block_addr.
        clear -Ha_oom. cbn [take concat fmap] in *. solve_addr. }
      subst a_oom.
      iDestruct "Hca1" as (wca1) "Hca1".
      iApply (allocator_malloc_oom_block_spec with
        "[- $HPC $Hca0 $Hca1 $Hoom_code]").
      { rewrite -Hstart; exact H. }
      { exact Hpc. }
      { exact Hdisjoint. }
      iNext. iIntros "(HPC & Hca0 & Hca1 & Hoom_code)".
      iDestruct ("Hmalloc_cont" with "Hoom_code") as "Hmalloc_code".
      iEval (rewrite -Hsplit8) in "Hmalloc_code".
      assert (Hsplit9 : allocator_malloc_instrs =
        concat (encodeInstrsW <$> take 9 assembled_allocator_malloc) ++
        allocator_malloc_instrs_n 9) by reflexivity.
      iEval (rewrite Hsplit9) in "Hmalloc_code".
      focus_block_nochangePC 1 "Hmalloc_code" as a_ret Ha_ret
        "Hret_code" "Hmalloc_cont".
      assert (Haddr9 : a_ret =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 9).
      { rewrite -Hstart. unfold allocator_malloc_block_addr.
        clear -Ha_ret. cbn [take concat fmap] in *. solve_addr. }
      subst a_ret.
      assert (Hret_eq : allocator_malloc_instrs_n 9 =
        encodeInstrsW [Jalr cnull cra]) by reflexivity.
      iEval (rewrite Hret_eq) in "Hret_code".
      iDestruct "Hcnull" as (wnull) "Hcnull".
      iApply (allocator_return_spec with
        "[- $HPC $Hcra $Hcnull $Hret_code]").
      { clear -Hpc. unfold allocator_malloc_block_addr in *; cbn in *; solve_addr. }
      { exact Hdisjoint. }
      iNext. iIntros "(HPC & Hcra & Hcnull & Hret_code & _)".
      iEval (rewrite -Hret_eq) in "Hret_code".
      iDestruct ("Hmalloc_cont" with "Hret_code") as "Hmalloc_code".
      iEval (rewrite -Hsplit9) in "Hmalloc_code".
      iDestruct ("Hcode_cont" with "Hmalloc_code") as "Hcode".
      iEval (rewrite -/allocator_code) in "Hcode".
      iMod ("Hclose" with "[Himports Hcode Hslot Hheaders Htoks Hcells Hna]") as "Hna".
      { iFrame "Hna". iNext. iSplitL "Himports Hcode"; first iFrame.
        iExists next, allocations, live, issued, Cs. iFrame. done. }
      iApply "Hpost". iFrame.
  Qed.

End AllocatorMalloc.
