From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode memory_region region_keys.
From griotte.allocators.no_ownership Require Import allocator_header_spec allocator_malloc_spec_states allocator_malloc_spec_world allocator_malloc_spec_size_check_blocks_1 allocator_malloc_spec_prepare_blocks_2 allocator_malloc_spec_zero_blocks_3 allocator_malloc_spec_translate_paint_blocks_4 allocator_malloc_spec_publish_blocks_5.

(** The top-level specifications of [malloc]. They compose the block groups
    of [allocator_malloc_spec_<segment>_blocks_<n>] and the logical steps of
    [allocator_malloc_spec_world]. *)

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
    iIntros "(#Hservice & Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 &
      Hct3 & Hct4 & Hctp & Hcnull & Hpost)".
    (* Open the service invariant and focus on the code of [malloc]. *)
    iMod (na_inv_acc with "Hservice Hna") as "(Hinv & Hna & Hclose)"; try exact HEservice.
    iDestruct "Hinv" as ">[[Himports Hcode] Hdata]".
    iEval (rewrite /allocator_code allocator_code_b_malloc) in "Hcode".
    focus_block_0 "Hcode" as "Hmalloc_code" "Hcode_cont".
    iEval (rewrite allocator_malloc_instrs_code) in "Hmalloc_code".
    iDestruct "Hca1" as (wca1) "Hca1".
    iDestruct "Hct3" as (w3) "Hct3".
    iDestruct "Hcnull" as (wnull) "Hcnull".
    (* Blocks 0, 9 and 11: the size check rejects the request. *)
    iApply (allocator_malloc_size_check_invalid_spec with
      "[- $HPC $Hcra $Hca0 $Hca1 $Hct3 $Hcnull $Hmalloc_code]");
      [apply allocator_malloc_entry_bounds|done|].
    iNext. iIntros "(HPC & Hcra & Hca0 & Hca1 & Hct3 & Hcnull & Hmalloc_code & _)".
    (* Close the service invariant. *)
    iEval (rewrite -allocator_malloc_instrs_code) in "Hmalloc_code".
    iDestruct ("Hcode_cont" with "Hmalloc_code") as "Hcode".
    iEval (rewrite -allocator_code_b_malloc -/allocator_code) in "Hcode".
    iMod ("Hclose" with "[$Hna $Himports $Hcode $Hdata]") as "Hna".
    iApply "Hpost". iFrame.
  Qed.



  (** A positive integer size either exceeds the remaining suffix or obtains
      a fresh, exactly bounded, zeroed allocation [ι ∉ S]. The client gets the
      capability with [ι], [alloc_obj ι b e], [free_auth_held ι] and the cells
      of [ι] with their shares; no receipt. The bump cursor stays hidden in
      the service invariant. *)

  Lemma allocator_malloc_valid_correct
    (S : gset AId) (E : coPset) (n : Z) (πn : option AId) (wret : LWord)
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
       ca0 ↦ᵣ WInt n @@? πn ∗
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
    (* Open the service invariant and focus on the code of [malloc]. *)
    iMod (na_inv_acc with "Hservice Hna") as "(Hinv & Hna & Hclose)"; try exact HEservice.
    iDestruct "Hinv" as ">[[Himports Hcode] Hdata]".
    iDestruct "Hdata" as (next allocations live issued Cs)
      "(%Hnext & Hslot & Hheaders & %Hwf & %Hcwf & Htoks & Hcells)".
    iDestruct (allocator_headers_chain_spec with "Hheaders") as %Hchain.
    iEval (rewrite /allocator_code allocator_code_b_malloc) in "Hcode".
    focus_block_0 "Hcode" as "Hmalloc_code" "Hcode_cont".
    iEval (rewrite allocator_malloc_instrs_code) in "Hmalloc_code".
    pose proof allocator_malloc_entry_bounds as Hbounds.
    iDestruct "Hca1" as (wca1) "Hca1".
    iDestruct "Hca2" as (wa2) "Hca2".
    iDestruct "Hct0" as (w0) "Hct0".
    iDestruct "Hct1" as (w1) "Hct1".
    iDestruct "Hct2" as (w2) "Hct2".
    iDestruct "Hct3" as (w3) "Hct3".
    iDestruct "Hct4" as (w4) "Hct4".
    iDestruct "Hctp" as (wctp) "Hctp".
    iDestruct "Hcnull" as (wnull) "Hcnull".

    (* Block 0: the size check passes. *)
    iApply (allocator_malloc_size_check_valid_spec with "[- $HPC $Hca0 $Hct3 $Hmalloc_code]");
      [done|by exists n|].
    iNext. iIntros "(HPC & Hca0 & Hct3 & Hmalloc_code)".
    iDestruct "Hct3" as (w3') "Hct3".
    destruct (decide (n + allocator_header_words <= heap_e - next)%Z) as [Hroom|Hoom].
    - unfold allocator_header_words in Hroom.
      pose proof heap_valid.
      assert (Hbase : (next + allocator_header_words)%a = Some (next ^+ 3)%a)
        by (unfold allocator_header_words; solve_addr).
      assert (Hfinish : ((next ^+ 3)%a + n)%a = Some ((next ^+ 3)%a ^+ n)%a) by solve_addr.
      assert (Hrange : (next < (next ^+ 3) /\ (next ^+ 3) < ((next ^+ 3) ^+ n)
                        /\ ((next ^+ 3) ^+ n) <= heap_e)%a) by solve_addr.
      set (b := (next ^+ 3)%a) in *.
      set (finish := (b ^+ n)%a) in *.
      clearbody b finish.
      (* Claim the cells of the new chunk for a fresh identifier [ι]. *)
      iMod (allocator_malloc_claim E (S ∪ issued) next b finish with "Hcells")
        as (ι Hι) "(#Hobj & Htok & Hhdr_mem & Hpay_mem & Hheader & Hpayload & Hcells_close)";
        [done|solve_addr|].
      apply not_elem_of_union in Hι as [HιS Hιissued].
      (* Block 1: the capacity check, the payload capability and the header. *)
      iApply (allocator_malloc_prepare_success_spec with
        "[- $HPC $Hcgp $Hca0 $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hca2 $Hslot $Hhdr_mem $Hobj $Htok
            $Hmalloc_code]"); [done|done|solve_addr|done|done|solve_addr|].
      iNext. iIntros "(HPC & Hcgp & Hca0 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 & Hslot &
        Hhead & Htok & Hmalloc_code)".
      (* Block 2: zero the payload. *)
      iApply (allocator_malloc_zero_spec with
        "[- $HPC $Hca2 $Hct2 $Hct3 $Hpay_mem $Hmalloc_code]"); [done|solve_addr|].
      iNext. iIntros "(HPC & Hca2 & Hct2 & Hct3 & Hzeros & Hmalloc_code)".
      (* Blocks 3-7: paint the header and store over the payload. *)
      iEval (rewrite allocator_imports_split) in "Himports".
      iDestruct "Himports" as "(Hshadow_import & Hseal_import & Hrevoker_import)".
      iApply (allocator_malloc_translate_paint_spec with
        "[- $HPC $Hctp $Hct3 $Hca2 $Hct0 $Hct1 $Hct2 $Hshadow_import $Hheader $Hpayload
            $Hmalloc_code]"); [done|solve_addr|done|solve_addr|].
      iNext. iIntros "(HPC & Hctp & Hct3 & Hca2 & Hct0 & Hct1 & Hct2 & Hshadow_import & Hheader &
        Hpayload & Hmalloc_code)".
      (* Blocks 8 and 11: publish the bump cursor and return. *)
      iApply (allocator_malloc_publish_spec with
        "[- $HPC $Hcgp $Hcra $Hct0 $Hct4 $Hca0 $Hca1 $Hcnull $Hslot $Hmalloc_code]");
        [done|done|done|solve_addr|].
      iNext. iIntros "(HPC & Hcgp & Hcra & Hct0 & Hct4 & Hca0 & Hca1 & Hcnull & Hslot &
        Hmalloc_code & _)".
      (* Publish the entry of [ι] and close the service invariant. *)
      iDestruct ("Hcells_close" with "Hheader Hpayload") as "Hcells".
      iDestruct (allocator_malloc_publish_entry with
        "Hcells Hslot Hheaders Hhead Htoks Hobj Htok Hzeros") as "(Hdata & Hheld & Hregion)";
        [solve_addr|done|done|done|done|solve_addr|done|].
      iEval (rewrite -allocator_malloc_instrs_code) in "Hmalloc_code".
      iDestruct ("Hcode_cont" with "Hmalloc_code") as "Hcode".
      iEval (rewrite -allocator_code_b_malloc -/allocator_code) in "Hcode".
      iMod ("Hclose" with "[$Hna Hshadow_import Hseal_import Hrevoker_import $Hcode Hdata]")
        as "Hna".
      { iNext. iSplitR "Hdata"; last (iExists finish; iFrame).
        iApply allocator_imports_split. iFrame. }
      iApply "Hpost".
      iFrame "Hna HPC Hcgp Hcra Hcnull Hca2 Hct0 Hct1 Hct2 Hct3 Hct4 Hctp".
      iRight. iExists ι, b, finish. iFrame "Hca0 Hca1 Hobj Hheld Hregion".
      iPureIntro. split; [solve_addr|done].
    - (* Blocks 1, 10 and 11: the heap is exhausted. *)
      iApply (allocator_malloc_prepare_oom_spec with
        "[- $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hca2 $Hcnull $Hslot
            $Hmalloc_code]"); [done|done|done|lia|].
      iNext. iIntros "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 &
        Hcnull & Hslot & Hmalloc_code)".
      (* Close the service invariant. *)
      iEval (rewrite -allocator_malloc_instrs_code) in "Hmalloc_code".
      iDestruct ("Hcode_cont" with "Hmalloc_code") as "Hcode".
      iEval (rewrite -allocator_code_b_malloc -/allocator_code) in "Hcode".
      iMod ("Hclose" with "[$Hna $Himports $Hcode Hslot Hheaders Htoks Hcells]") as "Hna".
      { iNext. iExists next, allocations, live, issued, Cs. iFrame. done. }
      iApply "Hpost". iFrame.
  Qed.

End AllocatorMalloc.
