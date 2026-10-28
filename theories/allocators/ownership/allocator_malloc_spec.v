From iris.proofmode Require Import proofmode.
From griotte Require Import switcher_namespace rules proofmode memory_region region_keys.
From griotte.allocators.ownership Require Import allocator_header_spec allocator_malloc_spec_states allocator_malloc_spec_world allocator_malloc_spec_owner_blocks_1 allocator_malloc_spec_size_check_blocks_2 allocator_malloc_spec_prepare_blocks_3 allocator_malloc_spec_publish_blocks_4.
From griotte.allocators.common Require Import allocator_common_malloc_spec_shadow_blocks.

(** The top-level specifications of [malloc]. They compose the block groups
    of [allocator_malloc_spec_<segment>_blocks_<n>], those of the shared code in
    [allocator_common_malloc_spec_shadow_blocks] and
    [allocator_common_malloc_spec_exit_blocks], and the logical steps of
    [allocator_malloc_spec_world]. *)

Section AllocatorMalloc.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} {th : Thread} {FA : FreeAuth Σ}
    {allocator_ownerg : allocatorOwnerG Σ}
    {MP : MachineParameters} {layout : allocatorLayout}.
  Context {layout_wf : allocatorLayoutWf}.

  (** A noninteger or nonpositive size in [ca1] is rejected before the heap
      is read. The owner word of the allocator capability in [ca0] is only
      read. Other registers and resources can be framed. *)

  Lemma allocator_malloc_invalid_correct
    (E F : coPset) (g_owner : Locality) (a_owner : Addr) (o : Z) (wreq wret : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    ↑Nallocator_service ⊆ E ->
    ↑Nallocator_service ⊆ F ->
    is_shadow_address a_owner = false ->
    withinBounds a_owner (a_owner ^+ 1) a_owner = true ->
    ¬ allocator_positive_size wreq.(lw) ->
    jalr_target_ok cnull cra wret.(lw) = true ->

    ⊢ (

       allocator_service_ctx ∗
       allocator_service_static ∗
       na_own (tpool th) F ∗
       a_owner ↦ₐ WInt o ∗

       (* Initial register file. *)
       PC ↦ₚ[th] Cap RX Global allocator_pcc_b allocator_pcc_e
         allocator_malloc_pcc_addr ∗
       cgp ↦ᵣ[th] Cap RW Global
         allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       cra ↦ᵣ[th] wret ∗
       ca0 ↦ᵣ[th] allocator_capability g_owner a_owner ∗
       ca1 ↦ᵣ[th] wreq ∗
       ca2 ↦ᵣ[th] - ∗
       ct0 ↦ᵣ[th] - ∗
       ct1 ↦ᵣ[th] - ∗
       ct2 ↦ᵣ[th] - ∗
       ca3 ↦ᵣ[th] - ∗
       ca4 ↦ᵣ[th] - ∗
       ctp ↦ᵣ[th] - ∗

       ▷ (na_own (tpool th) F ∗
          a_owner ↦ₐ WInt o ∗
          PC ↦ₚ[th] lupdatePcPerm wret ∗
          cgp ↦ᵣ[th] Cap RW Global
            allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
          cra ↦ᵣ[th] wret ∗
          ca0 ↦ᵣ[th] WInt ALLOC_INVALID ∗
          ca1 ↦ᵣ[th] WInt 0 ∗
          ca2 ↦ᵣ[th] - ∗
          ct0 ↦ᵣ[th] - ∗
          ct1 ↦ᵣ[th] - ∗
          ct2 ↦ᵣ[th] - ∗
          ca3 ↦ᵣ[th] - ∗
          ca4 ↦ᵣ[th] - ∗
          ctp ↦ᵣ[th] -

          -∗ WP Exec @[th] E {{ φ }})
       -∗ WP Exec @[th] E {{ φ }})%I.
  Proof.
    intros HEservice HFservice Hshadow_a Hbounds_a Hinvalid Htgt.
    iIntros "(#Hservice & #Hstatic & Hna & Howner & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 &
      Hct2 & Hct3 & Hct4 & Hctp & Hpost)".
    (* Open the service invariant and focus on the code of [malloc]. *)
    iMod (na_inv_acc with "Hservice Hna") as "(Hinv & Hna & Hclose)";
      [exact HEservice|exact HFservice|].
    iDestruct "Hinv" as ">Hdata".
    iDestruct "Hstatic" as "[#Himports #Hcode]".
    iEval (rewrite /allocator_code allocator_code_b_malloc) in "Hcode".
    focus_block_0 "Hcode" as "Hmalloc_code" "Hcode_cont".
    iEval (rewrite allocator_malloc_instrs_code) in "Hmalloc_code".
    iDestruct (allocator_imports_split_pers with "Himports")
      as "(#Hshadow_import & #Hkey & #Hrevoker_import)".
    iDestruct "Hct3" as (w3) "Hct3".
    iDestruct "Hct4" as (w4) "Hct4".
    iDestruct "Hctp" as (wtp) "Hctp".
    (* Block 0: the owner identifier of the allocator capability. *)
    iApply (allocator_malloc_owner_spec with
      "[- $HPC $Hctp $Hca0 $Hkey $Howner $Hmalloc_code]");
      [apply allocator_malloc_entry_bounds|apply allocator_malloc_pcc_addr_off|done
      |by apply withinBounds_true_iff in Hbounds_a as [_ ?]|].
    iNext. iIntros "(HPC & Hctp & Hca0 & _ & Howner & _)".
    (* Blocks 1 and 5: the size check rejects the request. *)
    iApply (allocator_malloc_size_check_invalid_spec with
      "[- $HPC $Hcra $Hca0 $Hca1 $Hct3 $Hmalloc_code]");
      [apply allocator_malloc_entry_bounds|done|done|].
    iNext. iIntros "(HPC & Hcra & Hca0 & Hca1 & Hct3 & _ & _)".
    (* Close the service invariant. *)
    iMod ("Hclose" with "[$Hna $Hdata]") as "Hna".
    iApply "Hpost". iFrame "∗".
  Qed.

  (** A positive integer size in [ca1] either exceeds the remaining suffix or
      obtains a fresh, exactly bounded, zeroed allocation [ι ∉ S], recorded
      with the owner [id] of the allocator capability in [ca0]. The client
      gets the capability with [ι], [alloc_obj ι b e], [free_auth_held ι], the
      cells of [ι] with their shares and the owner token extended with [ι];
      no receipt. Owner sets only contain issued identifiers, so [ι ∉ Ω].
      The bump cursor stays hidden in the service invariant. *)

  Lemma allocator_malloc_valid_correct
    (S : gset AId) (E F : coPset) (g_owner : Locality) (a_owner : Addr)
    (id : Z) (Ω : gset AId) (n : Z) (πn : option AId) (wret : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    ↑Nallocator_service ⊆ E ->
    ↑Nallocator_service ⊆ F ->
    is_shadow_address a_owner = false ->
    withinBounds a_owner (a_owner ^+ 1) a_owner = true ->
    (0 < n)%Z ->
    jalr_target_ok cnull cra wret.(lw) = true ->

    ⊢ (

       allocator_service_ctx ∗
       allocator_service_static ∗
       na_own (tpool th) F ∗
       allocator_owner_id id Ω ∗
       a_owner ↦ₐ WInt id ∗

       (* Initial register file. *)
       PC ↦ₚ[th] Cap RX Global allocator_pcc_b allocator_pcc_e
         allocator_malloc_pcc_addr ∗
       cgp ↦ᵣ[th] Cap RW Global
         allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       cra ↦ᵣ[th] wret ∗
       ca0 ↦ᵣ[th] allocator_capability g_owner a_owner ∗
       ca1 ↦ᵣ[th] WInt n @@? πn ∗
       ca2 ↦ᵣ[th] - ∗
       ct0 ↦ᵣ[th] - ∗
       ct1 ↦ᵣ[th] - ∗
       ct2 ↦ᵣ[th] - ∗
       ca3 ↦ᵣ[th] - ∗
       ca4 ↦ᵣ[th] - ∗
       ctp ↦ᵣ[th] - ∗

       ▷ (na_own (tpool th) F ∗
          a_owner ↦ₐ WInt id ∗
          PC ↦ₚ[th] lupdatePcPerm wret ∗
          cgp ↦ᵣ[th] Cap RW Global
            allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
          cra ↦ᵣ[th] wret ∗
          ca2 ↦ᵣ[th] - ∗
          ct0 ↦ᵣ[th] - ∗
          ct1 ↦ᵣ[th] - ∗
          ct2 ↦ᵣ[th] - ∗
          ca3 ↦ᵣ[th] - ∗
          ca4 ↦ᵣ[th] - ∗
          ctp ↦ᵣ[th] - ∗

          ((allocator_owner_id id Ω ∗
            ca0 ↦ᵣ[th] WInt ALLOC_NO_MEMORY ∗
            ca1 ↦ᵣ[th] WInt 0)
           ∨ (∃ (ι : AId) (b e : Addr),
                ⌜(heap_b < b /\ b < e /\ e <= heap_e)%a ∧
                  (e - b = n)%Z⌝ ∗
                ⌜ι ∉ S⌝ ∗
                ⌜ι ∉ Ω⌝ ∗
                ca0 ↦ᵣ[th] (Cap RW Global b e b) @@ ι ∗
                ca1 ↦ᵣ[th] WInt 0 ∗
                alloc_obj ι b e ∗
                free_auth_held ι ∗
                allocator_owner_id id (Ω ∪ {[ι]}) ∗
                [[b, e]] ↦ₕ[ι] [[region_addrs_zeroes b e]]))

          -∗ WP Exec @[th] E {{ φ }})
       -∗ WP Exec @[th] E {{ φ }})%I.
  Proof.
    intros HEservice HFservice Hshadow_a Hbounds_a Hpositive Htgt.
    iIntros "(#Hservice & #Hstatic & Hna & Hid & Howner & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hct0 &
      Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hpost)".
    (* Open the service invariant and focus on the code of [malloc]. *)
    iMod (na_inv_acc with "Hservice Hna") as "(Hinv & Hna & Hclose)";
      [exact HEservice|exact HFservice|].
    iDestruct "Hinv" as ">@".
    iDestruct "Hstatic" as "[#Himports #Hcode]".
    iDestruct (allocator_headers_chain_spec with "Hheaders") as %Hchain.
    iEval (rewrite /allocator_code allocator_code_b_malloc) in "Hcode".
    focus_block_0 "Hcode" as "Hmalloc_code" "Hcode_cont".
    iEval (rewrite allocator_malloc_instrs_code) in "Hmalloc_code".
    pose proof allocator_malloc_entry_bounds as Hbounds.
    iDestruct (allocator_imports_split_pers with "Himports")
      as "(#Hshadow_import & #Hkey & #Hrevoker_import)".
    iDestruct "Hca2" as (wa2) "Hca2".
    iDestruct "Hct0" as (w0) "Hct0".
    iDestruct "Hct1" as (w1) "Hct1".
    iDestruct "Hct2" as (w2) "Hct2".
    iDestruct "Hct3" as (w3) "Hct3".
    iDestruct "Hct4" as (w4) "Hct4".
    iDestruct "Hctp" as (wctp) "Hctp".

    (* Block 0: the owner identifier of the allocator capability. *)
    iApply (allocator_malloc_owner_spec with
      "[- $HPC $Hctp $Hca0 $Hkey $Howner $Hmalloc_code]");
      [done|apply allocator_malloc_pcc_addr_off|done
      |by apply withinBounds_true_iff in Hbounds_a as [_ ?]|].
    iNext. iIntros "(HPC & Hctp & Hca0 & _ & Howner & _)".
    (* Block 1: the size check passes. *)
    iApply (allocator_malloc_size_check_valid_spec with "[- $HPC $Hca1 $Hct3 $Hmalloc_code]");
      [done|by exists n|].
    iNext. iIntros "(HPC & Hca1 & Hct3 & _)".
    iDestruct "Hct3" as (w3') "Hct3".
    destruct (decide (n + allocator_header_words <= heap_e - next)%Z) as [Hroom|Hoom].
    - unfold allocator_header_words in Hroom.
      pose proof heap_valid.
      assert (Hbase : (next + allocator_header_words)%a = Some (next ^+ 3))
        by (unfold allocator_header_words; solve_addr).
      assert (Hfinish : ((next ^+ 3) + n)%a = Some ((next ^+ 3) ^+ n)) by solve_addr.
      assert (Hrange : (next < (next ^+ 3) /\ (next ^+ 3) < ((next ^+ 3) ^+ n)
                        /\ ((next ^+ 3) ^+ n) <= heap_e)%a) by solve_addr.
      set (b := next ^+ 3) in *.
      set (finish := b ^+ n) in *.
      clearbody b finish.
      (* Claim the cells of the new chunk for a fresh identifier [ι]. *)
      iMod (allocator_malloc_claim E (S ∪ issued) next b finish with "Hcells")
        as (ι Hι) "(#Hobj & Htok & Hhdr_mem & Hpay_mem & Hheader & Hpayload & Hcells_close)";
        [done|solve_addr|].
      apply not_elem_of_union in Hι as [HιS Hιissued].
      (* Block 2: the capacity check, the payload capability and the header,
         with the owner identifier. *)
      iApply (allocator_malloc_prepare_success_spec with
        "[- $HPC $Hcgp $Hca1 $Hctp $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hca2 $Hslot $Hshadow_import
            $Hhdr_mem $Hobj $Htok $Hmalloc_code]");
        [done|apply allocator_malloc_pcc_addr_off|done|solve_addr|done|done|solve_addr|].
      iNext. iIntros "(HPC & Hcgp & Hca1 & Hctp & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 &
        Hslot & _ & Hhead & Htok & _)".
      (* Block 3, the shadow segment: zero the payload. *)
      iDestruct (allocator_malloc_shadow_acc with "Hmalloc_code")
        as "#Hshadow_code".
      iApply (allocator_malloc_zero_spec with
        "[- $HPC $Hca2 $Htok $Hct2 $Hct3 $Hpay_mem $Hshadow_code]");
        [by apply allocator_malloc_shadow_bounds|solve_addr|].
      iNext. iIntros "(HPC & Hca2 & Htok & Hct2 & Hct3 & Hzeros & _)".
      (* Paint the header and store over the payload. *)
      iApply (allocator_malloc_translate_paint_spec with
        "[- $HPC $Hctp $Hct3 $Hca2 $Hct0 $Hct1 $Hct2 $Hheader $Hpayload
            $Hshadow_code]");
        [by apply allocator_malloc_shadow_bounds|solve_addr|done|solve_addr|].
      iNext. iIntros "(HPC & Hctp & Hct3 & Hca2 & Hct0 & Hct1 & Hct2 & Hheader &
        Hpayload & _)".
      iEval (rewrite (allocator_malloc_shadow_end _ _ _ Hbounds)) in "HPC".
      (* Blocks 4 and 5: publish the bump cursor and return. *)
      iApply (allocator_malloc_publish_spec with
        "[- $HPC $Hcgp $Hcra $Hct0 $Hct4 $Hca0 $Hca1 $Hslot $Hmalloc_code]");
        [done|done|done|solve_addr|done|].
      iNext. iIntros "(HPC & Hcgp & Hcra & Hct0 & Hct4 & Hca0 & Hca1 & Hslot &
        _ & _)".
      (* Publish the entry of [ι], record it for its owner, and close the
         service invariant. *)
      iDestruct ("Hcells_close" with "Hheader Hpayload") as "Hcells".
      iMod (allocator_malloc_publish_entry with
        "Hcells Hslot Hheaders Hhead Htoks Howners Hid Hobj Htok Hzeros")
        as "(Hdata & %HιΩ & Hid & Hheld & Hregion)";
        [solve_addr|done|done|done|done|solve_addr|done|].
      iMod ("Hclose" with "[$Hna Hdata]") as "Hna".
      { iNext. iExists finish. iFrame "Hdata". }
      iApply "Hpost".
      iFrame "Hna Howner HPC Hcgp Hcra Hca2 Hct0 Hct1 Hct2 Hct3 Hct4 Hctp".
      iRight. iExists ι, b, finish. iFrame "Hca0 Hca1 Hobj Hheld Hid Hregion".
      iSplit; first (iPureIntro; split; solve_addr).
      by iSplit.
    - (* Blocks 2 and 5: the heap is exhausted. *)
      iApply (allocator_malloc_prepare_oom_spec with
        "[- $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hca2 $Hslot
            $Hmalloc_code]"); [done|done|done|lia|done|].
      iNext. iIntros "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 &
        Hslot & _)".
      (* Close the service invariant. *)
      iMod ("Hclose" with "[$Hna Hslot Hheaders Htoks Howners Hcells]") as "Hna".
      { iNext. iExists next, allocations, live, issued, Cs. iFrame "∗". done. }
      iApply "Hpost". iFrame "∗". iLeft. iFrame "∗".
  Qed.

  (** A malformed allocator capability in [ca0] traps in the owner block. *)

  Lemma allocator_malloc_invalid_capability_spec
    (E F : coPset) (wsealed : LWord) (P : iProp Σ) :

    ↑Ntstack ⊆ E ->
    (is_sealed_with_o wsealed.(lw) AllocOtype = false \/ get_tag wsealed.(lw) = false) ->

    allocator_service_static ∗
    na_own (tpool th) F ∗
    PC ↦ₚ[th] Cap RX Global allocator_pcc_b allocator_pcc_e
      allocator_malloc_pcc_addr ∗
    ca0 ↦ᵣ[th] wsealed ∗
    ctp ↦ᵣ[th] - ∗
    ca3 ↦ᵣ[th] - ∗
    ca4 ↦ᵣ[th] - ∗
    (∀ a, ⌜a ∈ₐ [allocator_malloc_pcc_addr, allocator_malloc_pcc_addr ^+ length (allocator_owner_instrs allocator_malloc_owner_off ctp ca0))⌝ -∗
      na_own (tpool th) F ∗
      ctp ↦ᵣ[th] - ∗
      ca0 ↦ᵣ[th] wsealed ∗
      ca3 ↦ᵣ[th] - ∗
      ca4 ↦ᵣ[th] - -∗
      trap_safe (Cap RX Global allocator_pcc_b allocator_pcc_e a) E
        (λ v, ⌜v = HaltedV⌝ → P)%I)
    ⊢ WP Exec @[th] E {{ v, ⌜v = HaltedV⌝ → P }}.
  Proof.
    iIntros (HEswitcher Hwsealed)
      "(#Hstatic & Hna & HPC & Hca0 & [%wtp Hctp] & [%w3 Hct3] & [%w4 Hct4] & Hfailed)".
    (* Focus on the code of [malloc]. *)
    iDestruct "Hstatic" as "[#Himports #Hcode]".
    iEval (rewrite /allocator_code allocator_code_b_malloc) in "Hcode".
    focus_block_0 "Hcode" as "Hmalloc_code" "Hcode_cont".
    iEval (rewrite allocator_malloc_instrs_code) in "Hmalloc_code".
    iDestruct (allocator_imports_split_pers with "Himports")
      as "(_ & #Hkey & _)".
    (* Block 0: the owner block traps. *)
    iApply (allocator_malloc_owner_invalid_spec with
      "[$HPC $Hctp $Hca0 $Hkey $Hmalloc_code Hfailed Hna Hct3 Hct4]");
      [exact HEswitcher | apply allocator_malloc_entry_bounds | apply allocator_malloc_pcc_addr_off
      | done |].
    iIntros (a Ha) "[Hctp Hca0]".
    iApply ("Hfailed" with "[//] [$]").
  Qed.

End AllocatorMalloc.
