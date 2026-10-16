From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode memory_region region_keys.
From griotte.allocators.ownership Require Import allocator_header_spec allocator_free_spec_states allocator_free_spec_world allocator_free_spec_owner_blocks_1 allocator_free_spec_check_blocks_2 allocator_free_spec_header_blocks_3 allocator_free_spec_return_blocks_4.
From griotte.allocators.common Require Import allocator_common_free_spec_tail_blocks.

(** The top-level specifications of [free]. They compose the block groups
    of [allocator_free_spec_<segment>_blocks_<n>], those of the shared code in
    [allocator_common_free_spec_tail_blocks], and the logical steps of
    [allocator_free_spec_world]. *)

Section AllocatorFree.
  Context {Σ : gFunctors}
    {ceriseg : ceriseG Σ} {FA : FreeAuth Σ} {allocator_ownerg : allocatorOwnerG Σ}
    {MP : MachineParameters}
    {layout : allocatorLayout}.
  Context {layout_wf : allocatorLayoutWf}.

  (** Common call boundary for rejection. [P] carries the evidence for the
      particular rejection and is returned unchanged. The evidence is needed
      only for a request in the allocated prefix whose tag the GetTag of
      [free] reads as set: that read observes the request in [ca1] against
      the cells of the service; the evidence may also use the entries and the
      owner map. The owner word of the allocator capability in [ca0] is only
      read. Other client resources can be framed. *)

  #[local] Lemma allocator_free_reject_correct
    (E : coPset) (g_owner : Locality) (a_owner : Addr) (o : Z)
    (wreq wret : LWord) (P : iProp Σ)
    (φ : language.val griotte_lang → iPropI Σ) :
    (∀ next allocations live issued Cs,
      (heap_b < next /\ next <= heap_e)%a ->
      allocator_chain (heap_b ^+ 1)%a next allocations ->
      allocator_entries_wf allocations ->
      allocator_cells_wf next allocations live issued Cs ->
      allocator_free_in_prefix next wreq.(lw) ->
      allocator_request_observed Cs wreq ->
      P -∗
      allocator_entries_res live allocations -∗
      allocator_service_owners allocations -∗
      allocator_cells Cs -∗
      |~{E}~>
        P ∗
        allocator_entries_res live allocations ∗
        allocator_service_owners allocations ∗
        allocator_cells Cs ∗
        ⌜¬ allocator_free_valid next allocations o wreq.(lw)⌝) ->
    ↑Nallocator_service ⊆ E ->
    is_shadow_address a_owner = false ->
    withinBounds a_owner (a_owner ^+ 1)%a a_owner = true ->
    ⊢ (
       allocator_service_ctx ∗
       allocator_service_static ∗
       na_own cerise_nais E ∗
       P ∗
       a_owner ↦ₐ WInt o ∗
       PC ↦ₚ WCap true RX Global allocator_pcc_b allocator_pcc_e
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
       ca3 ↦ᵣ - ∗
       ca4 ↦ᵣ - ∗
       ctp ↦ᵣ - ∗
       cnull ↦ᵣ - ∗
       ▷ (na_own cerise_nais E ∗
          P ∗
          a_owner ↦ₐ WInt o ∗
          PC ↦ₚ lupdatePcPerm wret ∗
          cgp ↦ᵣ WCap true RW Global
            allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
          cra ↦ᵣ wret ∗
          ca0 ↦ᵣ WInt ALLOC_INVALID ∗
          ca1 ↦ᵣ WInt 0 ∗
          ca2 ↦ᵣ - ∗
          ct0 ↦ᵣ - ∗
          ct1 ↦ᵣ - ∗
          ct2 ↦ᵣ - ∗
          ca3 ↦ᵣ - ∗
          ca4 ↦ᵣ - ∗
          ctp ↦ᵣ - ∗
          cnull ↦ᵣ WInt 0
          -∗ WP Seq (Instr Executable) @ E {{ φ }})
       -∗ WP Seq (Instr Executable) @ E {{ φ }})%I.
  Proof.
    intros Hreject_request HEservice Hshadow_a Hbounds_a.
    iIntros "(#Hservice & #Hstatic & Hna & HP & Howner & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hct0 &
      Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hcnull & Hpost)".
    (* Open the service invariant and focus on the code of [free]. *)
    iMod (na_inv_acc with "Hservice Hna") as "(Hinv & Hna & Hclose)"; try exact HEservice.
    iDestruct "Hinv" as ">@".
    iDestruct "Hstatic" as "[#Himports #Hcode]".
    iDestruct (allocator_headers_chain_spec with "Hheaders") as %Hchain.
    iEval (rewrite /allocator_code) in "Hcode".
    focus_block_nochangePC 1 "Hcode" as a_free Ha_free "Hfree_code" "Hcode_cont".
    assert (a_free = allocator_free_pcc_addr) as ->
      by (pose proof allocator_code_free; solve_addr).
    iEval (rewrite allocator_free_instrs_code) in "Hfree_code".
    pose proof allocator_free_entry_bounds as Hbounds.
    iDestruct (allocator_imports_split_pers with "Himports")
      as "(#Hshadow_import & #Hkey & #Hrevoker_import)".
    iDestruct "Hca2" as (wa2) "Hca2".
    iDestruct "Hct0" as (w0) "Hct0".
    iDestruct "Hct1" as (w1) "Hct1".
    iDestruct "Hct2" as (w2) "Hct2".
    iDestruct "Hct3" as (w3) "Hct3".
    iDestruct "Hct4" as (w4) "Hct4".
    iDestruct "Hctp" as (wtp) "Hctp".
    iDestruct "Hcnull" as (wnull) "Hcnull".
    (* Block 0: the owner identifier of the allocator capability. *)
    iApply (allocator_free_owner_spec with
      "[- $HPC $Hctp $Hca0 $Hkey $Howner $Hfree_code]");
      [done|apply allocator_free_pcc_addr_off|done
      |by apply withinBounds_true_iff in Hbounds_a as [_ ?]|].
    iNext. iIntros "(HPC & Hctp & Hca0 & _ & Howner & _)".
    (* The tail: set ALLOC_INVALID, return and close the service
       invariant. *)
    iAssert (PC ↦ₚ WCap true RX Global allocator_pcc_b allocator_pcc_e
               (allocator_free_pcc_addr ^+ allocator_free_invalid_offset)%a ∗
             cgp ↦ᵣ WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
             ca0 ↦ᵣ WInt o ∗
             ca1 ↦ᵣ wreq ∗
             ca2 ↦ᵣ - ∗ ct0 ↦ᵣ - ∗ ct1 ↦ᵣ - ∗ ct2 ↦ᵣ - ∗ ca3 ↦ᵣ - ∗ ca4 ↦ᵣ - ∗ ctp ↦ᵣ - ∗
             allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
             allocator_headers (heap_b ^+ 1)%a next allocations ∗
             allocator_entries_res live allocations ∗
             allocator_service_owners allocations ∗
             allocator_cells Cs ∗
             P -∗
             WP Seq (Instr Executable) @ E {{ φ }})%I
      with "[- HPC Hca0 Hca1 Hslot Hheaders Htoks Howners Hcells HP Hct0 Hct1 Hct2
               Hct3 Hct4 Hca2 Hctp Hcgp]"
      as "Hreject".
    { iIntros "(HPC & Hcgp & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp &
        Hslot & Hheaders & Htoks & Howners & Hcells & HP)".
      iApply (allocator_free_invalid_spec with "[- $HPC $Hcra $Hca0 $Hca1 $Hcnull $Hfree_code]");
        first done.
      iNext. iIntros "(HPC & Hcra & Hca0 & Hca1 & Hcnull & _ & _)".
      iMod ("Hclose" with "[$Hna Hslot Hheaders Htoks Howners Hcells]") as "Hna".
      { iNext. iExists next, allocations, live, issued, Cs. iFrame "∗". done. }
      iApply "Hpost". iFrame "∗". }
    destruct (decide (allocator_free_in_prefix next wreq.(lw))) as [Hprefix|Hprefix].
    - (* Blocks 1 and 2: the request is a capability in the allocated prefix.
         Its GetTag reads the tag as set, observing the request against the
         cells, or as cleared. *)
      iApply (allocator_free_check_prefix_spec _ _ _ _ _ _ _ _ _ _ _ _ DerefNoId
        (allocator_cells Cs)
        (λ C, ∀ a (x : AddrClaim * AllocStatus * bool), Cs !! a = Some x -> C !! a = Some x.1.1)
        with "[- $Hslot $HPC $Hcgp $Hca0 $Hca1 $Hctp $Hct0 $Hct1 $Hct2 $Hct3 $Hcells
                 $Hfree_code]");
        [done|solve_addr|done| |].
      { iIntros (C) "HC Hcells". iApply (allocator_cells_claims with "HC Hcells"). }
      iNext. iIntros "(Hslot & Hcgp & Hca0 & Hca1 & Hctp & _ & Hcells & _ & [Hvalid | Hcleared])";
        last first.
      { iDestruct "Hcleared" as "(_ & HPC & Hct0 & Hct1 & Hct2 & Hct3)".
        iApply ("Hreject" with "[- ]"). iFrame "∗". }
      iDestruct "Hvalid" as (p g b e a) "(%Hvalid & %Hres & HPC & Hct0 & Hct1 & Hct2 & Hct3)".
      destruct Hvalid as [Heq Hvalid].
      (* The request is invalid. *)
      iMod (Hreject_request next allocations live issued Cs Hnext Hchain Hwf Hcwf
        Hprefix (gettag_result_cells _ _ _ Hres)
        with "HP Htoks Howners Hcells") as "(HP & Htoks & Howners & Hcells & %Hinvalid)".
      assert (Hmissing : ¬ allocator_owned_bounds allocations o b e).
      { intros Hmember. apply Hinvalid. exists p, g, b, e, a. auto. }
      (* Blocks 3 and 4: the local check of the header fails. *)
      iDestruct (allocator_free_header_acc next b e o with "Hcells Hheaders")
        as (s1 s2 eh oh Hcheck Hheader) "(Hs1 & Hs2 & Hhdr & Hheader_close)";
        [solve_addr|done|done|].
      iApply (allocator_free_header_spec with
        "[- $HPC $Hctp $Hct3 $Hct4 $Hca2 $Hct0 $Hct1 $Hct2 $Hshadow_import $Hrevoker_import
            $Hs1 $Hs2 $Hhdr $Hca0 $Hfree_code]");
        [done|apply allocator_free_pcc_addr_off|solve_addr|done|].
      iNext. iIntros "(_ & _ & Hs1 & Hs2 & Hhdr & Hca0 & Hct0 & Hct1 & Hct2 & Hct4 &
        _ & Hout)".
      iDestruct ("Hheader_close" with "Hs1 Hs2 Hhdr") as "[Hcells Hheaders]".
      iDestruct "Hout" as "[(%Hok & _)|(_ & HPC & Hct3 & Hca2 & Hctp)]".
      { exfalso. by apply Hmissing, Hcheck. }
      iApply ("Hreject" with "[- ]"). iFrame "∗".
    - (* Blocks 1 and 2: the request is not a capability in the allocated
         prefix. *)
      iApply (allocator_free_check_invalid_spec with
        "[- $Hslot $HPC $Hcgp $Hca0 $Hca1 $Hctp $Hct0 $Hct1 $Hct2 $Hct3 $Hfree_code]");
        [done|done|].
      iNext. iIntros "(Hslot & Hcgp & Hca0 & Hca1 & Hctp & _ & HPC & Hct0 & Hct1 &
        Hct2 & Hct3)".
      iApply ("Hreject" with "[- ]"). iFrame "∗".
  Qed.

  (** A strict subrange cannot be another allocation in the header chain.
      When the GetTag of [free] reads the tag of the capability in [ca1] as
      set, it observes the cell at its base claimed by [ι], hence the header
      entry of [ι], whose bounds are [b] and [e]. *)

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
       allocator_service_static ∗
       na_own cerise_nais E ∗
       alloc_obj ι b e ∗
       a_owner ↦ₐ WInt o ∗
       PC ↦ₚ WCap true RX Global allocator_pcc_b allocator_pcc_e
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
       ca3 ↦ᵣ - ∗
       ca4 ↦ᵣ - ∗
       ctp ↦ᵣ - ∗
       cnull ↦ᵣ - ∗
       ▷ (na_own cerise_nais E ∗
          a_owner ↦ₐ WInt o ∗
          PC ↦ₚ lupdatePcPerm wret ∗
          cgp ↦ᵣ WCap true RW Global
            allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
          cra ↦ᵣ wret ∗
          ca0 ↦ᵣ WInt ALLOC_INVALID ∗
          ca1 ↦ᵣ WInt 0 ∗
          ca2 ↦ᵣ - ∗
          ct0 ↦ᵣ - ∗
          ct1 ↦ᵣ - ∗
          ct2 ↦ᵣ - ∗
          ca3 ↦ᵣ - ∗
          ca4 ↦ᵣ - ∗
          ctp ↦ᵣ - ∗
          cnull ↦ᵣ WInt 0
          -∗ WP Seq (Instr Executable) @ E {{ φ }})
       -∗ WP Seq (Instr Executable) @ E {{ φ }})%I.

  Proof.
    intros Hbounds Hneq HEservice Hshadow_a Hbounds_a.
    iIntros "(#Hservice & #Hstatic & Hna & #Hobj & Howner & Hrest)".
    iDestruct "Hrest" as "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 &
      Hct3 & Hct4 & Hctp & Hcnull & Hpost)".
    iApply (allocator_free_reject_correct E g_owner a_owner o ((WCap true p g b' e' a) @@ ι) wret
      (alloc_obj ι b e) φ with "[-]"); [|exact HEservice|exact Hshadow_a|exact Hbounds_a|].
    { intros next allocations live issued Cs Hnext Hchain Hwf Hcwf Hprefix Hobs.
      iIntros "#Hobj Htoks Howners Hcells".
      destruct Hprefix as (p0 & g0 & b0 & e0 & a0 & Heq & Hin). cbn in Heq.
      injection Heq as <- <- <- <- <-.
      (* The request is observed at its base: the cell is claimed by [ι]. *)
      destruct (acw_dom _ _ _ _ _ Hcwf b') as [ [ [c s] hdr] Hc]; first solve_addr.
      assert (c = Claimed ι) as ->.
      { refine (Hobs b' _ _ Hc).
        cbn. rewrite decide_True; last solve_addr.
        assert (is_heap_address b' = true) as -> by (apply withinBounds_true_iff; solve_addr).
        done. }
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
    iFrame "Hservice Hstatic Hna Hobj Howner HPC Hcgp Hcra Hca0 Hca1 Hca2 Hct0 Hct1 Hct2 Hct3 Hct4 Hctp
      Hcnull".
    iNext. iIntros "(Hna & _ & Hrest)". iApply "Hpost". iFrame.
  Qed.

  (** An allocation of another owner is rejected: [ι] is not in the owner set
      of [id], the owner of the allocator capability in [ca0], so the header
      entry of [ι], found by the observation of [ca1] at its base by the
      GetTag of [free], records another owner. *)

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
       allocator_service_static ∗
       na_own cerise_nais E ∗
       allocator_owner_id id Ω ∗
       alloc_obj ι b e ∗
       a_owner ↦ₐ WInt id ∗
       PC ↦ₚ WCap true RX Global allocator_pcc_b allocator_pcc_e
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
       ca3 ↦ᵣ - ∗
       ca4 ↦ᵣ - ∗
       ctp ↦ᵣ - ∗
       cnull ↦ᵣ - ∗
       ▷ (na_own cerise_nais E ∗
          allocator_owner_id id Ω ∗
          a_owner ↦ₐ WInt id ∗
          PC ↦ₚ lupdatePcPerm wret ∗
          cgp ↦ᵣ WCap true RW Global
            allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
          cra ↦ᵣ wret ∗
          ca0 ↦ᵣ WInt ALLOC_INVALID ∗
          ca1 ↦ᵣ WInt 0 ∗
          ca2 ↦ᵣ - ∗
          ct0 ↦ᵣ - ∗
          ct1 ↦ᵣ - ∗
          ct2 ↦ᵣ - ∗
          ca3 ↦ᵣ - ∗
          ca4 ↦ᵣ - ∗
          ctp ↦ᵣ - ∗
          cnull ↦ᵣ WInt 0
          -∗ WP Seq (Instr Executable) @ E {{ φ }})
       -∗ WP Seq (Instr Executable) @ E {{ φ }})%I.

  Proof.
    intros HEservice Hshadow_a Hbounds_a HιΩ.
    iIntros "(#Hservice & #Hstatic & Hna & Hid & #Hobj & Howner & Hrest)".
    iDestruct "Hrest" as "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 &
      Hct3 & Hct4 & Hctp & Hcnull & Hpost)".
    iApply (allocator_free_reject_correct E g_owner a_owner id ((WCap true p g b e a) @@ ι) wret
      (allocator_owner_id id Ω ∗ alloc_obj ι b e) φ with "[-]");
      [|exact HEservice|exact Hshadow_a|exact Hbounds_a|].
    { intros next allocations live issued Cs Hnext Hchain Hwf Hcwf Hprefix Hobs.
      iIntros "[Hid #Hobj] Htoks Howners Hcells".
      destruct Hprefix as (p0 & g0 & b0 & e0 & a0 & Heq & Hin). cbn in Heq.
      injection Heq as <- <- <- <- <-.
      (* The request is observed at its base: the cell is claimed by [ι]. *)
      destruct (acw_dom _ _ _ _ _ Hcwf b) as [ [ [c s] hdr] Hc]; first solve_addr.
      assert (c = Claimed ι) as ->.
      { refine (Hobs b _ _ Hc).
        cbn. rewrite decide_True; last solve_addr.
        assert (is_heap_address b = true) as -> by (apply withinBounds_true_iff; solve_addr).
        done. }
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
    iFrame "Hservice Hstatic Hna Hid Hobj Howner HPC Hcgp Hcra Hca0 Hca1 Hca2 Hct0 Hct1 Hct2 Hct3 Hct4
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
       allocator_service_static ∗
       na_own cerise_nais E ∗
       a_owner ↦ₐ WInt o ∗

       (* Initial register file. *)
       PC ↦ₚ WCap true RX Global allocator_pcc_b allocator_pcc_e
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
       ca3 ↦ᵣ - ∗
       ca4 ↦ᵣ - ∗
       ctp ↦ᵣ - ∗
       cnull ↦ᵣ - ∗

       ▷ (na_own cerise_nais E ∗
          a_owner ↦ₐ WInt o ∗
          PC ↦ₚ lupdatePcPerm wret ∗
          cgp ↦ᵣ WCap true RW Global
            allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
          cra ↦ᵣ wret ∗
          ca0 ↦ᵣ WInt ALLOC_INVALID ∗
          ca1 ↦ᵣ WInt 0 ∗
          ca2 ↦ᵣ - ∗
          ct0 ↦ᵣ - ∗
          ct1 ↦ᵣ - ∗
          ct2 ↦ᵣ - ∗
          ca3 ↦ᵣ - ∗
          ca4 ↦ᵣ - ∗
          ctp ↦ᵣ - ∗
          cnull ↦ᵣ WInt 0

          -∗ WP Seq (Instr Executable) @ E {{ φ }})
       -∗ WP Seq (Instr Executable) @ E {{ φ }})%I.
  Proof.
    intros Hinvalid HEservice Hshadow_a Hbounds_a.
    iIntros "(#Hservice & #Hstatic & Hna & Howner & Hrest)".
    iDestruct "Hrest" as "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 &
      Hct3 & Hct4 & Hctp & Hcnull & Hpost)".
    iApply (allocator_free_reject_correct E g_owner a_owner o wreq wret emp%I φ with "[-]");
      [|exact HEservice|exact Hshadow_a|exact Hbounds_a|].
    { intros next allocations live issued Cs Hnext Hchain _ _ _ _.
      iIntros "_ Htoks Howners Hcells". iApply si_upd_intro. iFrame.
      iPureIntro. exact (Hinvalid next allocations Hnext Hchain). }
    iFrame "Hservice Hstatic Hna Howner HPC Hcgp Hcra Hca0 Hca1 Hca2 Hct0 Hct1 Hct2 Hct3 Hct4 Hctp Hcnull".
    iNext. iIntros "(Hna & _ & Hrest)". iApply "Hpost". iFrame.
  Qed.

  (** The functional [free]. The capability in [ca1] carries [ι]: observing
      it at its base finds the cell claimed by [ι], hence the header entry of
      [ι] (the claim/header clause). Its recorded owner is [id], the owner of
      the allocator capability in [ca0], since [ι ∈ Ω] and the owner sets are
      an exact view of the header list. The cells of [ι], with their shares,
      and the client's [free_auth_held ι] rebuild the whole status token,
      which is the dereference witness of the GetTag of the request, and
      moves to [APainting] before the paint loop and to [AQuar] right before
      the revoker store, which kills [ι]: no register holds a word with
      authority over [ι] there, since [ca0] holds [ALLOC_OK], [ca1] is zeroed and the
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
      {[cgp; cra; ca0; ca1; ca2; ct0; ct1; ct2; ca3; ca4; ctp; cnull]} ->
    (∀ r w, rmap !! r = Some w -> has_authority w.(lw) -> w.(lprov) = None) ->
    (has_authority wret.(lw) -> wret.(lprov) = None) ->

    ⊢ (

       allocator_service_ctx ∗
       allocator_service_static ∗
       na_own cerise_nais E ∗
       allocator_owner_id id Ω ∗
       a_owner ↦ₐ WInt id ∗
       alloc_obj ι b e ∗
       free_auth_held ι ∗

       (* Initial register file. *)
       PC ↦ₚ WCap true RX Global allocator_pcc_b allocator_pcc_e
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
       ca3 ↦ᵣ - ∗
       ca4 ↦ᵣ - ∗
       ctp ↦ᵣ - ∗
       cnull ↦ᵣ - ∗
       ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) ∗
       [[b, e]] ↦ₕ[ι] [[ws]] ∗

       ▷ (na_own cerise_nais E ∗
          allocator_owner_id id Ω ∗
          a_owner ↦ₐ WInt id ∗
          PC ↦ₚ lupdatePcPerm wret ∗
          cgp ↦ᵣ WCap true RW Global
            allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
          cra ↦ᵣ wret ∗
          ca0 ↦ᵣ WInt ALLOC_OK ∗
          ca1 ↦ᵣ WInt 0 ∗
          ca2 ↦ᵣ - ∗
          ct0 ↦ᵣ - ∗
          ct1 ↦ᵣ - ∗
          ct2 ↦ᵣ - ∗
          ca3 ↦ᵣ - ∗
          ca4 ↦ᵣ - ∗
          ctp ↦ᵣ - ∗
          cnull ↦ᵣ WInt 0 ∗
          ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) ∗
          ι ⊒ AQuar ∗
          £ 1

          -∗ WP Seq (Instr Executable) @ E {{ φ }})
       -∗ WP Seq (Instr Executable) @ E {{ φ }})%I.
  Proof.
    intros HEservice Hshadow_a Hbounds_a HιΩ Hbounds Hlen Hdom Hclean Hclean_ret.
    iIntros "(#Hservice & #Hstatic & Hna & Hid & Howner & #Hobj & Hheld & HPC & Hcgp & Hcra & Hca0 & Hca1 &
      Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hcnull & Hrmap & Hheap & Hpost)".
    (* Split the cells into their memory and their status shares. *)
    iDestruct (heap_region_pointsto_split with "Hobj") as "[Hto _]".
    iDestruct ("Hto" with "Hheap") as "[Hmem Hshares]".
    (* Open the service invariant. *)
    iMod (na_inv_acc with "Hservice Hna") as "(Hinv & Hna & Hclose)"; try exact HEservice.
    iDestruct "Hinv" as ">@".
    iDestruct "Hstatic" as "[#Himports #Hcode]".
    iDestruct (allocator_headers_chain_spec with "Hheaders") as %Hchain.
    (* Observe [ca1]: its bounds are those of the entry of [ι], which records
       the owner [id]; rebuild the whole status token of [ι]. *)
    iMod (allocator_free_observe with "Hca1 Hobj Hheld Hshares Hcells Htoks")
      as ([o0 r0] Hentry Hlive) "(Hca1 & Hcells & Hfull & Htoks_close)"; [done|apply Hwf|done|].
    iDestruct (allocator_free_owner_entry with "Howners Hid") as %Ho0; [done|done|done|].
    cbn in Ho0. subst o0.
    pose proof (allocator_chain_member_bounds _ _ _ _ _ _ _ Hchain Hentry) as Hentry_bounds.
    (* Focus on the code of [free]. *)
    iEval (rewrite /allocator_code) in "Hcode".
    focus_block_nochangePC 1 "Hcode" as a_free Ha_free "Hfree_code" "Hcode_cont".
    assert (a_free = allocator_free_pcc_addr) as ->
      by (pose proof allocator_code_free; solve_addr).
    iEval (rewrite allocator_free_instrs_code) in "Hfree_code".
    pose proof allocator_free_entry_bounds as Hcode_bounds.
    iDestruct (allocator_imports_split_pers with "Himports")
      as "(#Hshadow_import & #Hkey & #Hrevoker_import)".
    iDestruct "Hca2" as (wa2) "Hca2".
    iDestruct "Hct0" as (w0) "Hct0".
    iDestruct "Hct1" as (w1) "Hct1".
    iDestruct "Hct2" as (w2) "Hct2".
    iDestruct "Hct3" as (w3) "Hct3".
    iDestruct "Hct4" as (w4) "Hct4".
    iDestruct "Hctp" as (wctp) "Hctp".
    iDestruct "Hcnull" as (wnull) "Hcnull".

    (* Block 0: the owner identifier of the allocator capability. *)
    iApply (allocator_free_owner_spec with
      "[- $HPC $Hctp $Hca0 $Hkey $Howner $Hfree_code]");
      [done|apply allocator_free_pcc_addr_off|done
      |by apply withinBounds_true_iff in Hbounds_a as [_ ?]|].
    iNext. iIntros "(HPC & Hctp & Hca0 & _ & Howner & _)".
    (* Blocks 1 and 2: the request is a capability in the allocated prefix. *)
    (* The whole status token is the dereference witness of the GetTag. *)
    iApply (allocator_free_check_valid_spec _ _ _ _ next id _ ((WCap true p g b e a) @@ ι)
      _ _ _ _ (DerefLive ι 1) with
      "[- $Hslot $HPC $Hcgp $Hca0 $Hca1 $Hctp $Hct0 $Hct1 $Hct2 $Hct3 $Hfull $Hfree_code]").
    { done. }
    { solve_addr. }
    { exists p, g, b, e, a. split; first reflexivity. solve_addr. }
    { done. }
    iNext. iIntros "(Hslot & Hcgp & Hca0 & Hca1 & Hctp & Hfull & _ & Hvalid)".
    iDestruct "Hvalid" as (p0 g0 b0 e0 a0) "(%Hvalid & HPC & Hct0 & Hct1 & Hct2 & Hct3)".
    destruct Hvalid as [Heq Hvalid]. cbn in Heq.
    injection Heq as <- <- <- <- <-.
    (* Blocks 3 and 4: the local check of the header finds the entry of [ι],
       with the owner [id]. *)
    iDestruct (allocator_free_header_acc next b e id with "Hcells Hheaders")
      as (s1 s2 eh oh Hcheck Hheader) "(Hs1 & Hs2 & Hhdr & Hheader_close)";
      [solve_addr|done|done|].
    iApply (allocator_free_header_spec with
      "[- $HPC $Hctp $Hct3 $Hct4 $Hca2 $Hct0 $Hct1 $Hct2 $Hshadow_import $Hrevoker_import
          $Hs1 $Hs2 $Hhdr $Hca0 $Hfree_code]");
      [done|apply allocator_free_pcc_addr_off|solve_addr|done|].
    iNext. iIntros "(_ & _ & Hs1 & Hs2 & Hhdr & Hca0 & Hct0 & Hct1 & Hct2 & Hct4 &
      _ & Hout)".
    iDestruct ("Hheader_close" with "Hs1 Hs2 Hhdr") as "[Hcells Hheaders]".
    iDestruct "Hout" as "[(_ & HPC & Hct3 & Hca2 & Hctp)|(%Hmiss & _)]"; last first.
    { exfalso. apply Hmiss, Hcheck. by exists r0, ι. }
    iDestruct "Hct4" as (w4') "Hct4".
    (* Take the cells of [ι]; the status token moves to [APainting]. *)
    iDestruct (allocator_free_take_payload _ _ _ _ _ ws with "Hcells")
      as "[Hpayload Hcells_close]"; [done|done|done|].
    iMod (reg_painting E ι with "Hfull") as "Hpainting".
    (* Block 5, the tail: paint the payload quarantined; set ALLOC_OK. *)
    iDestruct (allocator_free_tail_acc with "Hfree_code") as "#Htail_code".
    pose proof (allocator_free_tail_bounds _ _ _ Hcode_bounds) as Htail_bounds.
    iApply (allocator_free_quarantine_spec with
      "[- $HPC $Hctp $Hca2 $Hca0 $Hca1 $Hpainting $Hpayload $Htail_code]"); [done|solve_addr|].
    iNext. iIntros "(HPC & Hctp & Hca2 & Hca0 & Hca1 & Hpainting & Hpayload & _)".
    (* Every cell is quarantined: right before the revoker store, the status
       token moves to [AQuar]; the store kills [ι]; unpaint the payload. *)
    iApply (allocator_free_revoke_spec with
      "[- $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hca2 $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hctp $Hcnull $Hrmap
          $Hobj $Hpainting $Hpayload $Htail_code]"); [done|done|done|done|done|].
    iNext. iIntros "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 &
      Hctp & Hcnull & Hrmap & Hdead & #Hq & Hcells_free & _)".
    (* Return. *)
    iApply (allocator_free_return_spec with "[- $HPC $Hcra $Hcnull $Htail_code]"); first done.
    iNext. iIntros "(HPC & Hcra & Hcnull & _ & Hlc)".
    (* Release the entry of [ι] and close the service invariant. *)
    iDestruct ("Hcells_close" with "Hcells_free Hmem") as "Hcells".
    iDestruct (allocator_free_release with
      "Hslot Hheaders Howners Hcells Htoks_close Hdead Hq") as "Hdata";
      [done|done|done|done|done|].
    iMod ("Hclose" with "[$Hna Hdata]") as "Hna".
    { iNext. iExists next. iFrame "Hdata". }
    iApply "Hpost". iFrame "∗ Hq".
  Qed.

  (** A malformed allocator capability in [ca0] traps in the owner block. *)

  Lemma allocator_free_invalid_capability_spec
    (E : coPset) (wsealed : LWord) (P : iProp Σ) :

    ↑Nallocator_service ⊆ E ->
    (is_sealed_with_o wsealed.(lw) AllocOtype = false \/ get_tag wsealed.(lw) = false) ->

    allocator_service_ctx ∗
    allocator_service_static ∗
    na_own cerise_nais E ∗
    PC ↦ₚ WCap true RX Global allocator_pcc_b allocator_pcc_e
      allocator_free_pcc_addr ∗
    ca0 ↦ᵣ wsealed ∗
    ctp ↦ᵣ - ∗
    ca3 ↦ᵣ - ∗
    ca4 ↦ᵣ -
    ⊢ WP Seq (Instr Executable) @ E {{ v, ⌜v = HaltedV⌝ → P }}.
  Proof.
    iIntros (HEservice Hwsealed)
      "(#Hservice & #Hstatic & Hna & HPC & Hca0 & [%wtp Hctp] & [%w3 Hct3] & [%w4 Hct4])".
    (* Open the service invariant and focus on the code of [free]. *)
    iMod (na_inv_acc with "Hservice Hna") as "(Hinv & Hna & Hclose)"; try exact HEservice.
    iDestruct "Hinv" as ">Hdata".
    iDestruct "Hstatic" as "[#Himports #Hcode]".
    iEval (rewrite /allocator_code) in "Hcode".
    focus_block_nochangePC 1 "Hcode" as a_free Ha_free "Hfree_code" "Hcode_cont".
    assert (a_free = allocator_free_pcc_addr) as ->
      by (pose proof allocator_code_free; solve_addr).
    iEval (rewrite allocator_free_instrs_code) in "Hfree_code".
    iDestruct (allocator_imports_split_pers with "Himports")
      as "(_ & #Hkey & _)".
    (* Block 0: the owner block traps. *)
    iApply (allocator_free_owner_invalid_spec with
      "[$HPC $Hctp $Hca0 $Hkey $Hfree_code]");
      [apply allocator_free_entry_bounds|apply allocator_free_pcc_addr_off|done].
  Qed.

End AllocatorFree.
