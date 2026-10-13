From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode memory_region region_keys.
From griotte.allocators.no_ownership Require Import allocator_header_spec allocator_free_spec_states allocator_free_spec_world allocator_free_spec_check_blocks_1 allocator_free_spec_header_blocks_2 allocator_free_spec_return_blocks_3.
From griotte.allocators.common Require Import allocator_common_free_spec_tail_blocks.

(** The top-level specifications of [free]. They compose the block groups
    of [allocator_free_spec_<segment>_blocks_<n>], those of the shared code in
    [allocator_common_free_spec_tail_blocks], and the logical steps of
    [allocator_free_spec_world]. *)

Section AllocatorFree.
  Context {Σ : gFunctors}
    {ceriseg : ceriseG Σ} {FA : FreeAuth Σ}
    {MP : MachineParameters}
    {layout : allocatorLayout}.
  Context {layout_wf : allocatorLayoutWf}.

  (** Common call boundary for rejection. [P] carries the evidence for the
      particular rejection and is returned unchanged; the rejection itself
      may observe the request in [ca0] against the cells and the entries of
      the service. Other client resources can be framed. *)

  Local Lemma allocator_free_reject_correct
    (E : coPset) (wreq wret : LWord) (P : iProp Σ)
    (φ : language.val griotte_lang → iPropI Σ) :
    (∀ next allocations live issued Cs,
      (heap_b < next /\ next <= heap_e)%a ->
      allocator_chain (heap_b ^+ 1)%a next allocations ->
      allocator_entries_wf allocations ->
      allocator_cells_wf next allocations live issued Cs ->
      P -∗
      ca0 ↦ᵣ wreq -∗
      allocator_entries_res live allocations -∗
      allocator_cells Cs -∗
      |~{E}~>
        P ∗
        ca0 ↦ᵣ wreq ∗
        allocator_entries_res live allocations ∗
        allocator_cells Cs ∗
        ⌜¬ allocator_free_valid next allocations wreq.(lw)⌝) ->
    ↑Nallocator_service ⊆ E ->
    ⊢ (
       allocator_service_ctx ∗
       allocator_service_static ∗
       na_own cerise_nais E ∗
       P ∗
       PC ↦ₚ WCap true RX Global allocator_pcc_b allocator_pcc_e
         allocator_free_pcc_addr ∗
       cgp ↦ᵣ WCap true RW Global
         allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ wreq ∗
       ca1 ↦ᵣ - ∗
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
    intros Hreject_request HEservice.
    iIntros "(#Hservice & #Hstatic & Hna & HP & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 &
      Hct3 & Hct4 & Hctp & Hcnull & Hpost)".
    (* Open the service invariant and focus on the code of [free]. *)
    iMod (na_inv_acc with "Hservice Hna") as "(Hinv & Hna & Hclose)"; try exact HEservice.
    iDestruct "Hinv" as ">Hdata".
    iDestruct "Hstatic" as "[#Himports #Hcode]".
    iDestruct "Hdata" as (next allocations live issued Cs)
      "(%Hnext & Hslot & Hheaders & %Hwf & %Hcwf & Htoks & Hcells)".
    iDestruct (allocator_headers_chain_spec with "Hheaders") as %Hchain.
    (* The request is invalid. *)
    iMod (Hreject_request next allocations live issued Cs Hnext Hchain Hwf Hcwf
      with "HP Hca0 Htoks Hcells") as "(HP & Hca0 & Htoks & Hcells & %Hinvalid)".
    iEval (rewrite /allocator_code) in "Hcode".
    focus_block_nochangePC 1 "Hcode" as a_free Ha_free "Hfree_code" "Hcode_cont".
    assert (a_free = allocator_free_pcc_addr) as ->
      by (pose proof allocator_code_free; solve_addr).
    iEval (rewrite allocator_free_instrs_code) in "Hfree_code".
    pose proof allocator_free_entry_bounds as Hbounds.
    iDestruct "Hca1" as (wca1) "Hca1".
    iDestruct "Hct0" as (w0) "Hct0".
    iDestruct "Hct1" as (w1) "Hct1".
    iDestruct "Hct2" as (w2) "Hct2".
    iDestruct "Hct3" as (w3) "Hct3".
    iDestruct "Hcnull" as (wnull) "Hcnull".
    (* The tail: set ALLOC_INVALID, return and close the service
       invariant. *)
    iAssert (PC ↦ₚ WCap true RX Global allocator_pcc_b allocator_pcc_e
               (allocator_free_pcc_addr ^+ allocator_free_invalid_offset)%a ∗
             cgp ↦ᵣ WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
             ca0 ↦ᵣ wreq ∗
             ca2 ↦ᵣ - ∗ ct0 ↦ᵣ - ∗ ct1 ↦ᵣ - ∗ ct2 ↦ᵣ - ∗ ca3 ↦ᵣ - ∗ ca4 ↦ᵣ - ∗ ctp ↦ᵣ - ∗
             allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
             allocator_headers (heap_b ^+ 1)%a next allocations ∗
             allocator_cells Cs -∗
             WP Seq (Instr Executable) @ E {{ φ }})%I
      with "[- HPC Hca0 Hslot Hheaders Hcells Hct0 Hct1 Hct2 Hct3 Hct4 Hca2
               Hctp Hcgp]"
      as "Hreject".
    { iIntros "(HPC & Hcgp & Hca0 & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hslot &
        Hheaders & Hcells)".
      iApply (allocator_free_invalid_spec with "[- $HPC $Hcra $Hca0 $Hca1 $Hcnull $Hfree_code]");
        first done.
      iNext. iIntros "(HPC & Hcra & Hca0 & Hca1 & Hcnull & _ & _)".
      iMod ("Hclose" with "[$Hna Hslot Hheaders Htoks Hcells]") as "Hna".
      { iNext. iExists next, allocations, live, issued, Cs. iFrame "∗". done. }
      iApply "Hpost". iFrame "∗". }
    destruct (decide (allocator_free_in_prefix next wreq.(lw))) as [Hprefix|Hprefix].
    - (* Blocks 0 and 1: the request is a capability in the allocated prefix. *)
      iApply (allocator_free_check_valid_spec with
        "[- $Hslot $HPC $Hcgp $Hca0 $Hct0 $Hct1 $Hct2 $Hct3 $Hfree_code]"); [done|done|].
      iNext. iIntros "(Hslot & Hcgp & Hca0 & _ & Hvalid)".
      iDestruct "Hvalid" as (p g b e a) "(%Hvalid & HPC & Hct0 & Hct1 & Hct2 & Hct3)".
      destruct Hvalid as [Heq Hvalid].
      assert (Hmissing : ¬ allocator_has_bounds allocations b e).
      { intros Hmember. apply Hinvalid. exists p, g, b, e, a. auto. }
      (* Blocks 2 and 3: the local check of the header fails. *)
      iDestruct (allocator_free_header_acc next b e with "Hcells Hheaders")
        as (s1 s2 eh Hcheck Hheader) "(Hs1 & Hs2 & Hhdr & Hheader_close)";
        [solve_addr|done|done|].
      iDestruct (allocator_imports_split_pers with "Himports")
        as "(#Hshadow_import & #Hseal_import & #Hrevoker_import)".
      iDestruct "Hct4" as (w4) "Hct4".
      iDestruct "Hca2" as (wa2) "Hca2".
      iDestruct "Hctp" as (wctp) "Hctp".
      iApply (allocator_free_header_spec with
        "[- $HPC $Hctp $Hct3 $Hct4 $Hca2 $Hct0 $Hct1 $Hct2 $Hshadow_import $Hrevoker_import
            $Hs1 $Hs2 $Hhdr $Hfree_code]");
        [done|apply allocator_free_pcc_addr_off|solve_addr|done|].
      iNext. iIntros "(_ & _ & Hs1 & Hs2 & Hhdr & Hct0 & Hct1 & Hct2 & Hct4 & _ &
        Hout)".
      iDestruct ("Hheader_close" with "Hs1 Hs2 Hhdr") as "[Hcells Hheaders]".
      iDestruct "Hout" as "[(%Hok & _)|(_ & HPC & Hct3 & Hca2 & Hctp)]".
      { exfalso. by apply Hmissing, Hcheck. }
      iApply ("Hreject" with "[- ]"). iFrame "∗".
    - (* Blocks 0 and 1: the request is not a capability in the allocated prefix. *)
      iApply (allocator_free_check_invalid_spec with
        "[- $Hslot $HPC $Hcgp $Hca0 $Hct0 $Hct1 $Hct2 $Hct3 $Hfree_code]"); [done|done|].
      iNext. iIntros "(Hslot & Hcgp & Hca0 & _ & HPC & Hct0 & Hct1 & Hct2 & Hct3)".
      iApply ("Hreject" with "[- ]"). iFrame "∗".
  Qed.


  (** A strict subrange cannot be another allocation in the header chain.
      Observing the capability in [ca0] at its base finds the cell claimed by
      [ι], hence the header entry of [ι], whose bounds are [b] and [e]. *)

  Lemma allocator_free_narrowed_spec
    (E : coPset) (p : Perm) (g : Locality)
    (ι : AId) (b e b' e' a : Addr) (wret : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    (b <= b' /\ b' < e' /\ e' <= e)%a ->
    (b', e') ≠ (b, e) ->
    ↑Nallocator_service ⊆ E ->
    ⊢ (
       allocator_service_ctx ∗
       allocator_service_static ∗
       na_own cerise_nais E ∗
       alloc_obj ι b e ∗
       PC ↦ₚ WCap true RX Global allocator_pcc_b allocator_pcc_e
         allocator_free_pcc_addr ∗
       cgp ↦ᵣ WCap true RW Global
         allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ (WCap true p g b' e' a) @@ ι ∗
       ca1 ↦ᵣ - ∗
       ca2 ↦ᵣ - ∗
       ct0 ↦ᵣ - ∗
       ct1 ↦ᵣ - ∗
       ct2 ↦ᵣ - ∗
       ca3 ↦ᵣ - ∗
       ca4 ↦ᵣ - ∗
       ctp ↦ᵣ - ∗
       cnull ↦ᵣ - ∗
       ▷ (na_own cerise_nais E ∗
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
    intros Hbounds Hneq HEservice.
    iIntros "(#Hservice & #Hstatic & Hna & #Hobj & Hrest)".
    iDestruct "Hrest" as "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 &
      Hct3 & Hct4 & Hctp & Hcnull & Hpost)".
    iApply (allocator_free_reject_correct E ((WCap true p g b' e' a) @@ ι) wret
      (alloc_obj ι b e) φ with "[-]"); [|exact HEservice|].
    { intros next allocations live issued Cs Hnext Hchain Hwf Hcwf.
      iIntros "#Hobj Hca0 Htoks Hcells".
      destruct (decide (heap_b < b' /\ b' < e' /\ e' <= next)%a) as [Hin|Hout]; last first.
      { iApply si_upd_intro. iFrame "∗ #". iPureIntro.
        intros (p0 & g0 & b0 & e0 & a0 & Heq & Hprefix & _). inversion Heq; subst. done. }
      (* Observe the capability at its base: the cell is claimed by [ι]. *)
      destruct (acw_dom _ _ _ _ _ Hcwf b') as [ [ [c s] hdr] Hc]; first solve_addr.
      iDestruct (allocator_cells_acc _ _ _ Hc with "Hcells") as "[Hcell Hcells_close]".
      iDestruct "Hcell" as "(Hclaim & Hcell)".
      iMod (observe_claim E ca0 _ b' c with "Hca0 Hclaim") as "(Hca0 & Hclaim & %Hclaim)".
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
      intros (p0 & g0 & b1 & e1 & a1 & Heq & _ & Hmember). inversion Heq; subst.
      apply (allocator_chain_subrange_spec _ _ _ _ _ _ _ Hchain
        (ex_intro _ r0 (ex_intro _ ι Hentry)) Hbounds Hneq Hmember). }
    iFrame "Hservice Hstatic Hna Hobj HPC Hcgp Hcra Hca0 Hca1 Hca2 Hct0 Hct1 Hct2 Hct3 Hct4 Hctp Hcnull".
    iNext. iIntros "(Hna & _ & Hrest)". iApply "Hpost". iFrame.
  Qed.

  (** A call with an invalid request leaves client memory untouched and returns
      [ALLOC_INVALID]. Other registers and resources can be framed. *)

  Lemma allocator_free_invalid_correct
    (E : coPset) (wreq wret : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    (∀ (next : Addr) (allocations : list allocator_header_entry),
      (heap_b < next /\ next <= heap_e)%a ->
      allocator_chain (heap_b ^+ 1)%a next allocations ->
      ¬ allocator_free_valid next allocations wreq.(lw)) ->
    ↑Nallocator_service ⊆ E ->

    ⊢ (
       allocator_service_ctx ∗
       allocator_service_static ∗
       na_own cerise_nais E ∗

       (* Initial register file. *)
       PC ↦ₚ WCap true RX Global allocator_pcc_b allocator_pcc_e
         allocator_free_pcc_addr ∗
       cgp ↦ᵣ WCap true RW Global
         allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ wreq ∗
       ca1 ↦ᵣ - ∗
       ca2 ↦ᵣ - ∗
       ct0 ↦ᵣ - ∗
       ct1 ↦ᵣ - ∗
       ct2 ↦ᵣ - ∗
       ca3 ↦ᵣ - ∗
       ca4 ↦ᵣ - ∗
       ctp ↦ᵣ - ∗
       cnull ↦ᵣ - ∗

       ▷ (na_own cerise_nais E ∗
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
    intros Hinvalid HEservice.
    iIntros "(#Hservice & #Hstatic & Hna & Hrest)".
    iDestruct "Hrest" as "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 &
      Hct3 & Hct4 & Hctp & Hcnull & Hpost)".
    iApply (allocator_free_reject_correct E wreq wret emp%I φ with "[-]");
      [|exact HEservice|].
    { intros next allocations live issued Cs Hnext Hchain _ _.
      iIntros "_ Hca0 Htoks Hcells". iApply si_upd_intro. iFrame.
      iPureIntro. exact (Hinvalid next allocations Hnext Hchain). }
    iFrame "Hservice Hstatic Hna HPC Hcgp Hcra Hca0 Hca1 Hca2 Hct0 Hct1 Hct2 Hct3 Hct4 Hctp Hcnull".
    iNext. iIntros "(Hna & _ & Hrest)". iApply "Hpost". iFrame.
  Qed.


  (** The functional [free]. The capability in [ca0] carries [ι]: observing
      it at its base finds the cell claimed by [ι], hence the header entry of
      [ι] (the claim/header clause). The cells of [ι], with their shares, and
      the client's [free_auth_held ι] rebuild the whole status token, which
      moves to [APainting] before the paint loop and to [AQuar] after it. The
      revoker store then kills [ι]: no register holds a word with authority
      over [ι] there, since [ca0] is overwritten, [ca1] is zeroed and the
      framed registers are identifier-free. The payload is unpainted and
      returns to the service as unclaimed cells. A successful call
      relinquishes the memory and returns [ι ⊒ AQuar]. *)

  Lemma allocator_free_valid_correct
    (E : coPset) (p : Perm) (g : Locality) (ι : AId) (b e a : Addr)
    (ws : list LWord) (wret : LWord) (rmap : LReg)
    (φ : language.val griotte_lang → iPropI Σ) :

    ↑Nallocator_service ⊆ E ->
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
       alloc_obj ι b e ∗
       free_auth_held ι ∗

       (* Initial register file. *)
       PC ↦ₚ WCap true RX Global allocator_pcc_b allocator_pcc_e
         allocator_free_pcc_addr ∗
       cgp ↦ᵣ WCap true RW Global
         allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ (WCap true p g b e a) @@ ι ∗
       ca1 ↦ᵣ - ∗
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
    intros HEservice Hbounds Hlen Hdom Hclean Hclean_ret.
    iIntros "(#Hservice & #Hstatic & Hna & #Hobj & Hheld & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 &
      Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hcnull & Hrmap & Hheap & Hpost)".
    (* Split the cells into their memory and their status shares. *)
    iDestruct (heap_region_pointsto_split with "Hobj") as "[Hto _]".
    iDestruct ("Hto" with "Hheap") as "[Hmem Hshares]".
    (* Open the service invariant. *)
    iMod (na_inv_acc with "Hservice Hna") as "(Hinv & Hna & Hclose)"; try exact HEservice.
    iDestruct "Hinv" as ">Hdata".
    iDestruct "Hstatic" as "[#Himports #Hcode]".
    iDestruct "Hdata" as (next allocations live issued Cs)
      "(%Hnext & Hslot & Hheaders & %Hwf & %Hcwf & Htoks & Hcells)".
    iDestruct (allocator_headers_chain_spec with "Hheaders") as %Hchain.
    (* Observe [ca0]: its bounds are those of the entry of [ι]; rebuild the
       whole status token of [ι]. *)
    iMod (allocator_free_observe with "Hca0 Hobj Hheld Hshares Hcells Htoks")
      as (r0 Hentry Hlive) "(Hca0 & Hcells & Hfull & Htoks_close)"; [done|apply Hwf|done|].
    pose proof (allocator_chain_member_bounds _ _ _ _ _ _ _ Hchain Hentry) as Hentry_bounds.
    (* Focus on the code of [free]. *)
    iEval (rewrite /allocator_code) in "Hcode".
    focus_block_nochangePC 1 "Hcode" as a_free Ha_free "Hfree_code" "Hcode_cont".
    assert (a_free = allocator_free_pcc_addr) as ->
      by (pose proof allocator_code_free; solve_addr).
    iEval (rewrite allocator_free_instrs_code) in "Hfree_code".
    pose proof allocator_free_entry_bounds as Hcode_bounds.
    iDestruct "Hca1" as (wca1) "Hca1".
    iDestruct "Hca2" as (wa2) "Hca2".
    iDestruct "Hct0" as (w0) "Hct0".
    iDestruct "Hct1" as (w1) "Hct1".
    iDestruct "Hct2" as (w2) "Hct2".
    iDestruct "Hct3" as (w3) "Hct3".
    iDestruct "Hct4" as (w4) "Hct4".
    iDestruct "Hctp" as (wctp) "Hctp".
    iDestruct "Hcnull" as (wnull) "Hcnull".

    (* Blocks 0 and 1: the request is a capability in the allocated prefix. *)
    iApply (allocator_free_check_valid_spec _ _ _ _ next ((WCap true p g b e a) @@ ι) with
      "[- $Hslot $HPC $Hcgp $Hca0 $Hct0 $Hct1 $Hct2 $Hct3 $Hfree_code]").
    { done. }
    { exists p, g, b, e, a. split; first reflexivity. solve_addr. }
    iNext. iIntros "(Hslot & Hcgp & Hca0 & _ & Hvalid)".
    iDestruct "Hvalid" as (p0 g0 b0 e0 a0) "(%Hvalid & HPC & Hct0 & Hct1 & Hct2 & Hct3)".
    destruct Hvalid as [Heq Hvalid]. cbn in Heq.
    injection Heq as <- <- <- <- <-.
    (* Blocks 2 and 3: the local check of the header finds the entry of [ι]. *)
    iDestruct (allocator_free_header_acc next b e with "Hcells Hheaders")
      as (s1 s2 eh Hcheck Hheader) "(Hs1 & Hs2 & Hhdr & Hheader_close)";
      [solve_addr|done|done|].
    iDestruct (allocator_imports_split_pers with "Himports")
      as "(#Hshadow_import & #Hseal_import & #Hrevoker_import)".
    iApply (allocator_free_header_spec with
      "[- $HPC $Hctp $Hct3 $Hct4 $Hca2 $Hct0 $Hct1 $Hct2 $Hshadow_import $Hrevoker_import
          $Hs1 $Hs2 $Hhdr $Hfree_code]");
      [done|apply allocator_free_pcc_addr_off|solve_addr|done|].
    iNext. iIntros "(_ & _ & Hs1 & Hs2 & Hhdr & Hct0 & Hct1 & Hct2 & Hct4 & _ &
      Hout)".
    iDestruct ("Hheader_close" with "Hs1 Hs2 Hhdr") as "[Hcells Hheaders]".
    iDestruct "Hout" as "[(_ & HPC & Hct3 & Hca2 & Hctp)|(%Hmiss & _)]"; last first.
    { exfalso. apply Hmiss, Hcheck. by exists r0, ι. }
    iDestruct "Hct4" as (w4') "Hct4".
    (* Take the cells of [ι]; the status token moves to [APainting]. *)
    iDestruct (allocator_free_take_payload _ _ _ _ _ ws with "Hcells")
      as "[Hpayload Hcells_close]"; [done|done|done|].
    iMod (reg_painting E ι with "Hfull") as "Hpainting".
    (* Block 4, the tail: paint the payload quarantined; set ALLOC_OK. *)
    iDestruct (allocator_free_tail_acc with "Hfree_code") as "#Htail_code".
    pose proof (allocator_free_tail_bounds _ _ _ Hcode_bounds) as Htail_bounds.
    iApply (allocator_free_quarantine_spec with
      "[- $HPC $Hctp $Hca2 $Hca0 $Hca1 $Hpainting $Hpayload $Htail_code]"); [done|solve_addr|].
    iNext. iIntros "(HPC & Hctp & Hca2 & Hca0 & Hca1 & Hpainting & Hpayload & _)".
    (* Every cell is quarantined: the status token moves to [AQuar]. *)
    iDestruct (big_sepL_sep with "Hpayload") as "[Hshadows Hclaims]".
    iMod (reg_quarantine E ι b e with "Hobj Hpainting Hshadows")
      as "(Hquar & #Hq & Hshadows)".
    iCombine "Hshadows Hclaims" as "Hpayload".
    rewrite -big_sepL_sep.
    (* The revoker store kills [ι]; unpaint the payload. *)
    iApply (allocator_free_revoke_spec with
      "[- $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hca2 $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hctp $Hcnull $Hrmap
          $Hobj $Hquar $Hpayload $Htail_code]"); [done|done|done|done|done|].
    iNext. iIntros "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 &
      Hctp & Hcnull & Hrmap & Hdead & Hcells_free & _)".
    (* Return. *)
    iApply (allocator_free_return_spec with "[- $HPC $Hcra $Hcnull $Htail_code]"); first done.
    iNext. iIntros "(HPC & Hcra & Hcnull & _ & Hlc)".
    (* Release the entry of [ι] and close the service invariant. *)
    iDestruct ("Hcells_close" with "Hcells_free Hmem") as "Hcells".
    iDestruct (allocator_free_release with "Hslot Hheaders Hcells Htoks_close Hdead Hq")
      as "Hdata"; [done|done|done|done|done|].
    iMod ("Hclose" with "[$Hna Hdata]") as "Hna".
    { iNext. iExists next. iFrame "Hdata". }
    iApply "Hpost". iFrame "∗ Hq".
  Qed.

End AllocatorFree.
