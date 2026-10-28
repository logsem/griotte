From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode memory_region region_keys.
From griotte.allocators.common Require Import allocator_common_preamble allocator_common_header_spec.

(** * Logical steps shared by the proofs of [malloc] and [free]

    The lemmas of this file do not execute code. They are used between the
    block groups in the proofs of the specifications of both allocators. *)

Section AllocatorCommonWorld.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {FA : FreeAuth Σ}
    {MP : MachineParameters}.

  (** A request observed against the cells: at the base of its authority,
      its cell is claimed by its identifier, or is a heap root. *)
  Definition allocator_request_observed
      (Cs : gmap Addr (AddrClaim * AllocStatus * bool)) (w : LWord) : Prop :=
    ∀ b (x : AddrClaim * AllocStatus * bool),
      heap_authority_base w.(lw) = Some b -> Cs !! b = Some x ->
      match w.(lprov) with
      | Some ι => x.1.1 = Claimed ι
      | None => x.1.1 = HeapRoot
      end.

  (** A GetTag returning 1 on the request, with the cells in hand, observes
      the request against the cells. *)
  Lemma gettag_result_cells dw Cs w :
    gettag_result dw
      (λ C, ∀ a (x : AddrClaim * AllocStatus * bool), Cs !! a = Some x -> C !! a = Some x.1.1)
      w 1 ->
    allocator_request_observed Cs w.
  Proof.
    intros (_ & _ & Hobs) b x Hab Hx.
    destruct (Hobs eq_refl) as (C & HC & Hb).
    specialize (Hb b Hab). rewrite (HC _ _ Hx) in Hb.
    destruct (lprov w); by simplify_eq.
  Qed.

  (** Take the cells of a new chunk [next, finish) above the bump cursor: they
      are unclaimed, unpainted and not headers. The header cells [next, b)
      stay unclaimed; the payload cells [b, finish) are claimed by a fresh
      identifier [ι ∉ S]. The cells are put back as header words and as cells
      claimed by [ι]. *)
  Lemma allocator_malloc_claim
    (E : coPset) (S : gset AId) (next b finish : Addr)
    (allocations : list allocator_header_entry) (live issued : gset AId)
    (Cs : gmap Addr (AddrClaim * AllocStatus * bool)) :
    allocator_cells_wf next allocations live issued Cs ->
    (next <= b /\ b < finish /\ finish <= heap_e)%a ->
    allocator_cells Cs -∗
    |~{E}~> ∃ ι : AId,
      ⌜ι ∉ S⌝ ∗
      alloc_obj ι b finish ∗
      ι ↦st{1} ALive ∗
      allocator_range_memory next b ∗
      allocator_range_memory b finish ∗
      ([∗ list] a ∈ finz.seq_between next b, a ↦ₛ ShadowLive ∗ addr_alloc a Unclaimed) ∗
      ([∗ list] a ∈ finz.seq_between b finish, a ↦ₛ ShadowLive ∗ addr_alloc a (Claimed ι)) ∗
      (([∗ list] a ∈ finz.seq_between next b,
          a ↦ₛ ShadowQuarantined ∗ addr_alloc a Unclaimed) -∗
       ([∗ list] a ∈ finz.seq_between b finish,
          a ↦ₛ ShadowLive ∗ addr_alloc a (Claimed ι)) -∗
       allocator_cells
         (allocator_cells_update (finz.seq_between next finish) (allocator_malloc_cell b ι) Cs)).
  Proof.
    intros Hcwf Hrange. iIntros "Hcells".
    iDestruct (allocator_cells_range_acc (finz.seq_between next finish)
                 (λ _, (Unclaimed, ShadowLive, false)) with "Hcells")
      as "[Hchunk Hcells_close]".
    { apply finz_seq_between_NoDup. }
    { intros a Ha. apply elem_of_finz_seq_between in Ha.
      apply (acw_cursor _ _ _ _ _ Hcwf). solve_addr. }
    assert (Hsplit : (next <= b /\ b <= finish)%a) by solve_addr.
    iEval (rewrite (finz_seq_between_split next b finish Hsplit) big_sepL_app) in "Hchunk".
    iDestruct "Hchunk" as "[Hhdr Hpay]".
    iEval (rewrite /cell_res' /cell_res /=) in "Hhdr Hpay".
    iDestruct (big_sepL_sep with "Hhdr") as "[Hhdr_claims Hhdr]".
    iDestruct (big_sepL_sep with "Hhdr") as "[Hhdr_shadow Hhdr_mem]".
    iDestruct (big_sepL_sep with "Hpay") as "[Hpay_claims Hpay]".
    iDestruct (big_sepL_sep with "Hpay") as "[Hpay_shadow Hpay_mem]".
    iCombine "Hpay_shadow Hpay_claims" as "Hpayload".
    rewrite -big_sepL_sep.
    iMod (rules_registry.reg_alloc _ b finish S with "Hpayload")
      as (ι Hι) "(#Hobj & Htok & Hpayload)".
    iModIntro. iExists ι. iFrame "Hobj Htok Hpayload". iSplit; first done.
    iSplitL "Hhdr_mem".
    { iApply (big_sepL_mono with "Hhdr_mem"). iIntros (k a _) "[_ $]". }
    iSplitL "Hpay_mem".
    { iApply (big_sepL_mono with "Hpay_mem"). iIntros (k a _) "[_ $]". }
    iSplitL "Hhdr_shadow Hhdr_claims".
    { iApply big_sepL_sep. iFrame. }
    iIntros "Hheader Hpayload".
    iApply "Hcells_close".
    iEval (rewrite (finz_seq_between_split next b finish Hsplit) big_sepL_app).
    iSplitL "Hheader".
    - iApply (big_sepL_mono with "Hheader"). iIntros (k a Hk) "[Hs Hc]".
      apply list_elem_of_lookup_2, elem_of_finz_seq_between in Hk.
      rewrite /cell_res' /allocator_malloc_cell decide_True; last solve_addr.
      rewrite /cell_res /=. iFrame.
    - iApply (big_sepL_mono with "Hpayload"). iIntros (k a Hk) "[Hs Hc]".
      apply list_elem_of_lookup_2, elem_of_finz_seq_between in Hk.
      rewrite /cell_res' /allocator_malloc_cell decide_False; last solve_addr.
      rewrite /cell_res /=. iFrame. done.
  Qed.

  (** Observe the capability in [r] at its base [b]: the cell is claimed by
      [ι], so the claim/header clause names the header entry of [ι], whose
      bounds are [b] and [e]. The allocator's piece of the status token of
      [ι], the client half and the shares of the cells rebuild the whole
      token. *)
  Lemma allocator_free_observe
    (E : coPset) (r : RegName) (p : Perm) (g : Locality) (ι : AId) (b e a next : Addr)
    (allocations : list allocator_header_entry) (live issued : gset AId)
    (Cs : gmap Addr (AddrClaim * AllocStatus * bool)) :
    (heap_b < b /\ b < e /\ e <= heap_e)%a ->
    NoDup (allocator_entry_ids allocations) ->
    allocator_cells_wf next allocations live issued Cs ->
    r ↦ᵣ (Cap p g b e a) @@ ι -∗
    alloc_obj ι b e -∗
    free_auth_held ι -∗
    ([∗ list] _ ∈ finz.seq_between b e, ι ↦st{share (finz.dist b e)} ALive) -∗
    allocator_cells Cs -∗
    allocator_entries_res live allocations -∗
    |~{E}~> ∃ r0,
      ⌜(b, e, r0, ι) ∈ allocations⌝ ∗
      ⌜ι ∈ live⌝ ∗
      r ↦ᵣ (Cap p g b e a) @@ ι ∗
      allocator_cells Cs ∗
      ι ↦st{1} ALive ∗
      (∀ live', ⌜∀ ι', ι' ≠ ι -> (ι' ∈ live <-> ι' ∈ live')⌝ -∗
         allocator_tok live' ι b e -∗ allocator_entries_res live' allocations).
  Proof.
    intros Hbounds Hnodup Hcwf.
    iIntros "Hr #Hobj Hheld Hshares Hcells Htoks".
    destruct (acw_dom _ _ _ _ _ Hcwf b) as [ [ [c s] hdr] Hc]; first solve_addr.
    iDestruct (allocator_cells_acc _ _ _ Hc with "Hcells") as "[Hcell Hcells_close]".
    iDestruct "Hcell" as "(Hclaim & Hcell)".
    (* The share of the base cell shows that [ι] is not dead. *)
    assert (Hseq : finz.seq_between b e = b :: finz.seq_between (b ^+ 1) e)
      by (apply finz_seq_between_cons; solve_addr).
    iEval (rewrite Hseq) in "Hshares".
    iDestruct (big_sepL_cons with "Hshares") as "[Hshare_b Hshares]".
    iMod (observe_claim E r _ b c _ ALive with "Hr Hclaim Hshare_b")
      as "(Hr & Hclaim & Hshare_b & %Hclaim)".
    { done. }
    { cbn. rewrite decide_True; last solve_addr.
      assert (is_heap_address b = true) as -> by (apply withinBounds_true_iff; solve_addr).
      done. }
    { done. }
    iSimpl in "Hshare_b".
    iAssert ([∗ list] _ ∈ finz.seq_between b e, ι ↦st{share (finz.dist b e)} ALive)%I
      with "[Hshare_b Hshares]" as "Hshares".
    { rewrite Hseq. iFrame. }
    cbn in Hclaim. subst c.
    iDestruct ("Hcells_close" $! (Claimed ι, s, hdr) with "[$Hclaim $Hcell]") as "Hcells".
    rewrite insert_id; last exact Hc.
    destruct (acw_claimed _ _ _ _ _ Hcwf _ _ _ _ Hc) as (b0 & e0 & r0 & Hentry & Hlive & _).
    iDestruct (allocator_entries_res_acc _ _ _ _ _ _ Hnodup Hentry with "Htoks")
      as "(#Hobj0 & Htok & Htoks_close)".
    iDestruct (alloc_obj_agree with "Hobj Hobj0") as %[<- <-].
    rewrite /allocator_tok decide_True //.
    iDestruct "Htok" as "[Hshare Hkept]".
    iModIntro. iExists r0. iFrame "Hr Hcells Htoks_close". iSplit; first done.
    iSplit; first done.
    rewrite (st_own_split_alloc ι (finz.seq_between b e))
      finz_seq_between_length -free_auth_split.
    iFrame.
  Qed.

  (** Take the cells of the live entry of [ι]: they are claimed by [ι] and
      unpainted. They are put back as unclaimed cells, with the memory of the
      payload. *)
  Lemma allocator_free_take_payload
    (next b e : Addr) (r0 : Z * Z) (ι : AId) (ws : list LWord)
    (allocations : list allocator_header_entry) (live issued : gset AId)
    (Cs : gmap Addr (AddrClaim * AllocStatus * bool)) :
    allocator_cells_wf next allocations live issued Cs ->
    (b, e, r0, ι) ∈ allocations ->
    ι ∈ live ->
    allocator_cells Cs -∗
    ([∗ list] a ∈ finz.seq_between b e, a ↦ₛ ShadowLive ∗ addr_alloc a (Claimed ι)) ∗
    (([∗ list] a ∈ finz.seq_between b e, a ↦ₛ ShadowLive ∗ addr_alloc a Unclaimed) -∗
     ([∗ list] a;w ∈ finz.seq_between b e; ws, a ↦ₐ w) -∗
     allocator_cells
       (allocator_cells_update (finz.seq_between b e) allocator_free_cell Cs)).
  Proof.
    intros Hcwf Hentry Hlive. iIntros "Hcells".
    iDestruct (allocator_cells_range_acc (finz.seq_between b e)
                 (λ _, (Claimed ι, ShadowLive, false)) with "Hcells")
      as "[Hrange Hcells_close]".
    { apply finz_seq_between_NoDup. }
    { intros x Hx. apply elem_of_finz_seq_between in Hx.
      by apply (acw_live _ _ _ _ _ Hcwf b e r0 ι). }
    iEval (rewrite /cell_res' /cell_res /=) in "Hrange".
    iDestruct (big_sepL_sep with "Hrange") as "[Hclaims Hrange]".
    iDestruct (big_sepL_sep with "Hrange") as "[Hshadows _]".
    iSplitL "Hclaims Hshadows"; first (iApply big_sepL_sep; iFrame).
    iIntros "Hcells_free Hmem".
    iApply "Hcells_close".
    iDestruct (big_sepL2_mono _ (λ _ a _, a ↦ₐ -)%I with "Hmem") as "Hmem".
    { iIntros (k a0 w Ha Hw) "H". by iExists _. }
    iDestruct (big_sepL2_const_sepL_l with "Hmem") as "[_ Hmem]".
    iCombine "Hcells_free Hmem" as "Hcells".
    rewrite -big_sepL_sep.
    iApply (big_sepL_mono with "Hcells").
    iIntros (k x _) "[[Hs Hc] Hm]".
    rewrite /cell_res' /allocator_free_cell /cell_res /=. iFrame. done.
  Qed.

End AllocatorCommonWorld.
