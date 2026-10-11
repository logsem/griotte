From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode memory_region region_keys.
From griotte.allocators.ownership Require Import allocator_header_spec allocator_free_spec_states.

(** * Logical steps of the proof of [free]

    The lemmas of this file do not execute code. They are used between the
    block groups of [allocator_free_spec_<segment>_blocks_<n>] in the proofs
    of the specifications of [free]. *)

Section AllocatorFreeWorld.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {FA : FreeAuth Σ}
    {allocator_ownerg : allocatorOwnerG Σ}
    {MP : MachineParameters} {layout : allocatorLayout}.

  (** Observe the capability in [ca1] at its base [b]: the cell is claimed by
      [ι], so the claim/header clause names the header entry of [ι], whose
      bounds are [b] and [e]. The allocator's piece of the status token of
      [ι], the client half and the shares of the cells rebuild the whole
      token. *)
  Lemma allocator_free_observe
    (E : coPset) (p : Perm) (g : Locality) (ι : AId) (b e a next : Addr)
    (allocations : list allocator_header_entry) (live issued : gset AId)
    (Cs : gmap Addr (AddrClaim * AllocStatus * bool)) :
    (heap_b < b /\ b < e /\ e <= heap_e)%a ->
    allocator_entries_wf allocations ->
    allocator_cells_wf next allocations live issued Cs ->
    ca1 ↦ᵣ (WCap true p g b e a) @@ ι -∗
    alloc_obj ι b e -∗
    free_auth_held ι -∗
    ([∗ list] _ ∈ finz.seq_between b e, ι ↦st{share (finz.dist b e)} ALive) -∗
    allocator_cells Cs -∗
    allocator_entries_res live allocations -∗
    |~{E}~> ∃ r0,
      ⌜(b, e, r0, ι) ∈ allocations⌝ ∗
      ⌜ι ∈ live⌝ ∗
      ca1 ↦ᵣ (WCap true p g b e a) @@ ι ∗
      allocator_cells Cs ∗
      ι ↦st{1} ALive ∗
      (∀ live', ⌜∀ ι', ι' ≠ ι -> (ι' ∈ live <-> ι' ∈ live')⌝ -∗
         allocator_tok live' ι b e -∗ allocator_entries_res live' allocations).
  Proof.
    intros Hbounds Hwf Hcwf.
    iIntros "Hca1 #Hobj Hheld Hshares Hcells Htoks".
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
    rewrite /allocator_tok decide_True //.
    iDestruct "Htok" as "[Hshare Hkept]".
    iModIntro. iExists r0. iFrame "Hca1 Hcells Htoks_close". iSplit; first done.
    iSplit; first done.
    rewrite (st_own_split_alloc ι (finz.seq_between b e))
      finz_seq_between_length -free_auth_split.
    iFrame.
  Qed.

  (** The shadow entries and the header read by the local check of [free]:
      the word below the requested base and the base, and the end and the
      owner recorded in the header when both shadow checks pass. The check
      succeeds exactly when the requested bounds are those of a ghost header
      entry recorded with the owner [o]: header words are exactly the painted
      cells, so the word below [b] is painted and [b] is not exactly when [b]
      is a payload base. *)
  Lemma allocator_free_header_acc
    (next b e : Addr) (o : Z) (allocations : list allocator_header_entry) (live issued : gset AId)
    (Cs : gmap Addr (AddrClaim * AllocStatus * bool)) :
    (heap_b < b /\ b < e /\ e <= next /\ next <= heap_e)%a ->
    allocator_chain (heap_b ^+ 1)%a next allocations ->
    allocator_cells_wf next allocations live issued Cs ->
    allocator_cells Cs -∗
    allocator_headers (heap_b ^+ 1)%a next allocations -∗
    ∃ (s1 s2 : AllocStatus) (eh : Addr) (oh : Z),
      ⌜s1 = ShadowQuarantined ∧ s2 = ShadowLive ∧ eh = e ∧ oh = o <->
        allocator_owned_bounds allocations o b e⌝ ∗
      ⌜s1 = ShadowQuarantined -> s2 = ShadowLive ->
        (heap_b + allocator_header_words < b)%Z⌝ ∗
      (b ^+ (-1))%a ↦ₛ s1 ∗
      b ↦ₛ s2 ∗
      (if decide (s1 = ShadowQuarantined ∧ s2 = ShadowLive)
       then (b ^+ (- allocator_header_words))%a ↦ₐ WInt eh ∗
            ((b ^+ (- allocator_header_words)) ^+ 1)%a ↦ₐ WInt oh
       else emp) ∗
      ((b ^+ (-1))%a ↦ₛ s1 -∗
       b ↦ₛ s2 -∗
       (if decide (s1 = ShadowQuarantined ∧ s2 = ShadowLive)
        then (b ^+ (- allocator_header_words))%a ↦ₐ WInt eh ∗
             ((b ^+ (- allocator_header_words)) ^+ 1)%a ↦ₐ WInt oh
        else emp) -∗
       allocator_cells Cs ∗ allocator_headers (heap_b ^+ 1)%a next allocations).
  Proof.
    intros Hbounds Hchain Hcwf.
    iIntros "Hcells Hheaders".
    assert (Hb1 : ((b ^+ -1) + 1)%a = Some b) by solve_addr.
    destruct (acw_dom _ _ _ _ _ Hcwf (b ^+ -1)%a) as [ [ [c1 s1] h1] Hc1]; first solve_addr.
    destruct (acw_dom _ _ _ _ _ Hcwf b) as [ [ [c2 s2] h2] Hc2]; first solve_addr.
    pose proof (acw_header _ _ _ _ _ Hcwf _ _ _ _ Hc1) as Hh1.
    pose proof (acw_header _ _ _ _ _ Hcwf _ _ _ _ Hc2) as Hh2.
    pose proof (acw_painted _ _ _ _ _ Hcwf _ _ _ _ Hc1) as Hp1.
    pose proof (acw_painted _ _ _ _ _ Hcwf _ _ _ _ Hc2) as Hp2.
    (* A ghost header entry at [b] is seen by the check. *)
    assert (Hseen : ∀ e' r ι, (b, e', r, ι) ∈ allocations ->
      s1 = ShadowQuarantined ∧ s2 = ShadowLive).
    { intros e' r ι Hin. split.
      - apply Hp1, Hh1. by eapply allocator_is_header_below.
      - destruct s2; first done. exfalso.
        pose proof (allocator_chain_member_bounds _ _ _ _ _ _ _ Hchain Hin).
        apply (allocator_chain_payload_not_header _ _ _ _ _ _ _ b Hchain Hin);
          first solve_addr.
        by apply Hh2, Hp2. }
    iDestruct (allocator_cells_shadow_pair _ (b ^+ -1)%a b with "Hcells")
      as "(Hs1 & Hs2 & Hcells_close)"; [solve_addr|exact Hc1|exact Hc2|].
    destruct (decide (s1 = ShadowQuarantined ∧ s2 = ShadowLive)) as [ [-> ->]|Hcheck].
    - (* The base follows a header word: it is the base of an entry. *)
      destruct (allocator_is_header_base allocations (b ^+ -1)%a b) as (e' & [oh r] & ι & Hin).
      { by apply Hh1, Hp1. }
      { intros Hh. by apply Hh2 in Hh; apply Hp2 in Hh. }
      { exact Hb1. }
      pose proof (allocator_chain_member_header _ _ _ _ _ _ _ Hchain Hin) as Hhb.
      iDestruct (allocator_headers_acc with "Hheaders") as "(Hend & Hown & Hheaders_close)";
        first exact Hin.
      iExists ShadowQuarantined, ShadowLive, e', oh.
      case_decide as Hd; last (exfalso; naive_solver).
      iFrame "Hs1 Hs2 Hend Hown". iSplit.
      { iPureIntro. split.
        - intros (_ & _ & -> & ->). by exists r, ι.
        - intros (r' & ι' & Hin').
          destruct (allocator_chain_base_unique _ _ _ _ _ _ _ _ _ _ Hchain Hin Hin')
            as (-> & Hr & _).
          injection Hr as -> _. done. }
      iSplit; first (iPureIntro; intros _ _; unfold allocator_header_words in *; solve_addr).
      iIntros "Hs1 Hs2 [Hend Hown]".
      iSplitL "Hcells_close Hs1 Hs2"; first iApply ("Hcells_close" with "Hs1 Hs2").
      iApply ("Hheaders_close" with "Hend Hown").
    - (* The check fails before the header is read. *)
      iExists s1, s2, b, o.
      case_decide as Hd; first (exfalso; naive_solver).
      iFrame "Hs1 Hs2". iSplit.
      { iPureIntro. split.
        - intros (? & ? & _). exfalso. by apply Hcheck.
        - intros (r & ι & Hin). exfalso. by apply Hcheck, (Hseen e (o, r) ι). }
      iSplit; first (iPureIntro; intros ? ?; exfalso; naive_solver).
      iSplitR; first done.
      iIntros "Hs1 Hs2 _". iFrame "Hheaders". iApply ("Hcells_close" with "Hs1 Hs2").
  Qed.

  (** The owner link: the entry of an identifier [ι] in the owner set [Ω] of
      [id] records [id], since the owner sets are an exact view of the header
      list. *)
  Lemma allocator_free_owner_entry
    (id : Z) (Ω : gset AId) (b e : Addr) (r0 : Z * Z) (ι : AId)
    (allocations : list allocator_header_entry) :
    allocator_entries_wf allocations ->
    (b, e, r0, ι) ∈ allocations ->
    ι ∈ Ω ->
    allocator_service_owners allocations -∗
    allocator_owner_id id Ω -∗
    ⌜r0.1 = id⌝.
  Proof.
    intros Hwf Hentry HιΩ. iIntros "Howners Hid".
    iDestruct "Howners" as (O) "[Howners %Hown_wf]".
    iDestruct (allocator_owners_agree with "Howners Hid") as %HOid.
    destruct r0 as [o0 r0].
    iPureIntro. exact (allocator_owners_wf_member _ _ _ _ _ _ _ _ _ Hown_wf (proj2 Hwf) Hentry
      HOid HιΩ).
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

  (** Release the entry of [ι], which is dead: its cells are unclaimed and
      unpainted, and the allocator holds its whole status token. *)
  Lemma allocator_free_release
    (next b e : Addr) (r0 : Z * Z) (ι : AId)
    (allocations : list allocator_header_entry) (live issued : gset AId)
    (Cs : gmap Addr (AddrClaim * AllocStatus * bool)) :
    (heap_b < next /\ next <= heap_e)%a ->
    allocator_chain (heap_b ^+ 1)%a next allocations ->
    allocator_entries_wf allocations ->
    allocator_cells_wf next allocations live issued Cs ->
    (b, e, r0, ι) ∈ allocations ->
    allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next -∗
    allocator_headers (heap_b ^+ 1)%a next allocations -∗
    allocator_service_owners allocations -∗
    allocator_cells (allocator_cells_update (finz.seq_between b e) allocator_free_cell Cs) -∗
    (∀ live', ⌜∀ ι', ι' ≠ ι -> (ι' ∈ live <-> ι' ∈ live')⌝ -∗
       allocator_tok live' ι b e -∗ allocator_entries_res live' allocations) -∗
    ι ↦st{1} ADead -∗
    ι ⊒ AQuar -∗
    allocator_service_data next.
  Proof.
    intros Hnext Hchain Hwf Hcwf Hentry.
    iIntros "Hslot Hheaders Howners Hcells Htoks_close Hdead #Hq".
    iExists allocations, (live ∖ {[ι]}), issued, _.
    iFrame "Hslot Hheaders Howners Hcells".
    iSplit; first done.
    iSplit; first done.
    iSplit.
    { iPureIntro. eapply allocator_cells_wf_free; eauto. }
    iApply ("Htoks_close" with "[] [Hdead]").
    { iPureIntro. intros ι' Hι'. clear -Hι'. set_solver. }
    rewrite /allocator_tok decide_False; last (clear; set_solver).
    iExists ADead. iFrame "Hdead Hq".
  Qed.

End AllocatorFreeWorld.
