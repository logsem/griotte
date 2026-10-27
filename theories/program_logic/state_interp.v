From iris.proofmode Require Import proofmode.
From griotte Require Import named_props_extra.
From griotte Require Export state_interp_def.

(** * The state interpretation: opening and closing, and its
    initialisation *)

Section state_interp.
  Context `{MP : MachineParameters}.
  Context `{!pcG Σ,
            !gen_heapGS RegName LWord Σ, !gen_heapGS SRegName LWord Σ,
            !gen_heapGS Addr LWord Σ, !gen_heapGS Addr AllocStatus Σ,
            !allocRegistryG Σ, !addrAllocG Σ, !trapVector, !cerise_na_invs Σ,
            !mtdcG Σ, !mieG Σ, !mpieG Σ}.

  Lemma SI_close σ lpc lreg ls lmem R C :
    erasure R C σ lpc lreg (ls_join ls) lmem →
    PC_auth lpc -∗ gen_heap_interp lreg -∗ sys_interp ls -∗ gen_heap_interp lmem -∗
    gen_heap_interp (shadowtbl σ) -∗ reg_auth R -∗ addr_alloc_auth C -∗
    cerise_state_interp σ.
  Proof.
    iIntros (Her) "HPCa Hr Hsys Hm Hst HR HC". iNamed "Hsys".
    destruct Hlsh as [Hn1 Hn2].
    destruct (erasure_split _ _ _ _ _ _ _ _ _ _ Hn1 Hn2 Her) as [Hsh Hth].
    iExists R, C. iSplitR "HPCa Hr Hmtdc Hmie Hmie_f Hwins".
    - iExists (ls_sh ls), lmem, (ls_mpie ls). iFrame. done.
    - iExists lpc, lreg, (ls_mtdc ls), (ls_vmtdc ls), (ls_mie ls). iFrame. done.
  Qed.

  Lemma SI_open σ :
    cerise_state_interp σ -∗
    ∃ (lpc : LWord) (lreg : LReg) (lsreg : LSys) (lmem : LMem) (R : RegState)
      (C : gmap Addr AddrClaim),
      "%Her" ∷ ⌜erasure R C σ lpc lreg (ls_join lsreg) lmem⌝ ∗
      "HPCa" ∷ PC_auth lpc ∗
      "Hr" ∷ gen_heap_interp lreg ∗
      "Hsr" ∷ sys_interp lsreg ∗
      "Hm" ∷ gen_heap_interp lmem ∗
      "Hst" ∷ gen_heap_interp (shadowtbl σ) ∗
      "HR" ∷ reg_auth R ∗
      "HC" ∷ addr_alloc_auth C.
  Proof.
    iIntros "(%R & %C & Hsh & Hth)". iNamed "Hsh". iNamed "Hth".
    iExists lpc, lreg, (MkLSys lsh m vm mie mpie), lmem, R, C. iFrame.
    iPureIntro. split_and!; [|done|apply Hersh|apply Hersh].
    by apply erasure_join.
  Qed.

  (** No points-to of the shared heap is at MTDC or mstatus. *)
  Lemma sys_interp_not_sys ls sr dq v :
    sys_interp ls -∗ sr ↦ₓ{dq} v -∗ ⌜sr ≠ MTDC ∧ sr ≠ MSTATUS⌝.
  Proof.
    iIntros "Hsys Hp". iNamed "Hsys". destruct Hlsh as [Hn1 Hn2].
    iDestruct (gen_heap_valid with "Hsr Hp") as %Hv.
    iPureIntro. split; intros ->; congruence.
  Qed.

  Lemma SI_sreg_not_sys σ sr dq v :
    cerise_state_interp σ -∗ sr ↦ₓ{dq} v -∗ ⌜sr ≠ MTDC ∧ sr ≠ MSTATUS⌝.
  Proof.
    iIntros "Hσ Hp". iDestruct (SI_open with "Hσ") as "Hσ". iNamed "Hσ".
    iApply (sys_interp_not_sys with "Hsr Hp").
  Qed.

  (** The points-to of the shared heap are in the logical system
      registers. *)
  Lemma sys_interp_valid ls (sregs : LSReg) :
    sys_interp ls -∗ ([∗ map] k↦y ∈ sregs, k ↦ₓ y) -∗
    ⌜sregs ⊆ ls_join ls ∧ ∀ sr, sr ∈ dom sregs → sr ≠ MTDC ∧ sr ≠ MSTATUS⌝.
  Proof.
    iIntros "Hsys Hmap". iNamed "Hsys". destruct Hlsh as [Hn1 Hn2].
    iAssert (⌜∀ l v, sregs !! l = Some v → ls_sh ls !! l = Some v⌝)%I as %Hincl.
    { iIntros (l v Hl). iDestruct (big_sepM_lookup with "Hmap") as "Hl"; first exact Hl.
      iApply (gen_heap_valid with "Hsr Hl"). }
    iPureIntro. split.
    - apply map_subseteq_spec. intros l v Hl. specialize (Hincl l v Hl).
      rewrite /ls_join lsregs_join_ne //; intros ->; congruence.
    - intros sr Hsr. apply elem_of_dom in Hsr as [v Hv]. specialize (Hincl sr v Hv).
      split; intros ->; congruence.
  Qed.

  Lemma sys_interp_valid_1 ls sr v :
    sys_interp ls -∗ sr ↦ₓ v -∗ ⌜ls_join ls !! sr = Some v ∧ sr ≠ MTDC ∧ sr ≠ MSTATUS⌝.
  Proof.
    iIntros "Hsys Hp". iDestruct (sys_interp_not_sys with "Hsys Hp") as %[H1 H2].
    iNamed "Hsys". iDestruct (gen_heap_valid with "Hsr Hp") as %Hv.
    iPureIntro. by rewrite /ls_join lsregs_join_ne.
  Qed.

  (** A write to the shared heap. *)
  Lemma sys_interp_update ls (sregs : LSReg) sr v :
    is_Some (sregs !! sr) →
    sys_interp ls -∗ ([∗ map] k↦y ∈ sregs, k ↦ₓ y) ==∗
    sys_interp (ls_insert_sh ls sr v) ∗ [∗ map] k↦y ∈ <[sr := v]> sregs, k ↦ₓ y.
  Proof.
    iIntros ([v0 Hv0]) "Hsys Hmap".
    iDestruct (big_sepM_lookup_acc with "Hmap") as "[Hp Hback]"; first exact Hv0.
    iDestruct (sys_interp_not_sys with "Hsys Hp") as %[H1 H2].
    iDestruct ("Hback" with "Hp") as "Hmap".
    iNamed "Hsys". destruct Hlsh as [Hn1 Hn2].
    rewrite (big_sepM_delete _ sregs sr) //. iDestruct "Hmap" as "[Hp Hmap]".
    iMod (gen_heap_update with "Hsr Hp") as "[Hsr Hp]".
    iModIntro. iSplitR "Hp Hmap".
    - iFrame. iPureIntro. rewrite /ls_insert_sh /= !lookup_insert_ne //.
    - rewrite big_sepM_insert_delete. iFrame.
  Qed.

  (** MTCC holds the trap vector. *)
  Lemma sys_interp_mtcc ls :
    sys_interp ls -∗ ⌜ls_join ls !! MTCC = Some (lword_of_word mtcc_vec)⌝.
  Proof.
    iIntros "Hsys". iNamed "Hsys".
    iDestruct (gen_heap_valid with "Hsr Hmtcc") as %Hv.
    iPureIntro. by rewrite /ls_join lsregs_join_ne.
  Qed.

  (** mstatus: each part pins its own bit. *)
  Lemma sys_interp_set_mstatus ls mie mpie :
    sys_interp ls ==∗ sys_interp (ls_set_mstatus ls mie mpie).
  Proof.
    iIntros "Hsys". iNamed "Hsys".
    iMod (MIE_update _ _ mie with "Hmie Hmie_f") as "[Hmie Hmie_f]".
    iMod (MPIE_update _ _ mpie with "Hmpie Hmpie_f") as "[Hmpie Hmpie_f]".
    iModIntro. by iFrame.
  Qed.

  (** mtdc: the fragment agrees with the ghost authority, and the write
      relabels it with any ghost value that stands for the new word. *)
  Lemma sys_interp_mtdc_agree ls m :
    sys_interp ls -∗ mtdc_frag m -∗ ⌜ls_mtdc ls = m ∧ mtdc_match m (ls_vmtdc ls)⌝.
  Proof.
    iIntros "Hsys Hf". iNamed "Hsys".
    iDestruct (mtdc_agree with "Hmtdc Hf") as %<-. done.
  Qed.

  Lemma sys_interp_set_mtdc ls m m' vm :
    mtdc_match m' vm →
    sys_interp ls -∗ mtdc_frag m ==∗ sys_interp (ls_set_mtdc ls m' vm) ∗ mtdc_frag m'.
  Proof.
    iIntros (Hm') "Hsys Hf". iNamed "Hsys".
    iMod (mtdc_update _ _ m' with "Hmtdc Hf") as "[Hmtdc Hf]".
    iModIntro. iFrame. done.
  Qed.
End state_interp.

(** * Initialisation of the ghost state

    The logical heaps start without identifiers: the logical registers and
    memory are the physical ones (with [lnull] at [cnull]), the registry is
    empty, and the heap addresses are heap roots on a given set [H] and
    unclaimed elsewhere. *)
(** The system registers that the state interpretation reserves. *)
Definition reserved_sregs : list SRegName := [MSTATUS; MEPCC; MCAUSE; MTVAL; MTCC].

Section ghost_init.
  Context `{MP : MachineParameters, TV : !trapVector}.

  (** The initial logical registers: the physical ones without identifiers,
      and [lnull] at [cnull]. *)
  Definition init_lregs (regs : Reg) : LReg :=
    match regs !! cnull with
    | Some _ => <[cnull := lnull]> (lword_of_word <$> regs)
    | None => lword_of_word <$> regs
    end.

  Definition init_lmem (m : Mem) : LMem := lword_of_word <$> m.

  Definition init_lsregs (sregs : SReg) : LSReg := lword_of_word <$> sregs.

  (** The initial claims: heap roots on [H], unclaimed elsewhere in the heap. *)
  Definition init_claims (H : gset Addr) : gmap Addr AddrClaim :=
    map_imap (λ a _, Some (if decide (a ∈ H) then HeapRoot else Unclaimed))
      (gset_to_gmap tt heap_addresses).

  (** Every initial word with authority is based on a heap root, heap roots
      are unpainted, memory avoids the memory-mapped devices and covers the
      heap, [cnull] holds zero, and every tagged executable word
      has closed bounds that avoid the heap; a tagged PC, MTCC or MEPCC is an
      unsealed executable capability; the system registers that the state
      interpretation reserves exist, MTCC holds the trap vector, mtval an
      integer and mstatus an encoding of MIE and MPIE. *)
  Record ghost_init_cond (σ : ExecConf) (H : gset Addr) : Prop := {
    gi_roots_heap a : a ∈ H → is_heap_address a = true;
    gi_roots_unpainted a : a ∈ H → shadowtbl σ !! a = Some ShadowLive;
    gi_shadow a : is_heap_address a = true → is_Some (shadowtbl σ !! a);
    gi_mem a w b : mem σ !! a = Some w → get_tag w = true → heap_authority_base w = Some b → b ∈ H;
    gi_pc b : get_tag (pcc σ) = true → heap_authority_base (pcc σ) = Some b → b ∈ H;
    gi_regs r w b : r ≠ cnull → reg σ !! r = Some w → get_tag w = true →
                    heap_authority_base w = Some b → b ∈ H;
    gi_sregs sr w b : sreg σ !! sr = Some w → get_tag w = true →
                      heap_authority_base w = Some b → b ∈ H;
    gi_mmio : mem_avoids_mmio (mem σ);
    gi_heap_mapped : heap_mapped (mem σ);
    gi_cnull w : reg σ !! cnull = Some w → w = WInt 0;
    gi_mem_exec a w : mem σ !! a = Some w → lword_exec (lword_of_word w);
    gi_pc_exec : lword_exec (lword_of_word (pcc σ));
    gi_regs_exec r w : reg σ !! r = Some w → lword_exec (lword_of_word w);
    gi_sregs_exec sr w : sreg σ !! sr = Some w → lword_exec (lword_of_word w);
    gi_pc_ok : pc_ok (pcc σ);
    gi_sregs_pc_ok sr w : is_pc_sreg sr = true → sreg σ !! sr = Some w → pc_ok w;
    gi_reserved_sregs sr : sr ∈ reserved_sregs → is_Some (sreg σ !! sr);
    gi_mtcc : sreg σ !! MTCC = Some mtcc_vec;
    gi_mtval : ∃ z, sreg σ !! MTVAL = Some (WInt z);
    gi_mstatus : ∃ mie mpie, sreg σ !! MSTATUS = Some (WInt (mstatus_enc mie mpie));
  }.

  Lemma lookup_init_claims H a :
    init_claims H !! a =
      if is_heap_address a then Some (if decide (a ∈ H) then HeapRoot else Unclaimed) else None.
  Proof.
    rewrite /init_claims map_lookup_imap lookup_gset_to_gmap.
    destruct (is_heap_address a) eqn:Ha.
    - rewrite option_guard_True //=. by apply elem_of_heap_addresses.
    - rewrite option_guard_False //=. by rewrite elem_of_heap_addresses Ha.
  Qed.

  Lemma lookup_init_lregs regs r :
    init_lregs regs !! r = if decide (r = cnull) then (λ _, lnull) <$> regs !! r
                           else lword_of_word <$> regs !! r.
  Proof.
    rewrite /init_lregs. destruct (regs !! cnull) eqn:Hc.
    - case_decide as Hr; first subst r.
      + by rewrite lookup_insert_eq Hc.
      + by rewrite lookup_insert_ne // lookup_fmap.
    - case_decide; subst; by rewrite lookup_fmap ?Hc.
  Qed.

  Lemma init_erasure σ H :
    ghost_init_cond σ H →
    erasure ∅ (init_claims H) σ (lword_of_word (pcc σ)) (init_lregs (reg σ))
      (init_lsregs (sreg σ)) (init_lmem (mem σ)).
  Proof.
    intros Hinit.
    assert (∀ w, (∀ b, get_tag w = true → heap_authority_base w = Some b → b ∈ H) →
              lword_exec (lword_of_word w) →
              reg_word_ok ∅ (init_claims H) (lword_of_word w)) as Hok.
    { intros w Hroot Hexec. split; first by apply lword_prov_no_id. split; last done.
      intros b Ht Hab; cbn. rewrite lookup_init_claims.
      assert (is_heap_address b = true) as ->.
      { apply heap_authority_base_memory_cap_bounds in Hab as (? & ? & ? & ?). done. }
      case_decide as Hb; first done. exfalso. apply Hb, Hroot; done. }
    constructor.
    - constructor.
      + intros ι x a Hx. by rewrite lookup_empty in Hx.
      + intros ι x a Hx. by rewrite lookup_empty in Hx.
      + intros ι x a Hx. by rewrite lookup_empty in Hx.
      + intros a. rewrite lookup_init_claims. destruct (is_heap_address a); naive_solver.
      + intros a ι. rewrite lookup_init_claims. split.
        * destruct (is_heap_address a); last done. case_decide; done.
        * intros (x & Hx & _). by rewrite lookup_empty in Hx.
      + intros a. rewrite lookup_init_claims. destruct (is_heap_address a); last done.
        case_decide; last done. intros _. by apply Hinit.
      + apply Hinit.
    - split.
      + apply set_eq. intros r. rewrite !elem_of_dom lookup_init_lregs.
        case_decide; by rewrite fmap_is_Some.
      + intros r v. rewrite lookup_init_lregs. case_decide as Hr.
        * subst r. intros Hv. apply fmap_Some in Hv as (w & Hc & ->).
          exists w. split; first done. rewrite (gi_cnull _ _ Hinit w Hc). apply reg_phys_lnull.
        * intros Hv. apply fmap_Some in Hv as (w & Hw & ->).
          exists w. split; first done. apply reg_phys_lword_of_word.
    - intros v. rewrite lookup_init_lregs. case_decide; last done. intros Hv.
      apply fmap_Some in Hv as (? & _ & ->). done.
    - intros r v. rewrite lookup_init_lregs. case_decide.
      + intros Hv. apply fmap_Some in Hv as (? & _ & ->). apply reg_word_ok_lnull.
      + intros Hv. apply fmap_Some in Hv as (w & Hw & ->).
        apply Hok; last by eapply gi_regs_exec. intros b. eapply gi_regs; eauto.
    - intros sr v. rewrite /init_lsregs lookup_fmap. intros Hv.
      apply fmap_Some in Hv as (w & Hw & ->).
      exists w. split; first done. apply reg_phys_lword_of_word.
    - intros sr v. rewrite /init_lsregs lookup_fmap. intros Hv.
      apply fmap_Some in Hv as (w & Hw & ->).
      apply Hok; last by eapply gi_sregs_exec. intros b. eapply gi_sregs; eauto.
    - intros sr v _. rewrite /init_lsregs lookup_fmap. intros Hv _.
      by apply fmap_Some in Hv as (w & Hw & ->).
    - intros sr v Hsr. rewrite /init_lsregs lookup_fmap. intros Hv.
      apply fmap_Some in Hv as (w & Hw & ->). by eapply gi_sregs_pc_ok.
    - by rewrite /init_lmem dom_fmap_L.
    - intros a v pw Hv Hpw. rewrite /init_lmem lookup_fmap Hpw /= in Hv.
      injection Hv as <-.
      apply (reg_phys_mem_word_ok _ _ (lword_of_word pw)); last apply reg_phys_lword_of_word.
      apply Hok; last by eapply gi_mem_exec.
      intros b. eapply gi_mem; eauto.
    - apply Hinit.
    - apply reg_phys_lword_of_word.
    - apply Hok; last by apply (gi_pc_exec _ _ Hinit). intros b. by apply gi_pc.
    - apply Hinit.
    - apply Hinit.
  Qed.

  Context `{!ceriseGpreS Σ, !cerise_na_invs Σ}.

  (** The generic ghost initialisation of every adequacy theorem. It returns
      the state interpretation, the logical PC, register, mtdc, memory and
      shadow points-to, and the address claims. mtdc receives a ghost value
      [m0] that stands for its initial word. *)
  Lemma cerise_ghost_init σ H (m0 : mtdc_val) (wmtdc : Word) :
    ghost_init_cond σ H →
    sreg σ !! MTDC = Some wmtdc →
    mtdc_match m0 (lword_of_word wmtdc) →
    ⊢ |==> ∃ (mg : gen_heapGS Addr LWord Σ) (sg : gen_heapGS Addr AllocStatus Σ)
             (pg : pcG Σ)
             (rg : gen_heapGS RegName LWord Σ) (srg : gen_heapGS SRegName LWord Σ)
             (regg : allocRegistryG Σ) (ag : addrAllocG Σ)
             (mtg : mtdcG Σ) (mieg : mieG Σ) (mpieg : mpieG Σ),
      cerise_state_interp σ ∗
      PC ↦ₚ lword_of_word (pcc σ) ∗
      ([∗ map] r ↦ w ∈ init_lregs (reg σ), r ↦ᵣ w) ∗
      mtdc ↦ₜ m0 ∗
      ([∗ map] a ↦ w ∈ init_lmem (mem σ), a ↦ₐ w) ∗
      ([∗ map] a ↦ s ∈ shadowtbl σ, a ↦ₛ s) ∗
      ([∗ map] a ↦ c ∈ init_claims H, addr_alloc a c).
  Proof.
    iIntros (Hinit Hmtdc Hm0).
    destruct (gi_mstatus _ _ Hinit) as (mie0 & mpie0 & Hmst).
    set (lsh := delete MTDC (delete MSTATUS (init_lsregs (sreg σ)))).
    iMod (PC_init (lword_of_word (pcc σ))) as (pg) "[Hpc Hpcs]".
    iMod (gen_heap_init (init_lregs (reg σ))) as (rg) "(Hr & Hrs & _)".
    iMod (gen_heap_init lsh) as (srg) "(Hsr & Hsrs & _)".
    iMod (gen_heap_init (init_lmem (mem σ))) as (mg) "(Hm & Hms & _)".
    iMod (gen_heap_init (shadowtbl σ)) as (sg) "(Hst & Hsts & _)".
    iMod registry_init as (regg) "HR".
    iMod (addr_alloc_init (init_claims H)) as (ag) "[HC HCs]".
    iMod (mtdc_init m0) as (mtg) "[Hmtdc Hmtdc_f]".
    iMod (MIE_init mie0) as (mieg) "[Hmie Hmie_f]".
    iMod (MPIE_init mpie0) as (mpieg) "[Hmpie Hmpie_f]".
    iModIntro. iExists mg, sg, pg, rg, srg, regg, ag, mtg, mieg, mpieg.
    assert (∀ sr, sr ≠ MTDC → sr ≠ MSTATUS → lsh !! sr = lword_of_word <$> sreg σ !! sr)
      as Hlsh.
    { intros sr H1 H2. rewrite /lsh !lookup_delete_ne; [|congruence..].
      by rewrite /init_lsregs lookup_fmap. }
    destruct (gi_reserved_sregs _ _ Hinit MEPCC) as [wepcc Hwepcc]; first set_solver.
    destruct (gi_reserved_sregs _ _ Hinit MCAUSE) as [wcause Hwcause]; first set_solver.
    destruct (gi_mtval _ _ Hinit) as [ztval Hwtval].
    pose proof (gi_mtcc _ _ Hinit) as Hwtcc.
    iDestruct (big_sepM_delete _ _ MEPCC with "Hsrs") as "[Hmepcc Hsrs]".
    { rewrite Hlsh // Hwepcc //. }
    iDestruct (big_sepM_delete _ _ MCAUSE with "Hsrs") as "[Hmcause Hsrs]".
    { rewrite lookup_delete_ne // Hlsh // Hwcause //. }
    iDestruct (big_sepM_delete _ _ MTVAL with "Hsrs") as "[Hmtval Hsrs]".
    { rewrite lookup_delete_ne // lookup_delete_ne // Hlsh // Hwtval //. }
    iDestruct (big_sepM_delete _ _ MTCC with "Hsrs") as "[Hmtcc Hsrs]".
    { rewrite lookup_delete_ne // lookup_delete_ne // lookup_delete_ne // Hlsh // Hwtcc //. }
    set (ls := MkLSys lsh m0 (lword_of_word wmtdc) mie0 mpie0).
    assert (ls_join ls = init_lsregs (sreg σ)) as Hjoin.
    { apply map_eq. intros i. rewrite /ls_join /lsregs_join /=.
      destruct (decide (i = MSTATUS)) as [->|H1].
      { by rewrite lookup_insert_eq /init_lsregs lookup_fmap Hmst. }
      rewrite lookup_insert_ne; last congruence.
      destruct (decide (i = MTDC)) as [->|H2].
      { by rewrite lookup_insert_eq /init_lsregs lookup_fmap Hmtdc. }
      rewrite lookup_insert_ne; last congruence.
      rewrite Hlsh //. by rewrite /init_lsregs lookup_fmap. }
    iAssert (sys_interp ls)
      with "[Hsr Hmtcc Hmepcc Hmcause Hmtval Hmtdc Hmie Hmie_f Hmpie Hmpie_f]" as "Hsys".
    { iFrame "Hsr Hmtcc Hmtdc Hmie Hmie_f Hmpie Hmpie_f". iSplit; first done.
      iSplitL "Hmepcc Hmcause Hmtval".
      - iSplitL "Hmepcc Hmcause"; iLeft; iFrame.
      - iPureIntro. rewrite /ls /lsh /=. split.
        + by rewrite lookup_delete_eq.
        + rewrite lookup_delete_ne //. by rewrite lookup_delete_eq. }
    iFrame "Hpcs Hrs Hmtdc_f Hms Hsts HCs".
    iApply (SI_close with "Hpc Hr Hsys Hm Hst HR HC").
    rewrite Hjoin. by apply init_erasure.
  Qed.

  (** The projection of the initial logical memory onto the physical one. *)
  Lemma init_lmem_pointsto `{!gen_heapGS Addr LWord Σ} (m : Mem) :
    ([∗ map] a ↦ w ∈ init_lmem m, a ↦ₐ w) ⊣⊢ [∗ map] a ↦ w ∈ m, a ↦ₐ lword_of_word w.
  Proof. by rewrite /init_lmem big_sepM_fmap. Qed.
End ghost_init.
