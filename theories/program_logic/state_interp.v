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
            !mtdcG Σ, !mieG Σ, !mpieG Σ, !postureG Σ, !mtdcLentG Σ, !hwmG Σ}.

  Lemma SI_close σ lpc lreg ls lmem R C :
    erasure R C σ lpc lreg (ls_join ls) lmem →
    PC_auth lpc -∗ gen_heap_interp lreg -∗ sys_interp ls -∗ gen_heap_interp lmem -∗
    gen_heap_interp (shadowtbl σ) -∗ reg_auth R -∗ addr_alloc_auth C -∗
    cerise_state_interp σ.
  Proof.
    iIntros (Her) "HPCa Hr Hsys Hm Hst HR HC". iNamed "Hsys".
    destruct Hlsh as [Hn1 Hn2]. destruct Hlsh_hwm as [Hn3 Hn4].
    destruct (erasure_split _ _ _ _ _ _ _ _ _ _ _ _ Hn1 Hn2 Hn3 Hn4 Her) as [Hsh Hth].
    iExists R, C.
    iSplitR "HPCa Hr Hmtdc Hlent Hmie Hmshwmb_a Hmshwm_a Hpend_si Hlent_a Hzone".
    - iExists (ls_sh ls), lmem, (ls_mpie ls). iFrame. done.
    - iExists lpc, lreg, (ls_mtdc ls), (ls_vmtdc ls), (ls_mie ls), (ls_hwmb ls), (ls_hwm ls),
        (ls_pend ls), (ls_lent ls).
      iFrame. done.
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
    iExists lpc, lreg, (MkLSys lsh m vm mie mpie mshwmb_v mshwm_v o L), lmem, R, C.
    iFrame "HPCa Hr Hm Hst HR HC". iSplitR; first (iPureIntro; by apply erasure_join).
    rewrite /sys_interp /=.
    iFrame "Hsr Hmtcc Hmpie Hmtdc Hlent Hmie Hmshwmb_a Hmshwm_a Hpend_si Hlent_a Hzone".
    iPureIntro. split_and!; try done; apply Hersh.
  Qed.

  (** No points-to of the shared heap is at MTDC or mstatus. *)
  Lemma sys_interp_not_sys ls sr dq v :
    sys_interp ls -∗ sr ↦ₓ{dq} v -∗ ⌜sr ≠ mtdc ∧ sr ≠ mstatus⌝.
  Proof.
    iIntros "Hsys Hp". iNamed "Hsys". destruct Hlsh as [Hn1 Hn2].
    iDestruct (gen_heap_valid with "Hsr Hp") as %Hv.
    iPureIntro. split; intros ->; congruence.
  Qed.

  (** No points-to of the shared heap is at MSHWM or MSHWMB. *)
  Lemma sys_interp_not_hwm ls sr dq v :
    sys_interp ls -∗ sr ↦ₓ{dq} v -∗ ⌜sr ≠ mshwm ∧ sr ≠ mshwmb⌝.
  Proof.
    iIntros "Hsys Hp". iNamed "Hsys". destruct Hlsh_hwm as [Hn1 Hn2].
    iDestruct (gen_heap_valid with "Hsr Hp") as %Hv.
    iPureIntro. split; intros ->; congruence.
  Qed.

  (** The same for a map of points-to. *)
  Lemma sys_interp_not_hwm_map ls (sregs : LSReg) :
    sys_interp ls -∗ ([∗ map] k↦y ∈ sregs, k ↦ₓ y) -∗
    ⌜∀ sr, sr ∈ dom sregs → sr ≠ mshwm ∧ sr ≠ mshwmb⌝.
  Proof.
    iIntros "Hsys Hmap" (sr Hsr). apply elem_of_dom in Hsr as [v Hv].
    iDestruct (big_sepM_lookup with "Hmap") as "Hp"; first exact Hv.
    iApply (sys_interp_not_hwm with "Hsys Hp").
  Qed.

  (** A full points-to is outside [hc, MSHWM), [hc] the cover base: the
      zone and the lent halves cover that range, and the state
      interpretation holds half of each of their cells. *)
  Lemma sys_interp_pointsto_outside ls (a : Addr) w :
    sys_interp ls -∗ a ↦ₐ w -∗
    ⌜¬ (hc_of (ls_hwmb ls) (ls_pend ls) ≤ a < ls_hwm ls)%Z⌝.
  Proof.
    iIntros "Hsys Ha". iNamed "Hsys". iNamed "Hzone".
    iDestruct (zone_cells_not_elem with "Hzone_cells Ha") as %Ha1.
    iDestruct (zone_cells_not_elem with "Hlent_cells Ha") as %Ha2.
    iPureIntro. intros Hin. apply Hzone_cover in Hin. set_solver.
  Qed.

  Lemma SI_sreg_not_sys σ sr dq v :
    cerise_state_interp σ -∗ sr ↦ₓ{dq} v -∗ ⌜sr ≠ mtdc ∧ sr ≠ mstatus⌝.
  Proof.
    iIntros "Hσ Hp". iDestruct (SI_open with "Hσ") as "Hσ". iNamed "Hσ".
    iApply (sys_interp_not_sys with "Hsr Hp").
  Qed.

  (** The points-to of the shared heap are in the logical system
      registers. *)
  Lemma sys_interp_valid ls (sregs : LSReg) :
    sys_interp ls -∗ ([∗ map] k↦y ∈ sregs, k ↦ₓ y) -∗
    ⌜sregs ⊆ ls_join ls ∧ ∀ sr, sr ∈ dom sregs → sr ≠ mtdc ∧ sr ≠ mstatus⌝.
  Proof.
    iIntros "Hsys Hmap". iNamed "Hsys". destruct Hlsh as [Hn1 Hn2].
    destruct Hlsh_hwm as [Hn3 Hn4].
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
    sys_interp ls -∗ sr ↦ₓ v -∗ ⌜ls_join ls !! sr = Some v ∧ sr ≠ mtdc ∧ sr ≠ mstatus⌝.
  Proof.
    iIntros "Hsys Hp". iDestruct (sys_interp_not_sys with "Hsys Hp") as %[H1 H2].
    iDestruct (sys_interp_not_hwm with "Hsys Hp") as %[H3 H4].
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
    iDestruct (sys_interp_not_hwm with "Hsys Hp") as %[H3 H4].
    iDestruct ("Hback" with "Hp") as "Hmap".
    iNamed "Hsys". destruct Hlsh as [Hn1 Hn2]. destruct Hlsh_hwm as [Hn3 Hn4].
    rewrite (big_sepM_delete _ sregs sr) //. iDestruct "Hmap" as "[Hp Hmap]".
    iMod (gen_heap_update with "Hsr Hp") as "[Hsr Hp]".
    iModIntro. iSplitR "Hp Hmap".
    - iFrame. iPureIntro. rewrite /ls_insert_sh /=.
      split_and!; try done; rewrite lookup_insert_ne //.
    - rewrite big_sepM_insert_delete. iFrame.
  Qed.

  (** MTCC holds the trap vector, for the holder of the unwedged token. *)
  Lemma sys_interp_mtcc ls :
    sys_interp ls -∗ unwedged -∗ ⌜ls_join ls !! mtcc = Some (lword_of_word mtcc_vec)⌝.
  Proof.
    iIntros "Hsys HU". iNamed "Hsys". destruct Hlsh as [Hn1 Hn2].
    destruct Hlsh_hwm as [Hn3 Hn4].
    iDestruct "Hmtcc" as "[ [Hmtcc _] | (%w & _ & _ & HU' & _)]"; last first.
    { iDestruct (unwedged_excl with "HU HU'") as %[]. }
    iDestruct (gen_heap_valid with "Hsr Hmtcc") as %Hv.
    iPureIntro. by rewrite /ls_join lsregs_join_ne.
  Qed.

  (** Once mtcc is wedged, it holds an untagged word. *)
  Lemma sys_interp_mtcc_wedged ls :
    sys_interp ls -∗
    mtcc_wedged -∗
    ∃ w : LWord, ⌜ls_join ls !! mtcc = Some w ∧ get_tag w.(lw) = false⌝.
  Proof.
    iIntros "Hsys #Hwedged". iNamed "Hsys". destruct Hlsh as [Hn1 Hn2].
    destruct Hlsh_hwm as [Hn3 Hn4].
    iDestruct "Hmtcc" as "[ [_ Hpend] | (%w & Hmtcc & %Htag & _ & _)]".
    { iDestruct (mtcc_pending_wedged with "Hpend Hwedged") as %[]. }
    iDestruct (gen_heap_valid with "Hsr Hmtcc") as %Hv.
    iExists w. iPureIntro. split; last done. by rewrite /ls_join lsregs_join_ne.
  Qed.

  (** The wedge of MTCC: from the pending branch of [SI_mtcc], with the
      unwedged token, MTCC receives an untagged word [w'], and [SI_mtcc]
      takes its wedged branch, which holds the token. *)
  Lemma mtcc_wedge_update (lsh : LSReg) (w' : LWord) :
    get_tag w'.(lw) = false →
    gen_heap_interp lsh ∗
    mtcc ↦ₓ lword_of_word mtcc_vec ∗
    mtcc_pending ∗
    unwedged
    ==∗
    gen_heap_interp (<[mtcc := w']> lsh) ∗
    SI_mtcc ∗
    mtcc_wedged.
  Proof.
    iIntros (Htag) "(Hsr & Hmtcc & Hpend & HU)".
    iMod (gen_heap_update _ _ _ w' with "Hsr Hmtcc") as "[$ Hmtcc]".
    iMod (own_update with "Hpend") as "#Hwedged"; last first.
    { iModIntro. iSplitL; last iExact "Hwedged".
      iRight. iExists w'. iFrame "Hmtcc HU". iSplit; first done. iExact "Hwedged". }
    by apply cmra_update_exclusive.
  Qed.

  (** MIE and MPIE: the fragments agree with the state interpretation. *)
  Lemma sys_interp_mie_agree ls b :
    sys_interp ls -∗ MIE_frag b -∗ ⌜ls_mie ls = b⌝.
  Proof. iIntros "Hsys Hf". iNamed "Hsys". iApply (MIE_agree with "Hmie Hf"). Qed.

  Lemma sys_interp_mpie_agree ls b :
    sys_interp ls -∗ MPIE_frag b -∗ ⌜ls_mpie ls = b⌝.
  Proof. iIntros "Hsys Hf". iNamed "Hsys". iApply (MPIE_agree with "Hmpie Hf"). Qed.

  (** mstatus: a write of MIE, with its fragment, and a write of MIE and
      MPIE, with both fragments. *)
  Lemma sys_interp_set_mie ls b mie :
    sys_interp ls -∗ MIE_frag b ==∗
    sys_interp (ls_set_mstatus ls mie (ls_mpie ls)) ∗ MIE_frag mie.
  Proof.
    iIntros "Hsys Hf". iNamed "Hsys".
    iMod (MIE_update _ _ mie with "Hmie Hf") as "[Hmie Hf]".
    iModIntro. by iFrame.
  Qed.

  Lemma sys_interp_set_mstatus ls b p mie mpie :
    sys_interp ls -∗ MIE_frag b -∗ MPIE_frag p ==∗
    sys_interp (ls_set_mstatus ls mie mpie) ∗ MIE_frag mie ∗ MPIE_frag mpie.
  Proof.
    iIntros "Hsys Hf Hpf". iNamed "Hsys".
    iMod (MIE_update _ _ mie with "Hmie Hf") as "[Hmie Hf]".
    iMod (MPIE_update _ _ mpie with "Hmpie Hpf") as "[Hmpie Hpf]".
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

  (** The write transfers the clause of the mtdc token: [L1] is given up
      for [L2]. *)
  Lemma sys_interp_set_mtdc ls m m' vm (L1 L2 : iProp Σ) :
    mtdc_match m' vm →
    (mtdc_clause m ∗ L1 ⊢ |==> mtdc_clause m' ∗ L2) →
    sys_interp ls -∗ mtdc_frag m -∗ L1 ==∗ sys_interp (ls_set_mtdc ls m' vm) ∗ mtdc_frag m' ∗ L2.
  Proof.
    iIntros (Hm' Htr) "Hsys Hf HL". iNamed "Hsys".
    iDestruct (mtdc_agree with "Hmtdc Hf") as %<-.
    iMod (Htr with "[$Hlent $HL]") as "[Hlent HL]".
    iMod (mtdc_update _ _ m' with "Hmtdc Hf") as "[Hmtdc Hf]".
    iModIntro. iFrame. done.
  Qed.

  (** The holder of the mtdc token knows that the ghost value is the home
      value. *)
  Lemma sys_interp_mtdc_lent ls :
    sys_interp ls -∗ mtdc_lent -∗ ⌜ls_mtdc ls = mtdc_home⌝.
  Proof. iIntros "Hsys Hl". iNamed "Hsys". iApply (mtdc_clause_lent with "Hlent Hl"). Qed.

  (** MSHWMB, MSHWM, the window and the lent set: the fragments agree with
      the state interpretation. *)
  Lemma sys_interp_mshwmb_agree ls mshwmb_v :
    sys_interp ls -∗ mshwmb_frag mshwmb_v -∗ ⌜ls_hwmb ls = mshwmb_v⌝.
  Proof. iIntros "Hsys Hf". iNamed "Hsys". iApply (mshwmb_agree with "Hmshwmb_a Hf"). Qed.

  Lemma sys_interp_mshwm_agree ls mshwm_v :
    sys_interp ls -∗ mshwm_frag mshwm_v -∗ ⌜ls_hwm ls = mshwm_v⌝.
  Proof. iIntros "Hsys Hf". iNamed "Hsys". iApply (mshwm_agree with "Hmshwm_a Hf"). Qed.

  Lemma sys_interp_pend_cl_agree ls o :
    sys_interp ls -∗ pend_cl o -∗ ⌜ls_pend ls = o⌝.
  Proof. iIntros "Hsys Hf". iNamed "Hsys". iApply (pend_si_agree with "Hpend_si Hf"). Qed.

  Lemma sys_interp_pend_frag_agree ls o :
    sys_interp ls -∗ pend_frag o -∗ ⌜ls_pend ls = o⌝.
  Proof. iIntros "Hsys Hf". iNamed "Hsys". iApply (pend_si_frag_agree with "Hpend_si Hf"). Qed.

  Lemma sys_interp_pend_half_agree ls o :
    sys_interp ls -∗ pend_half o -∗ ⌜ls_pend ls = o⌝.
  Proof. iIntros "Hsys Hf". iNamed "Hsys". iApply (pend_si_half_agree with "Hpend_si Hf"). Qed.

  Lemma sys_interp_lent_agree ls L :
    sys_interp ls -∗ lent_frag L -∗ ⌜ls_lent ls = L⌝.
  Proof. iIntros "Hsys Hf". iNamed "Hsys". iApply (lent_agree with "Hlent_a Hf"). Qed.

  (** The high-water-mark part of [sys_interp], and its closing with new
      values: the physical pair, the window and the lent set change; the
      rest is kept. *)
  Lemma sys_interp_hwm_open ls :
    sys_interp ls -∗
    mshwmb_auth (ls_hwmb ls) ∗
    mshwm_auth (ls_hwm ls) ∗
    pend_si (ls_pend ls) ∗
    lent_auth (ls_lent ls) ∗
    hwm_zone (hc_of (ls_hwmb ls) (ls_pend ls)) (ls_hwm ls) (ls_lent ls) ∗
    (∀ mshwmb_v mshwm_v o L, mshwmb_auth mshwmb_v -∗ mshwm_auth mshwm_v -∗ pend_si o -∗ lent_auth L -∗
       hwm_zone (hc_of mshwmb_v o) mshwm_v L -∗
       sys_interp (ls_set_win (ls_set_hwm (ls_set_hwmb ls mshwmb_v) mshwm_v) o L)).
  Proof.
    iIntros "Hsys". iNamed "Hsys".
    iFrame "Hmshwmb_a Hmshwm_a Hpend_si Hlent_a Hzone".
    iIntros (mshwmb_v mshwm_v o L) "Hmshwmb_a Hmshwm_a Hpend_si Hlent_a Hzone". rewrite /sys_interp /=.
    iFrame "Hsr Hmtcc Hmpie Hmtdc Hlent Hmie Hmshwmb_a Hmshwm_a Hpend_si Hlent_a Hzone".
    iPureIntro. done.
  Qed.

  Lemma ls_set_win_hwm_id ls :
    ls_set_win (ls_set_hwm (ls_set_hwmb ls (ls_hwmb ls)) (ls_hwm ls)) (ls_pend ls) (ls_lent ls)
    = ls.
  Proof. by destruct ls. Qed.
End state_interp.

(** * Initialisation of the ghost state

    The logical heaps start without identifiers: the logical registers and
    memory are the physical ones (with [lnull] at [cnull]), the registry is
    empty, and the heap addresses are heap roots on a given set [H] and
    unclaimed elsewhere. *)
(** The system registers that the state interpretation reserves. *)
Definition reserved_sregs : list SRegName := [mstatus; mepcc; mcause; mtval; mtcc].

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
      integer and mstatus an encoding of MIE and MPIE; MSHWMB and MSHWM hold
      two addresses in order, and memory holds integers between them. *)
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
    gi_mtcc : sreg σ !! mtcc = Some mtcc_vec;
    gi_mtval : ∃ z, sreg σ !! mtval = Some (WInt z);
    gi_mstatus : ∃ mie mpie, sreg σ !! mstatus = Some (WInt (mstatus_enc mie mpie));
    gi_hwm : ∃ zb zh : Addr,
      sreg σ !! mshwmb = Some (WInt zb) ∧ sreg σ !! mshwm = Some (WInt zh) ∧
      (zb <= zh)%a ∧
      ∀ a : Addr, (zb <= a < zh)%a → ∃ z, mem σ !! a = Some (WInt z);
  }.

  (** The initial zone: the addresses between MSHWMB and MSHWM. *)
  Definition init_zone (sregs : SReg) : gset Addr :=
    match sregs !! mshwmb, sregs !! mshwm with
    | Some (WInt zb), Some (WInt zh) =>
        match z_to_addr zb, z_to_addr zh with
        | Some b, Some e => list_to_set (finz.seq_between b e)
        | _, _ => ∅
        end
    | _, _ => ∅
    end.

  Lemma init_zone_eq (sregs : SReg) (zb zh : Addr) :
    sregs !! mshwmb = Some (WInt zb) → sregs !! mshwm = Some (WInt zh) →
    init_zone sregs = list_to_set (finz.seq_between zb zh).
  Proof. intros Hb Hh. by rewrite /init_zone Hb Hh !finz_of_z_to_z. Qed.

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

  Context `{!ceriseGpreS Σ, !cerise_na_invs Σ, !postureG Σ, !mtdcLentG Σ}.

  (** The generic ghost initialisation of every adequacy theorem. It returns
      the state interpretation, the logical PC, register, mtdc, memory and
      shadow points-to, the address claims, the fragments of MIE and MPIE
      at their initial values, the volatile registers (MEPCC, mcause,
      mtval), and the high-water-mark resources. mtdc receives a ghost value
      [m0] that stands for its initial word and is the home value of the
      mtdc token; MTCC is pending. The zone starts as [init_zone], the
      addresses between MSHWMB and MSHWM, whose memory points-to are cells
      of the zone; the window is closed, nothing is lent, and there is no
      last owner: the fragments of MSHWMB and MSHWM, the window clause's and
      the code's quarters, the lent fragment, both parts of the last owner
      and the stack base (the initial MSHWMB) are returned. *)
  Lemma cerise_ghost_init σ H (m0 : mtdc_val) (wmtdc : Word) :
    ghost_init_cond σ H →
    sreg σ !! mtdc = Some wmtdc →
    mtdc_match m0 (lword_of_word wmtdc) →
    mtdc_home = m0 →
    mtcc_pending ⊢ |==> ∃ (mg : gen_heapGS Addr LWord Σ) (sg : gen_heapGS Addr AllocStatus Σ)
             (pg : pcG Σ)
             (rg : gen_heapGS RegName LWord Σ) (srg : gen_heapGS SRegName LWord Σ)
             (regg : allocRegistryG Σ) (ag : addrAllocG Σ)
             (mtg : mtdcG Σ) (mieg : mieG Σ) (mpieg : mpieG Σ) (hwmg : hwmG Σ),
      cerise_state_interp σ ∗
      PC ↦ₚ lword_of_word (pcc σ) ∗
      ([∗ map] r ↦ w ∈ init_lregs (reg σ), r ↦ᵣ w) ∗
      mtdc ↦ₜ m0 ∗
      ([∗ map] a ↦ w ∈ init_lmem (mem σ),
         if decide (a ∈ init_zone (sreg σ)) then zone_cell a else a ↦ₐ w) ∗
      ([∗ map] a ↦ s ∈ shadowtbl σ, a ↦ₛ s) ∗
      ([∗ map] a ↦ c ∈ init_claims H, addr_alloc a c) ∗
      (∃ mie0 mpie0,
         ⌜sreg σ !! mstatus = Some (WInt (mstatus_enc mie0 mpie0))⌝ ∗
         MIE_frag mie0 ∗
         MPIE_frag mpie0) ∗
      (∃ v, mepcc ↦ₓ v) ∗
      (∃ v, mcause ↦ₓ v) ∗
      (∃ z : Z, mtval ↦ₓ lword_of_word (WInt z)) ∗
      (∃ zb zh : Z,
         ⌜sreg σ !! mshwmb = Some (WInt zb) ∧ sreg σ !! mshwm = Some (WInt zh)⌝ ∗
         mshwmb ↦ₜ zb ∗
         mshwm ↦ₜ zh ∗
         pend_cl None ∗
         pend_frag None ∗
         lent_frag ∅ ∗
         last_owner_auth None ∗
         last_owner_frag None ∗
         hwm_base zb).
  Proof.
    iIntros (Hinit Hmtdc Hm0 Hhome) "Hpending".
    destruct (gi_mstatus _ _ Hinit) as (mie0 & mpie0 & Hmst).
    destruct (gi_hwm _ _ Hinit) as (zb & zh & Hhwmb & Hhwm & Hzbh & Hzone_int).
    set (lsh := delete mshwm (delete mshwmb (delete mtdc (delete mstatus
                  (init_lsregs (sreg σ)))))).
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
    iMod (hwm_init_zone zb zh (init_zone (sreg σ)))
      as (hwmg) "(Hmshwmb_a & Hmshwmb_f & Hmshwm_a & Hmshwm_f & Hzone_auth & Hzone_toks &
                  (Hlent_a & Hlent_f & Hpend) & Hlast_owner_a & Hlast_owner_f & Hbase)".
    iDestruct (pend_full_split with "Hpend") as "(Hpend_si & Hpend_cl & Hpend_f)".
    iDestruct (zone_cells_init (init_zone (sreg σ)) with "Hms Hzone_toks")
      as "[Hms Hzone_cells]".
    { intros a. rewrite (init_zone_eq _ zb zh) // elem_of_list_to_set elem_of_finz_seq_between.
      intros Ha. destruct (Hzone_int a Ha) as [z Hz].
      exists z. rewrite /init_lmem lookup_fmap Hz //. }
    iModIntro. iExists mg, sg, pg, rg, srg, regg, ag, mtg, mieg, mpieg, hwmg.
    assert (∀ sr, sr ≠ mtdc → sr ≠ mstatus → sr ≠ mshwm → sr ≠ mshwmb →
              lsh !! sr = lword_of_word <$> sreg σ !! sr)
      as Hlsh.
    { intros sr H1 H2 H3 H4. rewrite /lsh !lookup_delete_ne; [|congruence..].
      by rewrite /init_lsregs lookup_fmap. }
    destruct (gi_reserved_sregs _ _ Hinit mepcc) as [wepcc Hwepcc]; first set_solver.
    destruct (gi_reserved_sregs _ _ Hinit mcause) as [wcause Hwcause]; first set_solver.
    destruct (gi_mtval _ _ Hinit) as [ztval Hwtval].
    pose proof (gi_mtcc _ _ Hinit) as Hwtcc.
    iDestruct (big_sepM_delete _ _ mepcc with "Hsrs") as "[Hmepcc Hsrs]".
    { rewrite Hlsh // Hwepcc //. }
    iDestruct (big_sepM_delete _ _ mcause with "Hsrs") as "[Hmcause Hsrs]".
    { rewrite lookup_delete_ne // Hlsh // Hwcause //. }
    iDestruct (big_sepM_delete _ _ mtval with "Hsrs") as "[Hmtval Hsrs]".
    { rewrite lookup_delete_ne // lookup_delete_ne // Hlsh // Hwtval //. }
    iDestruct (big_sepM_delete _ _ mtcc with "Hsrs") as "[Hmtcc Hsrs]".
    { rewrite lookup_delete_ne // lookup_delete_ne // lookup_delete_ne // Hlsh // Hwtcc //. }
    set (ls := MkLSys lsh m0 (lword_of_word wmtdc) mie0 mpie0 zb zh None ∅).
    assert (ls_join ls = init_lsregs (sreg σ)) as Hjoin.
    { apply map_eq. intros i. rewrite /ls_join /lsregs_join /=.
      destruct (decide (i = mstatus)) as [->|H1].
      { by rewrite lookup_insert_eq /init_lsregs lookup_fmap Hmst. }
      rewrite lookup_insert_ne; last congruence.
      destruct (decide (i = mtdc)) as [->|H2].
      { by rewrite lookup_insert_eq /init_lsregs lookup_fmap Hmtdc. }
      rewrite lookup_insert_ne; last congruence.
      destruct (decide (i = mshwmb)) as [->|H3].
      { by rewrite lookup_insert_eq /init_lsregs lookup_fmap Hhwmb. }
      rewrite lookup_insert_ne; last congruence.
      destruct (decide (i = mshwm)) as [->|H4].
      { by rewrite lookup_insert_eq /init_lsregs lookup_fmap Hhwm. }
      rewrite lookup_insert_ne; last congruence.
      rewrite Hlsh //. by rewrite /init_lsregs lookup_fmap. }
    iAssert (hwm_zone zb zh ∅) with "[Hzone_auth Hzone_cells]" as "Hzone".
    { iExists _. iFrame "Hzone_auth Hzone_cells". rewrite /zone_halves big_sepS_empty.
      iSplit; last done. iPureIntro. intros a Ha.
      rewrite union_empty_r_L (init_zone_eq _ zb zh) // elem_of_list_to_set
        elem_of_finz_seq_between.
      solve_addr. }
    iAssert (sys_interp ls)
      with "[Hsr Hmtcc Hpending Hmtdc Hmie Hmpie Hmshwmb_a Hmshwm_a Hpend_si Hlent_a Hzone]"
      as "Hsys".
    { iFrame "Hsr Hmtdc Hmie Hmpie Hmshwmb_a Hmshwm_a Hpend_si Hlent_a Hzone".
      iSplitL "Hmtcc Hpending".
      { iLeft. iFrame. }
      iSplit; first done. iSplit; first (iLeft; iPureIntro; by rewrite Hhome).
      iPureIntro. rewrite /ls /lsh /=. split_and!.
      + rewrite lookup_delete_ne // lookup_delete_ne //. by rewrite lookup_delete_eq.
      + rewrite lookup_delete_ne // lookup_delete_ne // lookup_delete_ne //.
        by rewrite lookup_delete_eq.
      + by rewrite lookup_delete_eq.
      + rewrite lookup_delete_ne //. by rewrite lookup_delete_eq. }
    iFrame "Hpcs Hrs Hmtdc_f Hms Hsts HCs".
    iSplitR "Hmie_f Hmpie_f Hmepcc Hmcause Hmtval Hmshwmb_f Hmshwm_f Hpend_cl Hpend_f Hlent_f
             Hlast_owner_a Hlast_owner_f Hbase".
    { iApply (SI_close with "Hpc Hr Hsys Hm Hst HR HC").
      rewrite Hjoin. by apply init_erasure. }
    iSplitL "Hmie_f Hmpie_f"; first by iExists mie0, mpie0; iFrame.
    iSplitL "Hmepcc"; first by iExists _.
    iSplitL "Hmcause"; first by iExists _.
    iSplitL "Hmtval"; first by iExists ztval.
    iExists zb, zh. iFrame. done.
  Qed.

  (** The projection of the initial logical memory onto the physical one. *)
  Lemma init_lmem_pointsto `{!gen_heapGS Addr LWord Σ} (m : Mem) :
    ([∗ map] a ↦ w ∈ init_lmem m, a ↦ₐ w) ⊣⊢ [∗ map] a ↦ w ∈ m, a ↦ₐ lword_of_word w.
  Proof. by rewrite /init_lmem big_sepM_fmap. Qed.

  (** The initial memory, with the cells of a zone [zn] there and the
      points-to elsewhere. *)
  Lemma init_lmem_pointsto_cond `{!gen_heapGS Addr LWord Σ} `{!hwmG Σ}
      (m : Mem) (zn : gset Addr) :
    ([∗ map] a ↦ w ∈ init_lmem m,
       if decide (a ∈ zn) then zone_cell a else a ↦ₐ w) ⊣⊢
    [∗ map] a ↦ w ∈ m,
      if decide (a ∈ zn) then zone_cell a else a ↦ₐ lword_of_word w.
  Proof. by rewrite /init_lmem big_sepM_fmap. Qed.
End ghost_init.
