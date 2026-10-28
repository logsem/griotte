From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre ectx_lifting.
From griotte Require Export rules_trap_entry rules_SpecialRW rules_Mret.

(** * The volatile control and status registers

    Trap entry lends MEPCC, mcause and mtval to the error path of the
    switcher, which gives them back before the next fault can occur (after
    reading them, or with [mret]). The rules for the volatile registers that
    are lent (MEPCC, mcause, mtval, [mret]) and for the register that the
    state interpretation keeps (mstatus) follow. *)

Section vcsr.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {CL : CritLink Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : griotte_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
  Implicit Types w : LWord.

  (** ** The lent registers *)

  (** "vcsr" stands for the volatile control and status registers: those
      that every trap entry overwrites (MEPCC and mcause, and on the machine
      also mtval and the MIE and MPIE bits of mstatus). Their contents are only
      meaningful between a trap entry and the next trap.

      [vcsr_res] is the right to read and write them now, and [vcsr_frag sr v]
      its view of one register [sr] holding [v]. They are backed by the
      points-to that trap entry lends out, while the state interpretation
      holds the trap-entry token. mtval is lent too, but given back on its
      own ([wp_vcsr_tval_return]). mstatus is not lent: it is read through
      the rules for the registers of the state interpretation below. Both
      definitions are sealed, so that their backing can change without
      changing the specifications that use them. *)

  (** The view of a lent volatile register [sr] (MEPCC, mcause or mtval),
      holding [vsr]. *)
  Definition vcsr_frag_def (sr : SRegName) (vsr : LWord) : iProp Σ := sr ↦ₓ vsr.
  #[local] Definition vcsr_frag_aux : seal (@vcsr_frag_def). Proof. by eexists. Qed.
  Definition vcsr_frag := vcsr_frag_aux.(unseal).
  #[local] Definition vcsr_frag_unseal : @vcsr_frag = @vcsr_frag_def := vcsr_frag_aux.(seal_eq).

  (** MEPCC and mcause, with any values: what the error path gives back
      first. *)
  Definition vcsr_res_def : iProp Σ :=
    ∃ wepcc wcause, vcsr_frag MEPCC wepcc ∗ vcsr_frag MCAUSE wcause.
  #[local] Definition vcsr_res_aux : seal (@vcsr_res_def). Proof. by eexists. Qed.
  Definition vcsr_res := vcsr_res_aux.(unseal).
  #[local] Definition vcsr_res_unseal : @vcsr_res = @vcsr_res_def := vcsr_res_aux.(seal_eq).

  #[global] Instance vcsr_frag_timeless sr vsr : Timeless (vcsr_frag sr vsr).
  Proof. rewrite vcsr_frag_unseal. apply _. Qed.

  #[global] Instance vcsr_res_timeless : Timeless vcsr_res.
  Proof. rewrite vcsr_res_unseal. apply _. Qed.

  Lemma vcsr_res_intro wepcc wcause :
    vcsr_frag MEPCC wepcc -∗
    vcsr_frag MCAUSE wcause -∗
    vcsr_res.
  Proof. rewrite vcsr_res_unseal. iIntros "Hmepcc Hmcause". iExists _, _. iFrame. Qed.

  Lemma vcsr_res_elim :
    vcsr_res -∗
    ∃ wepcc wcause, vcsr_frag MEPCC wepcc ∗ vcsr_frag MCAUSE wcause.
  Proof. rewrite vcsr_res_unseal. by iIntros "H". Qed.

  (** The resources of trap entry are the views of the lent volatile
      registers: MEPCC holds the faulting PC, mcause a cause that satisfies
      the cause predicate [P_mcause], mtval a value that satisfies the value
      predicate [P_mtval]. *)
  Lemma trap_entry_out_vcsr_frag P_mcause P_mtval w :
    trap_entry_out_cause P_mcause P_mtval w -∗
    vcsr_frag MEPCC (lmepcc_of_pc w) ∗
    (∃ cause : Z, ⌜P_mcause cause⌝ ∗ vcsr_frag MCAUSE (lword_of_word (WInt cause))) ∗
    (∃ tval : Z, ⌜P_mtval tval⌝ ∗ vcsr_frag MTVAL (lword_of_word (WInt tval))).
  Proof. rewrite trap_entry_out_unfold vcsr_frag_unseal. by iIntros "H". Qed.

  (** The return of MEPCC and mcause to the state interpretation, in front
      of any instruction: the trap-entry token without [Ntval] comes
      back. *)
  Lemma wp_vcsr_return E e Φ :
    to_val e = None →
    vcsr_res -∗
    (trap_vcsr_res -∗ WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    rewrite vcsr_res_unseal /vcsr_res_def vcsr_frag_unseal.
    iIntros (He) "(%wepcc & %wcause & Hmepcc & Hmcause) HΦ".
    by iApply (wp_trap_entry_return with "Hmepcc Hmcause").
  Qed.

  (** The return of mtval to the state interpretation, in front of any
      instruction, once MEPCC and mcause are back: the trap-entry token comes
      back. *)
  Lemma wp_vcsr_tval_return E e Φ (z : Z) :
    to_val e = None →
    vcsr_frag MTVAL (lword_of_word (WInt z)) -∗
    trap_vcsr_res -∗
    (trap_entry_res -∗ WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    rewrite vcsr_frag_unseal.
    iIntros (He) "Hmtval Hvcsr HΦ".
    iApply (wp_tval_return with "Hmtval"); first done.
    iIntros "Htval". iApply "HΦ".
    iApply trap_entry_res_vcsr_tval. iFrame.
  Qed.

  (** The converse of [wp_vcsr_return]: the trap-entry token without
      [Ntval] lends MEPCC and mcause, with their current values, in front of
      any instruction ([cspecialw mepcc] of the context install then writes
      MEPCC through its view). *)
  Lemma wp_vcsr_lend E e Φ :
    to_val e = None →
    trap_vcsr_res -∗
    (∀ wepcc wcause,
       vcsr_frag MEPCC wepcc -∗
       vcsr_frag MCAUSE wcause -∗
       WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    rewrite vcsr_frag_unseal.
    iIntros (He) "Htok HΦ".
    iEval (rewrite wp_unfold /wp_pre He).
    iIntros (σ1 ns κ κs nt) "[Hσ Hlink] /=".
    iDestruct (SI_open with "Hσ") as "Hσ". iNamed "Hσ".
    iDestruct (sys_interp_trap_lend with "Hsr Htok")
      as (wepcc wcause) "(_ & Hsr & Hmepcc & Hmcause)".
    iSpecialize ("HΦ" with "Hmepcc Hmcause").
    iEval (rewrite wp_unfold /wp_pre He) in "HΦ".
    iApply ("HΦ" $! σ1 ns κ κs nt). iFrame "Hlink".
    iApply (SI_close _ _ _ _ _ _ _ Her with "HPCa Hr Hsr Hm Hst HR HC").
  Qed.

  (** ** Rules for the lent registers *)

  (** [cspecialr dst, sr] on a lent volatile register (MEPCC, or mcause or
      mtval with [csrr]). *)
  Lemma wp_cspecialr_vcsr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst wdst sr vsr dq :
    decodeInstrW w.(lw) = SpecialRW dst sr (inr cnull) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ wdst ∗
        ▷ vcsr_frag sr vsr }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          dst ↦ᵣ vsr ∗
          vcsr_frag sr vsr }}}.
  Proof.
    rewrite vcsr_frag_unseal.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hcnull φ) "(>HPC & >Hpc_a & >Hdst & >Hsrc) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iDestruct (map_of_sregs_1 with "Hsrc") as "Hsmap".
    iApply (wp_SpecialRW with "[$HPC $Hmap $Hsmap $Hpc_a]");
      [exact Hinstr | exact Hvpc
      | rewrite /regs_of /operands_of /regs_of_argument dom_singleton_L; set_solver
      | rewrite Hxsr /sregs_of dom_singleton_L; set_solver |].
    iNext. iIntros (lpc' regs' sregs' retv) "(%Hspec & HPC & Hpc_a & Hmap & Hsmap)".
    destruct (SpecialRW_spec_success_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hxsr Hpca' Hspec)
      as (-> & -> & vold & Hvold & Hsr' & ->).
    rewrite /specialrw_sregs /= in Hsr'. case_decide as Hc; last done. simplify_map_eq.
    rewrite specialrw_regs_ne // insert_singleton_eq.
    iApply "Hφ". iFrame.
    iDestruct (regs_of_map_1 with "Hmap") as "$".
    iApply (sregs_of_map_1 with "Hsmap").
  Qed.

  (** [cspecialw mepcc, src]: the lent volatile register MEPCC receives the
      legalised word. *)
  Lemma wp_cspecialw_mepcc E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src vsrc vold dq :
    decodeInstrW w.(lw) = SpecialRW cnull MEPCC (inr src) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ vsrc ∗
        ▷ vcsr_frag MEPCC vold }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          src ↦ᵣ vsrc ∗
          vcsr_frag MEPCC (llegalise MEPCC vsrc) }}}.
  Proof.
    rewrite vcsr_frag_unseal.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hcnull φ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_1 with "Hsrc") as "Hmap".
    iDestruct (map_of_sregs_1 with "Hdst") as "Hsmap".
    iApply (wp_SpecialRW with "[$HPC $Hmap $Hsmap $Hpc_a]");
      [exact Hinstr | exact Hvpc
      | rewrite /regs_of /operands_of /regs_of_argument dom_singleton_L; set_solver
      | rewrite Hxsr /sregs_of dom_singleton_L; set_solver |].
    iNext. iIntros (lpc' regs' sregs' retv) "(%Hspec & HPC & Hpc_a & Hmap & Hsmap)".
    destruct (SpecialRW_spec_success_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hxsr Hpca' Hspec)
      as (-> & -> & vold' & Hvold & Hsr' & ->).
    rewrite /specialrw_sregs /= in Hsr'. case_decide as Hc; first done.
    rewrite llookup_reg_not_cnull // in Hsr'.
    simplify_map_eq. rewrite insert_singleton_eq.
    rewrite specialrw_regs_cnull.
    iApply "Hφ". iFrame.
    iDestruct (regs_of_map_1 with "Hmap") as "$".
    iApply (sregs_of_map_1 with "Hsmap").
  Qed.

  (** [mret] ends the window of the context install: the PC receives MEPCC,
      MIE receives MPIE in the state interpretation, and MEPCC and mcause
      return to it against the trap-entry token without [Ntval]. *)
  Lemma wp_mret_vcsr_link E pc_p pc_g pc_b pc_e pc_a pc_π w wepcc wcause dq
      (T1 T2 : iProp Σ) :
    decodeInstrW w.(lw) = Mret →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    link_transfer mie_from_mpie T1 T2 →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ vcsr_frag MEPCC wepcc ∗
        ▷ vcsr_frag MCAUSE wcause ∗
        ▷ T1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ wepcc ∗
          pc_a ↦ₐ{dq} w ∗
          trap_vcsr_res ∗
          T2 }}}.
  Proof.
    rewrite vcsr_frag_unseal.
    iIntros (Hinstr Hvpc Hxsr Htr φ) "(>HPC & >Hpc_a & >Hmepcc & >Hmcause & HT) Hφ".
    iAssert ([∗ map] k↦y ∈ (∅ : LReg), k ↦ᵣ y)%I as "Hmap0"; first by rewrite big_sepM_empty.
    iApply (wp_instr_step_link _ _ _ _ _ _ _ _ _ _ ∅ with "HPC Hpc_a Hmap0"); eauto.
    iNext; iIntros (r psr m st lreg lsreg lmem R C c σ') "@".
    iDestruct (sys_interp_valid_1 with "Hsr Hmepcc") as %[Hvepcc' _].
    pose proof (ls_join_mstatus lsreg) as Hvst'.
    rewrite Hinstr /exec in Hstep.
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hvepcc') as (wepcc' & Hwepcc & Hrelepcc).
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hvst') as (wst & Hwst & Hrelst).
    apply reg_phys_no_bounds in Hrelst; last done. cbn in Hrelst. subst wst.
    cbn in Hstep. rewrite Hxsr Hwepcc Hwst /= mpie_of_mstatus_enc in Hstep.
    injection Hstep as <- <-.
    rewrite /update_pcc /update_sreg /=.
    (* The new mstatus, then the new PC: MEPCC satisfies the PC invariant. *)
    pose proof (erasure_insert_sreg _ _ _ _ _ _ _ _ _ _ _ MSTATUS
      (lword_of_word (WInt (mstatus_enc (ls_mpie lsreg) InterruptEnabled)))
      (WInt (mstatus_enc (ls_mpie lsreg) InterruptEnabled)) Her) as Her1.
    specialize (Her1 ltac:(apply reg_word_ok_int) ltac:(by intros) ltac:(by intros)
                  ltac:(apply reg_phys_lword_of_word)).
    rewrite -ls_join_set_mstatus in Her1.
    pose proof (erasure_set_pc _ _ _ _ _ _ _ _ _ _ _ wepcc wepcc' Her1) as Her2.
    specialize (Her2 ltac:(by eapply (er_sreg_words _ _ _ _ _ _ _ Her)) Hrelepcc
                  ltac:(by eapply (er_sreg_pc_ok _ _ _ _ _ _ _ Her MEPCC))).
    iMod (sys_interp_set_mstatus _ (ls_mpie lsreg) InterruptEnabled with "Hsr") as "Hsr".
    (* The lent registers return. *)
    iDestruct (sys_interp_trap_return with "Hsr Hmepcc Hmcause") as "(_ & Hsr & Htok)".
    iMod (PC_update _ _ wepcc with "HPCa HPC") as "[HPCa HPC]".
    iMod (Htr _ (wepcc', r,
                 <[MSTATUS := WInt (mstatus_enc (ls_mpie lsreg) InterruptEnabled)]> psr, m, st)
           with "[$Hlink $HT]") as "[Hlink HT]".
    { split.
      - by rewrite /mie_st /mpie_st /= lookup_insert_eq Hwst /= mie_of_mstatus_enc
          mpie_of_mstatus_enc.
      - by rewrite /= lookup_insert_ne. }
    iPoseProof (SI_close _ _ _ _ _ _ _ Her2 with "HPCa Hr Hsr Hm Hst HR HC") as "HSI".
    iModIntro. iFrame "HSI Hlink". iApply "Hφ". iFrame.
  Qed.

  (** ** Rules for the registers of the state interpretation *)

  (** The MIE that [SpecialRW _ mstatus src] writes: none for the source
      [inr cnull], else MIE of the source. *)
  Definition mstatus_src_mie (regs : LReg) (src : Z + RegName) : option InterruptStatus :=
    match src with
    | inl z => Some (mie_of z)
    | inr rs =>
        if decide (rs = cnull) then None else (λ x : LWord, mie_of (get_a x.(lw))) <$> regs !!ₗ rs
    end.

  (** The physical mstatus after [SpecialRW _ mstatus src]. *)
  Lemma specialrw_mstatus_phys R (regs : LReg) pc (r : Reg) psr m st src psr' :
    lregs_phys R regs r →
    regs_of_argument src ∖ {[ cnull ]} ⊆ dom regs →
    (match src with
     | inr rs =>
         if decide (rs = cnull) then Some (pc, r, psr, m, st)
         else wsrc ← r !!ᵣ rs;
              Some (update_sreg (pc, r, psr, m, st) MSTATUS (legalise MSTATUS wsrc))
     | inl z => Some (update_sreg (pc, r, psr, m, st) MSTATUS (legalise MSTATUS (WInt z)))
     end) = Some (pc, r, psr', m, st) →
    match mstatus_src_mie regs src with
    | None => psr' = psr
    | Some b => ∃ mpie, psr' = <[MSTATUS := WInt (mstatus_enc b mpie)]> psr
    end.
  Proof.
    intros Hregs Dsrc Hφ. destruct src as [z|rs]; cbn in *.
    - simplify_eq. by eexists.
    - case_decide as Hrs; first by simplify_eq.
      assert (is_Some (regs !!ₗ rs)) as [v Hv].
      { apply elem_of_dom_lreg. apply Dsrc. set_solver. }
      destruct (llookup_reg_phys _ _ _ _ _ Hregs Hv) as (s & Hrs' & _).
      rewrite Hrs' /= in Hφ. rewrite Hv /=. simplify_eq.
      eexists. by rewrite get_a_and_tag.
  Qed.

  (** [SpecialRW dst mstatus src]: mstatus is held by the state
      interpretation, so its old value is any value, and a write to it is
      not observed. The write may change MIE: link-transfer premise. *)
  Lemma wp_specialrw_reserved_success_link E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst src
      (regs : LReg) dq (T1 T2 : iProp Σ) :
    decodeInstrW w.(lw) = SpecialRW dst MSTATUS src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    regs_of (SpecialRW dst MSTATUS src) ⊆ dom regs →
    link_transfer (mie_update (mstatus_src_mie regs src)) T1 T2 →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        ▷ T1 }}}
      Instr Executable @ E
      {{{ vold, RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          ([∗ map] k↦y ∈ specialrw_regs regs dst vold, k ↦ᵣ y) ∗
          T2 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Dregs Htr φ) "(>HPC & >Hpc_a & >Hmap & HT) Hφ".
    iApply (wp_instr_step_link with "HPC Hpc_a Hmap"); eauto.
    iNext; iIntros (r psr m st lreg lsreg lmem R C c σ') "@".
    set (vold := lword_of_word (WInt (mstatus_enc (ls_mie lsreg) (ls_mpie lsreg)))).
    assert (ls_join lsreg !! MSTATUS = Some vold) as Hvold' by apply ls_join_mstatus.
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hvold') as (wold & Hwold & Hrelold).
    pose proof (er_sreg_words _ _ _ _ _ _ _ Her _ _ Hvold') as Hokold.
    destruct (specialrw_sregs_phys R C _ r psr m st _ lreg (ls_join lsreg) lmem regs
                {[MSTATUS := vold]} MSTATUS src vold Her Hlregs Hregs)
      as (sregs' & psr' & lsreg' & _ & Hφ1 & _ & _).
    { by apply map_singleton_subseteq_l. }
    { rewrite /regs_of /operands_of in Dregs. set_solver. } { by simplify_map_eq. }
    rewrite Hinstr /exec in Hstep.
    cbn in Hstep. rewrite Hxsr Hwold /= Hφ1 /= in Hstep.
    assert (regs_of_argument src ∖ {[ cnull ]} ⊆ dom regs) as Dsrc.
    { rewrite /regs_of /operands_of in Dregs. set_solver. }
    pose proof (specialrw_mstatus_phys _ _ _ _ _ _ _ _ _ Hregs Dsrc Hφ1) as Hpsr'.
    iAssert (|==> ∃ ls',
               ⌜erasure R C (WCap true pc_p pc_g pc_b pc_e pc_a, r, psr', m, st)
                  (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) lreg (ls_join ls') lmem⌝ ∗
               ⌜mie_update (mstatus_src_mie regs src)
                  (WCap true pc_p pc_g pc_b pc_e pc_a, r, psr, m, st)
                  (WCap true pc_p pc_g pc_b pc_e pc_a, r, psr', m, st)⌝ ∗
               sys_interp ls')%I
      with "[Hsr]" as ">(%ls' & %Her1 & %Hrel & Hsr)".
    { destruct (mstatus_src_mie regs src) as [b|].
      - destruct Hpsr' as [mpie' ->].
        iMod (sys_interp_set_mstatus _ b mpie' with "Hsr") as "Hsr".
        iModIntro. iExists _. iFrame "Hsr". iPureIntro. split.
        + rewrite ls_join_set_mstatus. apply erasure_insert_sreg; first done.
          * apply reg_word_ok_int.
          * by intros.
          * by intros.
          * apply reg_phys_lword_of_word.
        + split; first by rewrite /= lookup_insert_ne.
          by rewrite /mie_st /= lookup_insert_eq /= mie_of_mstatus_enc.
      - subst psr'. iModIntro. iExists lsreg. by iFrame "Hsr". }
    assert (incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) =
              Some (WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π)) as Hi.
    { by apply incrementPC_add. }
    iApply (instr_close_link_transfer _ _ _ _ (WCap true pc_p pc_g pc_b pc_e pc_a, r, psr', m, st)
              with "Hlink HT"); [exact Htr | by apply mie_update_kept |].
    case_decide as Hdst.
    - (* The old value is dropped. *)
      destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hi) as (pc' & Hu & _).
      iApply (instr_close_pc_update _ _ _ _ _ _ _ _ _ _ _ _ 1 _ _ _
        (λ lpc' retv, lpc' = WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∧ retv = NextIV)
        with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
      { exact Her1. } { rewrite /nextPC in Hu Hstep. by rewrite Hu in Hstep |- *. }
      { intros lpc'' Hi'. rewrite /incrementPC in Hi. simplify_eq. done. }
      { intros Hi'. rewrite /incrementPC in Hi. congruence. }
      iIntros (lpc'' retv [-> ->]) "HPC Hmap HT". iApply ("Hφ" $! vold).
      subst dst. rewrite specialrw_regs_cnull. by iFrame.
    - (* [dst] receives the old value. *)
      destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _
        (erasure_linsert_reg _ _ _ _ _ _ _ _ _ _ _ dst vold wold Her1 Hokold Hrelold) Hi)
        as (pc' & Hu & _).
      iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ dst vold wold _ _ _
        (λ lpc' regs' retv, lpc' = WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∧
                            regs' = <[dst := vold]> regs ∧ retv = NextIV)
        with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
      { exact Her1. } { exact Hlregs. }
      { right. apply Dregs. rewrite /regs_of /operands_of. set_solver. }
      { exact Hokold. }
      { rewrite /update_reg /= in Hu Hstep |- *. by rewrite Hu in Hstep |- *. }
      { exact Hrelold. }
      { intros lpc'' Hi'. rewrite Hi in Hi'. simplify_eq. by rewrite linsert_reg_not_cnull. }
      { intros Hi'. congruence. }
      iIntros (lpc'' regs'' retv (-> & -> & ->)) "HPC Hmap HT". iApply "Hφ".
      rewrite specialrw_regs_ne //. by iFrame.
  Qed.

  (** [csrr dst, mstatus]: any value. It does not write mstatus. *)
  Lemma wp_csrr_mstatus E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst wdst dq :
    decodeInstrW w.(lw) = SpecialRW dst MSTATUS (inr cnull) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ wdst }}}
      Instr Executable @ E
      {{{ vst, RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          dst ↦ᵣ vst }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hcnull φ) "(>HPC & >Hpc_a & >Hdst) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iApply (wp_specialrw_reserved_success_link _ _ _ _ _ _ _ _ _ _ _ _ _ True%I True%I
             with "[$HPC $Hmap $Hpc_a]").
    all: try done.
    { rewrite /regs_of /operands_of /regs_of_argument dom_singleton_L; set_solver. }
    { rewrite /mstatus_src_mie /=. apply link_transfer_kept. }
    iNext. iIntros (vst) "(HPC & Hpc_a & Hmap & _)".
    rewrite specialrw_regs_ne // insert_singleton_eq.
    iApply "Hφ". iFrame.
    iApply (regs_of_map_1 with "Hmap").
  Qed.

  (** [csrw mstatus, src]: the legalised write goes to the state
      interpretation; MIE becomes MIE of the source. *)
  Lemma wp_csrw_mstatus_link E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src vsrc dq
      (T1 T2 : iProp Σ) :
    decodeInstrW w.(lw) = SpecialRW cnull MSTATUS (inr src) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    link_transfer (mie_set (mie_of (get_a vsrc.(lw)))) T1 T2 →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ vsrc ∗
        ▷ T1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          src ↦ᵣ vsrc ∗
          T2 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hcnull Htr φ) "(>HPC & >Hpc_a & >Hsrc & HT) Hφ".
    iDestruct (map_of_regs_1 with "Hsrc") as "Hmap".
    iApply (wp_specialrw_reserved_success_link _ _ _ _ _ _ _ _ _ _ _ _ _ T1 T2
             with "[$HPC $Hmap $Hpc_a $HT]").
    all: try done.
    { rewrite /regs_of /operands_of /regs_of_argument dom_singleton_L; set_solver. }
    { unfold mstatus_src_mie. case_decide; first done.
      rewrite llookup_reg_not_cnull // lookup_singleton_eq /=. exact Htr. }
    iNext. iIntros (vst) "(HPC & Hpc_a & Hmap & HT)".
    rewrite specialrw_regs_cnull.
    iApply "Hφ". iFrame.
    iApply (regs_of_map_1 with "Hmap").
  Qed.

End vcsr.

(** The core corollaries, with today's statements. *)
Section vcsr_core.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ}.
  Implicit Types w : LWord.

  Lemma wp_mret_vcsr E pc_p pc_g pc_b pc_e pc_a pc_π w wepcc wcause dq :
    decodeInstrW w.(lw) = Mret →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ vcsr_frag MEPCC wepcc ∗
        ▷ vcsr_frag MCAUSE wcause }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ wepcc ∗
          pc_a ↦ₐ{dq} w ∗
          trap_vcsr_res }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr φ) "(>HPC & >Hpc_a & >Hmepcc & >Hmcause) Hφ".
    iApply (wp_mret_vcsr_link _ _ _ _ _ _ _ _ _ _ _ True%I True%I
             with "[$HPC $Hpc_a $Hmepcc $Hmcause]").
    all: try done.
    { apply link_transfer_core. }
    iNext. iIntros "(HPC & Hpc_a & Htok & _)". iApply "Hφ". iFrame.
  Qed.

  (** [SpecialRW dst mstatus src]: unlike the lent volatile registers,
      mstatus is held by the state interpretation, so its old value is any
      value, and a write to it is not observed. *)
  Lemma wp_specialrw_reserved_success E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst src
      (regs : LReg) dq :
    decodeInstrW w.(lw) = SpecialRW dst MSTATUS src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    regs_of (SpecialRW dst MSTATUS src) ⊆ dom regs →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) }}}
      Instr Executable @ E
      {{{ vold, RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          ([∗ map] k↦y ∈ specialrw_regs regs dst vold, k ↦ᵣ y) }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Dregs φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
    iApply (wp_specialrw_reserved_success_link _ _ _ _ _ _ _ _ _ _ _ _ _ True%I True%I
             with "[$HPC $Hpc_a $Hmap]").
    all: try done.
    { apply link_transfer_core. }
    iNext. iIntros (vold) "(HPC & Hpc_a & Hmap & _)". iApply "Hφ". iFrame.
  Qed.

  (** [csrw mstatus, src]: the legalised write goes to the state
      interpretation. *)
  Lemma wp_csrw_mstatus E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src vsrc dq :
    decodeInstrW w.(lw) = SpecialRW cnull MSTATUS (inr src) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ vsrc }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          src ↦ᵣ vsrc }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hcnull φ) "(>HPC & >Hpc_a & >Hsrc) Hφ".
    iApply (wp_csrw_mstatus_link _ _ _ _ _ _ _ _ _ _ _ _ True%I True%I
             with "[$HPC $Hpc_a $Hsrc]").
    all: try done.
    { apply link_transfer_core. }
    iNext. iIntros "(HPC & Hpc_a & Hsrc & _)". iApply "Hφ". iFrame.
  Qed.
End vcsr_core.
