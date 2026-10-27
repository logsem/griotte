From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre ectx_lifting.
From griotte Require Export rules_base rules_SpecialRW rules_Mret.

(** * The volatile control and status registers

    Trap entry lends MEPCC, mcause and mtval to the error path of the
    switcher, which gives them back before the next fault can occur (after
    reading them, or with [mret]). The rules for the volatile registers that
    are lent (MEPCC, mcause, mtval, [mret]) and for the register that the
    state interpretation keeps (mstatus) follow. *)

Section vcsr.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ}.
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
    iIntros (σ1 ns κ κs nt) "Hσ /=".
    iNamed "Hσ".
    iDestruct (sreg_interp_trap_lend with "Hsr Htok")
      as (wepcc wcause) "(_ & Hsr & Hmepcc & Hmcause)".
    iSpecialize ("HΦ" with "Hmepcc Hmcause").
    iEval (rewrite wp_unfold /wp_pre He) in "HΦ".
    iApply ("HΦ" $! σ1 ns κ κs nt).
    iExists lpc, lreg, lsreg, lmem, R, C. by iFrame.
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
    rewrite vcsr_frag_unseal.
    iIntros (Hinstr Hvpc Hxsr φ) "(>HPC & >Hpc_a & >Hmepcc & >Hmcause) Hφ".
    iAssert ([∗ map] k↦y ∈ (∅ : LReg), k ↦ᵣ y)%I as "Hmap0"; first by rewrite big_sepM_empty.
    iApply (wp_instr_step _ _ _ _ _ _ _ _ _ _ ∅ with "HPC Hpc_a Hmap0"); eauto.
    iNext; iIntros (r psr m st lreg lsreg lmem R C c σ') "@".
    iAssert (⌜lsreg !! MEPCC = Some wepcc⌝)%I as %Hvepcc'.
    { iDestruct "Hsr" as "[Hsr _]". iApply (gen_heap_valid with "Hsr Hmepcc"). }
    iAssert (⌜∃ vst, lsreg !! MSTATUS = Some vst⌝)%I as %[vst Hvst'].
    { iApply (sreg_interp_mstatus with "Hsr"). }
    rewrite Hinstr /exec in Hstep.
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hvepcc') as (wepcc' & Hwepcc & Hrelepcc).
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hvst') as (wst & Hwst & Hrelst).
    assert (get_a wst = get_a vst.(lw)) as Hast.
    { destruct (reg_phys_and_tag _ _ _ Hrelst) as [s ->]. apply get_a_and_tag. }
    cbn in Hstep. rewrite Hxsr Hwepcc Hwst /= Hast in Hstep.
    injection Hstep as <- <-.
    (* The new mstatus, then the new PC: MEPCC satisfies the PC invariant. *)
    pose proof (erasure_insert_sreg _ _ _ _ _ _ _ _ _ _ _ MSTATUS (mret_mstatus vst)
      (WInt (mstatus_enc (mpie_of (get_a vst.(lw))) InterruptEnabled)) Her) as Her1.
    specialize (Her1 ltac:(apply reg_word_ok_int) ltac:(by intros) ltac:(by intros)
                  ltac:(apply reg_phys_lword_of_word)).
    pose proof (erasure_set_pc _ _ _ _ _ _ _ _ _ _ _ wepcc wepcc' Her1) as Her2.
    specialize (Her2 ltac:(by eapply (er_sreg_words _ _ _ _ _ _ _ Her)) Hrelepcc
                  ltac:(by eapply (er_sreg_pc_ok _ _ _ _ _ _ _ Her MEPCC))).
    iMod (sreg_interp_update_mstatus _ (mret_mstatus vst) with "Hsr") as "Hsr".
    (* The lent registers return. *)
    iDestruct (sreg_interp_trap_return with "Hsr Hmepcc Hmcause") as "(_ & Hsr & Htok)".
    iMod (PC_update _ _ wepcc with "HPCa HPC") as "[HPCa HPC]".
    iModIntro. iSplitR "Hφ HPC Hpc_a Htok".
    - iExists wepcc, _, _, lmem, R, C. iFrame. iPureIntro. exact Her2.
    - iApply "Hφ". iFrame.
  Qed.

  (** ** Rules for the registers of the state interpretation *)

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
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
    iNext; iIntros (r psr m st lreg lsreg lmem R C c σ') "@".
    (* Borrow mstatus from the state interpretation. *)
    iDestruct "Hsr" as "[Hsr Hres]". iNamed "Hres".
    set sr := MSTATUS.
    iDestruct "Hmstatus" as (vold) "Hpt".
    iAssert (∀ vnew, sr ↦ₓ vnew -∗ sreg_reserved)%I
      with "[Hwin Hwin_tval Hmtcc]" as "Hback".
    { iIntros (vnew) "Hmstatus". iFrame. }
    iDestruct (map_of_sregs_1 with "Hpt") as "Hsmap".
    iAssert (⌜{[sr := vold]} ⊆ lsreg⌝)%I as %Hlsregs.
    { iApply (gen_heap_valid_inclSepM with "Hsr Hsmap"). }
    rewrite Hinstr /exec in Hstep.
    assert (lsreg !! sr = Some vold) as Hvold'.
    { eapply lookup_weaken; last exact Hlsregs. by simplify_map_eq. }
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hvold') as (wold & Hwold & Hrelold).
    destruct (specialrw_sregs_phys R C _ r psr m st _ lreg lsreg lmem regs {[sr := vold]} sr src
                vold Her Hlregs Hregs Hlsregs)
      as (sregs' & psr' & lsreg' & Hsregs' & Hφ1 & Her1 & Hup).
    { rewrite /regs_of /operands_of in Dregs. set_solver. } { by simplify_map_eq. }
    cbn in Hstep. rewrite Hxsr Hwold /= Hφ1 /= in Hstep.
    assert (incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) =
              Some (WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π)) as Hi.
    { by apply incrementPC_add. }
    (* The ghost system registers: [sr] returns to the state interpretation. *)
    iAssert (|==> sreg_interp lsreg')%I with "[Hsr Hsmap Hback]" as ">Hsr".
    { destruct Hup as [[-> ->] | (nv & -> & ->)].
      - iModIntro. iFrame "Hsr". iDestruct (sregs_of_map_1 with "Hsmap") as "Hpt".
        iApply ("Hback" with "Hpt").
      - iMod (gen_heap_update_inSepM _ _ sr nv with "Hsr Hsmap") as "[Hsr Hsmap]";
          first by rewrite lookup_singleton_eq.
        rewrite insert_singleton_eq. iDestruct (sregs_of_map_1 with "Hsmap") as "Hpt".
        iModIntro. iFrame "Hsr". iApply ("Hback" with "Hpt"). }
    pose proof (er_sreg_words _ _ _ _ _ _ _ Her _ _ Hvold') as Hokold.
    case_decide as Hdst.
    - (* The old value is dropped. *)
      destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hi) as (pc' & Hu & _).
      iApply (instr_close_pc_update _ _ _ _ _ _ _ _ _ _ _ _ 1 _ _ _
        (λ lpc' retv, lpc' = WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∧ retv = NextIV)
        with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
      { exact Her1. } { rewrite /nextPC in Hu Hstep. by rewrite Hu in Hstep |- *. }
      { intros lpc'' Hi'. rewrite /incrementPC in Hi. simplify_eq. done. }
      { intros Hi'. rewrite /incrementPC in Hi. congruence. }
      iIntros (lpc'' retv [-> ->]) "HPC Hmap". iApply ("Hφ" $! vold).
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
      iIntros (lpc'' regs'' retv (-> & -> & ->)) "HPC Hmap". iApply "Hφ".
      rewrite specialrw_regs_ne //. by iFrame.
  Qed.

  (** [csrr dst, mstatus]: any value. *)
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
    iApply (wp_specialrw_reserved_success with "[$HPC $Hmap $Hpc_a]");
      [exact Hinstr | exact Hvpc | exact Hxsr | exact Hpca'
      | rewrite /regs_of /operands_of /regs_of_argument dom_singleton_L; set_solver |].
    iNext. iIntros (vst) "(HPC & Hpc_a & Hmap)".
    rewrite specialrw_regs_ne // insert_singleton_eq.
    iApply "Hφ". iFrame.
    iApply (regs_of_map_1 with "Hmap").
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
    iDestruct (map_of_regs_1 with "Hsrc") as "Hmap".
    iApply (wp_specialrw_reserved_success with "[$HPC $Hmap $Hpc_a]");
      [exact Hinstr | exact Hvpc | exact Hxsr | exact Hpca'
      | rewrite /regs_of /operands_of /regs_of_argument dom_singleton_L; set_solver |].
    iNext. iIntros (vst) "(HPC & Hpc_a & Hmap)".
    rewrite specialrw_regs_cnull.
    iApply "Hφ". iFrame.
    iApply (regs_of_map_1 with "Hmap").
  Qed.

End vcsr.
