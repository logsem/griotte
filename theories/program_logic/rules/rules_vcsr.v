From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre ectx_lifting.
From griotte Require Export rules_trap_entry rules_SpecialRW rules_Mret.
Import core_link.

(** * The volatile control and status registers

    Trap entry writes MEPCC, mcause and mtval, whose points-to the thread
    holds at InterruptDisabled ([handover_res]). The rules for the volatile
    registers (MEPCC, mcause, mtval, [mret]) and for mstatus follow. *)

Section vcsr.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : griotte_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
  Implicit Types w : LWord.

  (** ** The volatile registers *)

  (** "vcsr" stands for the volatile control and status registers: those
      that every trap entry overwrites (MEPCC and mcause, and on the machine
      also mtval and the MIE and MPIE bits of mstatus). Their contents are only
      meaningful between a trap entry and the next trap.

      [vcsr_res] is the right to read and write them now, and [vcsr_frag sr v]
      its view of one register [sr] holding [v]. They are backed by the
      points-to of the volatile registers. mstatus is read and written
      through the rules for mstatus below. Both definitions are sealed, so
      that their backing can change without changing the specifications that
      use them. *)

  (** The view of a volatile register [sr] (MEPCC, mcause or mtval), holding
      [vsr]. *)
  Definition vcsr_frag_def (sr : SRegName) (vsr : LWord) : iProp Σ := sr ↦ₓ vsr.
  #[local] Definition vcsr_frag_aux : seal (@vcsr_frag_def). Proof. by eexists. Qed.
  Definition vcsr_frag := vcsr_frag_aux.(unseal).
  #[local] Definition vcsr_frag_unseal : @vcsr_frag = @vcsr_frag_def := vcsr_frag_aux.(seal_eq).

  Lemma vcsr_frag_pointsto sr (v : LWord) : vcsr_frag sr v ⊣⊢ sr ↦ₓ v.
  Proof. by rewrite vcsr_frag_unseal. Qed.

  (** MEPCC and mcause, with any values: what the error path gives back
      first. *)
  Definition vcsr_res_def : iProp Σ :=
    ∃ wepcc wcause, vcsr_frag mepcc wepcc ∗ vcsr_frag mcause wcause.
  #[local] Definition vcsr_res_aux : seal (@vcsr_res_def). Proof. by eexists. Qed.
  Definition vcsr_res := vcsr_res_aux.(unseal).
  #[local] Definition vcsr_res_unseal : @vcsr_res = @vcsr_res_def := vcsr_res_aux.(seal_eq).

  #[global] Instance vcsr_frag_timeless sr vsr : Timeless (vcsr_frag sr vsr).
  Proof. rewrite vcsr_frag_unseal. apply _. Qed.

  #[global] Instance vcsr_res_timeless : Timeless vcsr_res.
  Proof. rewrite vcsr_res_unseal. apply _. Qed.

  Lemma vcsr_res_intro wepcc wcause :
    vcsr_frag mepcc wepcc -∗
    vcsr_frag mcause wcause -∗
    vcsr_res.
  Proof. rewrite vcsr_res_unseal. iIntros "Hmepcc Hmcause". iExists _, _. iFrame. Qed.

  Lemma vcsr_res_elim :
    vcsr_res -∗
    ∃ wepcc wcause, vcsr_frag mepcc wepcc ∗ vcsr_frag mcause wcause.
  Proof. rewrite vcsr_res_unseal. by iIntros "H". Qed.

  (** The resources of trap entry, with the views of the volatile
      registers: MEPCC holds the faulting PC, mcause a cause that satisfies
      the cause predicate [P_mcause], mtval a value that satisfies the value
      predicate [P_mtval]. *)
  Lemma trap_entry_out_vcsr_frag `{CR : !CritRoute Σ th CL} P_mcause P_mtval w
      (b : InterruptStatus) :
    trap_entry_out_cause P_mcause P_mtval w b -∗
    MIE ↦ₜ InterruptDisabled ∗
    na_own crit ⊤ ∗
    unwedged ∗
    vcsr_frag mepcc (lmepcc_of_pc w) ∗
    (∃ cause : Z, ⌜P_mcause cause⌝ ∗ vcsr_frag mcause (lword_of_word (WInt cause))) ∗
    (∃ tval : Z, ⌜P_mtval tval⌝ ∗ vcsr_frag mtval (lword_of_word (WInt tval))) ∗
    MPIE_frag b ∗
    (if b is InterruptEnabled then @posture_part _ _ _ th CL CR else True).
  Proof. rewrite trap_entry_out_unfold vcsr_frag_unseal. by iIntros "H". Qed.

  (** ** Rules for the volatile registers *)

  (** [cspecialr dst, sr] on a volatile register (MEPCC, or mcause or mtval
      with [csrr]). *)
  Lemma wp_cspecialr_vcsr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst wdst sr vsr dq :
    decodeInstrW w.(lw) = SpecialRW dst sr (inr cnull) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ wdst ∗
        ▷ vcsr_frag sr vsr }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
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
    rewrite tval_sw_none; last by apply sw_of_none.
    destruct (SpecialRW_spec_success_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hxsr Hpca' Hspec)
      as (-> & -> & vold & Hvold & Hsr' & ->).
    rewrite /specialrw_sregs /= in Hsr'. case_decide as Hc; last done. simplify_map_eq.
    rewrite specialrw_regs_ne // insert_singleton_eq.
    iApply "Hφ". iFrame.
    iDestruct (regs_of_map_1 with "Hmap") as "$".
    iApply (sregs_of_map_1 with "Hsmap").
  Qed.

  (** [cspecialw mepcc, src]: the volatile register MEPCC receives the
      legalised word. *)
  Lemma wp_cspecialw_mepcc E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src vsrc vold dq :
    decodeInstrW w.(lw) = SpecialRW cnull mepcc (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ vsrc ∗
        ▷ vcsr_frag mepcc vold }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          src ↦ᵣ vsrc ∗
          vcsr_frag mepcc (llegalise mepcc vsrc) }}}.
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
    rewrite tval_sw_none; last by apply sw_of_none.
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
      MIE receives MPIE [p] and MPIE becomes enabled; MEPCC, mcause and the
      new MPIE fragment go to the transfer. *)
  Lemma wp_mret_vcsr_link E pc_p pc_g pc_b pc_e pc_a pc_π w wepcc wcause (b p : InterruptStatus) dq
      (T1 T2 : iProp Σ) :
    decodeInstrW w.(lw) = Mret →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    link_transfer_si (mie_move b p)
      (vcsr_frag mepcc wepcc ∗ vcsr_frag mcause wcause ∗ MPIE_frag InterruptEnabled ∗ T1) T2 →
    (route_pre th b → route_pre th p) →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ vcsr_frag mepcc wepcc ∗
        ▷ vcsr_frag mcause wcause ∗
        ▷ MIE ↦ₜ b ∗
        ▷ MPIE_frag p ∗
        ▷ T1 }}}
      Instr Executable @ E
      {{{ RET tval_sw (kind_of th) Mret griotte_lang.NextIV;
          PC ↦ₚ wepcc ∗
          pc_a ↦ₐ{dq} w ∗
          MIE ↦ₜ p ∗
          T2 }}}.
  Proof.
    rewrite vcsr_frag_unseal.
    iIntros (Hinstr Hvpc Hxsr Htr Hroute φ)
      "(>HPC & >Hpc_a & >Hmepcc & >Hmcause & >Hmie & >Hmpie & HT) Hφ".
    iAssert ([∗ map] k↦y ∈ (∅ : LReg), k ↦ᵣ y)%I as "Hmap0"; first by rewrite big_sepM_empty.
    iApply (wp_instr_step_link E pc_p pc_g pc_b pc_e pc_a pc_π w dq ∅ with "HPC Hpc_a Hmap0"); eauto.
    iNext; iIntros (r psr m st td lreg lsreg lmem R C c σ') "@".
    iDestruct (sys_interp_mie_agree with "Hsr Hmie") as %<-.
    iDestruct (sys_interp_mpie_agree with "Hsr Hmpie") as %<-.
    destruct (erasure_mie_st _ _ _ _ _ _ _ Her) as [Hmie_st _].
    iDestruct (sys_interp_valid_1 with "Hsr Hmepcc") as %[Hvepcc' _].
    pose proof (ls_join_mstatus lsreg) as Hvst'.
    rewrite Hinstr /exec in Hstep. rewrite Hinstr.
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hvepcc') as (wepcc' & Hwepcc & Hrelepcc).
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hvst') as (wst & Hwst & Hrelst).
    apply reg_phys_no_bounds in Hrelst; last done. cbn in Hrelst. subst wst.
    cbn in Hstep. rewrite Hxsr Hwepcc Hwst /= mpie_of_mstatus_enc in Hstep.
    injection Hstep as <- <-.
    rewrite /update_pcc /update_sreg /=.
    (* The new mstatus, then the new PC: MEPCC satisfies the PC invariant. *)
    pose proof (erasure_insert_sreg _ _ _ _ _ _ _ _ _ _ _ _ mstatus
      (lword_of_word (WInt (mstatus_enc (ls_mpie lsreg) InterruptEnabled)))
      (WInt (mstatus_enc (ls_mpie lsreg) InterruptEnabled)) Her) as Her1.
    specialize (Her1 ltac:(apply reg_word_ok_int) ltac:(by intros) ltac:(by intros)
                  ltac:(apply reg_phys_lword_of_word)).
    rewrite -ls_join_set_mstatus in Her1.
    pose proof (erasure_set_pc _ _ _ _ _ _ _ _ _ _ _ _ wepcc wepcc' Her1) as Her2.
    specialize (Her2 ltac:(by eapply (er_sreg_words _ _ _ _ _ _ _ Her)) Hrelepcc
                  ltac:(by eapply (er_sreg_pc_ok _ _ _ _ _ _ _ Her mepcc))).
    iMod (sys_interp_set_mstatus _ _ _ (ls_mpie lsreg) InterruptEnabled
           with "Hsr Hmie Hmpie") as "(Hsr & Hmie & Hmpie)".
    iMod (PC_update _ _ wepcc with "HPCa HPC") as "[HPCa HPC]".
    iPoseProof (SI_close _ _ _ _ _ _ _ Her2 with "HPCa Hr Hsr Hm Hst HR HC") as "HSI".
    iMod (Htr _ (MkExecConf wepcc' r
                 (<[mstatus := WInt (mstatus_enc (ls_mpie lsreg) InterruptEnabled)]> psr) m st td)
           with "[$HSI $Hlink $Hmepcc $Hmcause $Hmpie $HT]") as "(HSI & Hlink & HT)".
    { split_and!.
      - done.
      - by rewrite /mie_st /= lookup_insert_eq /= mie_of_mstatus_enc.
      - by rewrite /= lookup_insert_ne. }
    iModIntro. iFrame "HSI Hlink". iSplitR.
    { iApply ctx_irq_post_route.
      rewrite /mie_st /= lookup_insert_eq /= mie_of_mstatus_enc. apply Hroute.
      rewrite -Hmie_st. by apply ctx_irq_off_route. }
    iApply "Hφ". iFrame.
  Qed.

  (** ** Rules for mstatus *)

  (** The MIE that [SpecialRW _ mstatus src] writes: none for the source
      [inr cnull], else MIE of the source. *)
  Definition mstatus_src_mie (regs : LReg) (src : Z + RegName) : option InterruptStatus :=
    match src with
    | inl z => Some (mie_of z)
    | inr rs =>
        if decide (rs = cnull) then None else (λ x : LWord, mie_of (get_a x.(lw))) <$> regs !!ₗ rs
    end.

  (** The MPIE that [SpecialRW _ mstatus src] writes. *)
  Definition mstatus_src_mpie (regs : LReg) (src : Z + RegName) : option InterruptStatus :=
    match src with
    | inl z => Some (mpie_of z)
    | inr rs =>
        if decide (rs = cnull) then None else (λ x : LWord, mpie_of (get_a x.(lw))) <$> regs !!ₗ rs
    end.

  (** The physical mstatus after [SpecialRW _ mstatus src]. *)
  Lemma specialrw_mstatus_phys R (regs : LReg) pc (r : Reg) psr m st td src psr' :
    lregs_phys R regs r →
    regs_of_argument src ∖ {[ cnull ]} ⊆ dom regs →
    (match src with
     | inr rs =>
         if decide (rs = cnull) then Some (MkExecConf pc r psr m st td)
         else wsrc ← r !!ᵣ rs;
              Some (update_sreg (MkExecConf pc r psr m st td) mstatus (legalise mstatus wsrc))
     | inl z => Some (update_sreg (MkExecConf pc r psr m st td) mstatus (legalise mstatus (WInt z)))
     end) = Some (MkExecConf pc r psr' m st td) →
    match mstatus_src_mie regs src with
    | None => psr' = psr
    | Some b =>
        ∃ mpie, mstatus_src_mpie regs src = Some mpie ∧
                psr' = <[mstatus := WInt (mstatus_enc b mpie)]> psr
    end.
  Proof.
    intros Hregs Dsrc Hφ. destruct src as [z|rs]; cbn in *; rewrite /update_sreg in Hφ.
    - simplify_eq. by eexists.
    - case_decide as Hrs; first by simplify_eq.
      assert (is_Some (regs !!ₗ rs)) as [v Hv].
      { apply elem_of_dom_lreg. apply Dsrc. set_solver. }
      destruct (llookup_reg_phys _ _ _ _ _ Hregs Hv) as (s & Hrs' & _).
      rewrite Hrs' /= in Hφ. rewrite Hv /=. simplify_eq.
      eexists. split; first done. by rewrite get_a_and_tag.
  Qed.

  (** [SpecialRW dst mstatus src]: the old value of mstatus is any value. A
      write must keep MIE disabled, from MIE disabled: it writes MPIE through
      its fragment, and the link is kept. *)
  Lemma wp_specialrw_reserved_success E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst src
      (regs : LReg) (p : InterruptStatus) dq :
    decodeInstrW w.(lw) = SpecialRW dst mstatus src →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    regs_of (SpecialRW dst mstatus src) ⊆ dom regs →
    mstatus_src_mie regs src ≠ Some InterruptEnabled →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        ▷ (if mstatus_src_mie regs src is Some _
           then MIE ↦ₜ InterruptDisabled ∗ MPIE_frag p
           else True) }}}
      Instr Executable @ E
      {{{ vold, RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          ([∗ map] k↦y ∈ specialrw_regs regs dst vold, k ↦ᵣ y) ∗
          (if mstatus_src_mie regs src is Some _
           then MIE ↦ₜ InterruptDisabled ∗ MPIE_frag (default p (mstatus_src_mpie regs src))
           else True) }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Dregs Hen φ) "(>HPC & >Hpc_a & >Hmap & >Hres) Hφ".
    iApply (wp_instr_step_link_nosw with "HPC Hpc_a Hmap"); [rewrite Hinstr; by apply sw_of_none|..]; eauto.
    iNext; iIntros (r psr m st td lreg lsreg lmem R C c σ') "@".
    destruct (erasure_mie_st _ _ _ _ _ _ _ Her) as [Hmie_st _].
    set (vold := lword_of_word (WInt (mstatus_enc (ls_mie lsreg) (ls_mpie lsreg)))).
    assert (ls_join lsreg !! mstatus = Some vold) as Hvold' by apply ls_join_mstatus.
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hvold') as (wold & Hwold & Hrelold).
    pose proof (er_sreg_words _ _ _ _ _ _ _ Her _ _ Hvold') as Hokold.
    destruct (specialrw_sregs_phys R C _ r psr m st td _ lreg (ls_join lsreg) lmem regs
                {[mstatus := vold]} mstatus src vold Her Hlregs Hregs)
      as (sregs' & psr' & lsreg' & _ & Hφ1 & _ & _).
    { by apply map_singleton_subseteq_l. }
    { rewrite /regs_of /operands_of in Dregs. set_solver. } { by simplify_map_eq. }
    rewrite Hinstr /exec in Hstep.
    cbn in Hstep. rewrite Hxsr Hwold /= Hφ1 /= in Hstep.
    assert (regs_of_argument src ∖ {[ cnull ]} ⊆ dom regs) as Dsrc.
    { rewrite /regs_of /operands_of in Dregs. set_solver. }
    pose proof (specialrw_mstatus_phys _ _ _ _ _ _ _ _ _ _ Hregs Dsrc Hφ1) as Hpsr'.
    iAssert (|==> ∃ ls',
               ⌜erasure R C (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r psr' m st td)
                  (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) lreg (ls_join ls') lmem⌝ ∗
               ⌜sys_kept (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r psr m st td)
                  (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r psr' m st td)⌝ ∗
               sys_interp ls' ∗
               (if mstatus_src_mie regs src is Some _
                then MIE ↦ₜ InterruptDisabled ∗ MPIE_frag (default p (mstatus_src_mpie regs src))
                else True))%I
      with "[Hsr Hres]" as ">(%ls' & %Her1 & %Hkept & Hsr & Hres)".
    { destruct (mstatus_src_mie regs src) as [b|] eqn:Hsm.
      - destruct Hpsr' as (mpie' & Hsp & ->). rewrite Hsp /=.
        assert (b = InterruptDisabled) as -> by (destruct b; done).
        iDestruct "Hres" as "[Hmie Hmpie]".
        iDestruct (sys_interp_mie_agree with "Hsr Hmie") as %Hb.
        iMod (sys_interp_set_mstatus _ _ _ InterruptDisabled mpie' with "Hsr Hmie Hmpie")
          as "(Hsr & Hmie & Hmpie)".
        iModIntro. iExists _. iFrame "Hsr Hmie Hmpie". iPureIntro. split.
        + rewrite ls_join_set_mstatus. apply erasure_insert_sreg; first done.
          * apply reg_word_ok_int.
          * by intros.
          * by intros.
          * apply reg_phys_lword_of_word.
        + split.
          * by rewrite Hmie_st /mie_st /= lookup_insert_eq /= mie_of_mstatus_enc Hb.
          * by rewrite /= lookup_insert_ne.
      - subst psr'. iModIntro. iExists lsreg. by iFrame "Hsr". }
    assert (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) =
              Some (Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π)) as Hi.
    { by apply incrementPC_add. }
    iApply (instr_close_link_kept_irq with "Hlink"); [done|].
    iApply (instr_close_kept_trans _ (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r psr' m st td));
      first exact Hkept.
    case_decide as Hdst.
    - (* The old value is dropped. *)
      destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hi) as (pc' & Hu & _).
      iApply (instr_close_pc_update _ _ _ _ _ _ _ _ _ _ _ _ _ 1 _ _ _
        (λ lpc' retv, lpc' = Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∧ retv = griotte_lang.NextIV)
        with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hres]").
      { exact Her1. } { rewrite /nextPC in Hu Hstep. by rewrite Hu in Hstep |- *. }
      { intros lpc'' Hi'. rewrite /incrementPC in Hi. simplify_eq. done. }
      { intros Hi'. rewrite /incrementPC in Hi. congruence. }
      iIntros (lpc'' retv [-> ->]) "HPC Hmap". iApply ("Hφ" $! vold).
      subst dst. rewrite specialrw_regs_cnull. by iFrame.
    - (* [dst] receives the old value. *)
      destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ _
        (erasure_linsert_reg _ _ _ _ _ _ _ _ _ _ _ _ dst vold wold Her1 Hokold Hrelold) Hi)
        as (pc' & Hu & _).
      iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ _ dst vold wold _ _ _
        (λ lpc' regs' retv, lpc' = Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∧
                            regs' = <[dst := vold]> regs ∧ retv = griotte_lang.NextIV)
        with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hres]").
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

  (** [csrr dst, mstatus]: any value. It does not write mstatus. *)
  Lemma wp_csrr_mstatus E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst wdst dq :
    decodeInstrW w.(lw) = SpecialRW dst mstatus (inr cnull) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ wdst }}}
      Instr Executable @ E
      {{{ vst, RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          dst ↦ᵣ vst }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hcnull φ) "(>HPC & >Hpc_a & >Hdst) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iApply (wp_specialrw_reserved_success _ _ _ _ _ _ _ _ _ _ _ _ InterruptDisabled
             with "[$HPC $Hmap $Hpc_a]").
    all: try done.
    { rewrite /regs_of /operands_of /regs_of_argument dom_singleton_L; set_solver. }
    iNext. iIntros (vst) "(HPC & Hpc_a & Hmap & _)".
    rewrite specialrw_regs_ne // insert_singleton_eq.
    iApply "Hφ". iFrame.
    iApply (regs_of_map_1 with "Hmap").
  Qed.

  (** [csrr dst, mstatus] with the fragments of MIE and MPIE: the exact
      value. *)
  Lemma wp_csrr_mstatus_frag E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst wdst
      (b p : InterruptStatus) dq :
    decodeInstrW w.(lw) = SpecialRW dst mstatus (inr cnull) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ wdst ∗
        ▷ MIE ↦ₜ b ∗
        ▷ MPIE_frag p }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          dst ↦ᵣ lword_of_word (WInt (mstatus_enc b p)) ∗
          MIE ↦ₜ b ∗
          MPIE_frag p }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hdst φ) "(>HPC & >Hpc_a & >Hdst & >Hmie & >Hmpie) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    assert (regs_of (SpecialRW dst mstatus (inr cnull)) ⊆ dom ({[dst := wdst]} : LReg))
      as Dregs.
    { rewrite /regs_of /operands_of /regs_of_argument dom_singleton_L; set_solver. }
    iApply (wp_instr_step_link_nosw with "HPC Hpc_a Hmap"); [rewrite Hinstr; by apply sw_of_none|..]; eauto.
    iNext; iIntros (r psr m st td lreg lsreg lmem R C c σ') "@".
    iDestruct (sys_interp_mie_agree with "Hsr Hmie") as %<-.
    iDestruct (sys_interp_mpie_agree with "Hsr Hmpie") as %<-.
    set (vold := lword_of_word (WInt (mstatus_enc (ls_mie lsreg) (ls_mpie lsreg)))).
    assert (ls_join lsreg !! mstatus = Some vold) as Hvold' by apply ls_join_mstatus.
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hvold') as (wold & Hwold & Hrelold).
    pose proof (er_sreg_words _ _ _ _ _ _ _ Her _ _ Hvold') as Hokold.
    destruct (specialrw_sregs_phys R C _ r psr m st td _ lreg (ls_join lsreg) lmem {[dst := wdst]}
                {[mstatus := vold]} mstatus (inr cnull) vold Her Hlregs Hregs)
      as (sregs' & psr' & lsreg' & _ & Hφ1 & _ & _).
    { by apply map_singleton_subseteq_l. }
    { rewrite /regs_of /operands_of in Dregs. set_solver. } { by simplify_map_eq. }
    rewrite Hinstr /exec in Hstep.
    cbn in Hstep. rewrite Hxsr Hwold /= Hφ1 /= in Hstep.
    cbn in Hφ1. destruct (decide (cnull = cnull)) as [_|Hc]; last done. simplify_eq.
    assert (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) =
              Some (Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π)) as Hi.
    { by apply incrementPC_add. }
    iApply (instr_close_link_kept_irq with "Hlink"); [done|].
    case_decide as Hdc; first done.
    destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ _
      (erasure_linsert_reg _ _ _ _ _ _ _ _ _ _ _ _ dst vold wold Her Hokold Hrelold) Hi)
      as (pc' & Hu & _).
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ _ dst vold wold _ _ _
      (λ lpc' regs' retv, lpc' = Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∧
                          regs' = <[dst := vold]> {[dst := wdst]} ∧ retv = griotte_lang.NextIV)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hmie Hmpie]").
    { exact Her. } { exact Hlregs. }
    { right. set_solver. }
    { exact Hokold. }
    { rewrite /update_reg /= in Hu Hstep |- *. by rewrite Hu in Hstep |- *. }
    { exact Hrelold. }
    { intros lpc'' Hi'. rewrite Hi in Hi'. simplify_eq. by rewrite linsert_reg_not_cnull. }
    { intros Hi'. congruence. }
    iIntros (lpc'' regs'' retv (-> & -> & ->)) "HPC Hmap". iApply "Hφ".
    rewrite insert_singleton_eq. iFrame. iApply (regs_of_map_1 with "Hmap").
  Qed.

  (** [csrw mstatus, src], restricted to MIE disabled before and after the
      write: MPIE becomes MPIE of the source. *)
  Lemma wp_csrw_mstatus E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src vsrc (p : InterruptStatus) dq :
    decodeInstrW w.(lw) = SpecialRW cnull mstatus (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    mie_of (get_a vsrc.(lw)) = InterruptDisabled →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ vsrc ∗
        ▷ MIE ↦ₜ InterruptDisabled ∗
        ▷ MPIE_frag p }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          src ↦ᵣ vsrc ∗
          MIE ↦ₜ InterruptDisabled ∗
          MPIE_frag (mpie_of (get_a vsrc.(lw))) }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hcnull Hdis φ) "(>HPC & >Hpc_a & >Hsrc & >Hmie & >Hmpie) Hφ".
    iDestruct (map_of_regs_1 with "Hsrc") as "Hmap".
    assert (mstatus_src_mie {[src := vsrc]} (inr src) = Some InterruptDisabled) as Hsm.
    { rewrite /mstatus_src_mie decide_False // llookup_reg_not_cnull // lookup_singleton_eq /=.
      by rewrite Hdis. }
    assert (mstatus_src_mpie {[src := vsrc]} (inr src) = Some (mpie_of (get_a vsrc.(lw)))) as Hsp.
    { by rewrite /mstatus_src_mpie decide_False // llookup_reg_not_cnull // lookup_singleton_eq. }
    iApply (wp_specialrw_reserved_success _ _ _ _ _ _ _ _ _ _ _ {[src := vsrc]} p
             with "[HPC Hmap Hpc_a Hmie Hmpie]").
    all: try done.
    { rewrite /regs_of /operands_of /regs_of_argument dom_singleton_L; set_solver. }
    { by rewrite Hsm. }
    { rewrite Hsm. iFrame. }
    iNext. iIntros (vst) "(HPC & Hpc_a & Hmap & Hres)".
    rewrite Hsm Hsp /=. iDestruct "Hres" as "[Hmie Hmpie]".
    rewrite specialrw_regs_cnull.
    iApply "Hφ". iFrame.
    iApply (regs_of_map_1 with "Hmap").
  Qed.

End vcsr.

(** The core corollaries, with today's statements. *)
Section vcsr_core.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread}.
  Implicit Types w : LWord.

  Lemma wp_mret_vcsr E pc_p pc_g pc_b pc_e pc_a pc_π w wepcc wcause (b p : InterruptStatus) dq :
    decodeInstrW w.(lw) = Mret →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (route_pre th b → route_pre th p) →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ vcsr_frag mepcc wepcc ∗
        ▷ vcsr_frag mcause wcause ∗
        ▷ MIE ↦ₜ b ∗
        ▷ MPIE_frag p }}}
      Instr Executable @ E
      {{{ RET tval_sw (kind_of th) Mret griotte_lang.NextIV;
          PC ↦ₚ wepcc ∗
          pc_a ↦ₐ{dq} w ∗
          vcsr_frag mepcc wepcc ∗
          vcsr_frag mcause wcause ∗
          MIE ↦ₜ p ∗
          MPIE_frag InterruptEnabled }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hroute φ) "(>HPC & >Hpc_a & >Hmepcc & >Hmcause & >Hmie & >Hmpie) Hφ".
    iApply (wp_mret_vcsr_link _ _ _ _ _ _ _ _ _ _ _ _ _ True%I
              (vcsr_frag mepcc wepcc ∗ vcsr_frag mcause wcause ∗
               MPIE_frag InterruptEnabled ∗ True)%I
             with "[$HPC $Hpc_a $Hmepcc $Hmcause $Hmie $Hmpie]").
    all: try done.
    { apply link_transfer_si_core. }
    iNext. iIntros "(HPC & Hpc_a & Hmie & Hmepcc & Hmcause & Hmpie & _)". iApply "Hφ". iFrame.
  Qed.
End vcsr_core.
