From iris.proofmode Require Import proofmode.
From griotte Require Import instructions.memory_accesses shapes.memory_access.

(** * The derived rules of the time devices

    The logical state does not record the time devices: a load gives some
    integer, a store to [mtimecmp] changes no resource, a store to [mtime]
    fails. *)
Section mmio_timer_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types w : LWord.
  Implicit Types reg : gmap RegName LWord.
  Implicit Types ms : gmap Addr LWord.

  (** A load from a time device, at an offset from the source capability. *)
  Lemma wp_load_success_timedev_imm E pc_p pc_g pc_b pc_e pc_a pc_π
      dst src (imm : Z) w regs mem dq p g b e a ea lpc' :
    decodeInstrW w.(lw) = CLoad dst src imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (CLoad dst src imm) ⊆ dom regs →
    mem !! pc_a = Some w →
    reg_allows_load_imm regs src imm p g b e a ea →
    (∀ v : LWord, regs !!ₗ src = Some v → v.(lprov) = None) →
    is_time_device_address ea = true →
    incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        (▷ [∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ z, RET NextIV;
        PC ↦ₚ lpc' ∗
        ([∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
        [∗ map] k↦y ∈ <[dst:=WInt z]ₗ> regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hmem Hallow Hnoid Htdev Hinc φ) "(>HPC & >Hmem & >Hmap) Hφ".
    iDestruct (big_sepM_lookup_acc with "Hmem") as "[Hpc_a Hmem]"; first exact Hmem.
    iApply (wp_instr_step_nosw with "HPC Hpc_a Hmap"); [rewrite Hinstr; by apply sw_of_none|..]; first done.
    iNext; iIntros (r sr m st td lreg lsreg lmem R C c σ') "@".
    rewrite Hinstr in Hstep.
    (* The source capability has no identifier and non-empty bounds: its
       physical copy is exact. *)
    pose proof Hallow as (Hsrcl & Hadd & Hra & Hwb).
    destruct (regs !!ₗ src) as [v2|] eqn:Hv2; last done. cbn in Hsrcl. simplify_eq.
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hv2) as (s2 & Hr2 & Hrel2).
    assert (and_tag s2 (lw v2) = lw v2) as Hex.
    { eapply reg_phys_exact_cond; first done.
      - intros (ι & x & Hι & _). by rewrite (Hnoid _ eq_refl) in Hι.
      - eapply (nonempty_exact_cond v2);
          [by rewrite Hsrcl | apply withinBounds_true_iff in Hwb; solve_addr]. }
    rewrite Hex Hsrcl in Hr2.
    rewrite /exec /= Hr2 /= Hadd /= Hra Hwb /= /is_mmio_address /mmio_load
      (time_device_not_shadow_address _ Htdev) (time_device_not_revoker_address _ Htdev) Htdev /=
      in Hstep.
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ _ dst
      (lword_of_word (WInt (time_dev_value td ea))) _ _ _ _
      (λ lpc'' regs' retv, lpc'' = lpc' ∧
         regs' = <[dst := lword_of_word (WInt (time_dev_value td ea))]ₗ> regs ∧ retv = NextIV)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hmem]").
    { exact Her. } { exact Hlregs. }
    { eapply elem_of_lregs_dom; [exact Dregs | rewrite /regs_of /operands_of; set_solver+]. }
    { apply reg_word_ok_int. } { exact Hstep. } { apply reg_phys_lword_of_word. }
    { intros lpc'' Hinc'. rewrite Hinc in Hinc'. by simplify_eq. }
    { by rewrite Hinc. }
    iIntros (lpc'' regs' retv (-> & -> & ->)) "HPC Hmap".
    iApply ("Hφ" $! (time_dev_value td ea)). iFrame. by iApply "Hmem".
  Qed.

  Lemma wp_load_success_timedev E pc_p pc_g pc_b pc_e pc_a pc_π
      dst src w regs mem dq p g b e a lpc' :
    decodeInstrW w.(lw) = CLoad dst src 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (CLoad dst src 0) ⊆ dom regs →
    mem !! pc_a = Some w →
    reg_allows_load regs src p g b e a →
    (∀ v : LWord, regs !!ₗ src = Some v → v.(lprov) = None) →
    is_time_device_address a = true →
    incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        (▷ [∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ z, RET NextIV;
        PC ↦ₚ lpc' ∗
        ([∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
        [∗ map] k↦y ∈ <[dst:=WInt z]ₗ> regs, k ↦ᵣ y }}}.
  Proof.
    intros Hinstr Hvpc Dregs Hmem (Hsrc & Hra & Hwb) Hnoid Htdev Hinc.
    apply (wp_load_success_timedev_imm E pc_p pc_g pc_b pc_e pc_a pc_π dst src 0 w regs mem dq
      p g b e a a lpc'); try done.
    split_and!; [done | apply finz_add_0 | done | done].
  Qed.

  Lemma wp_load_success_from_timedev E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' p g b e a pc_a' dq :
    is_time_device_address a = true →
    decodeInstrW w.(lw) = CLoad r1 r2 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r1 ↦ᵣ w'
        ∗ ▷ r2 ↦ᵣ Cap p g b e a }}}
      Instr Executable @ E
    {{{ z, RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ r1 ↦ᵣ WInt z
        ∗ pc_a ↦ₐ{dq} w
        ∗ r2 ↦ᵣ Cap p g b e a }}}.
  Proof.
    iIntros (Htdev Hinstr Hvpc [Hra Hwb] Hpca' Hcnull Hcnull' φ)
      "(>HPC & >Hi & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %Hr12]".
    iDestruct (memMap_resource_1_dq with "Hi") as "Hmem".
    iApply (wp_load_success_timedev E pc_p pc_g pc_b pc_e pc_a pc_π r1 r2 w _ _ dq p g b e a
      with "[$HPC $Hmem $Hmap]"); eauto; simplify_map_eq; eauto.
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    { unfold reg_allows_load. split; first by simplify_map_eq. auto. }
    all: try (by rewrite /incrementPC /incrementPC_gen Hpca').
    iNext. iIntros (z) "(HPC & Hmem & Hmap)".
    iDestruct (memMap_resource_1_dq with "Hmem") as "Hi".
    rewrite decide_False // insert_insert_eq.
    iDestruct (regs_of_map_2 with "Hmap") as "(Hr1 & Hr2)"; first done.
    iApply ("Hφ" $! z). iFrame.
  Qed.

  (** A store to a time device by a live authority [dst]: it succeeds at
      [mtimecmp] and faults at [mtime]; either way, no resource changes. *)
  Lemma wp_store_timedev {E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dq dst ρ imm} {regs : LReg}
      {p g b e a ea} {W : iProp Σ} :
    decodeInstrW w.(lw) = Store dst ρ imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    reg_allows_mem_access MemAccessWrite regs dst imm p g b e a ea →
    (∀ v, regs !! dst = Some v → live_witness W v) →
    is_time_device_address ea = true →
    (pc_a + 1)%a = Some pc_a' →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        W }}}
      Instr Executable @ E
    {{{ retv, RET retv;
        ((⌜retv = FaultedV⌝ ∗ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) ∨
         (⌜retv = NextIV⌝ ∗ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π)) ∗
        pc_a ↦ₐ{dq} w ∗
        ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        W }}}.
  Proof.
    iIntros (Hinstr Hvpc Hacc Hlive Htdev Hpca' φ) "(>HPC & >Hi & >Hmap & Hwit) Hφ".
    iApply (wp_instr_step_nosw with "HPC Hi Hmap"); [rewrite Hinstr; by apply sw_of_none | done |].
    iNext; iIntros (r sr m st td lreg lsreg lmem R C c σ') "@".
    iDestruct (live_witness_cond True W regs dst R (λ _, Hlive) with "HR Hwit") as %Hlive_ok.
    rewrite Hinstr /exec in Hstep.
    destruct (exec_opt (Store dst ρ imm) pc_p _) as [conf|] eqn:Hexec; cycle 1.
    { (* A fault. *)
      simplify_eq. iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); first done.
      iIntros "HPC Hmap". iApply "Hφ". iSplitL "HPC"; first (iLeft; by iFrame). iFrame. }
    subst conf.
    (* A step of the live authority is a store to the device. *)
    assert (is_mmio_address ea = true) as Hmmio.
    { by rewrite /is_mmio_address Htdev !orb_true_r. }
    destruct (store_step_device_inv _ R C _ _ _ _ _ _ dst imm _ p g b e a ea Her Hlregs Hacc
                (Hlive_ok I) Hmmio (Store_member_argument dst ρ imm pc_p _ _ Hexec))
      as (w' & φ' & _ & Hstore & Hnext).
    rewrite /mmio_store (time_device_not_shadow_address _ Htdev)
      (time_device_not_revoker_address _ Htdev) Htdev /= in Hstore.
    destruct (time_dev_store td ea w') as [td'|] eqn:Htds; simplify_eq/=.
    assert (erasure R C (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td')
              (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) lreg (ls_join lsreg) lmem) as Her1.
    { exact (erasure_set_timedevs _ _ _ _ _ _ _ td' Her). }
    assert (nextPC (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td') = Some (c, σ'))
      as Hnext' by exact Hnext.
    assert (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) =
              Some (Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π)) as Hinc.
    { by apply incrementPC_add. }
    destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hinc) as (pc'' & Hu & Her2).
    rewrite Hu in Hnext'. simplify_eq.
    iMod (PC_update _ _ (Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π) with "HPCa HPC") as "[HPCa HPC]".
    iModIntro. iSplit; first (iPureIntro; by apply sys_kept_same_sreg).
    iSplitR "Hφ HPC Hpc_a Hmap Hwit".
    { iApply (SI_close _ _ _ _ _ _ _ Her2 with "HPCa Hr Hsr Hm Hst HR HC"). }
    iApply "Hφ". iSplitL "HPC"; first (iRight; by iFrame). iFrame.
  Qed.

  (** A store to a time device through a capability without identifier: it
      succeeds at [mtimecmp] and faults at [mtime]; either way, no resource
      changes. *)
  Lemma wp_store_timedev_reg E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst src
      p g b e a wsrc dq :
    decodeInstrW w.(lw) = Store dst (inr src) 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    writeAllowed p = true →
    withinBounds b e a = true →
    is_time_device_address a = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ wsrc ∗
        ▷ dst ↦ᵣ Cap p g b e a }}}
      Instr Executable @ E
    {{{ retv, RET retv;
        (⌜retv = FaultedV⌝ ∗
         PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
         pc_a ↦ₐ{dq} w ∗
         src ↦ᵣ wsrc ∗
         dst ↦ᵣ Cap p g b e a) ∨
        (⌜retv = NextIV⌝ ∗
         PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
         pc_a ↦ₐ{dq} w ∗
         src ↦ᵣ wsrc ∗
         dst ↦ᵣ Cap p g b e a) }}}.
  Proof.
    iIntros (Hinstr Hvpc Hwa Hwb Htdev Hpca' Hdst_null φ) "(>HPC & >Hi & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "Hdst Hsrc") as "[Hmap %Hdst_src]".
    iApply (wp_store_timedev (W := emp%I) with "[$HPC $Hi $Hmap]");
      [exact Hinstr | exact Hvpc
      | split_and!; [by rewrite llookup_reg_not_cnull // lookup_insert_eq | apply finz_add_0
                    | exact Hwa | exact Hwb]
      | intros v Hv; apply live_witness_no_id; by simplify_map_eq
      | exact Htdev | exact Hpca' |].
    iIntros "!>" (retv) "(Hout & Hi & Hmap & _)".
    iDestruct (regs_of_map_2 with "Hmap") as "[Hdst Hsrc]"; first done.
    iApply "Hφ". iDestruct "Hout" as "[ [-> HPC] | [-> HPC] ]"; [iLeft | iRight]; by iFrame.
  Qed.
End mmio_timer_rules.
