From iris.proofmode Require Import proofmode.
From griotte Require Import rules_Load rules_Store.

(** * The derived rules of the time devices

    The logical state does not record the time devices: a load gives some
    integer, a store to [mtimecmp] changes no resource, a store to [mtime]
    fails. *)
Section mmio_timer_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : griotte_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
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
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); first done.
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

  Lemma wp_store_success_mtimecmp E pc_p pc_g pc_b pc_e pc_a pc_π
      dst src w regs lpc' p g b e a storev dq :
    decodeInstrW w.(lw) = Store dst src 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Store dst src 0) ⊆ dom regs →
    reg_allows_store regs dst p g b e a →
    (∀ v : LWord, regs !!ₗ dst = Some v → v.(lprov) = None) →
    lword_of_argument regs src = Some storev →
    a = mtimecmp_addr →
    incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV; PC ↦ₚ lpc' ∗ pc_a ↦ₐ{dq} w ∗ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hallow Hnoid Harg -> Hinc φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
    assert (is_time_device_address mtimecmp_addr = true) as Htdev.
    { apply is_time_device_address_spec. by right. }
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); first done.
    iNext; iIntros (r sr m st td lreg lsreg lmem R C c σ') "@".
    rewrite Hinstr in Hstep.
    (* The destination capability has no identifier and non-empty bounds:
       its physical copy is exact. *)
    pose proof Hallow as (Hdstl & Hwa & Hwb).
    destruct (regs !!ₗ dst) as [v1|] eqn:Hv1; last done. cbn in Hdstl. simplify_eq.
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hv1) as (s1 & Hr1 & Hrel1).
    assert (and_tag s1 (lw v1) = lw v1) as Hex.
    { eapply reg_phys_exact_cond; first done.
      - intros (ι & x & Hι & _). by rewrite (Hnoid _ eq_refl) in Hι.
      - eapply (nonempty_exact_cond v1);
          [by rewrite Hdstl | apply withinBounds_true_iff in Hwb; solve_addr]. }
    rewrite Hex Hdstl in Hr1.
    destruct (lword_of_argument_phys _ _ _ _ _ Hregs Harg) as (s & Hsv & _).
    rewrite /exec /= Hsv Hr1 /= finz_add_0 /= Hwa Hwb /= /is_mmio_address /mmio_store
      (time_device_not_shadow_address _ Htdev) (time_device_not_revoker_address _ Htdev) Htdev /=
      /time_dev_store bool_decide_eq_true_2 // /= in Hstep.
    pose proof (erasure_set_timedevs _ _ _ _ _ _ _
      (set_mtimecmp (word_to_bits (and_tag s storev.(lw))) td) Her) as Her1.
    rewrite /set_timedevs /= in Her1 Hstep.
    destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hinc) as (pc'' & Hu & Her2).
    rewrite Hu in Hstep. simplify_eq.
    iMod (PC_update _ _ lpc' with "HPCa HPC") as "[HPCa HPC]".
    iModIntro. iSplit; first (iPureIntro; by apply sys_kept_same_sreg).
    iSplitR "Hφ HPC Hpc_a Hmap".
    { iApply (SI_close _ _ _ _ _ _ _ Her2 with "HPCa Hr Hsr Hm Hst HR HC"). }
    iApply "Hφ". iFrame.
  Qed.

  Lemma wp_store_fail_timedev E pc_p pc_g pc_b pc_e pc_a pc_π
      dst src w regs p g b e a storev dq :
    decodeInstrW w.(lw) = Store dst src 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Store dst src 0) ⊆ dom regs →
    reg_allows_store regs dst p g b e a →
    (∀ v : LWord, regs !!ₗ dst = Some v → v.(lprov) = None) →
    lword_of_argument regs src = Some storev →
    is_time_device_address a = true →
    a = mtime_addr →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FaultedV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hallow Hnoid Harg Htdev Hmtime φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
    iAssert (▷ ([∗ map] k↦y ∈ (∅ : LMem), k ↦ₐ y))%I as "Hmem".
    { iNext. by rewrite big_sepM_empty. }
    iAssert (▷ ([∗ map] k↦revoked ∈ (∅ : ShadowTbl), k ↦ₛ revoked))%I as "Hshadow".
    { iNext. by rewrite big_sepM_empty. }
    iAssert ([∗ set] k ∈ (∅ : gset Addr), shadow_store_perm k)%I as "Hperms".
    { by rewrite big_sepS_empty. }
    iApply (wp_store_fetch _ pc_p pc_g pc_b pc_e pc_a pc_π dst src w ∅ regs ∅ ∅ dq
      with "[$HPC $Hpc_a $Hmem $Hshadow $Hperms $Hmap]"); try done.
    { intros p0 g0 b0 e0 a0 storev0 (Hdst0 & _) Harg0.
      destruct Hallow as (Hdst & _). rewrite Hdst in Hdst0. simplify_eq.
      by rewrite (time_device_not_shadow_address _ Htdev) Htdev. }
    iNext. iIntros (lpc0 mem' shadow' retv) "(%Hspec & HPC & Hpc_a & _ & _ & _ & Hmap)".
    destruct Hallow as (Hdst & Hwa & Hwb).
    destruct Hspec as
      [p0 g0 b0 e0 a0 ea0 v0 oldv0 Harg0 Hallow0 Hshadow0 Hlookup0 _ _ _
      |p0 g0 b0 e0 a0 ea0 heap_a0 v0 old_status0 Harg0 Hallow0 Hshadow0 Htranslate0 Hlookup0 _ _ _
      |p0 g0 b0 e0 a0 ea0 v0 Harg0 (Hdst0 & Hadd0 & _) Htdev0 Hmtimecmp0 _ _ _ _
      |_ _ Hfail ->].
    - exfalso. by rewrite lookup_empty in Hlookup0.
    - exfalso. by rewrite lookup_empty in Hlookup0.
    - exfalso. rewrite Hdst in Hdst0. simplify_eq.
      rewrite finz_add_0 in Hadd0. simplify_eq.
      by apply mtime_mtimecmp_ne.
    - iApply "Hφ". iFrame.
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
    iAssert (▷ ([∗ map] k↦y ∈ (∅ : LMem), k ↦ₐ y))%I as "Hmem".
    { iNext. by rewrite big_sepM_empty. }
    iAssert (▷ ([∗ map] k↦revoked ∈ (∅ : ShadowTbl), k ↦ₛ revoked))%I as "Hshadow".
    { iNext. by rewrite big_sepM_empty. }
    iAssert ([∗ set] k ∈ (∅ : gset Addr), shadow_store_perm k)%I as "Hperms".
    { by rewrite big_sepS_empty. }
    iApply (wp_store_fetch _ pc_p pc_g pc_b pc_e pc_a pc_π dst (inr src) w ∅ _ ∅ ∅ dq
      with "[$HPC $Hi $Hmem $Hshadow $Hperms $Hmap]").
    { exact Hinstr. }
    { exact Hvpc. }
    { rewrite /regs_of /operands_of !dom_insert_L. set_solver+. }
    { intros p0 g0 b0 e0 a0 storev0 (Hdst0 & _) _.
      simplify_map_eq.
      by rewrite (time_device_not_shadow_address _ Htdev) Htdev. }
    iNext. iIntros (lpc0 mem' shadow' retv) "(%Hspec & HPC & Hi & _ & _ & _ & Hmap)".
    destruct Hspec as
      [p0 g0 b0 e0 a0 ea0 v0 oldv0 Harg0 Hallow0 Hshadow0 Hlookup0 _ _ _
      |p0 g0 b0 e0 a0 ea0 heap_a0 v0 old_status0 Harg0 Hallow0 Hshadow0 Htranslate0 Hlookup0 _ _ _
      |p0 g0 b0 e0 a0 ea0 v0 Harg0 Hallow0 Htdev0 Hmtimecmp0 _ _ _ Hinc
      |_ _ Hfail ->].
    - exfalso. by rewrite lookup_empty in Hlookup0.
    - exfalso. by rewrite lookup_empty in Hlookup0.
    - rewrite /incrementPC /incrementPC_gen /= Hpca' in Hinc. simplify_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "(Hdst & Hsrc)"; first done.
      iApply "Hφ". iRight. iFrame. done.
    - iDestruct (regs_of_map_2 with "Hmap") as "(Hdst & Hsrc)"; first done.
      iApply "Hφ". iLeft. iFrame. done.
  Qed.
End mmio_timer_rules.
