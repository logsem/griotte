From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import switcher_error_handler switcher_exception.
From griotte Require Import
  error_handling_spec_states error_handling_spec_read_blocks
  error_handling_spec_handler_blocks.

(** * The error handler of [stats]

    [stats] keeps its invariant [stats_inv] (the lock released) open for
    the whole call of [stats_read]: at the faulting load, the lock is held
    and the token is [⊤ ∖ ↑Nstats]. The fault site gives the handler
    [stats_P_fault]: the lock, the closing of the invariant, and the
    continuation of [stats_read] after its release ([stats_resumed_return]).
    The handler sets the saved [a0] to [EINVAL], moves the saved PC past the
    load, and returns InstallContext. The installed context runs the release
    of [stats_read], closes the invariant, and continues with the site's
    continuation. *)

(** The namespace of the invariant of [stats]. *)
Definition Nstats : namespace := nroot .@ "stats".

Section Error_Handling_Handler.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
    {statslayout : statsLayout} {statslayoutwf : statsLayoutWf}
  .

  (** The invariant of [stats], at [Nstats]: the lock, the first global, is
      released. *)
  Definition stats_inv : iProp Σ := STATS_cgp_b ↦ₐ WInt 0.

  (** The PCC of [stats], with its cursor at [a]. *)
  Definition stats_pcc (a : Addr) : LWord :=
    lword_of_word (WCap true RX Global STATS_pcc_b STATS_pcc_e a).

  (** The PCC and CGP of the export table of [stats]. *)
  Definition stats_wpcc : LWord := stats_pcc STATS_pcc_b.
  Definition stats_wcgp : LWord :=
    lword_of_word (WCap true RW Global STATS_cgp_b STATS_cgp_e STATS_cgp_b).

  (** The fault site, [.Lread_load], and the instruction after it,
      [.Lread_release]. *)
  Definition stats_load_addr : Addr := (STATS_pcc_b ^+ stats_label ".Lread_load")%a.
  Definition stats_release_addr : Addr := (STATS_pcc_b ^+ stats_label ".Lread_release")%a.

  (** The registers of the installed context: the faulting ones, with
      [EINVAL] in [ca0] and [cnull] zero. *)
  Definition stats_resumed_regs (rfault : LReg) : LReg :=
    <[ca0 := lword_of_word (WInt EINVAL)]> (<[cnull := lword_of_word (WInt 0)]> rfault).

  (** The continuation of [stats_read] after the release of the installed
      context, with the invariant closed: the return to [cra], the
      [ErrorState] slot given back, at the count that the install leaves. *)
  Definition stats_resumed_return (cstk : CSTK) (rfault : LReg) : iProp Σ :=
    (PC ↦ₚ lupdatePcPerm (rfault !!! cra) -∗
     registers_pointsto (<[ca1 := lword_of_word (WInt 0)]> (stats_resumed_regs rfault)) -∗
     error_state_area rfault -∗
     cstack_frag (cstack_set_top_count cstk (top_error_count cstk + 2)) -∗
     na_own cerise_nais ⊤ -∗
     WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.

  (** What the fault site knows: the token is [⊤ ∖ ↑Nstats], the fault is
      at [.Lread_load], and the registers are those of [stats_read] (the
      stack of the callee, the globals of [stats], a return capability). *)
  Definition stats_fault_facts (F : coPset) (w : LWord) (rfault : LReg) : Prop :=
    F = ⊤ ∖ ↑Nstats ∧
    w = stats_pcc stats_load_addr ∧
    (∀ r, is_Some (rfault !! r)) ∧
    (∃ (g : Locality) (b e a : Addr), rfault !!! csp = lword_of_word (WCap true RWL g b e a)) ∧
    rfault !!! cgp = stats_wcgp ∧
    jalr_target_ok cnull cra (rfault !!! cra).(lw) = true.

  (** The fault obligation of [stats]: the facts of the site, the lock
      held, the closing of [stats_inv], and the continuation after the
      release. *)
  Definition stats_P_fault (F : coPset) (cstk : CSTK) (w : LWord) (rfault : LReg)
    : iProp Σ :=
    ("%Hfacts" ∷ ⌜stats_fault_facts F w rfault⌝ ∗
     "Hlock" ∷ STATS_cgp_b ↦ₐ WInt 1 ∗
     "Hclose" ∷ (▷ stats_inv ∗ na_own cerise_nais F ={⊤}=∗ na_own cerise_nais ⊤) ∗
     "Hret" ∷ ▷ stats_resumed_return cstk rfault)%I.

  (** The code of [stats] fits in its PCC. *)
  Lemma stats_code_bounds_layout : stats_code_bounds STATS_pcc_b STATS_pcc_e.
  Proof.
    pose proof STATS_size_imports as Hsize_imports.
    pose proof STATS_size_code as Hsize_code.
    split_and!.
    - rewrite /SubBounds. cbn in Hsize_code |- *. solve_addr.
    - apply STATS_pcc_disjoint_from_shadow.
    - apply STATS_pcc_base_not_heap.
  Qed.

  (** The release follows the load. *)
  Lemma stats_release_addr_next : (stats_load_addr + 1)%a = Some stats_release_addr.
  Proof.
    pose proof STATS_size_imports as Hsize_imports.
    pose proof STATS_size_code as Hsize_code.
    rewrite /stats_load_addr /stats_release_addr.
    cbn in Hsize_code |- *. solve_addr.
  Qed.

  (** The registers that InstallContext installs from the [ErrorState]
      written by the handler: the faulting ones, with [EINVAL] in [ca0];
      [cnull] is the handler's. *)
  Lemma stats_install_regs (rfault rmap : LReg) (w w0 : LWord) :
    (∀ r, is_Some (rfault !! r)) →
    rmap !! cnull = Some (lword_of_word (WInt 0)) →
    error_state_install rmap
      (lload_word RWL <$> drop 1
         (<[Z.to_nat TrustedStack_offset_ca0 := lword_of_word (WInt EINVAL)]>
            (<[0%nat := w0]> (error_state_words RWL w rfault)))) =
    stats_resumed_regs rfault.
  Proof.
    intros Hfull Hcnull.
    apply map_eq. intros r.
    pose proof (all_registers_correct r) as Hr. rewrite /all_registers in Hr.
    destruct (Hfull r) as [v Hv].
    rewrite /stats_resumed_regs /error_state_install /error_state_words /TrustedStack_offset_ca0.
    cbn. rewrite !lstore_word_isWL //.
    change (Z.to_nat 10) with 10%nat. cbn.
    rewrite !lload_word_RWL. cbn.
    repeat (apply elem_of_cons in Hr as [-> | Hr];
            [ rewrite lookup_union; simplify_map_eq;
              rewrite ?(lookup_total_correct _ _ _ Hv) ?Hv;
              try done;
              match goal with |- context [rmap !! ?r'] => by destruct (rmap !! r') end |]).
    by apply elem_of_nil in Hr.
  Qed.

  (** The installed context at [.Lread_release]: it releases the lock,
      returns to [cra], closes [stats_inv], and continues with the site's
      continuation. *)
  Lemma stats_resumed_release (F : coPset) (cstk : CSTK) (rfault : LReg) :
    (∀ r, is_Some (rfault !! r)) →
    rfault !!! cgp = stats_wcgp →
    jalr_target_ok cnull cra (rfault !!! cra).(lw) = true →
    codefrag_pers STATS_pcc_b stats_code -∗
    STATS_cgp_b ↦ₐ WInt 1 -∗
    (▷ stats_inv ∗ na_own cerise_nais F ={⊤}=∗ na_own cerise_nais ⊤) -∗
    ▷ stats_resumed_return cstk rfault -∗
    error_state_area rfault -∗
    context_resume F (cstack_set_top_count cstk (top_error_count cstk + 2))
      (stats_pcc stats_release_addr) (stats_resumed_regs rfault).
  Proof.
    iIntros (Hfull Hcgp Hcra) "#Hcode_stats Hlock Hclose Hret Harea".
    iIntros (_) "HPC Hregs Hcstk Hna".
    destruct (Hfull ca1) as [wca1 Hwca1].
    assert (rfault !! cgp = Some stats_wcgp) as Hrcgp.
    { destruct (Hfull cgp) as [wcgp Hwcgp]. by rewrite -Hcgp (lookup_total_correct _ _ _ Hwcgp). }
    assert (rfault !! cra = Some (rfault !!! cra)) as Hrcra.
    { destruct (Hfull cra) as [wcra Hwcra]. by rewrite (lookup_total_correct _ _ _ Hwcra). }
    rewrite /registers_pointsto /stats_resumed_regs.
    iDestruct (big_sepM_delete _ _ ca1 with "Hregs") as "[Hca1 Hregs]".
    { by simplify_map_eq. }
    iDestruct (big_sepM_delete _ _ cgp with "Hregs") as "[Hcgp Hregs]".
    { by simplify_map_eq. }
    iDestruct (big_sepM_delete _ _ cra with "Hregs") as "[Hcra Hregs]".
    { by simplify_map_eq. }
    pose proof STATS_size_data as Hsize_data.
    pose proof STATS_cgp_disjoint_from_shadow as Hcgp_shadow.
    (* Store cgp 0 0; Mov ca1 0; Jalr cnull cra *)
    iApply (stats_read_release_spec STATS_pcc_b STATS_pcc_e STATS_cgp_b STATS_cgp_e
              with "[- $HPC $Hcgp $Hca1 $Hcra $Hlock $Hcode_stats]").
    { apply stats_code_bounds_layout. }
    { cbn in Hsize_data. solve_addr. }
    { eapply disjoint_from_shadow_not_in; first exact Hcgp_shadow.
      apply withinBounds_true_iff. cbn in Hsize_data. solve_addr. }
    { done. }
    iNext. iIntros "(HPC & Hcgp & Hca1 & Hcra & Hlock & _)".
    (* The lock is released: close [stats_inv] *)
    iMod ("Hclose" with "[$Hlock $Hna]") as "Hna".
    iApply ("Hret" with "HPC [- Harea Hcstk Hna] Harea Hcstk Hna").
    iDestruct (big_sepM_delete _ _ cra with "[$Hregs $Hcra]") as "Hregs".
    { by simplify_map_eq. }
    iDestruct (big_sepM_delete _ _ cgp with "[$Hregs $Hcgp]") as "Hregs".
    { by simplify_map_eq. }
    rewrite /registers_pointsto /stats_resumed_regs big_sepM_insert_delete. iFrame.
  Qed.

  (** The handler of [stats] satisfies its obligation for [stats_P_fault]:
      for any token [F], it returns InstallContext through
      [switcher_handler_return_install], and the installed context runs
      [stats_resumed_release]. A fault of the install is excluded when the
      handler runs (the cell of the table is set, and the [ErrorState] can
      be loaded through [csp]), and otherwise goes to the unwind
      continuation. *)
  Lemma stats_handler_execute :
    codefrag_pers STATS_pcc_b stats_code -∗
    b_stats_exp_tbl ↦ₐ□ stats_wpcc -∗
    execute_error_handler b_stats_exp_tbl stats_wpcc stats_wcgp stats_handler_pcc_off
      Stackful stats_P_fault.
  Proof.
    iIntros "#Hcode_stats #Hpcc". iModIntro.
    iIntros (F cstk w rfault mcause mtval wpc regs). iNext.
    iIntros "(%Nswitcher & %Hns & #Hinv_switcher & #Hstatic) %Htbl %Heven %Hmcause %Hentry %Hinvoc
             HPC Hregs (_ & %Hshadow & Hes) _ HUP Hcstk Hna".
    destruct Hns as (HF & HFtrap & Hdisj).
    destruct Hinvoc as
      (Hfull & [mie Hcra] & Hcgp & (Hstores & wcsp & wa0 & Hsr & Hcsp & Hca0 & Hca1 & Hca2) & Hzero).
    (* The facts of the site, keeping the [∧] *)
    rewrite /stats_P_fault.
    iDestruct (and_pure_sep_r with "HUP") as "[%Hfacts HUP]".
    destruct Hfacts as (HFeq & -> & Hfull_f & (g & b & e & a & Hcsp_f) & Hcgp_f & Hcra_f).
    rewrite Hcsp_f /stackful_regs /= in Hsr.
    destruct (a + ErrorState_size)%a as [a16|] eqn:Ha16; last done.
    cbn in Hsr. injection Hsr as <- <-.
    rewrite /error_state_stores_ok Hcsp_f /= in Hstores. destruct Hstores as (_ & Hb_a & Ha_e).
    rewrite /error_state_shadow_free Hcsp_f /= in Hshadow.
    iEval (rewrite /error_state_pointsto Hcsp_f /=) in "Hes".
    rewrite /handler_entry /stats_wpcc /stats_pcc /= in Hentry.
    destruct (STATS_pcc_b + stats_handler_pcc_off)%a as [a_handler|] eqn:Ha_handler; last done.
    cbn in Hentry. injection Hentry as <-.
    assert (a_handler = (STATS_pcc_b ^+ stats_label ".Lstats_handler")%a) as ->.
    { rewrite /stats_handler_pcc_off in Ha_handler. cbn. solve_addr. }
    assert (regs !! ct0 = Some (lword_of_word (WInt 0))) as Hct0.
    { apply Hzero. set_solver. }
    assert (regs !! cnull = Some (lword_of_word (WInt 0))) as Hcnull.
    { apply Hzero. set_solver. }
    rewrite /registers_pointsto.
    iDestruct (big_sepM_delete _ _ ca0 with "Hregs") as "[Hca0 Hregs]"; first done.
    iDestruct (big_sepM_delete _ _ ct0 with "Hregs") as "[Hct0 Hregs]".
    { by simplify_map_eq. }
    iDestruct (big_sepM_delete _ _ cra with "Hregs") as "[Hcra Hregs]".
    { by simplify_map_eq. }
    pose proof stats_release_addr_next as Hrel.

    (* The body of the handler *)
    iApply (stats_handler_spec STATS_pcc_b STATS_pcc_e RWL g b e a _ RX Global STATS_pcc_b STATS_pcc_e
              stats_load_addr stats_release_addr with "[- $HPC $Hca0 $Hct0 $Hcra $Hes $Hcode_stats]").
    { apply stats_code_bounds_layout. }
    1-8: done.
    { rewrite /error_state_words /lmepcc_of_pc /mepcc_of_pc /stats_pcc /=.
      by destruct (negb _). }
    { apply STATS_pcc_base_not_heap. }
    { done. }
    { by destruct mie. }
    iNext. iIntros "(HPC & Hca0 & Hct0 & Hcra & Hes & _)".
    rewrite handler_return_sentry_pc.
    set (wrel := lword_of_word (WCap false RX Global STATS_pcc_b STATS_pcc_e stats_release_addr)).
    set (ws := <[Z.to_nat TrustedStack_offset_ca0 := lword_of_word (WInt EINVAL)]>
                 (<[0%nat := wrel]> (error_state_words RWL (stats_pcc stats_load_addr) rfault))).
    set (rmap := <[ca0 := lword_of_word (WInt 0)]> (<[ct0 := wrel]> regs)).
    iDestruct (big_sepM_delete _ _ cra with "[$Hregs $Hcra]") as "Hregs".
    { by simplify_map_eq. }
    iAssert (registers_pointsto rmap) with "[Hregs Hca0 Hct0]" as "Hregs".
    { rewrite /registers_pointsto /rmap big_sepM_insert_delete delete_insert_ne //.
      rewrite big_sepM_insert_delete. iFrame. }
    assert ((a16 ^+ (- ErrorState_size))%a = a) as Ha16_a.
    { rewrite /ErrorState_size in Ha16 |- *. solve_addr. }
    assert ((a ^+ ErrorState_size)%a = a16) as Ha_a16.
    { rewrite /ErrorState_size in Ha16 |- *. solve_addr. }

    (* InstallContext, at the token [F] of the site *)
    iApply (switcher_handler_return_install Nswitcher F
              (cstack_set_top_count cstk (top_error_count cstk + 1)) rmap stats_wpcc
              RWL g b e a16 ws with "[- ]"); [done | done | done | | | | | | |].
    { intros r. rewrite /rmap !lookup_insert_is_Some'. naive_solver. }
    { by rewrite /rmap lookup_total_insert. }
    { rewrite /rmap lookup_total_insert_ne // lookup_total_insert_ne //.
      by rewrite (lookup_total_correct _ _ _ Hcsp). }
    { exists a. rewrite /ErrorState_size in Ha16 |- *. solve_addr. }
    { by rewrite Ha16_a -Ha_a16. }
    { by rewrite /ws !length_insert length_error_state_words. }
    rewrite top_export_tbl_set_count Htbl.
    iFrame "Hinv_switcher Hstatic Hpcc HPC Hregs Hcstk Hna".
    iSplitL "Hes".
    { rewrite /install_region Ha16_a -Ha_a16. iExact "Hes". }
    iNext. iSplit.
    - (* The install faults: excluded when the handler runs *)
      iIntros (Hskip) "Hreg".
      iDestruct "HUP" as "[HUR _]".
      iDestruct "HUR" as "[(%eh' & %wpcc' & _ & _ & %Hruns) | HU]".
      + exfalso. destruct Hruns as (_ & Hset & _).
        destruct Hskip as [Hz | Hnl].
        { rewrite top_tframe_set_count in Hz. by apply Hset. }
        apply Hnl.
        rewrite /error_state_loads_ok /rmap lookup_total_insert_ne // lookup_total_insert_ne //.
        rewrite (lookup_total_correct _ _ _ Hcsp) /lea_result /=.
        rewrite (_ : (a16 + - ErrorState_size)%a = Some a);
          last (rewrite /ErrorState_size in Ha16 |- *; solve_addr).
        cbn. split_and!; [done | done | rewrite /ErrorState_size in Ha16 |- *; solve_addr].
      + rewrite unwind_cont_set_top_count.
        iApply (unwind_cont_give with "[Hreg] HU").
        rewrite /handler_unwind_res /error_state_area Hcsp_f /=.
        rewrite /install_region Ha16_a -Ha_a16.
        iExists ws. iFrame "Hreg". iPureIntro.
        by rewrite /ws !length_insert length_error_state_words.
    - (* The install succeeds: the release, then the site's continuation *)
      iIntros "Hreg".
      iDestruct "HUP" as "[_ (Hlock & Hclose & Hret)]".
      rewrite top_error_count_set_count cstack_set_top_count_twice.
      rewrite (_ : (top_error_count cstk + 1 + 1 = top_error_count cstk + 2)%Z); last lia.
      assert (llegalise MEPCC (resumed_pc stats_wpcc (get_a (lw (ws !!! 0%nat)))) =
                stats_pcc stats_release_addr) as ->.
      { rewrite /ws /resumed_pc /stats_wpcc /stats_pcc /lea_result /=.
        rewrite (_ : (STATS_pcc_b + (stats_release_addr - STATS_pcc_b))%a = Some stats_release_addr);
          last solve_addr.
        done. }
      rewrite (stats_install_regs rfault rmap); [ | done | by rewrite /rmap; simplify_map_eq].
      iApply (stats_resumed_release with "Hcode_stats Hlock Hclose Hret [Hreg]");
        [done | done | done |].
      rewrite /error_state_area Hcsp_f /= /install_region Ha16_a -Ha_a16.
      iExists ws. iFrame "Hreg". iPureIntro.
      by rewrite /ws !length_insert length_error_state_words.
  Qed.

End Error_Handling_Handler.
