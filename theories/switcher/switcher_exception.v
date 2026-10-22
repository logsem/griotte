From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import register_tactics map_simpl.
From griotte Require Import logrel fundamental switcher_preamble switcher_return_blocks_1
  interp_switcher_return.
From griotte Require Import switcher_call_blocks_6 switcher_blocks_15_16 switcher_exception_blocks_6
  switcher_spec_exception.
From griotte Require Export switcher_error_handler.

(** * Exception entry of the switcher

    The exception path ([exception_entry_asm], see [switcher_spec_exception])
    spills the interrupted context, then looks for an error handler of the
    faulting compartment. It reads the registers of the faulting
    compartment only to spill them, so its safety needs no validity of the
    register file, except when it resumes the faulting context (a fault of
    the first spill of the call path returns [-ENOTENOUGHSTACK] to the
    caller) or invokes an untrusted handler, which runs through the FTLR
    with the invocation registers.

    It is a safe trap vector ([switcher_trap_vector_safe]) for the faults
    in an untrusted compartment ([untrusted_fault]) and for the faults that
    it handles ([trap_handler_ok]): with no handler (or for a fault in the
    switcher, or of a running handler) the switcher unwinds the call; a
    trusted compartment's stackless handler runs through its table's
    [execute_error_handler]. This closes the faults of trusted code
    ([trap_safe_unwind], [trap_safe_exception_entry]); a resumed fault of
    trusted code is closed by [trap_safe_resume]. A handler returns to the
    switcher, which unwinds ([switcher_handler_return_unwind],
    [interp_handler_return_sentry]). The file also hosts the safety of the
    return-to-switcher entry point ([interp_expr_switcher_return],
    [interp_switcher_return]), which needs the trap vector and would
    otherwise form an import cycle. *)

Section Switcher_Exception.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** Block 16 from [.Lswitch_just_return], where the exception path resumes
      a context: the return to [cra]. *)
  Lemma switcher_just_return_spec (wret : LWord) :
    PC ↦ₚ switcher_label_pc ".Lswitch_just_return" ∗
    cra ↦ᵣ wret ∗
    switcher_code ∗
    ( ▷ ( PC ↦ₚ lupdatePcPerm wret ∗
          cra ↦ᵣ wret ∗
          £ 1 -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) ∧
      ( ⌜jalr_target_ok cnull cra wret.(lw) = false⌝ ∗
        cra ↦ᵣ wret -∗
        trap_safe (switcher_label_pc ".Lswitch_just_return") ⊤
          (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros "(HPC & Hcra & #Hswitcher & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size as Hsize; cbn in Hsize.
    rewrite (_ : (a_switcher_call ^+ switcher_label_offset ".Lswitch_just_return")%a =
                 (a_switcher_call ^+ switcher_label_offset ".Lswitcher_return_to_caller")%a);
      last by offsets_compute.
    switcher_unfold_code "Hswitcher".
    switcher_focus_block (switcher_block ".Lswitcher_return_to_caller") "Hswitcher"
      as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    iApply (switcher_return_block_16_spec _ _ _ _ ∅ with "[- $HPC $Hcra $Hcode]");
      first done.
    iSplitR; first by rewrite big_sepM_empty.
    iSplit.
    - iNext; iIntros "(HPC & Hcra & _ & _ & Hlc)".
      iDestruct "Hpost" as "[Hpost _]".
      iApply ("Hpost" with "[$HPC $Hcra $Hlc]").
    - iIntros "(%Hjalr & Hcra & _)".
      iDestruct "Hpost" as "[_ Hpost]".
      iApply ("Hpost" with "[$Hcra]"); done.
  Qed.

  (** The return to the caller of the context that the exception path
      resumes, at [.Lswitch_just_return]: with safe registers, in an
      untrusted topmost compartment, the jump to [cra] is safe, or faults. *)
  Lemma switcher_just_return_safe (trusted_fault : CSTK → LWord → LReg → iProp Σ)
    (W : WORLD) (C : CmptName) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (rmap : LReg) :
    (∀ r, is_Some (rmap !! r)) ->
    frame_match Ws Cs cstk W C ->

    trap_vector_safe trusted_fault (lword_of_word mtcc_vec) -∗
    (∀ (r : RegName) (v : LWord), ⌜rmap !! r = Some v⌝ → interp W C v) -∗
    top_cmpt_untrusted interp W C cstk -∗
    switcher_static -∗
    PC ↦ₚ switcher_label_pc ".Lswitch_just_return" -∗
    registers_pointsto rmap -∗
    world_interp W C -∗
    interp_cont interp cstk Ws Cs -∗
    na_own cerise_nais ⊤ -∗
    cstack_frag cstk -∗
    WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hfull Hframe) "#Htrap #Hregs #Htop #Hstatic HPC Hrmap Hworld_interp Hcont Hna Hcstk".
    iPoseProof "Hstatic" as "[#Hswitcher _]".
    iAssert (interp_reg interp W C rmap) as "#Hregs_interp".
    { by iApply interp_reg_intro. }
    rewrite /registers_pointsto.
    getRegValList [cra].
    iDestruct ("Hregs" $! cra wcra with "[//]") as "#Hinterp_wcra".
    iExtract "Hrmap" cra as "Hcra".
    iApply (switcher_just_return_spec with "[- $HPC $Hcra $Hswitcher]").
    iSplit.
    - (* The jump to [cra] *)
      iNext; iIntros "(HPC & Hcra & Hlc)".
      iInsert "Hrmap" cra.
      rewrite insert_id //.
      iDestruct (jmp_or_fail_spec with "Htrap Hinterp_wcra") as "Hjmp".
      destruct (decide (isCorrectPC (updatePcPerm wcra.(lw)))) as [Hpc | Hpc]; cycle 1.
      { (* The return address is not a valid PC: the jump faults *)
        iApply "Hjmp"; iFrame "HPC".
        iApply (interp_trap_safe_untrusted with
                 "Htrap Hregs_interp Htop [$Hrmap $Hworld_interp $Hcont $Hna $Hcstk]");
          done. }
      iDestruct "Hjmp" as (p g b e a π) "(%Hwcra_target & #Hjmp)".
      iAssert (future_world g W W) as "Hfuture".
      { destruct g; cbn; iPureIntro; [ apply related_sts_priv_refl_world
                                     | apply related_sts_pub_refl_world]. }
      iSpecialize ("Hjmp" $! W with "Hfuture").
      iDestruct (lc_fupd_elim_later with "Hlc Hjmp") as ">Hjmp'".
      iApply ("Hjmp'" $! cstk Ws Cs rmap); iFrame "∗ #".
      done.
    - (* The jump faults *)
      iIntros "(_ & Hcra)".
      iInsert "Hrmap" cra.
      rewrite insert_id //.
      iApply (interp_trap_safe_untrusted with
               "Htrap Hregs_interp Htop [$Hrmap $Hworld_interp $Hcont $Hna $Hcstk]");
        done.
  Qed.

  (** ** Small lemmas *)

  (** The header of the table of an untrusted topmost compartment. *)
  Lemma top_cmpt_untrusted_header (W : WORLD) (C : CmptName) (cstk : CSTK) :
    top_cmpt_untrusted interp W C cstk -∗ handler_header cstk.
  Proof.
    destruct cstk as [ef [|frm frms] ]; first by iIntros "[]".
    iIntros "(%pcc & %cgp & %eh & %ehs & #Hpcc & #Hcgp & #Heh & #Hehs & _)".
    iExists eh, ehs. iFrame "Heh Hehs".
    iIntros "_". iExists pcc, cgp. iFrame "Hpcc Hcgp".
  Qed.

  (** The handler's PC is safe when the table's PCC is: [interp] does not
      read the cursor of a capability. *)
  Lemma interp_handler_word (W : WORLD) (C : CmptName) (wpcc wpc : LWord) (off : Z) :
    handler_entry wpcc off = Some wpc →
    interp W C wpcc -∗ interp W C wpc.
  Proof.
    destruct wpcc as [w π]. rewrite /handler_entry.
    destruct_word w; try done.
    destruct (b + off)%a as [a'|]; cbn; last done.
    intros [= <-]. iIntros "H". by rewrite (interp_cap_cur_addr W C t c g b e a a' π).
  Qed.

  (** The stack of a stackless handler, the part of the topmost pushed
      frame's stack above the cursor, is safe. *)
  Lemma interp_cont_stackless_csp (W : WORLD) (C : CmptName)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    frame_match Ws Cs cstk W C →
    top_frame_stack_ok cstk →
    cstk.(cstk_frames) ≠ [] →
    interp_continuation cstk Ws Cs -∗
    interp_continuation cstk Ws Cs ∗
    interp W C (stackless_csp cstk).
  Proof.
    destruct cstk as [ef [|frm frms] ]; first done.
    intros Hframe Hstack _.
    destruct (Hstack ltac:(done)) as (b_stk & e_stk & a_stk & Hcsp & Hb & [a4 Ha4]).
    rewrite /top_tframe /= in Hcsp.
    destruct Ws as [|Wt Ws], Cs as [|Ct Cs]; try done.
    destruct Hframe as (Hrelated & <- & Hktk & _).
    rewrite /interp_continuation /interp_cont /= Hktk.
    iIntros "[Hrest [#Hcallee Htop]]". iFrame "Hrest Htop Hcallee".
    rewrite /stackless_csp /= Hcsp /tf_stk_b /tf_stk_e /tf_spill_a Hcsp /=.
    iDestruct "Hcallee" as "[%Hheap Hcallee]".
    assert (((a_stk ^+ 4) ^+ -4)%a = a_stk) as Hspill by solve_addr.
    rewrite Hspill. rewrite Hspill in Hheap.
    iDestruct (interp_monotone_cap_nonheap with "Hcallee") as "Hcallee'";
      [exact Hheap | exact Hrelated |].
    iApply (interp_weakeningEO with "Hcallee'"); try done.
    destruct (is_untrusted_caller_frm frm); solve_addr.
  Qed.

  (** The unwind continuation from the logical relation's resources, for a
      safe trap vector: the return routine pops the frame of the faulting
      compartment, whatever its error handler count. *)
  Lemma logrel_unwind_cont_gen (Nswitcher : namespace) (W : WORLD) (C : CmptName)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    Nswitcher ## N_trap →
    frame_match Ws Cs cstk W C →
    na_inv cerise_nais Nswitcher switcher_inv -∗
    switcher_static -∗
    trap_vector_safe (trap_handler_ok ⊤) (lword_of_word mtcc_vec) -∗
    world_interp W C -∗
    interp_continuation cstk Ws Cs -∗
    unwind_cont ⊤ cstk True.
  Proof.
    iIntros (Hdisj Hframe) "#Hinv #Hstatic #Htrap Hworld Hcont".
    iIntros (n rmap Hfull Hca0 Hca1) "HPC Hrmap Hcstk _ Hna".
    iEval (rewrite -(interp_cont_set_top_count cstk Ws Cs n)) in "Hcont".
    iApply (switcher_return_unwind _ W C Nswitcher (cstack_set_top_count cstk n) Ws Cs
             with "[$HPC $Hrmap $Hinv $Hstatic $Htrap $Hworld $Hcont $Hna $Hcstk]");
      [done | done | done | by apply frame_match_set_top_count |].
    iSplit; iApply interp_int.
  Qed.

  (** ** The handler return *)

  (** From [.Lhandle_error_handler_return], the switcher force-unwinds the
      call (blocks 34, 35 and [.Lcommon_force_unwind]). *)
  #[local] Lemma switcher_handler_return_force_unwind (rmap : LReg) :
    (∀ r, is_Some (rmap !! r)) →
    switcher_static -∗
    PC ↦ₚ switcher_label_pc ".Lhandle_error_handler_return" -∗
    registers_pointsto rmap -∗
    (∀ rmap' : LReg,
       ⌜∀ r, is_Some (rmap' !! r)⌝ -∗
       ⌜rmap' !! ca0 = Some (WInt ECOMPARTMENTFAIL : LWord)⌝ -∗
       ⌜rmap' !! ca1 = Some (WInt 0 : LWord)⌝ -∗
       PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_return -∗
       registers_pointsto rmap' -∗
       WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}) -∗
    WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hfull) "#Hstatic HPC Hrmap Hpost".
    iPoseProof "Hstatic" as "[#Hcode _]".
    rewrite /registers_pointsto.
    getRegValList [ca0;ca1].
    iExtractList "Hrmap" [ca0;ca1] as ["Hca0";"Hca1"].
    iApply (switcher_handler_return_block_spec with "[- $HPC $Hca0 $Hcode]").
    iNext; iIntros "(HPC & Hca0 & _)".
    iApply (switcher_call_block_18_spec with "[- $HPC $Hca0 $Hca1 $Hcode]").
    iNext; iIntros "(HPC & Hca0 & Hca1 & _)".
    iInsertList "Hrmap" [ca0;ca1].
    iApply ("Hpost" with "[] [] [] HPC Hrmap").
    - iPureIntro. intros r. rewrite !lookup_insert_is_Some'. clear -Hfull. naive_solver.
    - iPureIntro. rewrite lookup_insert_ne //. apply lookup_insert_eq.
    - iPureIntro. apply lookup_insert_eq.
  Qed.

  (** A trusted handler returns to the switcher: the switcher unwinds the
      call through the unwind continuation of the fault site. *)
  Lemma switcher_handler_return_unwind
    (F : coPset) (cstk : CSTK) (n : Z) (R_unwind_stk : iProp Σ) (rmap : LReg) :
    (∀ r, is_Some (rmap !! r)) →
    switcher_static -∗
    PC ↦ₚ switcher_label_pc ".Lhandle_error_handler_return" -∗
    registers_pointsto rmap -∗
    cstack_frag (cstack_set_top_count cstk n) -∗
    unwind_cont F cstk R_unwind_stk -∗
    R_unwind_stk -∗
    na_own cerise_nais F -∗
    WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hfull) "#Hstatic HPC Hrmap Hcstk HU HS Hna".
    iApply (switcher_handler_return_force_unwind with "Hstatic HPC Hrmap"); first done.
    iIntros (rmap' Hfull' Hca0 Hca1) "HPC Hrmap".
    iApply ("HU" with "[//] [//] [//] HPC Hrmap Hcstk HS Hna").
  Qed.

  (** The handler-return entry point is safe to execute, for a safe trap
      vector: the registers are re-filtered, then the switcher unwinds. *)
  Lemma interp_expr_handler_return_gen (W : WORLD) (C : CmptName) (Nswitcher : namespace) :
    Nswitcher ## N_trap ->
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static ∗
    trap_vector_safe (trap_handler_ok ⊤) (lword_of_word mtcc_vec)
    ⊢ interp_expr interp (interp_cont interp) W C
        (switcher_label_pc ".Lhandle_error_handler_return").
  Proof.
    iIntros (Hdisj) "(#Hinv_switcher & #Hstatic & #Htrap) %cstk %Ws %Cs %rmap0
             (Hregs & _ & HPC & Hrmap & Hworld_interp & Hcont_K & Hna & Hcstk & %Hframe)".
    iApply (interp_reg_refilter with "Hregs Hrmap Hworld_interp").
    iIntros (rmap) "%Hfull_rmap _ Hrmap Hworld_interp". clear rmap0.
    cbn in Hfull_rmap.
    iApply (switcher_handler_return_force_unwind with "Hstatic HPC Hrmap"); first done.
    iIntros (rmap' Hfull' Hca0 Hca1) "HPC Hrmap".
    iApply (switcher_return_unwind with
             "[$HPC $Hrmap $Hinv_switcher $Hstatic $Htrap $Hworld_interp $Hcont_K $Hna $Hcstk]");
      [done | done | done | done |].
    iSplit; iApply interp_int.
  Qed.

  (** The sentry that the switcher gives a handler is safe, for a safe trap
      vector (needed only under the sentry's later). *)
  Lemma interp_handler_return_sentry_gen
    (W : WORLD) (C : CmptName) (Nswitcher : namespace) (mie : InterruptStatus) :
    Nswitcher ## N_trap ->
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static ∗
    ▷ trap_vector_safe (trap_handler_ok ⊤) (lword_of_word mtcc_vec)
    ⊢ interp W C (handler_return_sentry mie).
  Proof.
    iIntros (Hdisj) "(#Hinv & #Hstatic & #Htrap)".
    rewrite /handler_return_sentry interp_unfold /=.
    iSplit; first (iPureIntro; exact switcher_not_heap_range).
    iIntros "!> %regs %W' % %".
    destruct g'; first done.
    iNext; iApply (interp_expr_handler_return_gen with "[$Hinv $Hstatic $Htrap]"); done.
  Qed.

  (** ** Untrusted handlers *)

  (** A stackless handler of an untrusted topmost compartment runs through
      the FTLR: its PC comes from the table's PCC, and the invocation
      registers are safe (the return sentry, the table's CGP, the stack
      above the frame's cursor, integers). *)
  Lemma untrusted_handler_invoke_safe (Nswitcher : namespace)
    (W : WORLD) (C : CmptName) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (rmap : LReg) (wpcc wcgp wpc : LWord) (ehs mcause mtval : Z) (regs : LReg) :
    Nswitcher ## N_trap ->
    frame_match Ws Cs cstk W C ->
    top_frame_stack_ok cstk ->
    handler_entry wpcc ehs = Some wpc ->
    handler_invocation_regs Stackless cstk wcgp rmap mcause mtval regs ->

    na_inv cerise_nais Nswitcher switcher_inv -∗
    switcher_static -∗
    trap_vector_safe (trap_handler_ok ⊤) (lword_of_word mtcc_vec) -∗
    top_cmpt_untrusted interp W C cstk -∗
    top_export_tbl cstk ↦ₐ□ wpcc -∗
    (top_export_tbl cstk ^+ ExportTable_offset_cgp)%a ↦ₐ□ wcgp -∗
    PC ↦ₚ wpc -∗
    registers_pointsto regs -∗
    world_interp W C -∗
    interp_continuation cstk Ws Cs -∗
    cstack_frag (cstack_set_top_count cstk (top_error_count cstk + 1)%Z) -∗
    na_own cerise_nais ⊤ -∗
    WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hdisj Hframe Hstack Hentry Hinv_regs)
      "#Hinv_switcher #Hstatic #Htrap #Htop #Hpcc #Hcgp HPC Hregs Hworld_interp Hcont Hcstk Hna".
    destruct (cstk_frames cstk) as [|frm frms] eqn:Hframes.
    { by rewrite /top_cmpt_untrusted Hframes. }
    iAssert (interp W C wpcc ∗ interp W C wcgp)%I as "[#Hpcc_interp #Hcgp_interp]".
    { iEval (rewrite /top_cmpt_untrusted Hframes) in "Htop".
      iDestruct "Htop" as (pcc cgp eh ehs') "(Hpcc' & Hcgp' & _ & _ & #Hsafe)".
      rewrite /top_export_tbl /top_tframe Hframes.
      iDestruct (pointsto_agree with "Hpcc Hpcc'") as %->.
      iDestruct (pointsto_agree with "Hcgp Hcgp'") as %->.
      iApply "Hsafe". iPureIntro. apply related_sts_priv_refl_world. }
    iDestruct (interp_handler_word with "Hpcc_interp") as "#Hwpc"; first exact Hentry.
    iDestruct (interp_cont_stackless_csp with "Hcont") as "[Hcont #Hcsp_interp]";
      [done | done | by rewrite Hframes |].
    iDestruct (fundamental (trap_handler_ok ⊤) with "Htrap Hwpc") as "Hexpr".
    iApply ("Hexpr" $! (cstack_set_top_count cstk (top_error_count cstk + 1)%Z) Ws Cs regs
             with "[- ]").
    iFrame "HPC Hregs Hworld_interp Hna Hcstk".
    rewrite top_cmpt_untrusted_set_top_count interp_cont_set_top_count.
    iFrame "Htop Hcont".
    iSplit; last (iPureIntro; by apply frame_match_set_top_count).
    destruct Hinv_regs as (Hfull & [mie Hcra] & Hcgp_r & (Hcsp_r & Hca0 & Hca1 & Hca2) & Hzero).
    iApply interp_reg_intro; first done.
    iIntros (r v Hv).
    destruct (decide (r = cra)) as [-> | Hr_cra].
    { rewrite Hcra in Hv. simplify_eq.
      iApply (interp_handler_return_sentry_gen with "[$Hinv_switcher $Hstatic $Htrap]"); done. }
    destruct (decide (r = cgp)) as [-> | Hr_cgp].
    { rewrite Hcgp_r in Hv. by simplify_eq. }
    destruct (decide (r = csp)) as [-> | Hr_csp].
    { rewrite Hcsp_r in Hv. by simplify_eq. }
    destruct (decide (r = ca0)) as [-> | Hr_ca0].
    { rewrite Hca0 in Hv. simplify_eq. iApply interp_int. }
    destruct (decide (r = ca1)) as [-> | Hr_ca1].
    { rewrite Hca1 in Hv. simplify_eq. iApply interp_int. }
    destruct (decide (r = ca2)) as [-> | Hr_ca2].
    { rewrite Hca2 in Hv. simplify_eq. iApply interp_int. }
    rewrite Hzero in Hv; first (simplify_eq; iApply interp_int).
    clear -Hr_cra Hr_cgp Hr_csp Hr_ca0 Hr_ca1 Hr_ca2. set_solver.
  Qed.

  (** ** The trap vector *)

  (** The safety of the exception entry, for a fault in an untrusted
      compartment (with the whole non-atomic token) or a fault that the
      switcher handles, for any token [F] that contains the switcher's
      invariant and the trap-entry part. *)
  Definition exception_entry_safe (Nswitcher : namespace) : iProp Σ :=
    □ ∀ (F : coPset) (cstk : CSTK) (rmap : LReg) (w : LWord),
      ⌜↑Nswitcher ⊆ F⌝ -∗
      ⌜↑N_trap ⊆ F⌝ -∗
      ⌜∀ r, is_Some (rmap !! r)⌝ -∗
      ((⌜F = ⊤⌝ ∗ untrusted_fault cstk rmap) ∨ trap_handler_ok F cstk w rmap) -∗
      PC ↦ₚ lword_of_word mtcc_vec -∗
      trap_entry_out w -∗
      registers_pointsto rmap -∗
      na_own cerise_nais (F ∖ ↑N_trap) -∗
      cstack_frag cstk -∗
      WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.

  #[global] Instance exception_entry_safe_persistent Nswitcher :
    Persistent (exception_entry_safe Nswitcher).
  Proof. rewrite /exception_entry_safe. apply _. Qed.

  Lemma exception_entry_safe_vector (Nswitcher : namespace) :
    exception_entry_safe Nswitcher ⊢
    trap_vector_safe (trap_handler_ok ⊤) (lword_of_word mtcc_vec).
  Proof.
    iIntros "#Hsafe !>" (cstk regs w Hfull) "Hfault HPC Hout Hrmap Hna Hcstk".
    iApply ("Hsafe" $! ⊤ with "[%] [%] [//] [Hfault] HPC Hout Hrmap Hna Hcstk");
      [set_solver | set_solver |].
    iDestruct "Hfault" as "[Hfault | Hfault]"; [iLeft; by iFrame | by iRight].
  Qed.

  (** A fault of the exception path itself is a fault in the switcher. *)
  Lemma exception_entry_safe_nested (Nswitcher : namespace) (F : coPset) (cstk : CSTK) :
    ↑Nswitcher ⊆ F →
    ↑N_trap ⊆ F →
    exception_entry_safe Nswitcher -∗
    unwind_cont F cstk True -∗
    path_nested_fault F cstk.
  Proof.
    iIntros (HF HFtrap) "#Hsafe HU".
    iIntros (off n rmap' Hno_resume Hfull) "Hrmap Hcstk Hna".
    iApply trap_safe_entry_intro.
    iSplit; last by iIntros "!> %Hv".
    iDestruct (trap_entry_res_split F with "Hna") as "[Htok Hna]"; first done.
    iModIntro. iFrame "Htok". iIntros "!> Hout HPC".
    iApply ("Hsafe" $! F (cstack_set_top_count cstk n) rmap' (switcher_pc off) with
             "[//] [//] [//] [HU] HPC Hout Hrmap Hna Hcstk").
    iRight. iApply trap_handler_ok_switcher; [done | apply switcher_fault_pc_cap |].
    by rewrite unwind_cont_set_top_count.
  Qed.

  Lemma unwind_cont_path_unwind_k (F : coPset) (cstk : CSTK) (w : LWord) :
    unwind_cont F cstk True -∗ path_unwind_k F cstk w.
  Proof.
    iIntros "HU" (_ n rmap' Hfull Hca0 Hca1) "HPC Hrmap Hcstk Hna".
    iApply ("HU" with "[//] [//] [//] HPC Hrmap Hcstk [//] Hna").
  Qed.

  (** A fault in an untrusted compartment: the registers are re-filtered;
      the switcher unwinds, resumes the caller, or invokes the
      compartment's stackless handler, which runs through the FTLR. *)
  Lemma exception_entry_untrusted_safe (Nswitcher : namespace)
    (cstk : CSTK) (rmap : LReg) (w : LWord) :
    Nswitcher ## N_trap ->
    (∀ r, is_Some (rmap !! r)) ->

    na_inv cerise_nais Nswitcher switcher_inv -∗
    switcher_static -∗
    ▷ exception_entry_safe Nswitcher -∗
    untrusted_fault cstk rmap -∗
    PC ↦ₚ lword_of_word mtcc_vec -∗
    trap_entry_out w -∗
    registers_pointsto rmap -∗
    na_own cerise_nais (⊤ ∖ ↑N_trap) -∗
    cstack_frag cstk -∗
    WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hdisj Hfull_rmap)
      "#Hinv_switcher #Hstatic #Hsafe Huntrusted HPC Hout Hrmap Hna Hcstk".
    iDestruct "Huntrusted" as (W C Ws Cs Hframe) "(#Hregs & #Htop & Hworld_interp & Hcont)".
    iApply (interp_reg_refilter with "Hregs Hrmap Hworld_interp").
    iIntros (rmap') "%Hfull_rmap' #Hregs' Hrmap Hworld_interp".
    iDestruct (top_cmpt_untrusted_header with "Htop") as "#Hheader".
    iApply (switcher_exception_path_spec Nswitcher ⊤ cstk (cstack_frag cstk) with
             "[$Hinv_switcher $Hstatic $HPC $Hrmap $Hout $Hna Hcstk Hworld_interp Hcont]");
      [set_solver | set_solver | done | done |].
    iSplitL "Hcstk"; first by case_decide.
    iSplitR; first (iIntros "_"; iExact "Hheader").
    iNext.
    iPoseProof (exception_entry_safe_vector with "Hsafe") as "#Htrap".
    iSplit; [|iSplit; [|iSplit] ].
    - (* The forced unwind *)
      iApply unwind_cont_path_unwind_k.
      by iApply (logrel_unwind_cont_gen with "Hinv_switcher Hstatic Htrap Hworld_interp Hcont").
    - (* The resumed caller returns to [cra], with safe registers *)
      iIntros (_ rmap'' Hfull_rmap'' Hsame Hca0 Hca1) "HPC Hrmap Hcstk Hna".
      iApply (switcher_just_return_safe with
               "Htrap [] Htop Hstatic HPC Hrmap Hworld_interp Hcont Hna Hcstk"); [done | done |].
      iIntros (r v Hv).
      destruct (decide (r = ca0)) as [-> | Hr0].
      { rewrite Hca0 in Hv. simplify_eq. iApply interp_int. }
      destruct (decide (r = ca1)) as [-> | Hr1].
      { rewrite Hca1 in Hv. simplify_eq. iApply interp_int. }
      rewrite Hsame in Hv; [| done | done].
      by iApply "Hregs'".
    - (* A fault of the path *)
      iIntros (_).
      iApply (exception_entry_safe_nested with "Hsafe"); [set_solver | set_solver |].
      by iApply (logrel_unwind_cont_gen with "Hinv_switcher Hstatic Htrap Hworld_interp Hcont").
    - (* The stackless handler *)
      iIntros (wpcc wcgp wpc ehs mcause mtval regs _ _ Hstack _ _ Hentry Hinv_regs)
        "Hpcc Hcgp _ HPC Hregs_h Hcstk Hna".
      iApply (untrusted_handler_invoke_safe with
               "Hinv_switcher Hstatic Htrap Htop Hpcc Hcgp HPC Hregs_h Hworld_interp Hcont
                Hcstk Hna");
        done.
  Qed.

  (** A fault in the switcher, in a compartment whose table declares no
      handler, or in a running trusted handler (odd count): the switcher
      unwinds; a nested fault of the path is a fault in the switcher. *)
  Lemma exception_entry_unwind_safe (Nswitcher : namespace) (F : coPset)
    (cstk : CSTK) (rmap : LReg) (w : LWord) :
    ↑Nswitcher ⊆ F ->
    ↑N_trap ⊆ F ->
    Nswitcher ## N_trap ->
    (∀ r, is_Some (rmap !! r)) ->
    trap_no_resume w ->

    na_inv cerise_nais Nswitcher switcher_inv -∗
    switcher_static -∗
    ▷ exception_entry_safe Nswitcher -∗
    unwind_cont F cstk True -∗
    (⌜switcher_fault_pc w⌝ ∨
     no_handler (top_export_tbl cstk) ∨
     (⌜Z.odd (top_error_count cstk) = true⌝ ∗
      ∃ eh ehs : Z,
        top_export_tbl cstk ↦ₕ□{stackful} eh ∗
        top_export_tbl cstk ↦ₕ□{stackless} ehs)) -∗
    PC ↦ₚ lword_of_word mtcc_vec -∗
    trap_entry_out w -∗
    registers_pointsto rmap -∗
    na_own cerise_nais (F ∖ ↑N_trap) -∗
    cstack_frag cstk -∗
    WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (HF HFtrap Hdisj Hfull_rmap Hno_resume)
      "#Hinv_switcher #Hstatic #Hsafe HU #Hcase HPC Hout Hrmap Hna Hcstk".
    iAssert (⌜¬ switcher_fault_pc w⌝ → handler_header cstk)%I as "#Hheader".
    { iIntros (Hnot). rewrite /no_handler.
      iDestruct "Hcase" as "[%Hpc | [[Heh Hehs] | [%Hodd (%eh & %ehs & Heh & Hehs)] ] ]";
        first done.
      - iExists _, _. iFrame "Heh Hehs". iIntros ([ [Hne | Hne] _]); by contradict Hne.
      - iExists eh, ehs. iFrame "Heh Hehs". iIntros ([_ Hev]).
        exfalso. rewrite -Z.negb_odd Hodd in Hev. done. }
    iApply (switcher_exception_path_spec Nswitcher F cstk (cstack_frag cstk) with
             "[$Hinv_switcher $Hstatic $HPC $Hrmap $Hout $Hna Hcstk HU]");
      [done | done | done | done |].
    iSplitL "Hcstk"; first by case_decide.
    iSplitR; first iExact "Hheader".
    iNext.
    iSplit; [|iSplit; [|iSplit] ].
    - by iApply unwind_cont_path_unwind_k.
    - by iIntros (Hresume).
    - iIntros (_). by iApply (exception_entry_safe_nested with "Hsafe HU").
    - iIntros (wpcc wcgp wpc ehs' mcause mtval regs Hnot Hev _ Hehs' _ _ _) "_ _ #Hehs _ _ _ _".
      rewrite /no_handler.
      iDestruct "Hcase" as "[%Hpc | [[_ Hnone] | [%Hodd _] ] ]"; first done.
      + iDestruct (handler_stackless_agree with "Hnone Hehs") as %Heq. by subst ehs'.
      + exfalso. rewrite -Z.negb_odd Hodd in Hev. done.
  Qed.

  (** A fault in a trusted compartment whose table declares trusted
      handlers: the switcher invokes the stackless handler, through the
      table's [execute_error_handler], or unwinds. *)
  Lemma exception_entry_trusted_handler_safe (Nswitcher : namespace)
    (cstk : CSTK) (rmap : LReg) (w : LWord)
    (P_fault : CSTK → LWord → LReg → iProp Σ) (eh : Z) :
    Nswitcher ## N_trap ->
    (∀ r, is_Some (rmap !! r)) ->
    trap_no_resume w ->

    na_inv cerise_nais Nswitcher switcher_inv -∗
    switcher_static -∗
    ▷ exception_entry_safe Nswitcher -∗
    trusted_handler (top_export_tbl cstk) P_fault -∗
    P_fault cstk w rmap -∗
    error_state_slot eh rmap -∗
    unwind_cont ⊤ cstk (error_state_slot eh rmap) -∗
    PC ↦ₚ lword_of_word mtcc_vec -∗
    trap_entry_out w -∗
    registers_pointsto rmap -∗
    na_own cerise_nais (⊤ ∖ ↑N_trap) -∗
    cstack_frag cstk -∗
    WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hdisj Hfull_rmap Hno_resume)
      "#Hinv_switcher #Hstatic #Hsafe #Hhandler HP Hslot HU HPC Hout Hrmap Hna Hcstk".
    iDestruct "Hhandler" as (wpcc wcgp eh' ehs) "(#Hpcc & #Hcgp & #Heh & #Hehs & _ & #Hexec)".
    iDestruct (unwind_cont_give with "Hslot HU") as "HU".
    (* The stackless handler's WP, for this fault *)
    iAssert (□ ∀ (mcause mtval : Z) (wpc : LWord) (regs : LReg),
               ▷ ( ⌜ehs ≠ ExportTable_no_handler⌝ -∗
                   ⌜top_export_tbl cstk = top_export_tbl cstk⌝ -∗
                   ⌜Z.even (top_error_count cstk) = true⌝ -∗
                   ⌜mcause_ok mcause⌝ -∗
                   ⌜handler_entry wpcc ehs = Some wpc⌝ -∗
                   ⌜handler_invocation_regs Stackless cstk wcgp rmap mcause mtval regs⌝ -∗
                   PC ↦ₚ wpc -∗
                   registers_pointsto regs -∗
                   P_fault cstk w rmap -∗
                   handler_slot Stackless w rmap -∗
                   unwind_cont ⊤ cstk (handler_unwind_res Stackless rmap) -∗
                   cstack_frag (cstack_set_top_count cstk (top_error_count cstk + 1)) -∗
                   na_own cerise_nais ⊤ -∗
                   WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ))%I
      as "#Hrun".
    { iIntros "!>" (mcause mtval wpc regs).
      destruct (decide (ehs = ExportTable_no_handler)) as [Hnone | Hsome].
      - iNext. iIntros (Hsome). done.
      - iDestruct ("Hexec" with "[//]") as "#Hexec'".
        iSpecialize ("Hexec'" $! cstk w rmap mcause mtval wpc regs).
        iNext. iIntros "_". iExact "Hexec'". }
    iApply (switcher_exception_path_spec Nswitcher ⊤ cstk (cstack_frag cstk) with
             "[$Hinv_switcher $Hstatic $HPC $Hrmap $Hout $Hna Hcstk HU HP]");
      [set_solver | set_solver | done | done |].
    iSplitL "Hcstk"; first by case_decide.
    iSplitR.
    { iIntros "_". iExists eh', ehs. iFrame "Heh Hehs".
      iIntros "_". iExists wpcc, wcgp. iFrame "Hpcc Hcgp". }
    iNext.
    iSplit; [|iSplit; [|iSplit] ].
    - by iApply unwind_cont_path_unwind_k.
    - by iIntros (Hresume).
    - iIntros (_). iApply (exception_entry_safe_nested with "Hsafe HU"); set_solver.
    - iIntros (wpcc' wcgp' wpc ehs' mcause mtval regs _ Hev _ Hehs_some Hmcause Hentry Hinv_regs)
        "#Hpcc' #Hcgp' #Hehs' HPC Hregs Hcstk Hna".
      iDestruct (pointsto_agree with "Hpcc Hpcc'") as %<-.
      iDestruct (pointsto_agree with "Hcgp Hcgp'") as %<-.
      iDestruct (handler_stackless_agree with "Hehs Hehs'") as %<-.
      iApply ("Hrun" with "[//] [//] [//] [//] [//] [//] HPC Hregs HP [//] HU Hcstk Hna").
  Qed.

  (** The exception entry is safe, by Löb induction: the exception path
      needs it only after its first instruction, and a nested fault of the
      path enters it again under the later of trap entry. *)
  Lemma switcher_exception_entry_safe (Nswitcher : namespace) :
    Nswitcher ## N_trap ->
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static
    ⊢ exception_entry_safe Nswitcher.
  Proof.
    iIntros (Hdisj) "[#Hinv_switcher #Hstatic]".
    iLöb as "IH".
    iIntros "!>" (F cstk rmap w HF HFtrap Hfull) "Hfault HPC Hout Hrmap Hna Hcstk".
    iDestruct "Hfault" as "[[-> Huntrusted] | Hhandled]".
    { iApply (exception_entry_untrusted_safe with
               "Hinv_switcher Hstatic IH Huntrusted HPC Hout Hrmap Hna Hcstk"); done. }
    iDestruct (trap_handler_ok_cases with "Hhandled")
      as (Hno_resume) "[ [HU Hcase] | [ [-> Hrow] | (HU & %Hodd & Hheader)] ]".
    - (* A fault in the switcher, or no handler *)
      iApply (exception_entry_unwind_safe with
               "Hinv_switcher Hstatic IH HU [Hcase] HPC Hout Hrmap Hna Hcstk"); [done.. |].
      iDestruct "Hcase" as "[Hcase | Hcase]"; [by iLeft | iRight; by iLeft].
    - (* Trusted handlers *)
      iDestruct "Hrow" as (P_fault eh) "(Hhandler & _ & HP & Hslot & HU)".
      iApply (exception_entry_trusted_handler_safe with
               "Hinv_switcher Hstatic IH Hhandler HP Hslot HU HPC Hout Hrmap Hna Hcstk"); done.
    - (* A fault in a running trusted handler *)
      iApply (exception_entry_unwind_safe with
               "Hinv_switcher Hstatic IH HU [Hheader] HPC Hout Hrmap Hna Hcstk"); [done.. |].
      iRight; iRight. by iFrame.
  Qed.

  (** The trap vector of the machine, the exception entry of the switcher,
      is safe, for the faults in an untrusted compartment and for the
      faults that it handles ([trap_handler_ok ⊤]). *)
  Lemma switcher_mtcc_vec_safe (Nswitcher : namespace) :
    Nswitcher ## N_trap ->
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static
    ⊢ trap_vector_safe (trap_handler_ok ⊤) (lword_of_word mtcc_vec).
  Proof.
    iIntros (Hdisj) "Hres".
    iApply exception_entry_safe_vector.
    by iApply switcher_exception_entry_safe.
  Qed.

  (** The exception entry of the switcher is a safe trap vector. *)
  Lemma switcher_trap_vector_safe (Nswitcher : namespace) :
    Nswitcher ## N_trap ->
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static
    ⊢ trap_vector_safe (trap_handler_ok ⊤) (switcher_label_pc "exception_entry_asm").
  Proof.
    iIntros (Hdisj) "[#Hinv_switcher #Hstatic]".
    iPoseProof "Hstatic" as "(_ & _ & %Hmtcc)".
    rewrite -Hmtcc.
    iApply (switcher_mtcc_vec_safe with "[$Hinv_switcher $Hstatic]"); done.
  Qed.

  (** The unwind continuation from the logical relation's resources. *)
  Lemma logrel_unwind_cont (Nswitcher : namespace) (W : WORLD) (C : CmptName)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    Nswitcher ## N_trap →
    frame_match Ws Cs cstk W C →
    na_inv cerise_nais Nswitcher switcher_inv -∗
    switcher_static -∗
    world_interp W C -∗
    interp_continuation cstk Ws Cs -∗
    unwind_cont ⊤ cstk True.
  Proof.
    iIntros (Hdisj Hframe) "#Hinv #Hstatic Hworld Hcont".
    iPoseProof (switcher_mtcc_vec_safe Nswitcher Hdisj with "[$Hinv $Hstatic]") as "#Htrap".
    by iApply (logrel_unwind_cont_gen with "Hinv Hstatic Htrap Hworld Hcont").
  Qed.

  (** The handler-return entry point is safe to execute. *)
  Lemma interp_expr_handler_return (W : WORLD) (C : CmptName) (Nswitcher : namespace) :
    Nswitcher ## N_trap ->
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static
    ⊢ interp_expr interp (interp_cont interp) W C
        (switcher_label_pc ".Lhandle_error_handler_return").
  Proof.
    iIntros (Hdisj) "[#Hinv #Hstatic]".
    iPoseProof (switcher_mtcc_vec_safe Nswitcher Hdisj with "[$Hinv $Hstatic]") as "#Htrap".
    by iApply (interp_expr_handler_return_gen with "[$Hinv $Hstatic $Htrap]").
  Qed.

  (** The sentry that the switcher gives a handler is safe. *)
  Lemma interp_handler_return_sentry
    (W : WORLD) (C : CmptName) (Nswitcher : namespace) (mie : InterruptStatus) :
    Nswitcher ## N_trap ->
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static
    ⊢ interp W C (handler_return_sentry mie).
  Proof.
    iIntros (Hdisj) "[#Hinv #Hstatic]".
    iPoseProof (switcher_mtcc_vec_safe Nswitcher Hdisj with "[$Hinv $Hstatic]") as "#Htrap".
    by iApply (interp_handler_return_sentry_gen with "[$Hinv $Hstatic $Htrap]").
  Qed.

  (** The callee's stack is smaller than the minimum stack size of the
      entry point: block 20 sets the return values, and the return routine
      pops the frame already pushed. No register needs to be safe. *)
  Lemma switcher_call_stack_too_small_unwind
    (W : WORLD) (C : CmptName) (Nswitcher : namespace)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (rmap : LReg) :
    Nswitcher ## N_trap ->
    (∀ r, is_Some (rmap !! r)) ->
    frame_match Ws Cs cstk W C ->

    PC ↦ₚ switcher_label_pc ".Lswitch_stack_too_small" ∗
    registers_pointsto rmap ∗
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static ∗
    world_interp W C ∗
    interp_cont interp cstk Ws Cs ∗
    na_own cerise_nais ⊤ ∗
    cstack_frag cstk
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hdisj Hfull_rmap Hframe)
      "(HPC & Hrmap & #Hinv_switcher & #Hstatic & Hworld_interp & Hcont & Hna & Hcstk)".
    iPoseProof "Hstatic" as "[#Hcode _]".
    iPoseProof (switcher_mtcc_vec_safe Nswitcher Hdisj with "[$Hinv_switcher $Hstatic]")
      as "#Htrap".
    rewrite /registers_pointsto.
    getRegValList [ca0;ca1].
    iExtractList "Hrmap" [ca0;ca1] as ["Hca0";"Hca1"].
    iApply (switcher_call_block_20_spec with "[- $HPC $Hca0 $Hca1 $Hcode]").
    iNext; iIntros "(HPC & Hca0 & Hca1 & _)".
    iInsertList "Hrmap" [ca0;ca1].
    iApply (switcher_return_unwind with
             "[$HPC $Hrmap $Hinv_switcher $Hstatic $Htrap $Hworld_interp $Hcont $Hna $Hcstk]");
      [|by simplify_map_eq|by simplify_map_eq|done|].
    { intros r. rewrite !lookup_insert_is_Some'. naive_solver. }
    iSplit; iApply interp_int.
  Qed.

  (** A fault closes through the exception path of the switcher: after
      trap entry, the switcher handles the fault ([trap_handler_ok F]). The
      resources come under an update at the time of the fault; the
      non-atomic token [F] provides the trap-entry token, and the exception
      path opens the invariant of the switcher with the rest of [F]. *)
  Lemma trap_safe_exception_entry (Nswitcher : namespace) (F : coPset) (w : LWord) :
    ↑Nswitcher ⊆ F →
    ↑N_trap ⊆ F →
    Nswitcher ## N_trap →
    na_inv cerise_nais Nswitcher switcher_inv -∗
    switcher_static -∗
    (|={⊤}=>
       ∃ (rmap : LReg) (cstk : CSTK),
         ⌜∀ r, is_Some (rmap !! r)⌝ ∗
         na_own cerise_nais F ∗
         registers_pointsto rmap ∗
         cstack_frag cstk ∗
         trap_handler_ok F cstk w rmap) -∗
    trap_safe w ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I.
  Proof.
    iIntros (HF HFtrap Hdisj) "#Hinv_switcher #Hstatic Hres".
    iPoseProof (switcher_exception_entry_safe with "[$Hinv_switcher $Hstatic]") as "#Hsafe";
      first done.
    iApply trap_safe_entry_intro.
    iSplit; last by iIntros "!> %Hv".
    iMod "Hres" as (rmap cstk Hfull_rmap) "(Hna & Hrmap & Hcstk & Hhandled)".
    iDestruct (trap_entry_res_split F with "Hna") as "[Htok Hna]"; first done.
    iModIntro. iFrame "Htok". iIntros "!> Hout HPC".
    iApply ("Hsafe" $! F cstk rmap w with "[//] [//] [//] [Hhandled] HPC Hout Hrmap Hna Hcstk").
    by iRight.
  Qed.

  (** A fault that the exception path resumes (a fault of the first spill
      of the call path) closes through the exception path of the switcher:
      after trap entry, the switcher spills the registers, overwrites the
      return values with [-ENOTENOUGHSTACK] and 0, and installs the context
      again, at [.Lswitch_just_return]. The resources come under an update
      at the time of the fault; the non-atomic token [F] provides the
      trap-entry token, and the exception path opens the invariant of the
      switcher with the rest of [F]. *)
  Lemma trap_safe_resume (Nswitcher : namespace) (F : coPset) (w : LWord) :
    ↑Nswitcher ⊆ F →
    ↑N_trap ⊆ F →
    Nswitcher ## N_trap →
    ¬ trap_no_resume w →
    na_inv cerise_nais Nswitcher switcher_inv -∗
    switcher_static -∗
    (|={⊤}=>
       ∃ rmap : LReg,
         ⌜∀ r, is_Some (rmap !! r)⌝ ∗
         na_own cerise_nais F ∗
         registers_pointsto rmap ∗
         (∀ rmap' : LReg,
            ⌜∀ r, is_Some (rmap' !! r)⌝ -∗
            ⌜∀ r, r ≠ ca0 → r ≠ ca1 → rmap' !! r = rmap !! r⌝ -∗
            ⌜rmap' !! ca0 = Some (WInt ENOTENOUGHSTACK : LWord)⌝ -∗
            ⌜rmap' !! ca1 = Some (WInt 0 : LWord)⌝ -∗
            PC ↦ₚ switcher_label_pc ".Lswitch_just_return" -∗
            registers_pointsto rmap' -∗
            na_own cerise_nais F -∗
            WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})) -∗
    trap_safe w ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I.
  Proof.
    iIntros (HF HFtrap Hdisj Hresume) "#Hinv_switcher #Hstatic Hres".
    (* A resumed fault is in the switcher *)
    assert (switcher_fault_pc w) as Hpc.
    { rewrite /switcher_fault_pc.
      destruct (decide (get_b (lmepcc_of_pc w).(lw) = (b_switcher : Z))) as [Hb | Hb];
        first done.
      exfalso. apply Hresume. by left. }
    iApply trap_safe_entry_intro.
    iSplit; last by iIntros "!> %Hv".
    iMod "Hres" as (rmap Hfull_rmap) "(Hna & Hrmap & Hcont)".
    iDestruct (trap_entry_res_split F with "Hna") as "[Htok Hna]"; first done.
    iModIntro. iFrame "Htok". iIntros "!> Hout HPC".
    (* The path only resumes: its call stack is not used, any one does *)
    iApply (switcher_exception_path_spec Nswitcher F
              (entry_cstack (MkTFrame (WInt 0) (WInt 0) 0)) True rmap with
             "[$Hinv_switcher $Hstatic $HPC $Hrmap $Hout $Hna Hcont]");
      [exact HF | exact HFtrap | exact Hdisj | exact Hfull_rmap |].
    rewrite decide_False; last exact Hresume.
    iSplitR; first done.
    iSplitR; first by iIntros (Hnot).
    iNext; iSplit; [|iSplit; [|iSplit] ].
    - by iIntros (Hno_resume).
    - iIntros (_ rmap' Hfull' Hsame Hca0 Hca1) "HPC Hrmap _ Hna".
      iApply ("Hcont" with "[//] [//] [//] [//] HPC Hrmap Hna").
    - by iIntros (Hnot).
    - by iIntros (wpcc wcgp wpc ehs mcause mtval regs Hnot).
  Qed.

  (** A fault in trusted code is safe: after exception entry, the exception
      entry of the switcher unwinds the call of the faulting compartment, or
      resumes a fault in an untrusted compartment. The resources and the
      fault's justification come under an update at the time of the fault
      (for instance, to close an invariant). *)
  Lemma trap_safe_unwind (Nswitcher : namespace) (cstk : CSTK) (rmap : LReg) (w : LWord) :
    Nswitcher ## N_trap ->
    (∀ r, is_Some (rmap !! r)) ->
    na_inv cerise_nais Nswitcher switcher_inv -∗
    switcher_static -∗
    (|={⊤}=>
       registers_pointsto rmap ∗
       na_own cerise_nais ⊤ ∗
       cstack_frag cstk ∗
       (untrusted_fault cstk rmap ∨ trap_handler_ok ⊤ cstk w rmap)) -∗
    trap_safe w ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I.
  Proof.
    iIntros (Hdisj Hfull_rmap) "#Hinv_switcher #Hstatic Hres".
    iPoseProof (switcher_mtcc_vec_safe Nswitcher Hdisj with "[$Hinv_switcher $Hstatic]")
      as "#Htrap".
    iApply (interp_trap_safe with "Htrap Hres"); done.
  Qed.

  (** A fault in trusted code, with the logical relation's resources, in
      the switcher ([switcher_fault_pc w]) or in a compartment whose table
      declares no handler: the switcher unwinds the call of the faulting
      compartment through the return routine. *)
  Lemma trap_safe_unwind_logrel
    (W : WORLD) (C : CmptName) (Nswitcher : namespace)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (rmap : LReg) (w : LWord) :
    Nswitcher ## N_trap ->
    (∀ r, is_Some (rmap !! r)) ->
    frame_match Ws Cs cstk W C ->
    trap_no_resume w ->

    na_inv cerise_nais Nswitcher switcher_inv -∗
    switcher_static -∗
    (⌜switcher_fault_pc w⌝ ∨ no_handler (top_export_tbl cstk)) -∗
    (|={⊤}=>
       registers_pointsto rmap ∗
       world_interp W C ∗
       interp_cont interp cstk Ws Cs ∗
       na_own cerise_nais ⊤ ∗
       cstack_frag cstk) -∗
    trap_safe w ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I.
  Proof.
    iIntros (Hdisj Hfull_rmap Hframe Hno_resume) "#Hinv_switcher #Hstatic Hcase Hres".
    iApply (trap_safe_unwind with "Hinv_switcher Hstatic"); [done | done |].
    iMod "Hres" as "(Hrmap & Hworld_interp & Hcont & Hna & Hcstk)".
    iModIntro. iFrame "Hrmap Hna Hcstk". iRight.
    iPoseProof (logrel_unwind_cont with "Hinv_switcher Hstatic Hworld_interp Hcont")
      as "HU"; [done | done |].
    iDestruct "Hcase" as "[%Hpc | Hnh]".
    - by iApply (trap_handler_ok_switcher with "HU").
    - by iApply (trap_handler_ok_no_handler with "Hnh HU").
  Qed.

  (** The return-to-switcher entry point is safe to execute: the registers
      are re-filtered, then the return routine runs ([switcher_return_unwind]). *)
  Lemma interp_expr_switcher_return (W : WORLD) (C : CmptName) (Nswitcher : namespace) :
    Nswitcher ## N_trap ->
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static
    ⊢ interp_expr interp (interp_cont interp) W C (WCap true XSRW_ Local b_switcher e_switcher a_switcher_return).
  Proof.
    iIntros (Hdisj) "[#Hinv_switcher #Hstatic] %cstk %Ws %Cs %rmap0
             (Hregs & _ & HPC & Hrmap & Hworld_interp & Hcont_K & Hna & Hcstk & %Hfreq)".
    iPoseProof (switcher_mtcc_vec_safe Nswitcher Hdisj with "[$Hinv_switcher $Hstatic]")
      as "#Htrap".
    iApply (interp_reg_refilter with "Hregs Hrmap Hworld_interp").
    iIntros (rmap) "%Hfull_rmap #Hrmap_interp Hrmap Hworld_interp". clear rmap0.
    cbn in Hfull_rmap.
    getRegValList [ca0;ca1].
    iApply (switcher_return_unwind with
             "[$HPC $Hrmap $Hinv_switcher $Hstatic $Htrap $Hworld_interp $Hcont_K $Hna $Hcstk]");
      [done|done|done|done|].
    iSplit; iApply "Hrmap_interp"; done.
  Qed.

  Lemma interp_switcher_return (W : WORLD) (C : CmptName) (Nswitcher : namespace)
    (mie : InterruptStatus) :
    Nswitcher ## N_trap ->
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static
    ⊢ interp W C (WSentry (ret_kind mie) true XSRW_ Local b_switcher e_switcher a_switcher_return).
  Proof.
    iIntros (Hdisj) "[#Hinv #Hstatic]".
    rewrite interp_unfold /=.
    iSplit; first (iPureIntro; exact switcher_not_heap_range).
    iIntros "!> %regs %W' % %".
    destruct g'; first done.
    iNext ; iApply (interp_expr_switcher_return with "[$Hinv $Hstatic]"); done.
  Qed.


End Switcher_Exception.
