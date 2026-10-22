From iris.proofmode Require Import proofmode.
From griotte Require Import logrel memory_region rules proofmode.
From griotte Require Export switcher_preamble.

(** * Error handlers

    The obligations of a fault that the switcher handles: the force-unwind
    continuation of a fault site, the invocation of a trusted error handler
    (mirrored for upward-growing stacks), and [trap_handler_ok], what a
    trusted fault site gives the trap vector. *)

Section Switcher_error_handler.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** [unwind_cont F cstk R_unwind_stk] is the force-unwind continuation of
      a fault site: the continuation of the unwind branch of
      [switcher_exception_path_spec] (PC at the return routine, [ca0] and
      [ca1] the error values, full registers, [na_own F]). It takes back the
      call-stack fragment, at any error handler count of the topmost frame,
      and [R_unwind_stk], the part of the callee's stack that the fault site
      holds and gives back to the unwind (the [ErrorState] slot for a
      stackful handler, the whole stack for a known callee, [True] when
      nothing is lent). *)
  Definition unwind_cont (F : coPset) (cstk : CSTK) (R_unwind_stk : iProp Σ) : iProp Σ :=
    ∀ (n : Z) (rmap : LReg),
      ⌜∀ r, is_Some (rmap !! r)⌝ -∗
      ⌜rmap !! ca0 = Some (WInt ECOMPARTMENTFAIL : LWord)⌝ -∗
      ⌜rmap !! ca1 = Some (WInt 0 : LWord)⌝ -∗
      PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_return -∗
      registers_pointsto rmap -∗
      cstack_frag (cstack_set_top_count cstk n) -∗
      R_unwind_stk -∗
      na_own cerise_nais F -∗
      WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.

  Lemma unwind_cont_give (F : coPset) (cstk : CSTK) (R_unwind_stk : iProp Σ) :
    R_unwind_stk -∗ unwind_cont F cstk R_unwind_stk -∗ unwind_cont F cstk True.
  Proof.
    iIntros "HS HU" (n rmap Hfull Hca0 Hca1) "HPC Hrmap Hcstk _ Hna".
    iApply ("HU" with "[//] [//] [//] HPC Hrmap Hcstk HS Hna").
  Qed.

  Lemma unwind_cont_weaken (F : coPset) (cstk : CSTK) (R_unwind_stk R_unwind_stk' : iProp Σ) :
    (R_unwind_stk' -∗ R_unwind_stk) -∗
    unwind_cont F cstk R_unwind_stk -∗
    unwind_cont F cstk R_unwind_stk'.
  Proof.
    iIntros "HSS HU" (n rmap Hfull Hca0 Hca1) "HPC Hrmap Hcstk HS Hna".
    iApply ("HU" with "[//] [//] [//] HPC Hrmap Hcstk [HSS HS] Hna"). by iApply "HSS".
  Qed.

  (** [unwind_cont] ignores the count of the topmost frame. *)
  Lemma unwind_cont_set_top_count (F : coPset) (cstk : CSTK) (R_unwind_stk : iProp Σ) (n : Z) :
    unwind_cont F (cstack_set_top_count cstk n) R_unwind_stk ⊣⊢
    unwind_cont F cstk R_unwind_stk.
  Proof.
    rewrite /unwind_cont. iSplit; iIntros "HU" (m).
    - rewrite -(cstack_set_top_count_twice cstk n m). iApply "HU".
    - rewrite cstack_set_top_count_twice. iApply "HU".
  Qed.

  (** ** The handler invocation (mirrored for upward-growing stacks) *)

  (** The sentry the switcher gives a handler in [cra] (link of the [cjalr],
      interrupts enabled), named through the label
      [.Lhandle_error_handler_return]. The switcher code does not yet contain
      this label, which then resolves to offset 0. *)
  Definition handler_return_sentry : LWord :=
    WSentry (ret_kind InterruptEnabled) true XSRW_ Local b_switcher e_switcher
      (a_switcher_call ^+ switcher_label_offset ".Lhandle_error_handler_return")%a.

  (** The handler's PC, as the switcher computes it from the table's PCC
      [wpcc] and the handler offset [off]: the address set to the base, then
      moved by [off]. [None] when the result is not a capability that can be
      addressed there (the [cjalr] then faults). *)
  Definition handler_entry (wpcc : LWord) (off : Z) : option LWord :=
    match wpcc with
    | MkLWord (WCap t p g b e _) π => (λ a, MkLWord (WCap t p g b e a) π) <$> (b + off)%a
    | _ => None
    end.

  (** The registers of the [ErrorState], in the order of the register save
      area (words 1 to 15; word 0 is MEPCC). *)
  Definition error_state_regs : list RegName :=
    [cra; csp; cgp; ctp; ct0; ct1; ct2; cs0; cs1; ca0; ca1; ca2; ca3; ca4; ca5].

  (** The switcher's room test for the [ErrorState] (mirrored: the 16 words
      above the cursor). *)
  Definition error_state_fits (wcsp : LWord) : Prop :=
    match wcsp.(lw) with
    | WCap true _ _ _ e a => (a + 16 <= e)%Z
    | _ => False
    end.

  (** The room test passes and the switcher's stores of the [ErrorState]
      through the faulting [csp] succeed. *)
  Definition error_state_stores_ok (wcsp : LWord) : Prop :=
    match wcsp.(lw) with
    | WCap true p _ b e a => writeAllowed p = true ∧ (b <= a)%a ∧ (a + 16 <= e)%Z
    | _ => False
    end.

  #[global] Instance error_state_stores_ok_dec wcsp : Decision (error_state_stores_ok wcsp).
  Proof. rewrite /error_state_stores_ok. repeat case_match; apply _. Defined.

  Lemma error_state_stores_ok_fits wcsp :
    error_state_stores_ok wcsp → error_state_fits wcsp.
  Proof. rewrite /error_state_stores_ok /error_state_fits. repeat case_match; naive_solver. Qed.

  (** The [ErrorState] the switcher writes for a fault at [w] with the
      registers [rfault], through a [csp] of permission [p]: the untagged
      MEPCC, then each register as stored through [p]. *)
  Definition error_state_words (p : Perm) (w : LWord) (rfault : LReg) : list LWord :=
    lclear_tag (lmepcc_of_pc w) :: ((λ r, lstore_word p (rfault !!! r)) <$> error_state_regs).

  (** The [ErrorState] at the faulting cursor, with the words the switcher
      writes. *)
  Definition error_state_pointsto (w : LWord) (rfault : LReg) : iProp Σ :=
    match (rfault !!! csp).(lw) with
    | WCap _ p _ _ _ a => [[ a , (a ^+ 16)%a ]] ↦ₐ [[ error_state_words p w rfault ]]
    | _ => True
    end.

  (** The [ErrorState] slot at the faulting cursor, any contents. *)
  Definition error_state_area (rfault : LReg) : iProp Σ :=
    match (rfault !!! csp).(lw) with
    | WCap _ _ _ _ _ a => ∃ ws, ⌜length ws = 16⌝ ∗ [[ a , (a ^+ 16)%a ]] ↦ₐ [[ ws ]]
    | _ => True
    end.

  (** What a fault site with a trusted handler lends: the slot, when the
      table declares a stackful handler (offset [eh]) and the switcher's
      stores succeed. *)
  Definition error_state_slot (eh : Z) (rfault : LReg) : iProp Σ :=
    if decide (eh ≠ ExportTable_no_handler ∧ error_state_stores_ok (rfault !!! csp))
    then error_state_area rfault else True%I.

  (** The stackless handler's stack: the invocation's slice of the topmost
      pushed frame's [csp], cursor at its end (mirror of CHERIoT's cursor at
      the base), or the entry frame's [csp] as is. *)
  Definition stackless_csp (cstk : CSTK) : LWord :=
    match cstk.(cstk_frames) with
    | frm :: _ =>
        match frm.(cf_tframe).(tf_csp) with
        | MkLWord (WCap t p g _ e a) π => MkLWord (WCap t p g a e e) π
        | wcsp => wcsp
        end
    | [] => cstk.(cstk_entry).(tf_csp)
    end.

  (** The stackful handler's [csp] and [a0], from the faulting [csp]: the
      cursor above the [ErrorState], and the [ErrorState] capability. *)
  Definition stackful_regs (wcsp : LWord) : option (LWord * LWord) :=
    match wcsp with
    | MkLWord (WCap t p g b e a) π =>
        (λ a16, (MkLWord (WCap t p g b e a16) π, MkLWord (WCap t p g b e a) π)) <$> (a + 16)%a
    | _ => None
    end.

  (** The registers at the handler's first instruction. *)
  Definition handler_invocation_regs (kind : handler_kind) (cstk : CSTK) (wcgp : LWord)
    (rfault : LReg) (mcause mtval : Z) (regs : LReg) : Prop :=
    (∀ r, is_Some (regs !! r)) ∧
    regs !! cra = Some handler_return_sentry ∧
    regs !! cgp = Some wcgp ∧
    match kind with
    | Stackful =>
        error_state_stores_ok (rfault !!! csp) ∧
        ∃ wcsp wa0, stackful_regs (rfault !!! csp) = Some (wcsp, wa0) ∧
          regs !! csp = Some wcsp ∧
          regs !! ca0 = Some wa0 ∧
          regs !! ca1 = Some (lword_of_word (WInt mcause)) ∧
          regs !! ca2 = Some (lword_of_word (WInt mtval))
    | Stackless =>
        regs !! csp = Some (stackless_csp cstk) ∧
        regs !! ca0 = Some (lword_of_word (WInt mcause)) ∧
        regs !! ca1 = Some (lword_of_word (WInt mtval)) ∧
        regs !! ca2 = Some (lword_of_word (WInt 0))
    end ∧
    (∀ r, r ∉ ({[cra; cgp; csp; ca0; ca1; ca2]} : gset RegName) →
          regs !! r = Some (lword_of_word (WInt 0))).

  (** What the handler receives of the slot, and what it gives back to the
      unwind continuation. *)
  Definition handler_slot (kind : handler_kind) (w : LWord) (rfault : LReg) : iProp Σ :=
    match kind with Stackful => error_state_pointsto w rfault | Stackless => True end.
  Definition handler_unwind_res (kind : handler_kind) (rfault : LReg) : iProp Σ :=
    match kind with Stackful => error_state_area rfault | Stackless => True end.

  (** ** Trusted handlers *)

  (** The WP of a trusted handler of kind [kind], at offset [off] of the
      PCC [wpcc] of the table at [b_tbl] (CGP [wcgp]), for its fault
      obligation [P_fault]: for every call stack [cstk] (the faulting one,
      count even), faulting PC [w] and registers [rfault], the handler runs
      safely from the invocation state. It does not mention the trap
      vector. *)
  Definition execute_error_handler (b_tbl : Addr) (wpcc wcgp : LWord) (off : Z)
    (kind : handler_kind) (P_fault : CSTK → LWord → LReg → iProp Σ) : iProp Σ :=
    □ ∀ (cstk : CSTK) (w : LWord) (rfault : LReg) (mcause mtval : Z) (wpc : LWord) (regs : LReg),
      ▷ ( ⌜top_export_tbl cstk = b_tbl⌝ -∗
          ⌜Z.even (top_error_count cstk) = true⌝ -∗
          ⌜mcause_ok mcause⌝ -∗
          ⌜handler_entry wpcc off = Some wpc⌝ -∗
          ⌜handler_invocation_regs kind cstk wcgp rfault mcause mtval regs⌝ -∗
          PC ↦ₚ wpc -∗
          registers_pointsto regs -∗
          P_fault cstk w rfault -∗
          handler_slot kind w rfault -∗
          unwind_cont ⊤ cstk (handler_unwind_res kind rfault) -∗
          cstack_frag (cstack_set_top_count cstk (top_error_count cstk + 1)) -∗
          na_own cerise_nais ⊤ -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ).

  #[global] Instance execute_error_handler_persistent b_tbl wpcc wcgp off kind P_fault :
    Persistent (execute_error_handler b_tbl wpcc wcgp off kind P_fault).
  Proof. rewrite /execute_error_handler. apply _. Qed.

  (** The table at [b_tbl] declares trusted handlers for [P_fault]: its
      header, and the WP of each handler it declares. *)
  Definition trusted_handler (b_tbl : Addr) (P_fault : CSTK → LWord → LReg → iProp Σ)
    : iProp Σ :=
    ∃ (wpcc wcgp : LWord) (eh ehs : Z),
      b_tbl ↦ₐ□ wpcc ∗
      (b_tbl ^+ ExportTable_offset_cgp)%a ↦ₐ□ wcgp ∗
      b_tbl ↦ₕ□{stackful} eh ∗
      b_tbl ↦ₕ□{stackless} ehs ∗
      (⌜eh ≠ ExportTable_no_handler⌝ →
         execute_error_handler b_tbl wpcc wcgp eh Stackful P_fault) ∗
      (⌜ehs ≠ ExportTable_no_handler⌝ →
         execute_error_handler b_tbl wpcc wcgp ehs Stackless P_fault).

  #[global] Instance trusted_handler_persistent b_tbl P_fault :
    Persistent (trusted_handler b_tbl P_fault).
  Proof. rewrite /trusted_handler. apply _. Qed.

  (** ** Faults that the switcher handles *)

  (** A fault at a PC of the switcher. *)
  Definition switcher_fault_pc (w : LWord) : Prop :=
    get_b (lmepcc_of_pc w).(lw) = (b_switcher : Z).

  Lemma switcher_fault_pc_cap (t : bool) (p : Perm) (g : Locality) (e a : Addr) :
    switcher_fault_pc (WCap t p g b_switcher e a).
  Proof. by rewrite /switcher_fault_pc /lmepcc_of_pc /= get_b_mepcc_of_pc. Qed.

  (** A fault at [w] with registers [regs] and call stack [cstk], at a site
      that holds [na_own F], is not resumed and is one of:
      - a fault in the switcher, or in a compartment whose table declares no
        handler;
      - a fault in a trusted compartment whose table declares trusted
        handlers for some [P_fault]: the site proves [P_fault] and lends the
        slot ([F = ⊤]: the handler runs with the whole token);
      - a fault in a running trusted handler (the top count is odd).
      Each case gives the site's unwind continuation. *)
  Definition trap_handler_ok_def (F : coPset) (cstk : CSTK) (w : LWord) (regs : LReg)
    : iProp Σ :=
    ⌜trap_no_resume w⌝ ∗
    ( (unwind_cont F cstk True ∗
       (⌜switcher_fault_pc w⌝ ∨ no_handler (top_export_tbl cstk)))
    ∨ (⌜F = ⊤⌝ ∗
       ∃ (P_fault : CSTK → LWord → LReg → iProp Σ) (eh : Z),
         trusted_handler (top_export_tbl cstk) P_fault ∗
         top_export_tbl cstk ↦ₕ□{stackful} eh ∗
         P_fault cstk w regs ∗
         error_state_slot eh regs ∗
         unwind_cont ⊤ cstk (error_state_slot eh regs))
    ∨ (unwind_cont F cstk True ∗
       ⌜Z.odd (top_error_count cstk) = true⌝) ).
  #[local] Definition trap_handler_ok_aux : seal (@trap_handler_ok_def). Proof. by eexists. Qed.
  Definition trap_handler_ok := trap_handler_ok_aux.(unseal).
  #[local] Definition trap_handler_ok_unseal :
    @trap_handler_ok = @trap_handler_ok_def := trap_handler_ok_aux.(seal_eq).

  (** A fault in the switcher. *)
  Lemma trap_handler_ok_switcher F cstk w regs :
    trap_no_resume w →
    switcher_fault_pc w →
    unwind_cont F cstk True -∗
    trap_handler_ok F cstk w regs.
  Proof.
    rewrite trap_handler_ok_unseal. iIntros (Hno Hpc) "HU".
    iSplit; first done. iLeft. iFrame. by iLeft.
  Qed.

  (** A fault in a compartment whose table declares no handler. *)
  Lemma trap_handler_ok_no_handler F cstk w regs :
    trap_no_resume w →
    no_handler (top_export_tbl cstk) -∗
    unwind_cont F cstk True -∗
    trap_handler_ok F cstk w regs.
  Proof.
    rewrite trap_handler_ok_unseal. iIntros (Hno) "Hnh HU".
    iSplit; first done. iLeft. iFrame.
  Qed.

  (** A fault in a trusted compartment with trusted handlers. *)
  Lemma trap_handler_ok_handler cstk w regs
    (P_fault : CSTK → LWord → LReg → iProp Σ) (eh : Z) :
    trap_no_resume w →
    trusted_handler (top_export_tbl cstk) P_fault -∗
    top_export_tbl cstk ↦ₕ□{stackful} eh -∗
    P_fault cstk w regs -∗
    error_state_slot eh regs -∗
    unwind_cont ⊤ cstk (error_state_slot eh regs) -∗
    trap_handler_ok ⊤ cstk w regs.
  Proof.
    rewrite trap_handler_ok_unseal. iIntros (Hno) "Hh Heh HP Hslot HU".
    iSplit; first done. iRight; iLeft. iSplit; first done.
    iExists P_fault, eh. iFrame "Hh Heh HP Hslot HU".
  Qed.

  (** A fault in a running trusted handler. *)
  Lemma trap_handler_ok_running F cstk w regs :
    trap_no_resume w →
    Z.odd (top_error_count cstk) = true →
    unwind_cont F cstk True -∗
    trap_handler_ok F cstk w regs.
  Proof.
    rewrite trap_handler_ok_unseal. iIntros (Hno Hodd) "HU".
    iSplit; first done. iRight; iRight. by iFrame.
  Qed.

  (** Every case unwinds: the fault is not resumed, and the site gave its
      unwind continuation and the resources that it takes back. This is all
      the trap vector uses while the switcher force-unwinds every fault. *)
  Lemma trap_handler_ok_unwind F cstk w regs :
    trap_handler_ok F cstk w regs -∗
    ⌜trap_no_resume w⌝ ∗
    ∃ R_unwind_stk : iProp Σ, R_unwind_stk ∗ unwind_cont F cstk R_unwind_stk.
  Proof.
    rewrite trap_handler_ok_unseal.
    iIntros "[%Hno [[HU _] | [[-> (%P_fault & %eh & _ & _ & _ & Hslot & HU)] | [HU _]]]]";
      iSplit; try done.
    - iExists True%I. by iFrame.
    - iExists _. iFrame.
    - iExists True%I. by iFrame.
  Qed.

End Switcher_error_handler.
