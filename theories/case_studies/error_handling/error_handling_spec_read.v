From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode map_simpl register_tactics.
From griotte Require Import switcher_base switcher_base_ktk.
From griotte Require Import rules_trap_cause.
From griotte Require Import
  error_handling_spec_states error_handling_spec_read_blocks error_handling_spec_handler_blocks
  error_handling_spec_handler.

(** * The entry [stats_read] for a known caller

    [stats_read] opens [stats_inv] at its entry, with [na_own ⊤], and keeps
    it open for the whole call. At the load of [.Lread_load], it holds the
    lock and [na_own (⊤ ∖ ↑Nstats)]:
    - when the load succeeds, the release closes the invariant, and the
      callee returns the loaded word;
    - when it faults, the fault site ([stats_read_fault_safe]) gives the
      trap the handler of [stats] with [stats_P_fault], at the exact cause
      and value of the fault ([stats_read_load_fault_spec]). The switcher
      invokes the handler ([handler_runs]): the count is even and below the
      limit, the callee's stack has room for the [ErrorState], and the
      cell of the frame's table holds the table. The handler retries a
      load out of the bounds of a capability with non-empty bounds and a
      base outside the [ErrorState] slot, at that base, and unwinds any
      other fault.

    The specification for a known caller
    ([stats_read_spec_known_to_known]): a tagged capability without
    identifier, with non-empty bounds, returns the word at its address, or
    at its base when its address is out of bounds (the retried load, at
    count 2); an untagged capability unwinds the callee, which may fault
    ([may_fault = true]), with [stats_inv] closed. *)

Section Error_Handling_Read.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
    {statslayout : statsLayout} {statslayoutwf : statsLayoutWf}
  .

  (** The static resources of [stats]: its code, the header of its export
      table (a stackful handler, no stackless one) and the entry of
      [stats_read]. *)
  Definition stats_static : iProp Σ :=
    ("#Hcode_stats" ∷ codefrag_pers STATS_pcc_b stats_code ∗
     "#Htbl_pcc" ∷ b_stats_exp_tbl ↦ₐ□ stats_wpcc ∗
     "#Htbl_cgp" ∷ (b_stats_exp_tbl ^+ ExportTable_offset_cgp)%a ↦ₐ□ stats_wcgp ∗
     "#Htbl_eh" ∷ b_stats_exp_tbl ↦ₕ□{stackful} stats_handler_pcc_off ∗
     "#Htbl_ehs" ∷ b_stats_exp_tbl ↦ₕ□{stackless} ExportTable_no_handler ∗
     "#Htbl_read" ∷ stats_read_exp_tbl_addr ↦ₐ□ lword_of_word stats_exp_tbl_entry_read)%I.

  #[global] Instance stats_static_persistent : Persistent stats_static.
  Proof. rewrite /stats_static. apply _. Qed.

  (** The table of [stats] declares trusted handlers for [stats_P_fault]. *)
  Lemma stats_trusted_handler :
    stats_static ⊢ trusted_handler b_stats_exp_tbl stats_P_fault.
  Proof.
    iIntros "Hstatic". iNamed "Hstatic".
    iExists stats_wpcc, stats_wcgp, (Z.of_nat stats_handler_pcc_off), ExportTable_no_handler.
    iFrame "Htbl_pcc Htbl_cgp Htbl_eh Htbl_ehs". iSplit.
    - iIntros (_). iApply (stats_handler_execute with "Hcode_stats Htbl_pcc").
    - by iIntros (Hne).
  Qed.

  (** The switcher invokes the handler of [stats] for a fault at the load,
      with a stack that has room for the [ErrorState], at an even count
      below the limit. *)
  Lemma stats_read_handler_runs (cstk : CSTK) (rfault : LReg) (g : Locality) (b e a : Addr) :
    STATS_pcc_b ≠ b_switcher →
    rfault !!! csp = lword_of_word (WCap true RWL g b e a) →
    (b + ErrorState_size <= a)%Z → (a <= e)%a →
    Z.even (top_error_count cstk) = true →
    (top_error_count cstk + 1 <= MAX_FAULTS_PER_COMPARTMENT_CALL)%Z →
    (top_tframe cstk).(tf_export_tbl) ≠ lword_of_word (WInt 0) →
    stackful_handler_runs cstk (stats_pcc stats_load_addr) rfault
      stats_handler_pcc_off stats_wpcc.
  Proof.
    intros Hswitcher Hcsp Hba Hae Heven Hmax Htbl.
    pose proof STATS_size_imports as Hsize_imports.
    pose proof STATS_size_code as Hsize_code.
    rewrite /stackful_handler_runs Hcsp.
    split_and!; try done.
    - rewrite /switcher_fault_pc /lmepcc_of_pc /= get_b_mepcc_of_pc /=.
      intros Hb. apply Hswitcher. solve_addr.
    - (* [csp] has authority: its range is not empty *)
      rewrite /tag_strippable /=. intros [_ [ [? ?] | [Hauth [x Hx] ] ] ]; first done.
      apply Hauth. split; first done. exists x. rewrite /heap_authority_base decide_True //.
      rewrite /ErrorState_size in Hba. solve_addr.
    - rewrite (handler_word_entry _ _
                 (lword_of_word (WCap true RX Global STATS_pcc_b STATS_pcc_e
                                   (STATS_pcc_b ^+ stats_handler_pcc_off)%a))).
      { done. }
      rewrite /handler_entry /stats_wpcc /stats_pcc /=.
      rewrite (_ : (STATS_pcc_b + stats_handler_pcc_off)%a =
                   Some (STATS_pcc_b ^+ stats_handler_pcc_off)%a); first done.
      rewrite /stats_handler_pcc_off. cbn in Hsize_code |- *. solve_addr.
  Qed.

  (** The continuations that a fault site gives the handler, at mcause [c]
      and mtval [v]: the retry and the unwind. *)
  Definition stats_fault_conts (cstk : CSTK) (rfault : LReg) (c v : Z) : iProp Σ :=
    (⌜stats_retries c v rfault⌝ -∗ stats_retry_cont (⊤ ∖ ↑Nstats) cstk rfault v) ∧
    (⌜¬ stats_retries c v rfault⌝ -∗
     unwind_cont (⊤ ∖ ↑Nstats) cstk (error_state_area rfault ∗ stats_inv)).

  (** The fault site of [stats]: a fault at the load, with mcause in
      [P_mcause] and mtval in [P_mtval], with the lock held,
      [na_own (⊤ ∖ ↑Nstats)], and a stack with room for the [ErrorState],
      outside the shadow table, at an even count below the limit. The site
      lends the slot of the [ErrorState], and gives the handler
      [stats_P_fault]: the lock, the saved capability of a repairable
      fault, and its continuations. The switcher invokes the handler, so
      the site gives the switcher no unwind continuation. *)
  Lemma stats_read_fault_safe (P_mcause P_mtval : Z → Prop) (cstk : CSTK) (rfault : LReg)
    (g : Locality) (b e a : Addr) :
    (∀ c, P_mcause c → mcause_ok c) →
    STATS_pcc_b ≠ b_switcher →
    (∀ r, is_Some (rfault !! r)) →
    rfault !!! csp = lword_of_word (WCap true RWL g b e a) →
    rfault !!! cgp = stats_wcgp →
    jalr_target_ok cnull cra (rfault !!! cra).(lw) = true →
    (b + ErrorState_size <= a)%Z → (a <= e)%a →
    disjoint_from_shadow (a ^+ (- ErrorState_size))%a a →
    top_export_tbl cstk = b_stats_exp_tbl →
    Z.even (top_error_count cstk) = true →
    (top_error_count cstk + 1 <= MAX_FAULTS_PER_COMPARTMENT_CALL)%Z →
    (top_tframe cstk).(tf_export_tbl) ≠ lword_of_word (WInt 0) →
    (∀ c v, P_mcause c → P_mtval v → stats_repairable c v →
       ∃ r p g b e a π, stats_saved_cap rfault v r p g b e a π) →
    na_inv (tpool th) Nswitcher switcher_inv -∗
    switcher_static -∗
    stats_static -∗
    registers_pointsto rfault -∗
    cstack_frag cstk -∗
    na_own (tpool th) (⊤ ∖ ↑Nstats) -∗
    STATS_cgp_b ↦ₐ WInt 1 -∗
    error_state_area rfault -∗
    (∀ c v, ⌜P_mcause c⌝ -∗ ⌜P_mtval v⌝ -∗ ▷ stats_fault_conts cstk rfault c v) -∗
    trap_safe_cause P_mcause P_mtval (stats_pcc stats_load_addr) ⊤
      (HO th).
  Proof.
    iIntros (HP_mcause Hswitcher Hfull Hcsp Hcgp Hcra Hba Hae Hshadow
               Htbl Heven Hmax Htbl_set Hsaved)
      "#Hinv_switcher #Hswitcher_static #Hstatic Hregs Hcstk Hna Hlock Harea Hcont".
    pose proof Nswitcher_Nstats as Hdisj_stats.
    iApply (trap_safe_exception_entry P_mcause P_mtval (⊤ ∖ ↑Nstats)
              with "Hinv_switcher Hswitcher_static");
      [done | solve_ndisj | rewrite /Ntrap /Nstats; solve_ndisj |].
    iModIntro. iExists rfault, cstk. iFrame "Hna Hregs Hcstk". iSplit; first done.
    iDestruct (stats_trusted_handler with "Hstatic") as "#Hhandler".
    iPoseProof "Hstatic" as "Hstatic'". iNamed "Hstatic'".
    rewrite -Htbl.
    assert (error_state_stores_ok (rfault !!! csp)) as Hstores.
    { by rewrite /error_state_stores_ok Hcsp /=. }
    iApply (trap_handler_ok_handler _ _ _ _ _ _ stats_P_fault stats_handler_pcc_off
             with "Hhandler Htbl_eh [Harea] [-]").
    { rewrite /trap_no_resume /lmepcc_of_pc /= get_b_mepcc_of_pc /=.
      left. intros Hb. apply Hswitcher. solve_addr. }
    { exact Htbl_set. }
    { rewrite /error_state_slot decide_True; last first.
      { split; first (rewrite /ExportTable_no_handler /stats_handler_pcc_off; lia).
        by apply error_state_stores_ok_first. }
      iDestruct (error_state_area_lent with "Harea") as "$"; first done.
      iSplit; first by rewrite Hcsp.
      iPureIntro. rewrite /error_state_lent_shadow_free.
      destruct (error_state_lent_e_stores_ok (rfault !!! csp) RWL g b e a)
        as [_ ->]; [by rewrite Hcsp | done |].
      by rewrite Hcsp /=. }
    iSplit.
    - (* The switcher invokes the handler: no unwind *)
      iLeft. iExists stats_handler_pcc_off, stats_wpcc. iFrame "Htbl_eh Htbl_pcc".
      iPureIntro. by eapply stats_read_handler_runs.
    - iIntros (mcause mtval Hc Hv). rewrite /stats_P_fault. iFrame "Hlock".
      iSplit.
      { iPureIntro. rewrite /stats_fault_facts. split_and!; try done. by exists g, b, e, a. }
      iSplit; first done.
      iSplit; first (iPureIntro; by apply Hsaved).
      by iApply "Hcont".
  Qed.

  (** ** The fault of the load *)

  (** The instruction of the load. *)
  Definition stats_load_instr : LWord := lword_of_word (encodeInstrW (CLoad ca0 ca0 0)).

  Lemma stats_load_instr_pers :
    codefrag_pers STATS_pcc_b stats_code -∗ stats_load_addr ↦ₐ□ stats_load_instr.
  Proof.
    iIntros "Hcode_stats". rewrite /stats_load_addr.
    by iApply (codefrag_lookup_pers _ _ 3 with "Hcode_stats").
  Qed.

  (** The PC of the load is a correct PC. *)
  Lemma stats_load_pc_correct : isCorrectPCb (stats_pcc stats_load_addr).(lw) = true.
  Proof.
    pose proof STATS_size_imports as Hsize_imports.
    pose proof STATS_size_code as Hsize_code.
    apply isCorrectPCb_isCorrectPC. constructor; last done.
    rewrite /stats_load_addr. cbn in Hsize_code |- *. solve_addr.
  Qed.

  (** The fault of the load from the logical view: the fault of the checks
      of the capability [wptr] in [ca0], when they fail. *)
  Lemma stats_load_lfault (wptr : LWord) (lm : LMem) (f : fault) :
    lm !! stats_load_addr = Some stats_load_instr →
    data_cap_check readAllowed PermitLoadViolation ca0 wptr.(lw) 0 = inl f →
    lfault (stats_pcc stats_load_addr) {[ca0 := wptr]} lm = f.
  Proof.
    intros Hinstr Hcheck. pose proof stats_load_pc_correct as Hpc.
    rewrite /lfault /lview /trap_fault /=. rewrite /= in Hpc. rewrite Hpc.
    rewrite lookup_fmap Hinstr /= ?decode_encode_instrW_inv ?decode_encode_instr_inv
      /instr_fault /load_fault.
    by rewrite lookup_reg_not_cnull // /= lookup_fmap lookup_insert_eq /= Hcheck.
  Qed.

  (** The faults that the logical view allows at the load: its logical
      fault, or a tag violation on [ca0] when [wptr] may be stripped. *)
  Lemma stats_load_fault_ok (wptr : LWord) (lm : LMem) (f : fault) :
    lm !! stats_load_addr = Some stats_load_instr →
    fault_ok (stats_pcc stats_load_addr) {[ca0 := wptr]} lm f →
    f = lfault (stats_pcc stats_load_addr) {[ca0 := wptr]} lm ∨
    (may_strip wptr ∧ f = FaultCheri TagViolation (CheriGPR ca0)).
  Proof.
    intros Hinstr [-> | (wi & r & v & Hwi & Hauth & _ & Hr & Hstrip & ->)]; first by left.
    right. pose proof stats_load_pc_correct as Hpc.
    rewrite /instr_at /stats_pcc /= in Hwi Hpc. rewrite Hpc Hinstr in Hwi.
    injection Hwi as <-.
    rewrite /stats_load_instr /= ?decode_encode_instrW_inv ?decode_encode_instr_inv in Hauth.
    injection Hauth as <-. rewrite lookup_insert_eq in Hr. by injection Hr as <-.
  Qed.

  (** The cause and the value of a fault of the load whose logical fault
      is [f], through the capability [wptr]. *)
  Definition stats_load_mcause (f : fault) (c : Z) : Prop :=
    mcause_ok c ∧ c = fault_mcause f.
  Definition stats_load_mtval (wptr : LWord) (f : fault) (v : Z) : Prop :=
    v = fault_mtval f ∨
    (may_strip wptr ∧ v = fault_mtval (FaultCheri TagViolation (CheriGPR ca0))).

  (** A fault of the load, with the memory [lm] that gives its logical
      fault [f]: the trap with the exact cause and value. *)
  Lemma stats_load_trap E Φ (wptr : LWord) (lm : LMem) (f : fault) dq :
    lm !! stats_load_addr = Some stats_load_instr →
    lfault (stats_pcc stats_load_addr) {[ca0 := wptr]} lm = f →
    fault_is_access f = false →
    PC ↦ₚ[th] stats_pcc stats_load_addr -∗
    ca0 ↦ᵣ[th] wptr -∗
    ([∗ map] a ↦ x ∈ lm, a ↦ₐ{dq} x) -∗
    (ca0 ↦ᵣ[th] wptr -∗
     ([∗ map] a ↦ x ∈ lm, a ↦ₐ{dq} x) -∗
     trap_safe_cause (stats_load_mcause f) (stats_load_mtval wptr f)
       (stats_pcc stats_load_addr) E Φ) -∗
    WP Seq (Instr Faulted) @[th] E {{ Φ }}.
  Proof.
    iIntros (Hinstr Hf Hnaccess) "HPC Hca0 Hlm Hcont".
    iDestruct (big_sepM_singleton (λ r w, r ↦ᵣ w)%I ca0 wptr with "Hca0") as "Hregs".
    iTrap cause with "Hregs" "Hlm".
    { split; last by rewrite Hf.
      intros p g b e a wi Hpc Hwi. rewrite /stats_pcc /= in Hpc.
      injection Hpc as <- <- <- <- <-.
      rewrite Hinstr in Hwi. injection Hwi as <-.
      rewrite /stats_load_instr /= ?decode_encode_instrW_inv ?decode_encode_instr_inv /=
        dom_singleton_L.
      set_solver. }
    iDestruct (big_sepM_singleton (λ r w, r ↦ᵣ w)%I ca0 wptr with "Hregs") as "Hca0".
    iApply (trap_safe_cause_mono with "(Hcont Hca0 Hlm)").
    - intros c [Hok ->]. split; first done. by rewrite lcause_lfault Hf.
    - intros v (f' & Hok & ->). rewrite /stats_load_mtval.
      destruct (stats_load_fault_ok wptr lm f' Hinstr Hok) as [-> | [Hstrip ->] ];
        [left; by rewrite Hf | by right].
  Qed.

  (** The load through a capability whose checks fail faults, with the
      exact cause and value. *)
  Lemma stats_read_load_fault_spec (wptr : LWord) (f : fault) :
    data_cap_check readAllowed PermitLoadViolation ca0 wptr.(lw) 0 = inl f →
    PC ↦ₚ[th] stats_pcc stats_load_addr ∗
    ca0 ↦ᵣ[th] wptr ∗
    codefrag_pers STATS_pcc_b stats_code ∗
    (ca0 ↦ᵣ[th] wptr -∗
     trap_safe_cause (stats_load_mcause f) (stats_load_mtval wptr f)
       (stats_pcc stats_load_addr) ⊤ (HO th))
    ⊢ WP Seq (Instr Executable) @[th] {{ HO th }}.
  Proof.
    iIntros (Hcheck) "(HPC & Hca0 & #Hcode_stats & Hfailed)".
    iDestruct (stats_load_instr_pers with "Hcode_stats") as "#Hinstr".
    pose proof stats_code_bounds_layout as (HsubBounds & Hpc_shadow & Hpc_nonheap).
    iDestruct (codefrag_contiguous_region_pers with "Hcode_stats") as %Hpc_contiguous;
    cbn [length map encodeInstrsW] in Hpc_contiguous.
    stats_unfold_code.
    rewrite /stats_pcc /stats_load_addr.
    (* Block 2: the load *)
    focus_block (stats_block ".Lread_load") "Hcode_stats" of stats_blocks at STATS_pcc_b
      as a_load Ha_load "Hcode" "Hcont".
    (* CLoad ca0 ca0 0 *)
    iInstr_fail "Hcode".
    { (* The checks of the capability fail *)
      intros reg sreg mem st s1 Hr. apply exec_opt_exec_none. cbn. rewrite /lookup_reg Hr /=.
      destruct (decide (ca0 = cnull)) as [Hcnull | _]; first done.
      destruct wptr as [w π]. cbn in Hcheck |- *. destruct s1; cbn [and_tag].
      - destruct w as [z | [ [] p g b e a | t p g b e a ] | k t p g b e a | ot sb ];
          cbn; try done.
        cbn in Hcheck. destruct (a + 0)%a as [ea|]; cbn; last done.
        destruct (readAllowed p); cbn in Hcheck |- *; last done.
        by destruct (withinBounds b e ea).
      - by destruct w as [z | [ [] p g b e a | t p g b e a ] | k t p g b e a | ot [ [] | [] ] ]. }
    (* The trap, with the cell of the instruction *)
    iDestruct (big_sepM_singleton (λ a w, a ↦ₐ□ w)%I a_load stats_load_instr with "Hinstr")
      as "Hlm".
    assert (a_load = stats_load_addr) as Ha_load_eq
      by (rewrite /stats_load_addr; offsets_compute; solve_addr).
    rewrite Ha_load_eq.
    iApply (stats_load_trap _ _ wptr {[stats_load_addr := stats_load_instr]} f
             with "HPC Hca0 Hlm"); [by simplify_map_eq | | |].
    { apply stats_load_lfault; [by simplify_map_eq | done]. }
    { revert Hcheck. rewrite /data_cap_check.
      destruct (lw wptr) as [| [ [] | [] ] | ? [] | ? [ [] | [] ] ]; cbn; try (intros [=<-]; done).
      all: repeat case_match; intros [=<-]; done. }
    iIntros "Hca0 _". iApply ("Hfailed" with "Hca0").
  Qed.

  (** ** The body of [stats_read] *)

  (** The entry: open [stats_inv], test the lock and take it, up to the
      load. *)
  Lemma stats_read_take_open (rmap : LReg) :
    (∀ r, is_Some (rmap !! r)) →
    rmap !! cgp = Some stats_wcgp →
    na_inv (tpool th) Nstats stats_inv -∗
    stats_static -∗
    PC ↦ₚ[th] stats_pcc (STATS_pcc_b ^+ stats_read_pcc_off)%a -∗
    registers_pointsto rmap -∗
    na_own (tpool th) ⊤ -∗
    ▷ (PC ↦ₚ[th] stats_pcc stats_load_addr -∗
       registers_pointsto (<[ct0 := lword_of_word (WInt 0)]> rmap) -∗
       STATS_cgp_b ↦ₐ WInt 1 -∗
       na_own (tpool th) (⊤ ∖ ↑Nstats) -∗
       (▷ stats_inv ∗ na_own (tpool th) (⊤ ∖ ↑Nstats) ={⊤}=∗ na_own (tpool th) ⊤) -∗
       WP Seq (Instr Executable) @[th] {{ HO th }}) -∗
    WP Seq (Instr Executable) @[th] {{ HO th }}.
  Proof.
    iIntros (Hfull Hcgp) "#Hinv_stats #Hstatic HPC Hregs Hna Hcont".
    iNamed "Hstatic".
    iMod (na_inv_acc with "Hinv_stats Hna") as "(>Hlock & Hna & Hclose)"; [done | done |].
    destruct (Hfull ct0) as [wct0 Hct0].
    iDestruct (registers_pointsto_extract2 _ cgp ct0 with "Hregs") as "(Hcgp & Hct0 & Hregs)";
      [done | done | done |].
    pose proof STATS_size_data as Hsize_data.
    pose proof STATS_cgp_disjoint_from_shadow as Hcgp_shadow.
    (* CLoad ct0 cgp 0; Jne .Lread_busy ct0 0; Store cgp 1 0 *)
    iApply (stats_read_take_spec STATS_pcc_b STATS_pcc_e STATS_cgp_b STATS_cgp_e
              with "[- $HPC $Hcgp $Hct0 $Hlock $Hcode_stats]").
    { apply stats_code_bounds_layout. }
    { cbn in Hsize_data. solve_addr. }
    { eapply disjoint_from_shadow_not_in; first exact Hcgp_shadow.
      apply withinBounds_true_iff. cbn in Hsize_data. solve_addr. }
    iNext. iIntros "(HPC & Hcgp & Hct0 & Hlock & _)".
    iDestruct ("Hregs" with "Hcgp Hct0") as "Hregs".
    rewrite insert_insert_ne // (insert_id rmap cgp) //.
    iApply ("Hcont" with "HPC Hregs Hlock Hna Hclose").
  Qed.

  (** The release, the closing of [stats_inv], and the return to [cra]. *)
  Lemma stats_read_release_close (rmap : LReg) (wlock : LWord) :
    (∀ r, is_Some (rmap !! r)) →
    rmap !! cgp = Some stats_wcgp →
    jalr_target_ok cnull cra (rmap !!! cra).(lw) = true →
    stats_static -∗
    PC ↦ₚ[th] stats_pcc stats_release_addr -∗
    registers_pointsto rmap -∗
    STATS_cgp_b ↦ₐ wlock -∗
    na_own (tpool th) (⊤ ∖ ↑Nstats) -∗
    (▷ stats_inv ∗ na_own (tpool th) (⊤ ∖ ↑Nstats) ={⊤}=∗ na_own (tpool th) ⊤) -∗
    ▷ (PC ↦ₚ[th] lupdatePcPerm (rmap !!! cra) -∗
       registers_pointsto (<[ca1 := lword_of_word (WInt 0)]> rmap) -∗
       na_own (tpool th) ⊤ -∗
       WP Seq (Instr Executable) @[th] {{ HO th }}) -∗
    WP Seq (Instr Executable) @[th] {{ HO th }}.
  Proof.
    iIntros (Hfull Hcgp Hcra) "#Hstatic HPC Hregs Hlock Hna Hclose Hcont".
    iNamed "Hstatic".
    destruct (Hfull ca1) as [wca1 Hca1].
    iDestruct (registers_pointsto_extract3 _ cgp ca1 cra with "Hregs") as "(Hcgp & Hca1 & Hcra & Hregs)";
      [done | done | done | done | done | apply lookup_lookup_total, Hfull |].
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
    iMod ("Hclose" with "[$Hlock $Hna]") as "Hna".
    iDestruct ("Hregs" with "Hcgp Hca1 Hcra") as "Hregs".
    rewrite (insert_id rmap cra); last by apply lookup_lookup_total, Hfull.
    rewrite insert_insert_ne // (insert_id rmap cgp) //.
    iApply ("Hcont" with "HPC Hregs Hna").
  Qed.

  (** ** The specification for a known caller *)

  (** The address that the load reads: the address of the capability when
      it is in its bounds, otherwise its base, where the handler moves
      it. *)
  Definition stats_read_addr (b e a : Addr) : Addr :=
    if withinBounds b e a then a else b.

  (** The callee faults, and is unwound, for an untagged pointer. *)
  Definition stats_may_fault (wptr : LWord) : bool := negb (get_tag wptr.(lw)).

  (** What the caller lends for the pointer [wptr] it passes: for a tagged
      capability without identifier, outside the heap, that allows loads
      and has non-empty bounds, the cell that the load reads (the load
      reads it, so the caller cannot keep it); for an untagged capability,
      nothing (the load faults, and the callee is unwound). *)
  Definition stats_arg_pre (wptr v : LWord) : iProp Σ :=
    match wptr with
    | MkLWord (WCap true p _ b e a) None =>
        ⌜readAllowed p = true ∧ (b < e)%a ∧ is_heap_address b = false ∧
         is_shadow_address (stats_read_addr b e a) = false ∧ is_heap_cap v.(lw) = false⌝ ∗
        stats_read_addr b e a ↦ₐ v
    | MkLWord (WCap false _ _ _ _ _) _ => True
    | _ => False
    end%I.

  (** What the caller gets back, with the result [wca0]: the cell and the
      loaded word, or [ECOMPARTMENTFAIL] for an untagged capability. *)
  Definition stats_arg_post (wptr v wca0 : LWord) : iProp Σ :=
    match wptr with
    | MkLWord (WCap true p _ b e a) None =>
        ⌜wca0 = lload_word p v⌝ ∗ stats_read_addr b e a ↦ₐ v
    | MkLWord (WCap false _ _ _ _ _) _ => ⌜wca0 = WInt ECOMPARTMENTFAIL⌝
    | _ => False
    end%I.

  (** The pointer of [stats_arg_pre] is a capability. *)
  Lemma stats_arg_pre_cap (wptr v : LWord) :
    stats_arg_pre wptr v ⊢
    ⌜∃ t p g b e a π, wptr = MkLWord (WCap t p g b e a) π⌝ ∗ stats_arg_pre wptr v.
  Proof.
    iIntros "HP".
    destruct wptr as [ [z | [ [] p g b e a | ] | | ] π]; try (by iDestruct "HP" as "[]");
      iFrame "HP"; iPureIntro; by eexists _, _, _, _, _, _, _.
  Qed.

  (** A tagged capability without identifier, outside the heap, cannot be
      stripped; nor can an untagged one. *)
  Lemma stats_not_may_strip (t : bool) (p : Perm) (g : Locality) (b e a : Addr)
    (π : option AId) :
    (t = false ∨ (π = None ∧ is_heap_address b = false)) →
    ¬ may_strip (MkLWord (WCap t p g b e a) π).
  Proof.
    intros Ht [Htag Hsome]. destruct Ht as [-> | [-> Hb] ]; first done.
    destruct Hsome as [ [? ?] | [? Hbase] ]; first done.
    by rewrite /heap_cap_base /memory_cap_base /= Hb in Hbase.
  Qed.

  Lemma reg_index_ca0 : reg_index ca0 = TrustedStack_offset_ca0.
  Proof. reflexivity. Qed.

  (** [stats_read] for a known caller, with the pointer [wptr] in [ca0]:
      it returns the word at [stats_read_addr] and 0 in [ca1] for a tagged
      capability (when its address is out of bounds, the handler retries
      the load at the base, and the callee returns at count 2), and it is
      unwound for an untagged capability ([may_fault = true]). The caller
      runs with [na_own ⊤] ([stats_read] opens [stats_inv]), and the
      callee's stack is outside the shadow table (the switcher stores the
      [ErrorState] there). The base of the pointer is outside the
      [ErrorState] slot of the callee: the caller lends its cell, and the
      callee holds the slot. *)
  Lemma stats_read_spec_known_to_known
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : LWord)
    (b_stk e_stk a_stk : Addr)
    (arg_rmap : LReg) (cstk : CSTK)
    (wptr v : LWord) :
    STATS_pcc_b ≠ b_switcher →
    disjoint_from_shadow (stk_callee_b b_stk a_stk) (stk_callee_e e_stk a_stk) →
    arg_rmap !! ca0 = Some wptr →
    na_inv (tpool th) Nswitcher switcher_inv ∗
    switcher_static ∗
    stats_static ∗
    na_inv (tpool th) Nstats stats_inv
    ⊢
    switcher_cc_specification_known_to_known_function (stats_may_fault wptr)
      (stats_arg_pre wptr v)
      (λ wca0 wca1, ⌜wca1 = WInt 0⌝ ∗ stats_arg_post wptr v wca0)
      wcgp_caller wcra_caller wcs0_caller wcs1_caller
      b_stk e_stk a_stk arg_rmap cstk stats_read_nargs stats_read_min_stack ⊤
      STATS_pcc_b STATS_pcc_e STATS_cgp_b STATS_cgp_e stats_read_pcc_off
      (WCap true RO Global b_stats_exp_tbl e_stats_exp_tbl stats_read_exp_tbl_addr).
  Proof.
    iIntros (Hswitcher Hstk_shadow Hwptr)
      "(#Hinv_switcher & #Hswitcher_static & #Hstatic & #Hinv_stats)".
    rewrite /switcher_cc_specification_known_to_known_function.
    iIntros (mie arg_rmap' rmap')
      "(%Hminstk & %Harg_rmap' & %Hrmap' & Hna & HPC & Hcgp & Hcra & Hcsp
       & Hargs & Hrmap & Hstk & Hcstk & HP & Hret)".
    set (frm := {| cf_tframe := _ ; cf_saved := _ ; ccrel := Known_to_Known |}).
    set (wret := WSentry (ret_kind mie) true XSRW_ Local b_switcher e_switcher a_switcher_return).
    rewrite /stats_read_min_stack in Hminstk.

    (* The registers, as one full map *)
    iDestruct (big_sepM_sep with "Hargs") as "[Hargs Hargs_facts]".
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    assert (is_Some (arg_rmap' !! ca0)) as [w0 Hw0].
    { apply elem_of_dom. rewrite Harg_rmap'. set_solver+. }
    iDestruct (big_sepM_lookup with "Hargs_facts") as "Hw0"; first exact Hw0.
    destruct (decide (ca0 ∈ dom_arg_rmap stats_read_nargs)) as [_ | Hnot];
      last (exfalso; apply Hnot; cbn; set_solver+).
    iDestruct "Hw0" as %Hw0'.
    rewrite Hwptr in Hw0'. injection Hw0' as <-.
    assert (arg_rmap' ##ₘ rmap') as Hdisj_args.
    { apply map_disjoint_dom. rewrite Harg_rmap' Hrmap'. set_solver+. }
    iDestruct (big_sepM_union with "[$Hargs $Hrmap]") as "Hregs"; first exact Hdisj_args.
    assert (dom (arg_rmap' ∪ rmap') = all_registers_s ∖ {[cgp; cra; csp]}) as Hdom_args.
    { rewrite dom_union_L Harg_rmap' Hrmap'.
      pose proof (all_registers_s_correct ca0). pose proof (all_registers_s_correct ca1).
      pose proof (all_registers_s_correct ca2). pose proof (all_registers_s_correct ca3).
      pose proof (all_registers_s_correct ca4). pose proof (all_registers_s_correct ca5).
      pose proof (all_registers_s_correct ct0).
      rewrite /dom_arg_rmap /=. set_solver. }
    iDestruct (big_sepM_insert _ _ csp with "[$Hregs $Hcsp]") as "Hregs".
    { apply not_elem_of_dom. rewrite Hdom_args. set_solver+. }
    iDestruct (big_sepM_insert _ _ cra with "[$Hregs $Hcra]") as "Hregs".
    { rewrite lookup_insert_ne //. apply not_elem_of_dom. rewrite Hdom_args. set_solver+. }
    iDestruct (big_sepM_insert _ _ cgp with "[$Hregs $Hcgp]") as "Hregs".
    { rewrite !lookup_insert_ne //. apply not_elem_of_dom. rewrite Hdom_args. set_solver+. }
    set (rfull := <[cgp:=_]> (<[cra:=_]> (<[csp:=_]> (arg_rmap' ∪ rmap')))).
    assert (∀ r, is_Some (rfull !! r)) as Hfull.
    { intros r. apply elem_of_dom. rewrite /rfull !dom_insert_L Hdom_args.
      pose proof (all_registers_s_correct r).
      destruct (decide (r ∈ ({[cgp; cra; csp]} : gset RegName))); set_solver. }

    (* Open [stats_inv], take the lock *)
    iApply (stats_read_take_open rfull with "Hinv_stats Hstatic HPC Hregs Hna");
      [done | by rewrite /rfull lookup_insert_eq |].
    iNext. iIntros "HPC Hregs Hlock Hna Hclose".
    set (rtake := <[ct0:=lword_of_word (WInt 0)]> rfull).
    assert (∀ r, is_Some (rtake !! r)) as Hfull_take.
    { intros r. rewrite /rtake lookup_insert_is_Some'. by right. }
    assert (rtake !! cgp = Some stats_wcgp) as Hcgp_take.
    { by rewrite /rtake /rfull lookup_insert_ne // lookup_insert_eq. }
    assert (rtake !!! csp = lword_of_word (callee_csp b_stk e_stk a_stk)) as Hcsp_take.
    { rewrite /rtake /rfull lookup_total_alt. by simplify_map_eq. }
    assert (rtake !!! cra = lword_of_word wret) as Hcra_take.
    { rewrite /rtake /rfull lookup_total_alt. by simplify_map_eq. }
    assert (rtake !! ca0 = Some wptr) as Hca0_take.
    { rewrite /rtake /rfull !lookup_insert_ne //. by apply lookup_union_Some_l. }
    clearbody rtake.
    iDestruct (registers_pointsto_extract _ ca0 with "Hregs") as "[Hca0 Hregs]"; first exact Hca0_take.
    iPoseProof "Hstatic" as "Hstatic'". iNamed "Hstatic'".

    (* The slot of the [ErrorState], below the cursor of the callee's stack *)
    set (bc := stk_callee_b b_stk a_stk).
    set (ec := stk_callee_e e_stk a_stk).
    set (cur := stk_start_a bc ec).
    set (es := (cur ^+ (- ErrorState_size))%a).
    assert ((bc <= es)%a ∧ (es + ErrorState_size)%a = Some cur ∧ (cur <= ec)%a) as
      (Hbc_es & Hes_cur & Hcur_ec).
    { rewrite /es /cur /stk_start_a /ErrorState_size /StackEntry_reserved_space in Hminstk |- *.
      rewrite /bc /ec /stk_callee_b /stk_callee_e /SpillSlot_size in Hminstk |- *.
      split_and!; solve_addr. }
    rewrite /ErrorState_size in Hes_cur.
    (* The callee's stack, from the slot and the parts around it *)
    iAssert (□ ∀ ws, ⌜length ws = Z.to_nat ErrorState_size⌝ -∗
               [[ bc , es ]] ↦ₐ [[ region_addrs_zeroes bc es ]] -∗
               [[ es , cur ]] ↦ₐ [[ ws ]] -∗
               [[ cur , ec ]] ↦ₐ [[ region_addrs_zeroes cur ec ]] -∗
               ∃ stk_mem, [[ bc , ec ]] ↦ₐ [[ stk_mem ]])%I as "#Hstk_join".
    { iIntros "!>" (ws Hws) "Hstk_lo Hslot Hstk_hi".
      iDestruct (region_pointsto_split es ec cur with "[$Hslot $Hstk_hi]") as "Hstk".
      { solve_addr. }
      { rewrite Hws /finz.dist /ErrorState_size. solve_addr. }
      iDestruct (region_pointsto_split bc ec es with "[$Hstk_lo $Hstk]") as "Hstk".
      { solve_addr. }
      { by rewrite /region_addrs_zeroes length_replicate. }
      by iExists _. }
    rewrite /stats_arg_pre.
    destruct wptr as [w π].
    destruct w as [z | [ [] p g b e a | ] | | ]; try (by iDestruct "HP" as "[]").
    - (* A tagged capability *)
      destruct π as [ι|]; first by iDestruct "HP" as "[]".
      iDestruct "HP" as "[%Hload Ha]".
      destruct Hload as (Hread & Hbe & Hb_heap & Ha_shadow & Hv_heap).
      iEval (rewrite /stats_may_fault /=) in "Hret".
      destruct (withinBounds b e a) eqn:Hbounds.
      + (* In bounds: the load succeeds *)
        rewrite /stats_read_addr Hbounds in Ha_shadow.
        iEval (rewrite /stats_read_addr Hbounds) in "Ha".
        (* CLoad ca0 ca0 0 *)
        iApply (stats_read_load_spec with "[- $HPC $Hca0 $Ha $Hcode_stats]");
          [apply stats_code_bounds_layout | done | done | done | done |].
        iNext. iIntros "(HPC & Hca0 & Ha & _)".
        iDestruct ("Hregs" with "Hca0") as "Hregs".
        iApply (stats_read_release_close with "Hstatic HPC Hregs Hlock Hna Hclose").
        { intros r. rewrite lookup_insert_is_Some'. by right. }
        { by rewrite lookup_insert_ne. }
        { rewrite lookup_total_insert_ne // Hcra_take.
          apply jalr_target_ok_switcher_return_sentry. }
        iNext. iIntros "HPC Hregs Hna".
        (* The return, at count 0 *)
        iDestruct (registers_pointsto_switcher_return with "Hregs") as (rmap_ret)
          "(%Hdom_ret & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp & Hca0 & Hca1 & Hrmap)".
        { intros r. rewrite !lookup_insert_is_Some'. by right; right. }
        set (M := <[ca1:=lword_of_word (WInt 0)]> (<[ca0:=lload_word p v]> rtake)).
        assert (M !!! ca0 = lload_word p v) as Hret_ca0.
        { rewrite /M lookup_total_alt. by simplify_map_eq. }
        assert (M !!! ca1 = lword_of_word (WInt 0)) as Hret_ca1.
        { rewrite /M lookup_total_alt. by simplify_map_eq. }
        assert (M !!! csp = lword_of_word (callee_csp b_stk e_stk a_stk)) as Hret_csp.
        { rewrite /M -Hcsp_take !lookup_total_alt. by simplify_map_eq. }
        assert (<[ca0:=lload_word p v]> rtake !!! cra = lword_of_word wret) as Hret_cra.
        { rewrite -Hcra_take !lookup_total_alt. by simplify_map_eq. }
        iEval (rewrite Hret_cra /=) in "HPC".
        iEval (rewrite Hret_csp) in "Hcsp".
        iEval (rewrite Hret_ca0) in "Hca0".
        iEval (rewrite Hret_ca1) in "Hca1".
        iApply ("Hret" $! 0%Z _ _ rmap_ret with "[- ]").
        rewrite (_ : cstack_set_top_count (cstack_push frm cstk) 0 = cstack_push frm cstk);
          last exact (cstack_set_top_count_id (cstack_push frm cstk)).
        rewrite /stats_arg_post /stats_read_addr Hbounds.
        iFrame "∗ %". done.
      + (* Out of bounds: the load faults, the handler retries it at the base *)
        rewrite /stats_read_addr Hbounds in Ha_shadow.
        iEval (rewrite /stats_read_addr Hbounds) in "Ha".
        set (f := FaultCheri BoundsViolation (CheriGPR ca0)).
        assert (data_cap_check readAllowed PermitLoadViolation ca0 (WCap true p g b e a) 0 = inl f)
          as Hcheck.
        { rewrite /data_cap_check Hread (_ : (a + 0)%a = Some a); last solve_addr.
          by rewrite /= Hbounds. }
        assert (stats_saved_cap rtake (fault_mtval f) ca0 p g b e a None) as Hsaved.
        { split; last done. by rewrite /f /= mtval_reg_field_encode cheri_reg_num_gpr. }
        rewrite (region_addrs_zeroes_split bc es ec); last solve_addr.
        rewrite (region_addrs_zeroes_split es cur ec); last solve_addr.
        iDestruct (region_pointsto_split bc ec es with "Hstk") as "[Hstk_lo Hstk]".
        { solve_addr. }
        { by rewrite /region_addrs_zeroes length_replicate. }
        iDestruct (region_pointsto_split es ec cur with "Hstk") as "[Hslot Hstk_hi]".
        { solve_addr. }
        { by rewrite /region_addrs_zeroes length_replicate. }
        (* The base is outside the [ErrorState] slot: the caller lends its
           cell, the callee holds the slot *)
        iDestruct (big_sepL2_disjoint_pointsto with "[$Hslot $Ha]") as %Hb_slot.
        assert (stats_outside_slot rtake b) as Hb_out.
        { rewrite elem_of_finz_seq_between in Hb_slot.
          rewrite /stats_outside_slot Hcsp_take /=.
          rewrite /es /ErrorState_size in Hb_slot Hes_cur |- *. fold bc ec cur. solve_addr. }
        (* CLoad ca0 ca0 0 *)
        iApply (stats_read_load_fault_spec _ f with "[- $HPC $Hca0 $Hcode_stats]");
          first done.
        iIntros "Hca0".
        iDestruct ("Hregs" with "Hca0") as "Hregs".
        rewrite insert_id; last exact Hca0_take.
        iApply (stats_read_fault_safe _ _ (cstack_push frm cstk) rtake Local bc ec cur
                 with "Hinv_switcher Hswitcher_static Hstatic Hregs Hcstk Hna Hlock [Hslot] [-]").
        { by intros c [Hok _]. }
        1-3: done.
        { by apply lookup_total_correct. }
        { rewrite Hcra_take. apply jalr_target_ok_switcher_return_sentry. }
        { rewrite /ErrorState_size. solve_addr. }
        { done. }
        { apply (disjoint_from_shadow_weaken bc ec es cur); [done | done | exact Hstk_shadow]. }
        1-2: done.
        { by apply Z.leb_le. }
        { done. }
        { intros c v' _ [-> | [Hstrip _] ] _.
          - by exists ca0, p, g, b, e, a, None.
          - exfalso. revert Hstrip. apply stats_not_may_strip. by right. }
        { rewrite /error_state_area Hcsp_take /=. iExists _. iFrame "Hslot".
          iPureIntro. rewrite /region_addrs_zeroes length_replicate /finz.dist.
          rewrite /ErrorState_size. solve_addr. }
        iIntros (c v' [Hok ->] [-> | [Hstrip _] ]);
          last (exfalso; revert Hstrip; apply stats_not_may_strip; by right).
        iNext. rewrite /stats_fault_conts. iSplit; last first.
        { iIntros (Hnot). exfalso. apply Hnot. split.
          - apply stats_repairable_bounds.
            rewrite reg_index_ca0 /TrustedStack_offset_cra /TrustedStack_offset_ca5
              /TrustedStack_offset_ca0. lia.
          - exists ca0, p, g, b, e, a, None. split_and!; [exact Hsaved | done | exact Hb_out]. }
        iIntros (_ r' p' g' b' e' a' π' w' [Hidx Hr'] Hbe' _ Hw') "Hlock Harea".
        rewrite /f /= mtval_reg_field_encode cheri_reg_num_gpr in Hidx.
        apply (inj reg_index) in Hidx as ->.
        rewrite Hca0_take in Hr'. injection Hr' as <- <- <- <- <- <-.
        destruct Hw' as [-> | [Hheap _] ];
          last by rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hb_heap in Hheap.
        iIntros (_) "HPC Hregs Hcstk Hna".
        rewrite /stats_retry_regs /=.
        iDestruct (registers_pointsto_extract _ ca0 with "Hregs") as "[Hca0 Hregs]";
          first by simplify_map_eq.
        (* CLoad ca0 ca0 0, at the base *)
        iApply (stats_read_load_spec with "[- $HPC $Hca0 $Ha $Hcode_stats]");
          [apply stats_code_bounds_layout | done | apply withinBounds_true_iff; solve_addr
          | done | done |].
        iNext. iIntros "(HPC & Hca0 & Ha & _)".
        iDestruct ("Hregs" with "Hca0") as "Hregs".
        rewrite insert_insert_eq.
        iApply (stats_read_release_close with "Hstatic HPC Hregs Hlock Hna Hclose").
        { intros r. rewrite !lookup_insert_is_Some'. by right; right. }
        { by simplify_map_eq. }
        { rewrite lookup_total_insert_ne // lookup_total_insert_ne // Hcra_take.
          apply jalr_target_ok_switcher_return_sentry. }
        iNext. iIntros "HPC Hregs Hna".
        (* The return, at count 2 *)
        rewrite /error_state_area Hcsp_take /=.
        iDestruct "Harea" as (ws) "[%Hws Hslot]".
        iDestruct ("Hstk_join" with "[//] Hstk_lo Hslot Hstk_hi") as (stk_mem) "Hstk".
        iDestruct (registers_pointsto_switcher_return with "Hregs") as (rmap_ret)
          "(%Hdom_ret & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp & Hca0 & Hca1 & Hrmap)".
        { intros r. rewrite !lookup_insert_is_Some'. by right; right; right. }
        set (M := <[ca1:=lword_of_word (WInt 0)]> (<[ca0:=lload_word p v]>
                    (<[cnull:=lword_of_word (WInt 0)]> rtake))).
        assert (M !!! ca0 = lload_word p v) as Hret_ca0.
        { rewrite /M lookup_total_alt. by simplify_map_eq. }
        assert (M !!! ca1 = lword_of_word (WInt 0)) as Hret_ca1.
        { rewrite /M lookup_total_alt. by simplify_map_eq. }
        assert (M !!! csp = lword_of_word (callee_csp b_stk e_stk a_stk)) as Hret_csp.
        { rewrite /M -Hcsp_take !lookup_total_alt. by simplify_map_eq. }
        assert (<[ca0:=lload_word p v]> (<[cnull:=lword_of_word (WInt 0)]> rtake) !!! cra =
                  lword_of_word wret) as Hret_cra.
        { rewrite -Hcra_take !lookup_total_alt. by simplify_map_eq. }
        iEval (rewrite Hret_cra /=) in "HPC".
        iEval (rewrite Hret_csp) in "Hcsp".
        iEval (rewrite Hret_ca0) in "Hca0".
        iEval (rewrite Hret_ca1) in "Hca1".
        iApply ("Hret" $! 2%Z _ _ rmap_ret with "[- ]").
        rewrite /stats_arg_post /stats_read_addr Hbounds.
        iFrame "∗ %". done.
    - (* An untagged capability: the load faults, and the handler unwinds *)
      iEval (rewrite /stats_may_fault /=) in "Hret".
      iDestruct "Hret" as "[ [_ Hfault_cont] _]".
      set (f := FaultCheri TagViolation (CheriGPR ca0)).
      assert (data_cap_check readAllowed PermitLoadViolation ca0 (WCap false p g b e a) 0 = inl f)
        as Hcheck by by apply data_cap_check_untagged.
      assert (¬ stats_repairable (fault_mcause f) (fault_mtval f)) as Hnrep.
      { intros (_ & Hcode & _). rewrite /f /= mtval_code_field_encode in Hcode.
        by apply (inj cause_code_num) in Hcode. }
      rewrite (region_addrs_zeroes_split bc es ec); last solve_addr.
      rewrite (region_addrs_zeroes_split es cur ec); last solve_addr.
      iDestruct (region_pointsto_split bc ec es with "Hstk") as "[Hstk_lo Hstk]".
      { solve_addr. }
      { by rewrite /region_addrs_zeroes length_replicate. }
      iDestruct (region_pointsto_split es ec cur with "Hstk") as "[Hslot Hstk_hi]".
      { solve_addr. }
      { by rewrite /region_addrs_zeroes length_replicate. }
      (* CLoad ca0 ca0 0 *)
      iApply (stats_read_load_fault_spec _ f with "[- $HPC $Hca0 $Hcode_stats]");
        first done.
      iIntros "Hca0".
      iDestruct ("Hregs" with "Hca0") as "Hregs".
      rewrite insert_id; last exact Hca0_take.
      iApply (stats_read_fault_safe _ _ (cstack_push frm cstk) rtake Local bc ec cur
               with "Hinv_switcher Hswitcher_static Hstatic Hregs Hcstk Hna Hlock [Hslot] [-]").
      { by intros c [Hok _]. }
      1-3: done.
      { by apply lookup_total_correct. }
      { rewrite Hcra_take. apply jalr_target_ok_switcher_return_sentry. }
      { rewrite /ErrorState_size. solve_addr. }
      { done. }
      { apply (disjoint_from_shadow_weaken bc ec es cur); [done | done | exact Hstk_shadow]. }
      1-2: done.
      { by apply Z.leb_le. }
      { done. }
      { intros c v' [Hok ->] [-> | [Hstrip _] ] Hrep.
        - by exfalso.
        - exfalso. revert Hstrip. apply stats_not_may_strip. by left. }
      { rewrite /error_state_area Hcsp_take /=. iExists _. iFrame "Hslot".
        iPureIntro. rewrite /region_addrs_zeroes length_replicate /finz.dist.
        rewrite /ErrorState_size. solve_addr. }
      iIntros (c v' [Hok ->] [-> | [Hstrip _] ]);
        last (exfalso; revert Hstrip; apply stats_not_may_strip; by left).
      iNext. rewrite /stats_fault_conts. iSplit.
      { iIntros ([Hrep _]). by exfalso. }
      (* The unwind: close [stats_inv], give back the stack *)
      iIntros (_ n rmap Hfull_rmap Hca0_rmap Hca1_rmap) "HPC Hregs Hcstk [Harea Hinv] Hna".
      iMod ("Hclose" with "[$Hinv $Hna]") as "Hna".
      rewrite /error_state_area Hcsp_take /=.
      iDestruct "Harea" as (ws) "[%Hws Hslot]".
      iDestruct ("Hstk_join" with "[//] Hstk_lo Hslot Hstk_hi") as "Hstk".
      iApply ("Hfault_cont" $! n rmap with "[//] [//] [//] HPC Hregs Hcstk Hstk Hna").
  Qed.

End Error_Handling_Read.
