From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode map_simpl register_tactics.
From griotte Require Import switcher_base.
From griotte Require Import
  error_handling_spec_states error_handling_spec_read_blocks
  error_handling_spec_handler_blocks.

(** * The error handler of [stats]

    [stats] keeps its invariant [stats_inv] (the lock released) open for
    the whole call of [stats_read]: at the faulting load, the lock is held
    and the token is [⊤ ∖ ↑Nstats]. The fault site gives the handler
    [stats_P_fault]: the lock, what the site knows of the saved register
    that the fault names ([stats_saved_cap]), and two continuations. The
    handler follows its code:
    - when the fault is a bounds violation on a register of the save area
      whose saved capability has non-empty bounds and a base outside the
      [ErrorState] slot ([stats_retries]), it moves the capability's
      address to its base and returns InstallContext; the installed context
      retries the load, with the site's retry continuation
      ([stats_retry_cont]);
    - otherwise, it releases the lock and returns ForceUnwind; the switcher
      unwinds the call with the site's unwind continuation, which receives
      the [ErrorState] slot and [stats_inv]. *)

(** The namespace of the invariant of [stats]. *)
Definition Nstats : namespace := nroot .@ "stats".

Lemma Nswitcher_Nstats : Nswitcher ## Nstats.
Proof. rewrite /Nswitcher /Nstats. solve_ndisj. Qed.

Section Error_Handling_Handler.
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

  (** The register [r] that mtval [v] names, and its saved word in
      [rfault], a capability. *)
  Definition stats_saved_cap (rfault : LReg) (v : Z) (r : RegName)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId) : Prop :=
    reg_index r = mtval_reg_field v ∧
    rfault !! r = Some (MkLWord (WCap true p g b e a) π).

  (** The base [b] lies outside the [ErrorState] slot, the
      [ErrorState_size] words below the cursor of the faulting [csp]. *)
  Definition stats_outside_slot (rfault : LReg) (b : Addr) : Prop :=
    match (rfault !!! csp).(lw) with
    | WCap _ _ _ _ _ a => (b < a ^+ (- ErrorState_size))%a ∨ (a <= b)%a
    | _ => False
    end.

  (** The handler retries the faulting instruction: the fault is
      repairable, and the saved capability has non-empty bounds and a base
      outside the [ErrorState] slot. *)
  Definition stats_retries (c v : Z) (rfault : LReg) : Prop :=
    stats_repairable c v ∧
    ∃ r p g b e a π, stats_saved_cap rfault v r p g b e a π ∧
                     (b < e)%a ∧ stats_outside_slot rfault b.

  (** The registers of the retried context: the faulting ones, with the
      repaired word [w] in [r], and [cnull] zero. *)
  Definition stats_retry_regs (rfault : LReg) (r : RegName) (w : LWord) : LReg :=
    <[r := stats_repair_word w]> (<[cnull := lword_of_word (WInt 0)]> rfault).

  (** The continuation of the retried context, at the faulting PC: for the
      saved capability of [r], with non-empty bounds and a base outside the
      [ErrorState] slot, and its loaded copy [w] (whose tag the load may
      strip), with the lock held and the [ErrorState] slot, at the count
      that the install leaves. *)
  Definition stats_retry_cont (F : coPset) (cstk : CSTK) (rfault : LReg) (v : Z) : iProp Σ :=
    ∀ r p g b e a π w,
      ⌜stats_saved_cap rfault v r p g b e a π⌝ -∗
      ⌜(b < e)%a⌝ -∗
      ⌜stats_outside_slot rfault b⌝ -∗
      ⌜lload_heap (MkLWord (WCap true p g b e a) π) w⌝ -∗
      STATS_cgp_b ↦ₐ WInt 1 -∗
      error_state_area rfault -∗
      context_resume F (cstack_set_top_count cstk (top_error_count cstk + 2))
        (stats_pcc stats_load_addr) (stats_retry_regs rfault r w).

  (** The fault obligation of [stats], at mcause [c] and mtval [v]: the
      facts of the site, the cell of the topmost table set, the saved
      capability of the register that a repairable fault names, the lock
      held, and the continuation of each outcome of the handler: the retry
      of the load, or the unwind, which receives the [ErrorState] slot and
      [stats_inv]. *)
  Definition stats_P_fault (F : coPset) (cstk : CSTK) (w : LWord) (rfault : LReg)
    (c v : Z) : iProp Σ :=
    ("%Hfacts" ∷ ⌜stats_fault_facts F w rfault⌝ ∗
     "%Htbl_set" ∷ ⌜(top_tframe cstk).(tf_export_tbl) ≠ lword_of_word (WInt 0)⌝ ∗
     "%Hsaved" ∷ ⌜stats_repairable c v → ∃ r p g b e a π, stats_saved_cap rfault v r p g b e a π⌝ ∗
     "Hlock" ∷ STATS_cgp_b ↦ₐ WInt 1 ∗
     "Hcont" ∷ ▷ ((⌜stats_retries c v rfault⌝ -∗ stats_retry_cont F cstk rfault v) ∧
                 (⌜¬ stats_retries c v rfault⌝ -∗
                  unwind_cont F cstk (error_state_area rfault ∗ stats_inv))))%I.

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

  (** ** The register that a fault names *)

  Lemma reg_index_cnull : reg_index cnull = 0%Z.
  Proof. reflexivity. Qed.

  (** The faults that the handler repairs are bounds violations on a
      general register other than [cnull]. *)
  Lemma stats_repairable_fault (f : fault) :
    stats_repairable (fault_mcause f) (fault_mtval f) →
    ∃ r, f = FaultCheri BoundsViolation (CheriGPR r) ∧ r ≠ cnull.
  Proof.
    rewrite /stats_repairable /TrustedStack_offset_cra /TrustedStack_offset_ca5.
    destruct f as [cc cr | | fa | fa | fa]; cbn [fault_mcause fault_mtval];
      try (intros [Hc _]; exfalso; revert Hc;
           rewrite /MCAUSE_CHERI /MCAUSE_ILLEGAL_INSTRUCTION /MCAUSE_INST_ACCESS_FAULT
             /MCAUSE_LOAD_ACCESS_FAULT /MCAUSE_STORE_ACCESS_FAULT; lia).
    intros (_ & Hcode & Hreg).
    rewrite mtval_code_field_encode in Hcode. apply (inj cause_code_num) in Hcode as ->.
    rewrite mtval_reg_field_encode in Hreg.
    destruct cr as [r | | | |].
    2-5: exfalso;
      match type of Hreg with context [cheri_reg_num ?s] =>
        apply (cheri_reg_num_special s); [intros ?r' ?Hr'; inversion Hr' | rewrite /RegNum; lia]
      end.
    exists r. split; first done.
    intros ->. rewrite cheri_reg_num_gpr reg_index_cnull in Hreg. lia.
  Qed.

  (** A bounds violation on a register of the save area is repairable. *)
  Lemma stats_repairable_bounds (r : RegName) :
    (TrustedStack_offset_cra <= reg_index r <= TrustedStack_offset_ca5)%Z →
    stats_repairable MCAUSE_CHERI (encode_mtval BoundsViolation (CheriGPR r)).
  Proof.
    intros Hr. split_and!; first done.
    - apply mtval_code_field_encode.
    - rewrite mtval_reg_field_encode cheri_reg_num_gpr. lia.
    - rewrite mtval_reg_field_encode cheri_reg_num_gpr. lia.
  Qed.

  (** The index of a register other than [cnull] is positive. *)
  Lemma reg_index_pos (r : RegName) : r ≠ cnull → (1 <= reg_index r)%Z.
  Proof.
    intros Hr. pose proof (reg_index_range r) as Hrange.
    destruct (decide (reg_index r = 0%Z)) as [Hidx_zero | Hidx_nonzero]; last lia.
    exfalso. apply Hr, (inj reg_index). by rewrite Hidx_zero reg_index_cnull.
  Qed.

  (** Word [i] of the save area holds the register [x_i]. *)
  Lemma error_state_regs_index (r : RegName) :
    r ≠ cnull → error_state_regs !! (Z.to_nat (reg_index r) - 1)%nat = Some r.
  Proof.
    intros Hr. pose proof (reg_index_pos r Hr) as Hpos.
    pose proof (reg_index_range r) as Hrange.
    assert (∃ r', error_state_regs !! (Z.to_nat (reg_index r) - 1)%nat = Some r' ∧
                  reg_index r' = reg_index r) as (r' & Hr' & Heq).
    { destruct r as [n fin]. cbn in Hpos, Hrange |- *. rewrite /RegNum in Hrange.
      rewrite Nat2Z.id.
      assert (n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨
              n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15)%nat as Hn by lia.
      destruct_or! Hn; subst n; eexists; split; reflexivity. }
    by rewrite Hr' (inj reg_index _ _ Heq).
  Qed.

  Lemma error_state_regs_NoDup : NoDup error_state_regs.
  Proof. rewrite /error_state_regs. repeat constructor; set_solver. Qed.

  Lemma error_state_regs_cnull : cnull ∉ error_state_regs.
  Proof. rewrite /error_state_regs. set_solver. Qed.

  (** Word [reg_index r] of the [ErrorState] holds the register [r]. *)
  Lemma error_state_words_index (p : Perm) (w : LWord) (rfault : LReg) (r : RegName) :
    r ≠ cnull →
    error_state_words p w rfault !! Z.to_nat (reg_index r) = Some (lstore_word p (rfault !!! r)).
  Proof.
    intros Hr. pose proof (reg_index_pos r Hr) as Hpos.
    rewrite (_ : Z.to_nat (reg_index r) = S (Z.to_nat (reg_index r) - 1)); last lia.
    rewrite /error_state_words lookup_cons list_lookup_fmap error_state_regs_index //.
  Qed.

  (** The register [r ≠ cnull] after InstallContext: word [reg_index r] of
      the [ErrorState]. *)
  Lemma error_state_install_lookup (rmap : LReg) (ls : list LWord) (r : RegName) :
    length ls = length error_state_regs →
    r ≠ cnull →
    error_state_install rmap ls !! r = ls !! (Z.to_nat (reg_index r) - 1)%nat.
  Proof.
    intros Hlen Hr. pose proof (error_state_regs_index r Hr) as Hi.
    destruct (lookup_lt_is_Some_2 ls (Z.to_nat (reg_index r) - 1)) as [x Hx].
    { rewrite Hlen. by eapply lookup_lt_Some. }
    rewrite Hx /error_state_install.
    apply lookup_union_Some_l, elem_of_list_to_map_1.
    - rewrite fst_zip; [apply error_state_regs_NoDup | lia].
    - eapply list_elem_of_lookup_2. apply lookup_zip_with_Some. eauto.
  Qed.

  (** The registers that InstallContext installs from the [ErrorState]
      written by the handler: the faulting ones, with the repaired word
      [w'] in [r]; [cnull] is the handler's. *)
  Lemma stats_install_retry_regs (rfault rmap : LReg) (w w' : LWord) (r : RegName) :
    (∀ r, is_Some (rfault !! r)) →
    rmap !! cnull = Some (lword_of_word (WInt 0)) →
    r ≠ cnull →
    error_state_install rmap
      (lload_word RWL <$> drop 1
         (<[Z.to_nat (reg_index r) := w']> (error_state_words RWL w rfault))) =
    <[r := w']> (<[cnull := lword_of_word (WInt 0)]> rfault).
  Proof.
    intros Hfull Hcnull Hr. apply map_eq. intros r'.
    set (ls := lload_word RWL <$> drop 1 _).
    assert (length ls = length error_state_regs) as Hlen.
    { by rewrite /ls length_fmap length_drop length_insert length_error_state_words. }
    destruct (decide (r' = cnull)) as [-> | Hr'].
    { rewrite lookup_insert_ne // lookup_insert_eq /error_state_install.
      rewrite lookup_union_r //. apply not_elem_of_list_to_map_1.
      rewrite fst_zip; [apply error_state_regs_cnull | lia]. }
    pose proof (reg_index_pos r' Hr') as Hpos'.
    rewrite error_state_install_lookup // /ls list_lookup_fmap lookup_drop.
    rewrite (_ : (1 + (Z.to_nat (reg_index r') - 1))%nat = Z.to_nat (reg_index r')); last lia.
    destruct (decide (r' = r)) as [-> | Hne].
    - rewrite list_lookup_insert_eq; last first.
      { rewrite length_error_state_words. pose proof (reg_index_range r) as Hrange.
        rewrite /ErrorState_size. rewrite /RegNum in Hrange. lia. }
      by rewrite /= lload_word_RWL lookup_insert_eq.
    - rewrite list_lookup_insert_ne; last first.
      { intros Heq. apply Hne, (inj reg_index). pose proof (reg_index_range r) as Hrange.
        pose proof (reg_index_range r') as Hrange'. lia. }
      rewrite error_state_words_index // /= lload_word_RWL lstore_word_isWL //.
      rewrite lookup_insert_ne // lookup_insert_ne //.
      destruct (Hfull r') as [x Hx]. by rewrite (lookup_total_correct _ _ _ Hx) Hx.
  Qed.

  (** The resumed PC, from the untouched word 0 of the [ErrorState]: the
      faulting load. *)
  Lemma stats_resumed_pc_load :
    llegalise MEPCC
      (resumed_pc stats_wpcc (get_a (lclear_tag (lmepcc_of_pc (stats_pcc stats_load_addr))).(lw))) =
    stats_pcc stats_load_addr.
  Proof.
    pose proof STATS_size_imports as Hsize_imports.
    pose proof STATS_size_code as Hsize_code.
    rewrite /resumed_pc /stats_wpcc /stats_pcc /lmepcc_of_pc /mepcc_of_pc /=.
    destruct (negb _); cbn;
      rewrite /lea_result /=;
      rewrite (_ : (STATS_pcc_b + (stats_load_addr - STATS_pcc_b))%a = Some stats_load_addr);
      [done | | done |];
      rewrite /stats_load_addr; cbn in Hsize_code |- *; solve_addr.
  Qed.

  (** ** The [ErrorState] slot *)

  (** The slot test of block 6, from the faulting [csp]: the slot starts at
      [a16], [ErrorState_size] below its cursor. *)
  Lemma stats_outside_slot_base (rfault : LReg) (g : Locality) (b e a a16 b' : Addr) :
    rfault !!! csp = lword_of_word (WCap true RWL g b e a) →
    (a + - ErrorState_size)%a = Some a16 →
    stats_outside_slot rfault b' ↔ stats_base_outside a16 b'.
  Proof.
    intros Hcsp Ha16. rewrite /stats_outside_slot Hcsp /= /stats_base_outside.
    rewrite /ErrorState_size in Ha16 |- *.
    assert ((a ^- 16)%f = a16) as -> by solve_addr.
    split; (intros [Hb' | Hb']; [left | right]); solve_addr.
  Qed.

  (** ** The handler *)

  (** The unwind of the handler, from [.Lstats_handler_unwind]: it releases
      the lock, returns ForceUnwind, and the switcher unwinds with the
      site's continuation, which receives the [ErrorState] slot and
      [stats_inv]. *)
  Lemma stats_handler_unwind_return (F : coPset) (cstk : CSTK) (rfault regs : LReg)
    (mie : InterruptStatus) :
    (∀ r, is_Some (regs !! r)) →
    regs !! cra = Some (handler_return_sentry mie) →
    regs !! cgp = Some stats_wcgp →
    switcher_static -∗
    codefrag_pers STATS_pcc_b stats_code -∗
    PC ↦ₚ[th] stats_pcc (STATS_pcc_b ^+ stats_label ".Lstats_handler_unwind")%a -∗
    registers_pointsto regs -∗
    STATS_cgp_b ↦ₐ WInt 1 -∗
    error_state_area rfault -∗
    cstack_frag (cstack_set_top_count cstk (top_error_count cstk + 1)) -∗
    na_own (tpool th) F -∗
    ▷ unwind_cont F cstk (error_state_area rfault ∗ stats_inv) -∗
    WP Seq (Instr Executable) @[th] {{ HO th }}.
  Proof.
    iIntros (Hfull Hcra Hcgp) "#Hstatic #Hcode_stats HPC Hregs Hlock Harea Hcstk Hna HU".
    destruct (Hfull ca0) as [wca0 Hca0].
    iDestruct (registers_pointsto_extract3 _ cgp ca0 cra with "Hregs")
      as "(Hcgp & Hca0 & Hcra & Hregs)"; [done | done | done | done | done | done |].
    pose proof STATS_size_data as Hsize_data.
    pose proof STATS_cgp_disjoint_from_shadow as Hcgp_shadow.
    (* Store cgp 0 0; Mov ca0 ForceUnwind; Jalr cnull cra *)
    iApply (stats_handler_unwind_spec STATS_pcc_b STATS_pcc_e STATS_cgp_b STATS_cgp_e
              with "[- $HPC $Hcgp $Hca0 $Hcra $Hlock $Hcode_stats]").
    { apply stats_code_bounds_layout. }
    { cbn in Hsize_data. solve_addr. }
    { eapply disjoint_from_shadow_not_in; first exact Hcgp_shadow.
      apply withinBounds_true_iff. cbn in Hsize_data. solve_addr. }
    { by destruct mie. }
    iNext. iIntros "(HPC & Hcgp & Hca0 & Hcra & Hlock & _)".
    iDestruct ("Hregs" with "Hcgp Hca0 Hcra") as "Hregs".
    rewrite handler_return_sentry_pc.
    iApply (switcher_handler_return_unwind F cstk (top_error_count cstk + 1)
              (error_state_area rfault ∗ stats_inv)
             with "Hstatic HPC Hregs Hcstk HU [$Harea $Hlock] Hna").
    { intros r. rewrite !lookup_insert_is_Some'. naive_solver. }
    { by rewrite lookup_total_insert_ne // lookup_total_insert. }
  Qed.

  (** The handler of [stats] satisfies its obligation for [stats_P_fault],
      for any token [F]. It decodes the fault: when [stats_retries] holds,
      it returns InstallContext through [switcher_handler_return_install]
      (block 6 checks the bounds and the base, block 7 repairs),
      and the installed context continues with [stats_retry_cont]; a fault
      of the install is excluded, since the [ErrorState] can be loaded
      through the handler's [csp]. Otherwise, it returns ForceUnwind
      ([stats_handler_unwind_return]). *)
  Lemma stats_handler_execute :
    codefrag_pers STATS_pcc_b stats_code -∗
    b_stats_exp_tbl ↦ₐ□ stats_wpcc -∗
    execute_error_handler b_stats_exp_tbl stats_wpcc stats_wcgp stats_handler_pcc_off
      Stackful stats_P_fault.
  Proof.
    iIntros "#Hcode_stats #Hpcc". iModIntro.
    iIntros (F cstk w rfault mcause mtval wpc regs). iNext.
    iIntros "((%HF & %HFtrap) & #Hinv_switcher & #Hstatic) %Htbl %Heven %Hmcause %Hentry
             %Hinvoc HPC Hregs (_ & %Hshadow & Hes) _ HUP Hcstk Hna".
    destruct Hinvoc as
      (Hfull & [mie Hcra] & Hcgp &
       (Hstores & wcsp & wa0 & Hsr & Hcsp & Hca0 & Hca1 & Hca2) & Hzero).
    (* The obligation of the site *)
    iDestruct "HUP" as "[_ HP]". iNamed "HP".
    destruct Hfacts as (HFeq & -> & Hfull_f & (g & b & e & a & Hcsp_f) & Hcgp_f & Hcra_f).
    rewrite Hcsp_f /stackful_regs /= in Hsr.
    destruct (a + - ErrorState_size)%a as [a16|] eqn:Ha16; last done.
    cbn in Hsr. injection Hsr as <- <-.
    rewrite /error_state_stores_ok Hcsp_f /= in Hstores. destruct Hstores as (_ & Hb_a & Ha_e).
    assert ((a ^+ (- ErrorState_size))%a = a16) as Ha_a16.
    { rewrite /ErrorState_size in Ha16 |- *. solve_addr. }
    assert ((a16 ^+ ErrorState_size)%a = a) as Ha16_a.
    { rewrite /ErrorState_size in Ha16 |- *. solve_addr. }
    rewrite /error_state_shadow_free Hcsp_f /= Ha_a16 -Ha16_a in Hshadow.
    iEval (rewrite /error_state_pointsto Hcsp_f /= Ha_a16 -Ha16_a) in "Hes".
    rewrite /handler_entry /stats_wpcc /stats_pcc /= in Hentry.
    destruct (STATS_pcc_b + stats_handler_pcc_off)%a as [a_handler|] eqn:Ha_handler; last done.
    cbn in Hentry. injection Hentry as <-.
    assert (a_handler = (STATS_pcc_b ^+ stats_label ".Lstats_handler")%a) as ->.
    { rewrite /stats_handler_pcc_off in Ha_handler. cbn. solve_addr. }
    assert (regs !! ct0 = Some (lword_of_word (WInt 0))) as Hct0.
    { apply Hzero. set_solver. }
    assert (regs !! ct1 = Some (lword_of_word (WInt 0))) as Hct1.
    { apply Hzero. set_solver. }
    assert (regs !! ct2 = Some (lword_of_word (WInt 0))) as Hct2.
    { apply Hzero. set_solver. }
    assert (regs !! ctp = Some (lword_of_word (WInt 0))) as Hctp.
    { apply Hzero. set_solver. }
    assert (regs !! cnull = Some (lword_of_word (WInt 0))) as Hcnull.
    { apply Hzero. set_solver. }
    assert (regs !! cgp = Some stats_wcgp) as Hcgp_stats by done.
    set (ws := error_state_words RWL (stats_pcc stats_load_addr) rfault).
    (* The [ErrorState] slot, for the unwind *)
    iAssert (∀ ws', ⌜length ws' = Z.to_nat ErrorState_size⌝ -∗
                    [[ a16 , (a16 ^+ ErrorState_size)%a ]] ↦ₐ [[ ws' ]] -∗
                    error_state_area rfault)%I as "Harea_of".
    { iIntros (ws' Hws') "Hws'". rewrite /error_state_area Hcsp_f /= Ha_a16 -Ha16_a.
      iExists ws'. by iFrame. }

    (* The registers of the handler's body *)
    pose proof (lregmap_full_dom _ Hfull) as Hdom_regs.
    rewrite /registers_pointsto.
    iExtractList "Hregs" [ca0; ca1; ca2; ct0; ct1; ct2; ctp; cra]
      as ["Hca0"; "Hca1"; "Hca2"; "Hct0"; "Hct1"; "Hct2"; "Hctp"; "Hcra"].

    (* Block 5: decode the fault *)
    iApply (stats_handler_decode_spec STATS_pcc_b STATS_pcc_e mcause mtval
             with "[- $HPC $Hca1 $Hca2 $Hct0 $Hcode_stats]"); first apply stats_code_bounds_layout.
    iNext. iSplit; last first.
    { (* Not repairable: unwind *)
      iIntros (Hnrep) "(HPC & Hca1 & Hca2 & [%wct0 Hct0] & _)".
      iInsertList "Hregs" [cra; ctp; ct2; ct1; ct0; ca2; ca1; ca0].
      iDestruct "Hcont" as "[_ Hcont]".
      iApply (stats_handler_unwind_return F cstk rfault _ mie
               with "Hstatic Hcode_stats HPC Hregs Hlock [Hes Harea_of] Hcstk Hna [Hcont]").
      { intros r'. apply elem_of_dom. rewrite !dom_insert_L ?dom_delete_L Hdom_regs.
        pose proof (all_registers_s_correct r'). set_solver. }
      { by simplify_map_eq. }
      { by simplify_map_eq. }
      { iApply ("Harea_of" with "[] Hes"). iPureIntro. apply length_error_state_words. }
      iNext. iApply "Hcont". iPureIntro. by intros [? _]. }
    (* Repairable: the saved capability *)
    iIntros (Hrep) "(HPC & Hca1 & Hca2 & Hct0 & _)".
    destruct (Hsaved Hrep) as (r & p & g' & b' & e' & a' & π & Hidx & Hr).
    pose proof Hrep as (_ & _ & Hrange).
    assert (r ≠ cnull) as Hr_cnull.
    { intros ->. rewrite reg_index_cnull in Hidx. rewrite /TrustedStack_offset_cra in Hrange. lia. }
    assert (ws !! Z.to_nat (mtval_reg_field mtval) = Some (MkLWord (WCap true p g' b' e' a') π))
      as Hws_r.
    { rewrite -Hidx /ws error_state_words_index // lstore_word_isWL //.
      by rewrite (lookup_total_correct _ _ _ Hr). }

    (* Block 6: load the saved capability, check its bounds and its base *)
    iApply (stats_handler_check_spec STATS_pcc_b STATS_pcc_e g b e a16 ws
              (mtval_reg_field mtval) p g' b' e' a' π
             with "[- $HPC $Hca0 $Hct0 $Hct1 $Hct2 $Hctp $Hes $Hcode_stats]").
    { apply stats_code_bounds_layout. }
    1-2: rewrite /ErrorState_size in Ha16 Hb_a |- *; solve_addr.
    { done. }
    { apply length_error_state_words. }
    { done. }
    { done. }
    iNext. iSplit; last first.
    { (* Empty bounds, or a base in the slot: unwind *)
      iIntros (Hnfix)
        "(HPC & Hca0 & [%wct0 Hct0] & [%wct1 Hct1] & [%wct2 Hct2] & [%wctp Hctp] & Hes & _)".
      iInsertList "Hregs" [cra; ctp; ct2; ct1; ct0; ca2; ca1; ca0].
      iDestruct "Hcont" as "[_ Hcont]".
      iApply (stats_handler_unwind_return F cstk rfault _ mie
               with "Hstatic Hcode_stats HPC Hregs Hlock [Hes Harea_of] Hcstk Hna [Hcont]").
      { intros r'. apply elem_of_dom. rewrite !dom_insert_L ?dom_delete_L Hdom_regs.
        pose proof (all_registers_s_correct r'). set_solver. }
      { by simplify_map_eq. }
      { by simplify_map_eq. }
      { iApply ("Harea_of" with "[] Hes"). iPureIntro. apply length_error_state_words. }
      iNext. iApply "Hcont". iPureIntro.
      intros (_ & r2 & p2 & g2 & b2 & e2 & a2 & π2 & (Hidx2 & Hr2) & Hlt & Hout).
      rewrite -Hidx in Hidx2. apply (inj reg_index) in Hidx2 as ->.
      rewrite Hr in Hr2. simplify_eq.
      apply Hnfix. split; first done.
      by apply (stats_outside_slot_base rfault g b e _ a16 b2 Hcsp_f Ha16). }
    (* Non-empty bounds, base outside the slot: block 7, InstallContext *)
    iIntros (t Hbe Hout Hwrep)
      "(HPC & Hca0 & Hct0 & Hct1 & Hct2 & [%wctp Hctp] & Hes & _)".
    iApply (stats_handler_fix_spec STATS_pcc_b STATS_pcc_e g b e a16 ws
              (mtval_reg_field mtval) t p g' b' e' a' π
             with "[- $HPC $Hca0 $Hct0 $Hct1 $Hct2 $Hcra $Hes $Hcode_stats]").
    { apply stats_code_bounds_layout. }
    1-2: rewrite /ErrorState_size in Ha16 Hb_a |- *; solve_addr.
    { done. }
    { apply length_error_state_words. }
    { done. }
    { by destruct mie. }
    iNext. iIntros "(HPC & Hca0 & [%wct0 Hct0] & [%wct1 Hct1] & [%wct2 Hct2] & Hcra & Hes & _)".
    set (wrep := MkLWord (WCap t p g' b' e' a') π).
    iInsertList "Hregs" [cra; ctp; ct2; ct1; ct0; ca2; ca1; ca0].
    rewrite handler_return_sentry_pc.
    match goal with
    | |- context [ ([∗ map] k↦y ∈ ?m, k ↦ᵣ y)%I ] => set (rmap := m)
    end.
    assert (∀ r', is_Some (rmap !! r')) as Hfull_rmap.
    { intros r'. apply elem_of_dom. rewrite /rmap !dom_insert_L ?dom_delete_L Hdom_regs.
      pose proof (all_registers_s_correct r'). set_solver. }
    assert (rmap !!! csp = lword_of_word (WCap true RWL g b e a16)) as Hcsp_rmap.
    { rewrite /rmap lookup_total_alt. by simplify_map_eq. }
    set (ws' := <[Z.to_nat (mtval_reg_field mtval) := stats_repair_word wrep]> ws).

    (* InstallContext, at the token [F] of the site *)
    iApply (switcher_handler_return_install F
              (cstack_set_top_count cstk (top_error_count cstk + 1)) rmap stats_wpcc
              RWL g b e a16 ws' with "[- ]"); [done | done | done | | | done | | done | | ].
    { by rewrite /rmap lookup_total_alt; simplify_map_eq. }
    { by rewrite top_tframe_set_count. }
    { exists a. rewrite /ErrorState_size in Ha16 |- *. solve_addr. }
    { by rewrite /ws' length_insert length_error_state_words. }
    rewrite top_export_tbl_set_count Htbl.
    iFrame "Hinv_switcher Hstatic Hpcc HPC Hcstk Hna".
    iSplitL "Hregs"; first iExact "Hregs".
    iSplitL "Hes".
    { rewrite /install_region. iExact "Hes". }
    iNext. iSplit.
    - (* The install faults: excluded, the [ErrorState] can be loaded *)
      iIntros (Hskip) "_". exfalso. apply Hskip.
      rewrite /error_state_loads_ok Hcsp_rmap /=.
      split_and!; [done | rewrite /ErrorState_size in Ha16 Hb_a |- *; solve_addr..].
    - (* The install succeeds: the retry *)
      iIntros "Hreg".
      iDestruct "Hcont" as "[Hcont _]".
      rewrite top_error_count_set_count cstack_set_top_count_twice.
      rewrite (_ : (top_error_count cstk + 1 + 1 = top_error_count cstk + 2)%Z); last lia.
      assert (ws' !!! 0%nat = ws !!! 0%nat) as ->.
      { rewrite /ws' list_lookup_total_insert_ne //. rewrite -Hidx.
        pose proof (reg_index_pos r Hr_cnull) as Hidx_pos. lia. }
      rewrite stats_resumed_pc_load.
      rewrite /ws' -Hidx (stats_install_retry_regs rfault rmap); [ | done | | done]; last first.
      { rewrite /rmap. by simplify_map_eq. }
      assert (stats_outside_slot rfault b') as Hout_slot
        by (by apply (stats_outside_slot_base rfault g b e a a16 b' Hcsp_f Ha16)).
      iApply ("Hcont" with "[%] [%] [%] [%] [%] Hlock [Hreg Harea_of]").
      { split; first done. exists r, p, g', b', e', a', π. split_and!; [by split | done | done]. }
      { by split. }
      { done. }
      { done. }
      { done. }
      iApply ("Harea_of" with "[] Hreg"). iPureIntro.
      by rewrite length_insert length_error_state_words.
  Qed.

End Error_Handling_Handler.
