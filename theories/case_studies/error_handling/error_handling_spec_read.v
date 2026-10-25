From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode map_simpl register_tactics.
From griotte Require Import switcher_base switcher_base_ktk.
From griotte Require Import
  error_handling_spec_states error_handling_spec_read_blocks error_handling_spec_handler.

(** * The entry [stats_read] for a known caller

    [stats_read] opens [stats_inv] at its entry, with [na_own ⊤], and keeps
    it open for the whole call. At the load of [.Lread_load], it holds the
    lock and [na_own (⊤ ∖ ↑Nstats)]:
    - when the load succeeds, the release closes the invariant, and the
      callee returns the loaded word;
    - when it faults, the fault site ([stats_read_fault_safe]) gives the
      trap the handler of [stats] with [stats_P_fault]. It proves that the
      switcher invokes the handler ([handler_runs]): the count is 0, the
      callee's stack has room for the [ErrorState], and the cell of the
      frame's table holds the table. No unwind is then possible, so the
      site needs no unwind continuation. The handler resumes after the load
      with [EINVAL] in [ca0]; the release closes the invariant, and the
      callee returns [EINVAL], at count 2.

    The callee never unwinds: the specification for a known caller
    ([stats_read_spec_known_to_known]) is that of a callee that does not
    fault ([may_fault = false]). *)

Section Error_Handling_Read.
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
      with a stack that has room for the [ErrorState], at count 0. *)
  Lemma stats_read_handler_runs (cstk : CSTK) (rfault : LReg) (g : Locality) (b e a : Addr) :
    STATS_pcc_b ≠ b_switcher →
    rfault !!! csp = lword_of_word (WCap true RWL g b e a) →
    (b + ErrorState_size <= a)%Z → (a <= e)%a →
    top_error_count cstk = 0 →
    (top_tframe cstk).(tf_export_tbl) ≠ lword_of_word (WInt 0) →
    stackful_handler_runs cstk (stats_pcc stats_load_addr) rfault
      stats_handler_pcc_off stats_wpcc.
  Proof.
    intros Hswitcher Hcsp Hba Hae Hcount Htbl.
    pose proof STATS_size_imports as Hsize_imports.
    pose proof STATS_size_code as Hsize_code.
    rewrite /stackful_handler_runs Hcsp Hcount.
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

  (** The fault site of [stats]: a fault at the load, with the lock held,
      [na_own (⊤ ∖ ↑Nstats)], and a stack with room for the [ErrorState],
      outside the shadow table, at count 0. The site lends the slot of the
      [ErrorState], and gives the handler [stats_P_fault]: the lock, the
      closing of [stats_inv], and the continuation after the release
      ([stats_resumed_return]). The switcher invokes the handler, so the
      site gives no unwind continuation. *)
  Lemma stats_read_fault_safe (cstk : CSTK) (rfault : LReg)
    (g : Locality) (b e a : Addr) :
    STATS_pcc_b ≠ b_switcher →
    (∀ r, is_Some (rfault !! r)) →
    rfault !!! csp = lword_of_word (WCap true RWL g b e a) →
    rfault !!! cgp = stats_wcgp →
    jalr_target_ok cnull cra (rfault !!! cra).(lw) = true →
    (b + ErrorState_size <= a)%Z → (a <= e)%a →
    disjoint_from_shadow (a ^+ (- ErrorState_size))%a a →
    top_export_tbl cstk = b_stats_exp_tbl →
    top_error_count cstk = 0 →
    (top_tframe cstk).(tf_export_tbl) ≠ lword_of_word (WInt 0) →
    na_inv cerise_nais Nswitcher switcher_inv -∗
    switcher_static -∗
    stats_static -∗
    registers_pointsto rfault -∗
    cstack_frag cstk -∗
    na_own cerise_nais (⊤ ∖ ↑Nstats) -∗
    (▷ stats_inv ∗ na_own cerise_nais (⊤ ∖ ↑Nstats) ={⊤}=∗ na_own cerise_nais ⊤) -∗
    STATS_cgp_b ↦ₐ WInt 1 -∗
    error_state_area rfault -∗
    ▷ stats_resumed_return cstk rfault -∗
    trap_safe (stats_pcc stats_load_addr) ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I.
  Proof.
    iIntros (Hswitcher Hfull Hcsp Hcgp Hcra Hba Hae Hshadow
               Htbl Hcount Htbl_set)
      "#Hinv_switcher #Hswitcher_static #Hstatic Hregs Hcstk Hna Hclose Hlock Harea Hret".
    pose proof Nswitcher_Nstats as Hdisj_stats.
    iApply (trap_safe_exception_entry mcause_ok (⊤ ∖ ↑Nstats)
              with "Hinv_switcher Hswitcher_static");
      [done | solve_ndisj | rewrite /N_trap /Nstats; solve_ndisj |].
    iModIntro. iExists rfault, cstk. iFrame "Hna Hregs Hcstk". iSplit; first done.
    iDestruct (stats_trusted_handler with "Hstatic") as "#Hhandler".
    iPoseProof "Hstatic" as "Hstatic'". iNamed "Hstatic'".
    rewrite -Htbl.
    assert (error_state_stores_ok (rfault !!! csp)) as Hstores.
    { by rewrite /error_state_stores_ok Hcsp /=. }
    iApply (trap_handler_ok_handler _ _ _ _ _ stats_P_fault stats_handler_pcc_off
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
    - iIntros (mcause _). rewrite /stats_P_fault. iFrame "Hlock Hclose Hret". iPureIntro.
      split; last done.
      rewrite /stats_fault_facts. split_and!; try done.
      by exists g, b, e, a.
  Qed.

  (** The load through an untagged capability faults. *)
  Lemma stats_read_load_untagged_spec
    (pc_b pc_e : Addr) (p : Perm) (g : Locality) (b e a : Addr) (π : option AId) :
    stats_code_bounds pc_b pc_e ->
    PC ↦ₚ WCap true RX Global pc_b pc_e (pc_b ^+ stats_label ".Lread_load")%a ∗
    ca0 ↦ᵣ MkLWord (WCap false p g b e a) π ∗
    codefrag_pers pc_b stats_code ∗
    (ca0 ↦ᵣ MkLWord (WCap false p g b e a) π -∗
     trap_safe (WCap true RX Global pc_b pc_e (pc_b ^+ stats_label ".Lread_load")%a) ⊤
       (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I)
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((HsubBounds & Hpc_shadow & Hpc_nonheap)) "(HPC & Hca0 & Hcode_stats & Hfailed)".
    iDestruct (codefrag_contiguous_region_pers with "Hcode_stats") as %Hpc_contiguous;
    cbn [length map encodeInstrsW] in Hpc_contiguous.
    stats_unfold_code.
    (* Block 2: the load *)
    focus_block (stats_block ".Lread_load") "Hcode_stats" of stats_blocks at pc_b
      as a_load Ha_load "Hcode" "Hcont".
    (* CLoad ca0 ca0 0 *)
    iInstr_fail "Hcode".
    iTrap with "Hfailed".
  Qed.

  (** ** The body of [stats_read] *)

  (** The entry: open [stats_inv], test the lock and take it, up to the
      load. *)
  Lemma stats_read_take_open (rmap : LReg) :
    (∀ r, is_Some (rmap !! r)) →
    rmap !! cgp = Some stats_wcgp →
    na_inv cerise_nais Nstats stats_inv -∗
    stats_static -∗
    PC ↦ₚ stats_pcc (STATS_pcc_b ^+ stats_read_pcc_off)%a -∗
    registers_pointsto rmap -∗
    na_own cerise_nais ⊤ -∗
    ▷ (PC ↦ₚ stats_pcc stats_load_addr -∗
       registers_pointsto (<[ct0 := lword_of_word (WInt 0)]> rmap) -∗
       STATS_cgp_b ↦ₐ WInt 1 -∗
       na_own cerise_nais (⊤ ∖ ↑Nstats) -∗
       (▷ stats_inv ∗ na_own cerise_nais (⊤ ∖ ↑Nstats) ={⊤}=∗ na_own cerise_nais ⊤) -∗
       WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}) -∗
    WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
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
    PC ↦ₚ stats_pcc stats_release_addr -∗
    registers_pointsto rmap -∗
    STATS_cgp_b ↦ₐ wlock -∗
    na_own cerise_nais (⊤ ∖ ↑Nstats) -∗
    (▷ stats_inv ∗ na_own cerise_nais (⊤ ∖ ↑Nstats) ={⊤}=∗ na_own cerise_nais ⊤) -∗
    ▷ (PC ↦ₚ lupdatePcPerm (rmap !!! cra) -∗
       registers_pointsto (<[ca1 := lword_of_word (WInt 0)]> rmap) -∗
       na_own cerise_nais ⊤ -∗
       WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}) -∗
    WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
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

  (** What the caller lends for the pointer [wptr] it passes: for a tagged
      capability, without identifier, that allows the load of [a], the cell
      [a ↦ₐ v] (the load reads it, so the caller cannot keep it); for an
      untagged capability, nothing (the load faults). *)
  Definition stats_arg_pre (wptr v : LWord) : iProp Σ :=
    match wptr with
    | MkLWord (WCap true p _ b e a) None =>
        ⌜readAllowed p = true ∧ withinBounds b e a = true ∧
         is_shadow_address a = false ∧ is_heap_cap v.(lw) = false⌝ ∗
        a ↦ₐ v
    | MkLWord (WCap false _ _ _ _ _) _ => True
    | _ => False
    end%I.

  (** What the caller gets back, with the result [wca0]: the cell and the
      loaded word, or [EINVAL] for an untagged capability. *)
  Definition stats_arg_post (wptr v wca0 : LWord) : iProp Σ :=
    match wptr with
    | MkLWord (WCap true p _ _ _ a) None => ⌜wca0 = lload_word p v⌝ ∗ a ↦ₐ v
    | MkLWord (WCap false _ _ _ _ _) _ => ⌜wca0 = WInt EINVAL⌝
    | _ => False
    end%I.

  (** [stats_read] for a known caller, with the pointer [wptr] in [ca0]:
      it returns the loaded word or [EINVAL], and 0 in [ca1]. It does not
      fault ([may_fault = false]): the handler of [stats] resumes a fault
      of the load, and the callee returns at count 2. The caller runs with
      [na_own ⊤] ([stats_read] opens [stats_inv]), and the callee's stack
      is outside the shadow table (the switcher stores the [ErrorState]
      there). *)
  Lemma stats_read_spec_known_to_known
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : LWord)
    (b_stk e_stk a_stk : Addr)
    (arg_rmap : LReg) (cstk : CSTK)
    (wptr v : LWord) :
    STATS_pcc_b ≠ b_switcher →
    disjoint_from_shadow (stk_callee_b b_stk a_stk) (stk_callee_e e_stk a_stk) →
    arg_rmap !! ca0 = Some wptr →
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static ∗
    stats_static ∗
    na_inv cerise_nais Nstats stats_inv
    ⊢
    switcher_cc_specification_known_to_known_function false
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
    rewrite /stats_arg_pre.
    destruct wptr as [w π].
    destruct w as [z | [ [] p g b e a | ] | | ]; try (by iDestruct "HP" as "[]").
    - (* A tagged capability: the load succeeds *)
      destruct π as [ι|]; first by iDestruct "HP" as "[]".
      iDestruct "HP" as "[%Hload Ha]". destruct Hload as (Hread & Hbounds & Ha_shadow & Hv_heap).
      (* CLoad ca0 ca0 0 *)
      iApply (stats_read_load_spec with "[- $HPC $Hca0 $Ha $Hcode_stats]");
        [apply stats_code_bounds_layout | done | done | done | done |].
      iNext. iIntros "(HPC & Hca0 & Ha & _)".
      iDestruct ("Hregs" with "Hca0") as "Hregs".
      iApply (stats_read_release_close with "Hstatic HPC Hregs Hlock Hna Hclose").
      { intros r. rewrite lookup_insert_is_Some'. by right. }
      { by rewrite lookup_insert_ne. }
      { rewrite lookup_total_insert_ne // Hcra_take. apply jalr_target_ok_switcher_return_sentry. }
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
      iFrame "∗ %". done.
    - (* An untagged capability: the load faults, and the handler resumes it *)
      (* CLoad ca0 ca0 0 *)
      iApply (stats_read_load_untagged_spec with "[- $HPC $Hca0 $Hcode_stats]");
        first apply stats_code_bounds_layout.
      iIntros "Hca0".
      iDestruct ("Hregs" with "Hca0") as "Hregs".
      rewrite insert_id; last exact Hca0_take.
      (* The slot of the [ErrorState], below the cursor of the callee's
         stack *)
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
      rewrite (region_addrs_zeroes_split bc es ec); last solve_addr.
      rewrite (region_addrs_zeroes_split es cur ec); last solve_addr.
      iDestruct (region_pointsto_split bc ec es with "Hstk") as "[Hstk_lo Hstk]".
      { solve_addr. }
      { by rewrite /region_addrs_zeroes length_replicate. }
      iDestruct (region_pointsto_split es ec cur with "Hstk") as "[Hslot Hstk_hi]".
      { solve_addr. }
      { by rewrite /region_addrs_zeroes length_replicate. }
      iApply (stats_read_fault_safe (cstack_push frm cstk) rtake Local bc ec cur
               with "Hinv_switcher Hswitcher_static Hstatic Hregs Hcstk Hna Hclose Hlock [Hslot]").
      1-3: done.
      { by apply lookup_total_correct. }
      { rewrite Hcra_take. apply jalr_target_ok_switcher_return_sentry. }
      { rewrite /ErrorState_size. solve_addr. }
      { done. }
      { apply (disjoint_from_shadow_weaken bc ec es cur); [done | done | exact Hstk_shadow]. }
      1-3: done.
      { rewrite /error_state_area Hcsp_take /=. iExists _. iFrame "Hslot".
        iPureIntro. rewrite /region_addrs_zeroes length_replicate /finz.dist.
        rewrite /ErrorState_size. solve_addr. }
      (* The installed context released the lock: the return, at count 2 *)
      iNext. iIntros "HPC Hregs Harea Hcstk Hna".
      rewrite /error_state_area Hcsp_take /=.
      iDestruct "Harea" as (ws) "[%Hws Hslot]".
      iDestruct (region_pointsto_split es ec cur with "[$Hslot $Hstk_hi]") as "Hstk".
      { solve_addr. }
      { rewrite Hws /finz.dist /ErrorState_size. solve_addr. }
      iDestruct (region_pointsto_split bc ec es with "[$Hstk_lo $Hstk]") as "Hstk".
      { solve_addr. }
      { by rewrite /region_addrs_zeroes length_replicate. }
      rewrite /stats_resumed_regs.
      iDestruct (registers_pointsto_switcher_return with "Hregs") as (rmap_ret)
        "(%Hdom_ret & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp & Hca0 & Hca1 & Hrmap)".
      { intros r. rewrite !lookup_insert_is_Some'. by right; right; right. }
      set (M := <[ca1:=lword_of_word (WInt 0)]> (<[ca0:=lword_of_word (WInt EINVAL)]>
                  (<[cnull:=lword_of_word (WInt 0)]> rtake))).
      assert (M !!! ca0 = lword_of_word (WInt EINVAL)) as Hret_ca0.
      { rewrite /M lookup_total_alt. by simplify_map_eq. }
      assert (M !!! ca1 = lword_of_word (WInt 0)) as Hret_ca1.
      { rewrite /M lookup_total_alt. by simplify_map_eq. }
      assert (M !!! csp = lword_of_word (callee_csp b_stk e_stk a_stk)) as Hret_csp.
      { rewrite /M -Hcsp_take !lookup_total_alt. by simplify_map_eq. }
      iEval (rewrite Hcra_take /=) in "HPC".
      iEval (rewrite Hret_csp) in "Hcsp".
      iEval (rewrite Hret_ca0) in "Hca0".
      iEval (rewrite Hret_ca1) in "Hca1".
      iApply ("Hret" $! 2%Z _ _ rmap_ret with "[- ]").
      iFrame "∗ %". done.
  Qed.

End Error_Handling_Read.
