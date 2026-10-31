From iris.proofmode Require Import proofmode.
From griotte Require Import logrel rules.
From griotte Require Import
  world_interp_revocation wp_rules_interp interp_weakening.
From griotte Require Import switcher_base switcher_base_ktk.
From griotte Require Import
  error_handling_spec_states error_handling_spec_main_blocks_1 error_handling_spec_main_blocks_2
  error_handling_spec_main_blocks_3 error_handling_spec_handler error_handling_spec_read.
From griotte Require Import map_simpl register_tactics proofmode.

(** * The specification of [main]

    [main] calls the adversary [adv] through the switcher, as an unknown
    callee ([switcher_cc_specification]). It then calls [stats_read] three
    times, as a known callee ([stats_read_spec_known_to_known]):
    - with the capability of [x] one past its end, lent with
      [x ↦ₐ X_INIT]: the load faults, the handler moves the address to the
      base and retries the load, and [main] asserts that it returned
      [X_INIT];
    - with the untagged capability of [x]: the load faults, the handler
      unwinds, and [main] asserts that it returned [ECOMPARTMENTFAIL];
    - with the capability of [x]: [main] asserts that it returned
      [X_INIT].
    Each call to [stats_read] may also return [ENOTENOUGHTRUSTEDSTACK], on
    which [main] returns: the thread exits.

    The asserts do not depend on [adv]: whenever [adv] runs, the invariant
    [stats_inv] of [stats] is closed, so the lock is free when [main] calls
    [stats_read], and the handler releases the lock before it unwinds. *)

Section Error_Handling_Main_Spec.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
    {statslayout : statsLayout} {statslayoutWf : statsLayoutWf}
  .

  Context {C : CmptName}.

  (** The call stack of a thread that starts in [main], with the stack
      [b, e) and the export table word [w] *)
  #[local] Notation main_entry_cstack b e w :=
    (entry_cstack {| tf_csp := Cap RWL Local b e (stk_start_a b e);
                     tf_export_tbl := w;
                     tf_error_count := 0 |}) (only parsing).

  (** The import cells of [main], from its persistent import table. *)
  Lemma error_handling_main_imports_pointsto (pc_b pc_a : Addr) (adv_f : Sealable) :
    (pc_b + length (error_handling_main_imports adv_f))%a = Some pc_a ->
    [[ pc_b, pc_a ]] ↦ₐ□ [[ lword_of_word <$> error_handling_main_imports adv_f ]]
    ⊢
    pc_b ↦ₐ□ switcher_entry_call ∗
    (pc_b ^+ 1) ↦ₐ□ assert_entry ∗
    (pc_b ^+ 2) ↦ₐ□ WSealed ot_switcher adv_f ∗
    (pc_b ^+ 3) ↦ₐ□ WSealed ot_switcher (STATS_read Global).
  Proof.
    intros Himports.
    rewrite /error_handling_main_imports /= in Himports.
    rewrite /region_pointsto_pers /error_handling_main_imports !fmap_cons fmap_nil.
    rewrite (finz_seq_between_cons pc_b); last solve_addr.
    rewrite (finz_seq_between_cons (pc_b ^+ 1)); last solve_addr.
    rewrite (finz_seq_between_cons (pc_b ^+ 1 ^+ 1)); last solve_addr.
    rewrite (finz_seq_between_cons (pc_b ^+ 1 ^+ 1 ^+ 1)); last solve_addr.
    assert (pc_b ^+ 1 ^+ 1 = pc_b ^+ 2) as -> by solve_addr.
    assert (pc_b ^+ 2 ^+ 1 = pc_b ^+ 3) as -> by solve_addr.
    iIntros "($ & $ & $ & $ & _)".
  Qed.

  (** The arguments of the call to [adv]: none, all registers zero. *)
  Definition main_adv_arg_rmap : LReg :=
    {[ ca0 := lword_of_word (WInt 0);
       ca1 := lword_of_word (WInt 0);
       ca2 := lword_of_word (WInt 0);
       ca3 := lword_of_word (WInt 0);
       ca4 := lword_of_word (WInt 0);
       ca5 := lword_of_word (WInt 0);
       ct0 := lword_of_word (WInt 0) ]}.

  Lemma main_adv_arg_rmap_is_arg : is_arg_rmap main_adv_arg_rmap 8.
  Proof. by rewrite /is_arg_rmap /main_adv_arg_rmap. Qed.

  Lemma main_adv_arg_rmap_resources (W : WORLD) :
    ca0 ↦ᵣ[th] WInt 0 ∗
    ca1 ↦ᵣ[th] WInt 0 ∗
    ca2 ↦ᵣ[th] WInt 0 ∗
    ca3 ↦ᵣ[th] WInt 0 ∗
    ca4 ↦ᵣ[th] WInt 0 ∗
    ca5 ↦ᵣ[th] WInt 0 ∗
    ct0 ↦ᵣ[th] WInt 0 -∗
    [∗ map] rarg ↦ warg ∈ main_adv_arg_rmap, rarg ↦ᵣ[th] warg ∗ interp W C warg.
  Proof.
    iIntros "(Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & Hct0)".
    iAssert (interp W C (WInt 0)) as "#Hint"; first iApply interp_int.
    rewrite /main_adv_arg_rmap.
    repeat (iApply big_sepM_insert; [done | iFrame "∗#"]).
    done.
  Qed.

  (** A call of [main] to [stats_read], from the entry point of the
      switcher, with the pointer [wptr] in [ca0], lending
      [stats_arg_pre wptr v]. The call returns to [a_ret] with [main]'s
      [cgp], either with the result of [stats_read] and
      [stats_arg_post wptr v], or with [ENOTENOUGHTRUSTEDSTACK] and
      [stats_arg_pre wptr v] back. *)
  Lemma main_read_call_spec
    (pc_b pc_e a_ret csp_b csp_e : Addr) (mie : InterruptStatus)
    (wcgp wcs0 wcs1 wptr wca1 v : LWord) (rmap : LReg)
    (stk_mem : list LWord) (cstk : CSTK) :
    STATS_pcc_b ≠ b_switcher ->
    is_heap_address pc_b = false ->
    is_heap_cap wcgp.(lw) = false ->
    is_heap_cap wcs0.(lw) = false ->
    disjoint_from_mmio csp_b csp_e ->
    disjoint_from_heap csp_b csp_e ->
    (csp_b + SpillSlot_size + 2 * StackEntry_reserved_space + stats_read_min_stack <= csp_e)%Z ->
    dom rmap = all_registers_s ∖ {[ cgp; cra; csp; ct1; ca0; ca1; cs0; cs1 ]} ->
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static ∗
    stats_static ∗
    na_inv (tpool th) Nstats stats_inv ∗
    na_own (tpool th) ⊤ ∗
    PC ↦ₚ[th] Cap XSRW_ Local b_switcher e_switcher a_switcher_call ∗
    cgp ↦ᵣ[th] wcgp ∗
    cra ↦ᵣ[th] Sentry (ret_kind mie) RX Global pc_b pc_e a_ret ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    csp ↦ᵣ[th] Cap RWL Local csp_b csp_e (stk_start_a csp_b csp_e) ∗
    ct1 ↦ᵣ[th] WSealed ot_switcher (STATS_read Global) ∗
    ca0 ↦ᵣ[th] wptr ∗
    ca1 ↦ᵣ[th] wca1 ∗
    regs[th] rmap ∗
    [[ csp_b, stk_start_a csp_b csp_e ]] ↦ₐ [[ stk_mem ]] ∗
    ◯(CSTK)[th] cstk ∗
    stats_arg_pre wptr v ∗
    ▷ (∀ (wca0 : LWord) (rmap_ret : LReg) (stk_mem' : list LWord) (rcs1 : LWord),
        ⌜dom rmap_ret = all_registers_s ∖ {[ cgp; cra; csp; ca0; ca1; cs0; cs1 ]}⌝ ∗
        na_own (tpool th) ⊤ ∗
        PC ↦ₚ[th] Cap RX Global pc_b pc_e a_ret ∗
        cgp ↦ᵣ[th] wcgp ∗
        cra ↦ᵣ[th] Sentry (ret_kind mie) RX Global pc_b pc_e a_ret ∗
        cs0 ↦ᵣ[th] wcs0 ∗
        cs1 ↦ᵣ[th] rcs1 ∗
        csp ↦ᵣ[th] Cap RWL Local csp_b csp_e (stk_start_a csp_b csp_e) ∗
        ca0 ↦ᵣ[th] wca0 ∗
        ca1 ↦ᵣ[th] WInt 0 ∗
        regs₀[th] rmap_ret ∗
        [[ csp_b, stk_start_a csp_b csp_e ]] ↦ₐ [[ stk_mem' ]] ∗
        ◯(CSTK)[th] cstk ∗
        (stats_arg_post wptr v wca0 ∨
         ⌜wca0 = WInt ENOTENOUGHTRUSTEDSTACK⌝ ∗ stats_arg_pre wptr v)
        -∗ safe[th])
    ⊢ safe[th].
  Proof.
    iIntros (Hswitcher Hpc_nonheap Hcgp_nonheap Hcs0_nonheap Hstk_mmio Hstk_heap Hstk_min
               Hdom_rmap)
      "(#Hinv_switcher & #Hswitcher_static & #Hstats_static & #Hinv_stats
      & Hna & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp & Hct1 & Hca0 & Hca1 & Hrmap
      & Hstk & Hcstk & HP & Hpost)".
    iDestruct (stats_arg_pre_cap with "HP") as "[%Hwptr_cap HP]".
    iExtractList "Hrmap" [ca2; ca3; ca4; ca5; ct0] as ["Hca2"; "Hca3"; "Hca4"; "Hca5"; "Hct0"].
    set (arg_rmap := {[ ca0 := wptr; ca1 := wca1; ca2 := wca2; ca3 := wca3; ca4 := wca4;
                        ca5 := wca5; ct0 := wct0 ]} : LReg).
    iAssert ([∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg)%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hargs".
    { subst arg_rmap. repeat (iApply big_sepM_insert; [done | iFrame]). done. }
    iPoseProof (stats_read_spec_known_to_known wcgp
                  (Sentry (ret_kind mie) RX Global pc_b pc_e a_ret)
                  wcs0 wcs1 csp_b csp_e (stk_start_a csp_b csp_e) arg_rmap cstk wptr v
                 with "[$Hinv_switcher $Hswitcher_static $Hstats_static $Hinv_stats]")
      as "Hread"; [done | | done |].
    { eapply disjoint_from_shadow_weaken;
        [| | exact (disjoint_from_mmio_shadow _ _ Hstk_mmio)];
        rewrite /stk_callee_b /stk_callee_e /stk_start_a /SpillSlot_size
          /StackEntry_reserved_space /stats_read_min_stack in Hstk_min |- *;
        solve_addr+Hstk_min. }
    iPoseProof "Hstats_static" as "Hstats_static'". iNamed "Hstats_static'".
    pose proof stats_exp_tbl_size as Hstats_exp_tbl_size.
    rewrite /length_stats_exports_tbl /stats_nb_exports in Hstats_exp_tbl_size.
    assert (∀ a, a ∈ₐ [b_stats_exp_tbl, e_stats_exp_tbl) → is_shadow_address a = false)
      as Hexport_shadow.
    { intros a Ha. eapply disjoint_from_shadow_not_in;
        [exact stats_exp_tbl_disjoint_from_shadow | by apply withinBounds_true_iff]. }
    iApply (switcher_cc_specification_known_to_known_end_to_end
              _ _ wcs0 wcs1 csp_b csp_e (stk_start_a csp_b csp_e) stk_mem arg_rmap _ cstk
              stats_read_nargs stats_read_min_stack ⊤
              b_stats_exp_tbl stats_read_exp_tbl_addr e_stats_exp_tbl
              STATS_pcc_b STATS_pcc_e STATS_cgp_b STATS_cgp_e
              stats_read_pcc_off InterruptDisabled (stats_may_fault wptr)
             with "[$Hinv_switcher $Hswitcher_static $Htbl_pcc $Htbl_cgp $Htbl_read
                 $Hna $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1
                 $Hargs $Hrmap $Hstk $Hcstk $Hread $HP Hpost]").
    all: [> exact Hstk_heap | exact Hstk_mmio
      | apply stk_start_cursor_ok;
        rewrite /SpillSlot_size /StackEntry_reserved_space in Hstk_min |- *;
        solve_addr+Hstk_min
      | apply Hexport_shadow;
        rewrite /stats_read_exp_tbl_addr /stats_read_exp_tbl_off /stats_entry_read;
        solve_addr+Hstats_exp_tbl_size
      | apply Hexport_shadow; solve_addr+Hstats_exp_tbl_size
      | apply Hexport_shadow; solve_addr+Hstats_exp_tbl_size
      | exact stats_exp_tbl_disjoint_from_shadow
      | exact STATS_pcc_base_not_heap | exact STATS_cgp_base_not_heap
      | solve_ndisj | solve_ndisj
      | rewrite /stats_read_exp_tbl_addr /stats_read_exp_tbl_off /stats_entry_read;
        solve_addr+Hstats_exp_tbl_size
      | solve_addr+Hstats_exp_tbl_size
      | rewrite /stats_read_exp_tbl_addr /stats_read_exp_tbl_off /stats_entry_read;
        solve_addr+Hstats_exp_tbl_size
      | rewrite /stats_read_nargs; lia
      | pose proof STATS_size_imports as Himports_size;
        pose proof STATS_size_code as Hcode_size;
        rewrite stats_read_pcc_off_eq; solve_addr
      | apply stk_start_callee_fits;
        rewrite /stats_read_min_stack /SpillSlot_size /StackEntry_reserved_space in Hstk_min |- *;
        solve_addr+Hstk_min
      | rewrite !dom_delete_L Hdom_rmap /dom_arg_rmap /=; set_solver+
      | done
      | destruct mie; reflexivity
      | rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=; reflexivity
      | ].
    iIntros "!> Hcases".
    destruct (stats_may_fault wptr) eqn:Hmf.
    - (* The callee may fault: an untagged pointer *)
      iDestruct "Hcases" as "[@|[@|@] ]";
        destruct Hrestored as (Hrcgp & Hrcra & Hrcs0 & _);
        (apply load_heap_nonheap in Hrcgp; last exact Hcgp_nonheap);
        (apply load_heap_nonheap in Hrcra;
         last (rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=;
               reflexivity));
        (apply load_heap_nonheap in Hrcs0; last exact Hcs0_nonheap);
        subst rcgp rcra rcs0;
        iEval (rewrite /lupdatePcPerm /lift_word /=) in "HPC".
      + iDestruct "HQ" as "[-> HQ]".
        iApply ("Hpost" with "[$Hna $HPC $Hcgp $Hcra $Hcs0 $Hcs1 $Hcsp $Hca0 $Hca1 $Hrmap $Hstk
                  $Hcstk $HQ]").
        iPureIntro. rewrite Hdom_rmap_ret. set_solver+.
      + iApply ("Hpost" with "[$Hna $HPC $Hcgp $Hcra $Hcs0 $Hcs1 $Hcsp $Hca0 $Hca1 $Hrmap $Hstk
                  $Hcstk HP]").
        iSplit; first done.
        iRight. by iFrame.
      + (* The callee faulted: [ECOMPARTMENTFAIL] *)
        destruct Hwptr_cap as (t & p & g & b & e & a & π & ->).
        destruct t; first done.
        iApply ("Hpost" with "[$Hna $HPC $Hcgp $Hcra $Hcs0 $Hcs1 $Hcsp $Hca0 $Hca1 $Hrmap $Hstk
                  $Hcstk]").
        iSplit; first done.
        by iLeft.
    - iDestruct "Hcases" as "[@|@]";
        destruct Hrestored as (Hrcgp & Hrcra & Hrcs0 & _);
        (apply load_heap_nonheap in Hrcgp; last exact Hcgp_nonheap);
        (apply load_heap_nonheap in Hrcra;
         last (rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=;
               reflexivity));
        (apply load_heap_nonheap in Hrcs0; last exact Hcs0_nonheap);
        subst rcgp rcra rcs0;
        iEval (rewrite /lupdatePcPerm /lift_word /=) in "HPC".
      + iDestruct "HQ" as "[-> HQ]".
        iApply ("Hpost" with "[$Hna $HPC $Hcgp $Hcra $Hcs0 $Hcs1 $Hcsp $Hca0 $Hca1 $Hrmap $Hstk
                  $Hcstk $HQ]").
        iPureIntro. rewrite Hdom_rmap_ret. set_solver+.
      + iApply ("Hpost" with "[$Hna $HPC $Hcgp $Hcra $Hcs0 $Hcs1 $Hcsp $Hca0 $Hca1 $Hrmap $Hstk
                  $Hcstk HP]").
        iSplit; first done.
        iRight. by iFrame.
  Qed.

  (** The third call to [stats_read], with the capability of [x], its
      assert, and the return: from [.Lmain_arg_3]. *)
  Lemma main_read_3_phase_spec
    (pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e : Addr)
    (wca0 wca1 wcra wcs1 : LWord) (rmap : LReg)
    (stk_mem : list LWord) (cstk : CSTK) :
    STATS_pcc_b ≠ b_switcher ->
    main_code_bounds pc_b pc_e pc_a ->
    cstk.(cstk_frames) = [] ->
    (cgp_b + 1)%a = Some cgp_e ->
    is_heap_address cgp_b = false ->
    is_shadow_address cgp_b = false ->
    disjoint_from_mmio csp_b csp_e ->
    disjoint_from_heap csp_b csp_e ->
    (csp_b + SpillSlot_size + 2 * StackEntry_reserved_space + stats_read_min_stack <= csp_e)%Z ->
    dom rmap = all_registers_s ∖ {[ cgp; cra; csp; ca0; ca1; cs0; cs1 ]} ->
    assert_static b_assert e_assert a_flag ∗
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static ∗
    stats_static ∗
    na_inv (tpool th) Nstats stats_inv ∗
    na_own (tpool th) ⊤ ∗
    PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ main_label_offset ".Lmain_arg_3")%a ∗
    cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e cgp_b ∗
    cra ↦ᵣ[th] wcra ∗
    cs0 ↦ᵣ[th] thread_return_sentry ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    csp ↦ᵣ[th] Cap RWL Local csp_b csp_e (stk_start_a csp_b csp_e) ∗
    ca0 ↦ᵣ[th] wca0 ∗
    ca1 ↦ᵣ[th] wca1 ∗
    regs[th] rmap ∗
    [[ csp_b, stk_start_a csp_b csp_e ]] ↦ₐ [[ stk_mem ]] ∗
    ◯(CSTK)[th] cstk ∗
    cgp_b ↦ₐ WInt X_INIT ∗
    pc_b ↦ₐ□ switcher_entry_call ∗
    (pc_b ^+ 1) ↦ₐ□ assert_entry ∗
    (pc_b ^+ 3) ↦ₐ□ WSealed ot_switcher (STATS_read Global) ∗
    codefrag_pers pc_a error_handling_main_code
    ⊢ safe[th].
  Proof.
    iIntros (Hswitcher Hbounds Hframes Hcgp_size Hcgp_nonheap Hcgp_shadow
               Hstk_mmio Hstk_heap Hstk_min Hdom_rmap)
      "(#Hassert & #Hinv_switcher & #Hswitcher_static & #Hstats_static & #Hinv_stats
      & Hna & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp & Hca0 & Hca1 & Hrmap & Hstk & Hcstk & Hx
      & #Himport_switcher & #Himport_assert & #Himport_read & #Hcode_main)".
    pose proof Hbounds as (HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap).

    (* Blocks 15-18: the capability of [x] in [ca0], and the jump to the switcher *)
    iExtractList "Hrmap" [ctp; ct1] as ["Hctp"; "Hct1"].
    iApply (main_call_read_3_spec with
             "[- $HPC $Hcgp $Hca0 $Hctp $Hct1 $Hcra $Himport_switcher $Himport_read $Hcode_main]");
      first exact Hbounds.
    iIntros "!>" (mie) "(HPC & Hcgp & Hca0 & Hctp & Hct1 & Hcra & _)".

    iInsertList "Hrmap" [ctp].

    (* The call to [stats_read], known to [main], lending [x] *)
    iApply (main_read_call_spec pc_b pc_e _ csp_b csp_e mie _ thread_return_sentry wcs1 _ wca1
              (WInt X_INIT)
             with "[$Hinv_switcher $Hswitcher_static $Hstats_static $Hinv_stats $Hna $HPC
                    $Hcgp $Hcra $Hcs0 $Hcs1 $Hcsp $Hct1 $Hca0 $Hca1 $Hrmap $Hstk $Hcstk Hx]");
      [done | done | | exact thread_return_sentry_not_heap | done | done | done | |].
    { by rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hcgp_nonheap. }
    { rewrite dom_insert_L dom_delete_L Hdom_rmap.
      pose proof (all_registers_s_correct ctp). set_solver. }
    iSplitL "Hx".
    { rewrite /stats_arg_pre /= /stats_read_addr.
      rewrite (_ : withinBounds cgp_b cgp_e cgp_b = true);
        last (apply withinBounds_true_iff; solve_addr+Hcgp_size).
      iFrame "Hx". iPureIntro.
      split_and!; [done | solve_addr+Hcgp_size | done | done | done]. }
    iIntros "!>" (wret rmap_ret stk_mem' rcs1)
      "(%Hdom_rmap_ret & Hna & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp & Hca0 & Hca1
      & Hrmap & Hstk & Hcstk & Hret)".
    iExtractList "Hrmap" [ctp; ct0; ct1; ct2; ca2]
      as ["[Hctp _]"; "[Hct0 _]"; "[Hct1 _]"; "[Hct2 _]"; "[Hca2 _]"].
    iDestruct "Hret" as "[ [-> _] | [-> _] ]".
    - (* Blocks 19-21: the assert of [X_INIT], and the return *)
      iApply (main_check_3_spec _ _ _ X_INIT with
               "[- $Hassert $Hinv_switcher $Hswitcher_static $Hna $HPC $Hca0 $Hctp $Hct0 $Hct1
                 $Hct2 $Hca2 $Hcra $Hcs0 $Hcstk $Himport_assert $Hcode_main]");
        [exact Hbounds | by right | exact Hframes].
    - (* Block 19: the trusted stack is exhausted, return *)
      iApply (main_check_3_spec with
               "[- $Hassert $Hinv_switcher $Hswitcher_static $Hna $HPC $Hca0 $Hctp $Hct0 $Hct1
                 $Hct2 $Hca2 $Hcra $Hcs0 $Hcstk $Himport_assert $Hcode_main]");
        [exact Hbounds | by left | exact Hframes].
  Qed.

  (** The second call to [stats_read], with the untagged capability of [x],
      which the handler unwinds, and its assert: from [.Lmain_arg_2]. *)
  Lemma main_read_2_phase_spec
    (pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e : Addr)
    (wca0 wca1 wcra wcs1 : LWord) (rmap : LReg)
    (stk_mem : list LWord) (cstk : CSTK) :
    STATS_pcc_b ≠ b_switcher ->
    main_code_bounds pc_b pc_e pc_a ->
    cstk.(cstk_frames) = [] ->
    (cgp_b + 1)%a = Some cgp_e ->
    is_heap_address cgp_b = false ->
    is_shadow_address cgp_b = false ->
    disjoint_from_mmio csp_b csp_e ->
    disjoint_from_heap csp_b csp_e ->
    (csp_b + SpillSlot_size + 2 * StackEntry_reserved_space + stats_read_min_stack <= csp_e)%Z ->
    dom rmap = all_registers_s ∖ {[ cgp; cra; csp; ca0; ca1; cs0; cs1 ]} ->
    assert_static b_assert e_assert a_flag ∗
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static ∗
    stats_static ∗
    na_inv (tpool th) Nstats stats_inv ∗
    na_own (tpool th) ⊤ ∗
    PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ main_label_offset ".Lmain_arg_2")%a ∗
    cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e cgp_b ∗
    cra ↦ᵣ[th] wcra ∗
    cs0 ↦ᵣ[th] thread_return_sentry ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    csp ↦ᵣ[th] Cap RWL Local csp_b csp_e (stk_start_a csp_b csp_e) ∗
    ca0 ↦ᵣ[th] wca0 ∗
    ca1 ↦ᵣ[th] wca1 ∗
    regs[th] rmap ∗
    [[ csp_b, stk_start_a csp_b csp_e ]] ↦ₐ [[ stk_mem ]] ∗
    ◯(CSTK)[th] cstk ∗
    cgp_b ↦ₐ WInt X_INIT ∗
    pc_b ↦ₐ□ switcher_entry_call ∗
    (pc_b ^+ 1) ↦ₐ□ assert_entry ∗
    (pc_b ^+ 3) ↦ₐ□ WSealed ot_switcher (STATS_read Global) ∗
    codefrag_pers pc_a error_handling_main_code
    ⊢ safe[th].
  Proof.
    iIntros (Hswitcher Hbounds Hframes Hcgp_size Hcgp_nonheap Hcgp_shadow
               Hstk_mmio Hstk_heap Hstk_min Hdom_rmap)
      "(#Hassert & #Hinv_switcher & #Hswitcher_static & #Hstats_static & #Hinv_stats
      & Hna & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp & Hca0 & Hca1 & Hrmap & Hstk & Hcstk & Hx
      & #Himport_switcher & #Himport_assert & #Himport_read & #Hcode_main)".
    pose proof Hbounds as (HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap).

    (* Blocks 9-12: the untagged capability of [x] in [ca0], and the jump to
       the switcher *)
    iExtractList "Hrmap" [ctp; ct1] as ["Hctp"; "Hct1"].
    iApply (main_call_read_2_spec with
             "[- $HPC $Hcgp $Hca0 $Hctp $Hct1 $Hcra $Himport_switcher $Himport_read $Hcode_main]");
      first exact Hbounds.
    iIntros "!>" (mie) "(HPC & Hcgp & Hca0 & Hctp & Hct1 & Hcra & _)".
    iInsertList "Hrmap" [ctp].

    (* The call to [stats_read], known to [main]: the load faults, and the
       handler of [stats] unwinds it *)
    iApply (main_read_call_spec pc_b pc_e _ csp_b csp_e mie _ thread_return_sentry wcs1 _ wca1
              (WInt 0)
             with "[$Hinv_switcher $Hswitcher_static $Hstats_static $Hinv_stats $Hna $HPC
                    $Hcgp $Hcra $Hcs0 $Hcs1 $Hcsp $Hct1 $Hca0 $Hca1 $Hrmap $Hstk $Hcstk Hx]");
      [done | done | | exact thread_return_sentry_not_heap | done | done | done | |].
    { by rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hcgp_nonheap. }
    { rewrite dom_insert_L dom_delete_L Hdom_rmap.
      pose proof (all_registers_s_correct ctp). set_solver. }
    iSplitR; first by rewrite /stats_arg_pre.
    iIntros "!>" (wret rmap_ret stk_mem' rcs1)
      "(%Hdom_rmap_ret & Hna & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp & Hca0 & Hca1
      & Hrmap & Hstk & Hcstk & Hret)".
    iAssert (⌜∃ z : Z, wret = WInt z ∧ (z = ENOTENOUGHTRUSTEDSTACK ∨ z = ECOMPARTMENTFAIL)⌝)%I
      with "[Hret]" as %(z & -> & Hz).
    { iDestruct "Hret" as "[%Hwret | [%Hwret _] ]"; iPureIntro; eexists;
        (split; first exact Hwret); [right | left]; done. }
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iExtractList "Hrmap" [ctp; ct0; ct1; ct2; ca2] as ["Hctp"; "Hct0"; "Hct1"; "Hct2"; "Hca2"].

    (* Blocks 13-14: return on trusted-stack exhaustion, and the assert of
       [ECOMPARTMENTFAIL] *)
    iApply (main_check_2_spec _ _ _ z with
             "[- $Hassert $Hinv_switcher $Hswitcher_static $Hna $HPC $Hca0 $Hctp $Hct0 $Hct1
               $Hct2 $Hca2 $Hcra $Hcs0 $Hcstk $Himport_assert $Hcode_main]");
      [exact Hbounds | exact Hz | exact Hframes |].
    iIntros "!> (Hna & HPC & Hca0 & Hct0 & Hct1 & Hct2 & Hca2 & Hcra & Hctp & Hcs0 & Hcstk
                & _)".
    iInsertList "Hrmap" [ctp; ct0; ct1; ct2; ca2].

    (* Blocks 15-21 *)
    iApply (main_read_3_phase_spec with
             "[$Hassert $Hinv_switcher $Hswitcher_static $Hstats_static $Hinv_stats $Hna $HPC
               $Hcgp $Hcra $Hcs0 $Hcs1 $Hcsp $Hca0 $Hca1 $Hrmap $Hstk $Hcstk $Hx
               $Himport_switcher $Himport_assert $Himport_read $Hcode_main]"); try done.
    rewrite !dom_insert_L Hdom_rmap_ret.
    pose proof (all_registers_s_correct ctp).
    pose proof (all_registers_s_correct ct0). pose proof (all_registers_s_correct ct1).
    pose proof (all_registers_s_correct ct2). pose proof (all_registers_s_correct ca2).
    set_solver.
  Qed.

  (** The first call to [stats_read], with the capability of [x] one past
      its end, which the handler repairs, and its assert: from
      [.Lmain_ret_adv], the return from [adv]. *)
  Lemma main_read_1_phase_spec
    (pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e : Addr)
    (wca0 wca1 wcra wcs1 : LWord) (rmap : LReg)
    (stk_mem : list LWord) (cstk : CSTK) :
    STATS_pcc_b ≠ b_switcher ->
    main_code_bounds pc_b pc_e pc_a ->
    cstk.(cstk_frames) = [] ->
    (cgp_b + 1)%a = Some cgp_e ->
    is_heap_address cgp_b = false ->
    is_shadow_address cgp_b = false ->
    disjoint_from_mmio csp_b csp_e ->
    disjoint_from_heap csp_b csp_e ->
    (csp_b + SpillSlot_size + 2 * StackEntry_reserved_space + stats_read_min_stack <= csp_e)%Z ->
    dom rmap = all_registers_s ∖ {[ cgp; cra; csp; ca0; ca1; cs0; cs1 ]} ->
    assert_static b_assert e_assert a_flag ∗
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static ∗
    stats_static ∗
    na_inv (tpool th) Nstats stats_inv ∗
    na_own (tpool th) ⊤ ∗
    PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ main_label_offset ".Lmain_ret_adv")%a ∗
    cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e cgp_b ∗
    cra ↦ᵣ[th] wcra ∗
    cs0 ↦ᵣ[th] thread_return_sentry ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    csp ↦ᵣ[th] Cap RWL Local csp_b csp_e (stk_start_a csp_b csp_e) ∗
    ca0 ↦ᵣ[th] wca0 ∗
    ca1 ↦ᵣ[th] wca1 ∗
    regs[th] rmap ∗
    [[ csp_b, stk_start_a csp_b csp_e ]] ↦ₐ [[ stk_mem ]] ∗
    ◯(CSTK)[th] cstk ∗
    cgp_b ↦ₐ WInt X_INIT ∗
    pc_b ↦ₐ□ switcher_entry_call ∗
    (pc_b ^+ 1) ↦ₐ□ assert_entry ∗
    (pc_b ^+ 3) ↦ₐ□ WSealed ot_switcher (STATS_read Global) ∗
    codefrag_pers pc_a error_handling_main_code
    ⊢ safe[th].
  Proof.
    iIntros (Hswitcher Hbounds Hframes Hcgp_size Hcgp_nonheap Hcgp_shadow
               Hstk_mmio Hstk_heap Hstk_min Hdom_rmap)
      "(#Hassert & #Hinv_switcher & #Hswitcher_static & #Hstats_static & #Hinv_stats
      & Hna & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp & Hca0 & Hca1 & Hrmap & Hstk & Hcstk & Hx
      & #Himport_switcher & #Himport_assert & #Himport_read & #Hcode_main)".
    pose proof Hbounds as (HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap).

    (* Blocks 3-6: the capability of [x] one past its end in [ca0], and the jump
       to the switcher *)
    iExtractList "Hrmap" [ctp; ct1] as ["Hctp"; "Hct1"].
    iApply (main_call_read_1_spec with
             "[- $HPC $Hcgp $Hca0 $Hctp $Hct1 $Hcra $Himport_switcher $Himport_read $Hcode_main]");
      [exact Hbounds | exact Hcgp_size |].
    iIntros "!>" (mie) "(HPC & Hcgp & Hca0 & Hctp & Hct1 & Hcra & _)".

    iInsertList "Hrmap" [ctp].

    (* The call to [stats_read], known to [main], lending [x] *)
    iApply (main_read_call_spec pc_b pc_e _ csp_b csp_e mie _ thread_return_sentry wcs1 _ wca1
              (WInt X_INIT)
             with "[$Hinv_switcher $Hswitcher_static $Hstats_static $Hinv_stats $Hna $HPC
                    $Hcgp $Hcra $Hcs0 $Hcs1 $Hcsp $Hct1 $Hca0 $Hca1 $Hrmap $Hstk $Hcstk Hx]");
      [done | done | | exact thread_return_sentry_not_heap | done | done | done | |].
    { by rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hcgp_nonheap. }
    { rewrite dom_insert_L dom_delete_L Hdom_rmap.
      pose proof (all_registers_s_correct ctp). set_solver. }
    iSplitL "Hx".
    { rewrite /stats_arg_pre /= /stats_read_addr.
      rewrite (_ : withinBounds cgp_b cgp_e cgp_e = false);
        last (apply not_true_iff_false; rewrite withinBounds_true_iff; solve_addr+Hcgp_size).
      iFrame "Hx". iPureIntro.
      split_and!; [done | solve_addr+Hcgp_size | done | done | done]. }
    iIntros "!>" (wret rmap_ret stk_mem' rcs1)
      "(%Hdom_rmap_ret & Hna & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp & Hca0 & Hca1
      & Hrmap & Hstk & Hcstk & Hret)".
    iAssert (⌜∃ z : Z, wret = WInt z ∧ (z = ENOTENOUGHTRUSTEDSTACK ∨ z = X_INIT)⌝ ∗
             cgp_b ↦ₐ WInt X_INIT)%I
      with "[Hret]" as "[%Hz Hx]".
    { rewrite /stats_arg_post /= /stats_read_addr.
      rewrite (_ : withinBounds cgp_b cgp_e cgp_e = false);
        last (apply not_true_iff_false; rewrite withinBounds_true_iff; solve_addr+Hcgp_size).
      iDestruct "Hret" as "[ [-> Hx] | [-> [_ Hx] ] ]"; iFrame "Hx"; iPureIntro; eexists;
        (split; first done); [right | left]; done. }
    destruct Hz as (z & -> & Hz).
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iExtractList "Hrmap" [ctp; ct0; ct1; ct2; ca2] as ["Hctp"; "Hct0"; "Hct1"; "Hct2"; "Hca2"].

    (* Blocks 7-8: return on trusted-stack exhaustion, and the assert of
       [X_INIT] *)
    iApply (main_check_1_spec _ _ _ z with
             "[- $Hassert $Hinv_switcher $Hswitcher_static $Hna $HPC $Hca0 $Hctp $Hct0 $Hct1
               $Hct2 $Hca2 $Hcra $Hcs0 $Hcstk $Himport_assert $Hcode_main]");
      [exact Hbounds | exact Hz | exact Hframes |].
    iIntros "!> (Hna & HPC & Hca0 & Hct0 & Hct1 & Hct2 & Hca2 & Hcra & Hctp & Hcs0 & Hcstk
                & _)".
    iInsertList "Hrmap" [ctp; ct0; ct1; ct2; ca2].

    (* Blocks 9-21 *)
    iApply (main_read_2_phase_spec with
             "[$Hassert $Hinv_switcher $Hswitcher_static $Hstats_static $Hinv_stats $Hna $HPC
               $Hcgp $Hcra $Hcs0 $Hcs1 $Hcsp $Hca0 $Hca1 $Hrmap $Hstk $Hcstk $Hx
               $Himport_switcher $Himport_assert $Himport_read $Hcode_main]"); try done.
    rewrite !dom_insert_L Hdom_rmap_ret.
    pose proof (all_registers_s_correct ctp).
    pose proof (all_registers_s_correct ct0). pose proof (all_registers_s_correct ct1).
    pose proof (all_registers_s_correct ct2). pose proof (all_registers_s_correct ca2).
    set_solver.
  Qed.

  (** The specification of [main], from its entry. [main] gets the
      initial registers of the thread, cleared, its import table, its code
      and its global [x]; the world of the adversary [C], in which the
      export [adv_f] of [adv] is safe, and the stack is safe to share. *)
  Lemma error_handling_main_spec
    (pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e : Addr) (rmap : LReg)
    (adv_f : Sealable) (W0 : WORLD) (Ws : list WORLD) (Cs : list CmptName)
    (* The capability to the export table of [main], as the entry frame of
       the thread records it *)
    (w_main_tbl : LWord) :
    let imports := error_handling_main_imports adv_f in
    STATS_pcc_b ≠ b_switcher ->
    main_code_bounds pc_b pc_e pc_a ->
    (cgp_b + length error_handling_main_data)%a = Some cgp_e ->
    is_heap_address cgp_b = false ->
    is_shadow_address cgp_b = false ->
    dom rmap = all_registers_s ∖ {[ cgp; cra; csp ]} ->
    (∀ r, r ∈ dom rmap → rmap !! r = Some (lword_of_word (WInt 0))) ->
    (* The stack holds the spill of the switcher calls, the space reserved at
       the top of the callee's stack, and the minimum stack of [stats_read],
       below the space reserved at its own top *)
    (csp_b + SpillSlot_size + 2 * StackEntry_reserved_space + stats_read_min_stack <= csp_e)%Z ->
    is_heap_cap (WSealed ot_switcher adv_f) = false ->
    frame_match Ws Cs (main_entry_cstack csp_b csp_e w_main_tbl) W0 C ->
    assert_static b_assert e_assert a_flag ∗
    thread_in th C ∗
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static ∗
    stats_static ∗
    na_inv (tpool th) Nstats stats_inv ∗
    na_own (tpool th) ⊤ ∗
    (* The initial registers *)
    PC ↦ₚ[th] Cap RX Global pc_b pc_e pc_a ∗
    cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e cgp_b ∗
    csp ↦ᵣ[th] Cap RWL Local csp_b csp_e (stk_start_a csp_b csp_e) ∗
    cra ↦ᵣ[th] thread_return_sentry ∗
    regs[th] rmap ∗
    (* The memory of [main] *)
    [[ pc_b, pc_a ]] ↦ₐ□ [[ lword_of_word <$> imports ]] ∗
    codefrag_pers pc_a error_handling_main_code ∗
    [[ cgp_b, cgp_e ]] ↦ₐ [[ lword_of_word <$> error_handling_main_data ]] ∗
    (* The world of the adversary *)
    world_interp W0 C ∗
    interp_continuation (main_entry_cstack csp_b csp_e w_main_tbl) Ws Cs ∗
    ◯(CSTK)[th] (main_entry_cstack csp_b csp_e w_main_tbl) ∗
    interp W0 C (WSealed ot_switcher adv_f) ∗
    adv_f ↦ₑ□{nargs} 0 ∗
    interp W0 C (Cap RWL Local csp_b csp_e (stk_start_a csp_b csp_e))
    ⊢ safe[th].
  Proof.
    intros imports. subst imports.
    set (cstk0 := main_entry_cstack csp_b csp_e w_main_tbl).
    iIntros (Hswitcher Hbounds Hcgp_size Hcgp_nonheap Hcgp_shadow
               Hdom_rmap Hrmap_zero Hstk_min Hadv_nonheap Hframe_match)
      "(#Hassert & #Hthread & #Hinv_switcher & #Hswitcher_static & #Hstats_static & #Hinv_stats
      & Hna & HPC & Hcgp & Hcsp & Hcra & Hrmap & #Himports & #Hcode_main & Hdata
      & Hworld & HK & Hcstk & #Hinterp_adv & #Hentry_adv & #Hinterp_csp)".
    pose proof Hbounds as (HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap).
    iDestruct (error_handling_main_imports_pointsto with "Himports")
      as "(Himport_switcher & Himport_assert & Himport_adv & Himport_read)";
      first exact Himports_contiguous.
    iDestruct (region_pointsto_single with "Hdata") as (vx) "[Hx %Hvx]"; first exact Hcgp_size.
    injection Hvx as <-.

    (* Revoke the world to get the stack frame *)
    iDestruct (interp_cap_disjoint_wl with "Hinterp_csp") as %[Hstk_mmio Hstk_heap]; first done.
    iMod (world_interp_revoke_stack with "[$Hinterp_csp $Hworld]")
      as (l) "(%Hl_unk & Hworld & #Hstack_revoked_W0 & >%Hstack_revoked_W0 & >[%stk_mem Hstk]
              & [Hrevoked_l _])".
    (* The free part of the stack, below the space reserved at its top *)
    assert (csp_b + StackEntry_reserved_space <= csp_e)%Z as Hstk_res_size.
    { rewrite /SpillSlot_size /StackEntry_reserved_space /stats_read_min_stack in Hstk_min |- *.
      solve_addr+Hstk_min. }
    iDestruct (stk_start_region_split with "Hstk") as (stk_mem_free stk_res) "[Hstk _]";
      first exact Hstk_res_size.
    set (W1 := revoke W0).
    assert (related_sts_priv_world W0 W1) as Hrelated_priv_W0_W1
      by eapply revoke_related_sts_priv_world.
    iAssert (interp W1 C (WSealed ot_switcher adv_f)) as "#Hinterp_W1_adv".
    { iDestruct (switcher_static_seal_pred with "Hswitcher_static") as "#Hseal_switcher".
      iApply (monotone.interp_monotone_sd W0 W1 C with "[] Hseal_switcher Hinterp_adv").
      iPureIntro. exact Hrelated_priv_W0_W1. }
    iDestruct (StackRevokedResources_mono_priv with "Hstack_revoked_W0")
      as "Hstack_revoked_W1"; eauto.

    (* The stack is revoked in [W1] *)
    assert (revoked_addresses W1 (finz.seq_between csp_b csp_e)) as Hstack_revoked_W1.
    { rewrite /revoked_addresses Forall_forall.
      rewrite Forall_forall in Hstack_revoked_W0.
      intros a Ha; cbn in *. by apply Hstack_revoked_W0. }
    iDestruct (stk_start_revoked_split _ _ _ _ Hstk_res_size with "Hstack_revoked_W1")
      as "[Hstack_revoked_W1_free _]".
    pose proof (stk_start_revoked_addresses _ _ _ Hstk_res_size Hstack_revoked_W1)
      as Hstack_revoked_W1_free.

    (* Blocks 0-2: the jump to the switcher, to call [adv] *)
    iAssert ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜w = WInt 0⌝)%I with "[Hrmap]" as "Hrmap".
    { iApply (big_sepM_impl with "Hrmap"). iIntros "!>" (r w Hr) "$". iPureIntro.
      pose proof (elem_of_dom_2 _ _ _ Hr) as Hr_dom.
      rewrite Hrmap_zero in Hr; [by simplify_eq | done]. }
    iExtractList "Hrmap" [ctp; ct1; cs0] as ["[Hctp _]"; "[Hct1 _]"; "[Hcs0 _]"].
    iApply (main_call_adv_spec with
             "[- $HPC $Hctp $Hct1 $Hcra $Hcs0 $Himport_switcher $Himport_adv $Hcode_main]");
      [exact Hbounds | exact Hadv_nonheap |].
    iIntros "!>" (mie) "(HPC & Hctp & Hct1 & Hcra & Hcs0 & _)".

    (* The call to [adv], unknown to [main]: [stats_inv] is closed *)
    iExtractList "Hrmap" [ca0; ca1; ca2; ca3; ca4; ca5; ct0] as
      ["[Hca0 %Hwca0]"; "[Hca1 %Hwca1]"; "[Hca2 %Hwca2]"; "[Hca3 %Hwca3]"; "[Hca4 %Hwca4]";
       "[Hca5 %Hwca5]"; "[Hct0 %Hwct0]"].
    subst wca0 wca1 wca2 wca3 wca4 wca5 wct0.
    iExtractList "Hrmap" [cs1] as ["[Hcs1 _]"].
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iInsertList "Hrmap" [ctp].
    iPoseProof (main_adv_arg_rmap_resources W1 with
                 "[$Hca0 $Hca1 $Hca2 $Hca3 $Hca4 $Hca5 $Hct0]") as "Hargs".
    iApply (switcher_cc_specification W1 C _ _ _ _ csp_b csp_e (stk_start_a csp_b csp_e) adv_f
              stk_mem_free main_adv_arg_rmap _ cstk0 Ws Cs 0 with
             "[$Hthread $Hinv_switcher $Hswitcher_static $Hna $HPC $Hcgp $Hcra $Hcsp $Hct1
               $Hcs0 $Hcs1 $Hrmap $Hstk $Hworld $Hstack_revoked_W1_free $Hcstk $HK
               $Hinterp_W1_adv Hargs Hx]").
    all: [> exact Hstk_mmio | exact Hstk_heap | apply stk_start_cursor_ok, Hstk_res_size
      | rewrite dom_insert_L !dom_delete_L Hdom_rmap /dom_arg_rmap /=;
        pose proof (all_registers_s_correct ctp); set_solver
      | apply main_adv_arg_rmap_is_arg
      | destruct mie; reflexivity
      | rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=; reflexivity
      | ].
    iSplitR; first iExact "Hentry_adv".
    iSplitL "Hargs".
    { iApply (big_sepM_impl with "Hargs"). iIntros "!>" (r w Hr) "[Hr _]". iFrame. }
    iSplitR; first done.
    (* The spill of the switcher call cannot fault: the stack holds it *)
    iSplit; last (iApply switcher_cc_fault_stack_fits; apply stk_start_spill_fits;
                  rewrite /SpillSlot_size /StackEntry_reserved_space /stats_read_min_stack
                    in Hstk_min |- *;
                  solve_addr+Hstk_min).
    iIntros "!>" (W2 rmap' stk_mem' l' rcgp rcra rcs0 rcs1)
      "(_ & _ & _ & _ & _ & %Hdom_rmap' & _ & _ & Hna & _ & _ & Hcstk & HPC & Hcgp & Hcra
      & Hcs0 & Hcs1 & Hcsp & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ] & Hrmap & Hstk & _
      & %Hrestored)".
    destruct Hrestored as (Hrcgp & Hrcra & Hrcs0 & _).
    apply load_heap_nonheap in Hrcgp;
      last (rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hcgp_nonheap /=;
            reflexivity).
    apply load_heap_nonheap in Hrcra;
      last (rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=;
            reflexivity).
    apply load_heap_nonheap in Hrcs0; last exact thread_return_sentry_not_heap.
    subst rcgp rcra rcs0.
    iEval (rewrite /lupdatePcPerm /lift_word /=) in "HPC".
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".

    (* Blocks 3-21: the three calls to [stats_read], whatever [adv] did *)
    iApply (main_read_1_phase_spec with
             "[$Hassert $Hinv_switcher $Hswitcher_static $Hstats_static $Hinv_stats $Hna $HPC
               $Hcgp $Hcra $Hcs0 $Hcs1 $Hcsp $Hca0 $Hca1 $Hrmap $Hstk $Hcstk $Hx
               $Himport_switcher $Himport_assert $Himport_read $Hcode_main]"); done.
  Qed.

End Error_Handling_Main_Spec.
