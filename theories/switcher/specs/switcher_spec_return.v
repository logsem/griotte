From iris.proofmode Require Import proofmode.
From griotte Require Import logrel memory_region rules proofmode monotone.
From griotte Require Import map_simpl register_tactics.
From griotte Require Export switcher_spec_return_gen.
From griotte Require Import switcher_exception.
From griotte Require Import switcher_return_states.
From griotte.switcher.callback Require Import callback_path.

(** * Functional specification of the switcher's return routine

    [switcher_ret_specification_gen], instantiated with the trap safety of
    the switcher ([switcher_trap_safety_intro]), and the safety of a fault
    in a trusted callee without handler. *)

Section Thread_Return_Sentry.
  Context `{MP: MachineParameters} {swlayout : switcherLayout}.

  (** The switcher's return sentry, which CHERIoT's loader gives a thread in
      [cra] ([boot.cc:963-978]): interrupt-disabling, Local, at
      [switcher_after_compartment_call]. A return from the thread's entry
      through it exits the thread ([switcher_ret_thread_exit_specification]). *)
  Definition thread_return_sentry : Word :=
    WSentry RetDisable true XSRW_ Local b_switcher e_switcher a_switcher_return.

  Lemma thread_return_sentry_pc :
    lupdatePcPerm (lword_of_word thread_return_sentry) =
    lword_of_word (WCap true XSRW_ Local b_switcher e_switcher a_switcher_return).
  Proof. reflexivity. Qed.

  (** A return ([Jalr cnull cra]) accepts it. *)
  Lemma thread_return_sentry_jalr_ok :
    jalr_target_ok cnull cra thread_return_sentry = true.
  Proof. reflexivity. Qed.

  Lemma thread_return_sentry_not_heap {swlayoutwf : switcherLayoutWf} :
    is_heap_cap thread_return_sentry = false.
  Proof.
    rewrite /thread_return_sentry /is_heap_cap /heap_cap_base /memory_cap_base /=
      switcher_base_not_heap /=.
    reflexivity.
  Qed.
End Thread_Return_Sentry.

Section Switcher.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).

  Lemma switcher_ret_specification
    (W0 Wcur : WORLD)
    (C : CmptName)
    (rmap : LReg)
    (csp_e csp_b: Addr)
    (l : list LAddr)
    (stk_mem : list LWord)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (wca0 wca1 wcsp : LWord)
    :
    let Wfixed := (close_list (l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) Wcur) in
    related_sts_pub_world W0 Wfixed ->
    dom rmap = all_registers_s ∖ ({[ csp ; ca0 ; ca1 ]} ) ->
    frame_match Ws Cs cstk W0 C ->
    csp_sync cstk csp_b csp_e ->
    (* NOTE: there is only one side of the implication... *)
    NoDup (l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) ->
    (∀ a : LAddr, (std W0) !! a = Some Temporary -> a ∈ l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) ->

    (* Switcher Invariant *)
    na_inv (tpool th) Nswitcher switcher_inv
    ∗ switcher_static
    ∗ interp Wfixed C wca0
    ∗ interp Wfixed C wca1
    ∗ [[csp_b,csp_e]]↦ₐ[[stk_mem]]
    ∗ ◯(CSTK)[th] cstk
    ∗ interp_continuation cstk Ws Cs
    ∗ world_interp Wcur C
    ∗ na_own (tpool th) ⊤
    ∗ PC ↦ₚ[th] WCap true XSRW_ Local b_switcher e_switcher a_switcher_return
    ∗ ▷ RevokedResources Wfixed C l
    ∗ ([∗ map] k↦y ∈ rmap, k ↦ᵣ[th] y)
    ∗ ca0 ↦ᵣ[th] wca0
    ∗ ca1 ↦ᵣ[th] wca1
    ∗ csp ↦ᵣ[th] wcsp
    ⊢ WP Seq (Instr Executable) @[th] {{ HO th }}.
  Proof.
    intros Wfixed.
    iIntros (Hrelated_pub_W0_Wfixed Hrmap Hframe Hcsp_sync Hnodup_revoked Htemp_revoked)
      "(#Hswitcher & #Hstatic & Hres)".
    iPoseProof (switcher_trap_safety_intro with "[$Hswitcher $Hstatic]") as "#Hsafety".
    by iApply (switcher_ret_specification_gen with "[$Hsafety $Hres]").
  Qed.

  (** A return through the switcher's return entry at the thread's entry call
      stack: the switcher finds no frame to pop and goes to
      [.Lcommon_defer_irqs_and_thread_exit], and the thread exits, with the
      switcher invariant closed. Only three scratch registers are used: the
      stack, the world and the other registers are not read. *)
  Lemma switcher_ret_thread_exit_specification
    (cstk : CSTK) (wctp wct0 wct2 : LWord) :
    cstk.(cstk_frames) = [] ->
    na_inv (tpool th) Nswitcher switcher_inv ∗
    switcher_static ∗
    na_own (tpool th) ⊤ ∗
    PC ↦ₚ[th] WCap true XSRW_ Local b_switcher e_switcher a_switcher_return ∗
    ctp ↦ᵣ[th] wctp ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    ◯(CSTK)[th] cstk
    ⊢ WP Seq (Instr Executable) @[th] {{ HO th }}.
  Proof.
    destruct cstk as [ef frms]; cbn; intros ->.
    iIntros "(#Hswitcher & #Hstatic & Hna & HPC & Hctp & Hct0 & Hct2 & Hcstk)".
    iPoseProof "Hstatic" as "[#Hcode _]".
    (* Open the switcher invariant *)
    iMod (na_inv_acc with "Hswitcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)"; auto.
    iModNamed switcher_inv_open "Hswitcher_inv".
    iDestruct (switcher_hazard_open with "Hsave_area Hhazard_slots") as "[Hhazard Hsave_area]";
      first done.
    iDestruct (cstack_agree with "Hcstk_full Hcstk") as %Heq; subst cstk'.
    iEval (rewrite switcher_return_block_13) in "HPC".
    (* No frame to pop: to the thread exit *)
    iApply (switcher_after_compartment_call_exit_spec with
      "[- $HPC $Hctp $Hct0 $Hct2 $Hmtdc $Hframeoffset $Hhazard $Hcode]").
    iIntros "!>" (g_tstk) "(HPC & _ & _ & _ & Hmtdc & Hframeoffset & Hhazard)".
    iApply (common_defer_irqs_and_thread_exit_spec with "[- $HPC $Hcode]").
    iIntros "!> _".
    iMod (switcher_return_exit_close ⊤ (entry_cstack ef) with
           "Hclose_switcher_inv Hna Hmtdc Hsave_area Hframeoffset Hhazard HthreadID Htstk
            Hcstk_full Hstk_interp Hp_ot_switcher") as "Hna"; [done|done|done|].
    iModIntro; iIntros (_); iExact "Hna".
  Qed.

  (** A fault in a trusted callee whose table declares no handler, with its
      frame's table word set, is safe:
      the exception entry sets the return values to integers, then the
      return routine returns to the caller as in
      [switcher_ret_specification], for a fault that the exception path
      does not resume. The return values need no validity. The resources
      come under an update at the time of the fault (for instance, to close
      an invariant). *)
  Lemma trap_safe_return
    (W0 Wcur : WORLD)
    (C : CmptName)
    (rmap : LReg)
    (csp_e csp_b: Addr)
    (l : list LAddr)
    (stk_mem : list LWord)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (w : LWord)
    :
    let Wfixed := (close_list (l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) Wcur) in
    related_sts_pub_world W0 Wfixed ->
    dom rmap = all_registers_s ∖ ({[ csp ; ca0 ; ca1 ]} ) ->
    frame_match Ws Cs cstk W0 C ->
    csp_sync cstk csp_b csp_e ->
    NoDup (l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) ->
    (∀ a : LAddr, (std W0) !! a = Some Temporary -> a ∈ l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) ->
    trap_no_resume w ->

    na_inv (tpool th) Nswitcher switcher_inv -∗
    switcher_static -∗
    no_handler (top_export_tbl cstk) ∗
    ⌜(top_tframe cstk).(tf_export_tbl) ≠ lword_of_word (WInt 0)⌝ -∗
    (|={⊤}=>
       [[csp_b,csp_e]]↦ₐ[[stk_mem]] ∗
       ◯(CSTK)[th] cstk ∗
       interp_continuation cstk Ws Cs ∗
       world_interp Wcur C ∗
       na_own (tpool th) ⊤ ∗
       RevokedResources Wfixed C l ∗
       ([∗ map] k↦y ∈ rmap, k ↦ᵣ[th] y) ∗
       ca0 ↦ᵣ[th] - ∗
       ca1 ↦ᵣ[th] - ∗
       csp ↦ᵣ[th] -) -∗
    trap_safe w ⊤ (HO th).
  Proof.
    intros Wfixed.
    iIntros (Hrelated_pub_W0_Wfixed Hrmap Hframe Hcsp_sync Hnodup_revoked Htemp_revoked
               Hno_resume)
      "#Hswitcher #Hstatic [#Hno_handler %Htbl_set] Hres".
    iApply (trap_safe_exception_entry mcause_ok (λ _ : Z, True%type) ⊤
              with "Hswitcher Hstatic");
      [done | set_solver | set_solver |].
    iMod "Hres" as "(Hstk & Hcstk & HK & Hworld_interp & Hna & Hclose_list_res & Hrmap
                     & [%wca0 Hca0] & [%wca1 Hca1] & [%wcsp Hcsp])".
    iModIntro.
    iInsertList "Hrmap" [csp;ca0;ca1].
    iExists _, cstk. iFrame "Hna Hrmap Hcstk".
    iSplit.
    { iPureIntro. intros r. apply elem_of_dom. rewrite !dom_insert_L Hrmap.
      pose proof (all_registers_s_correct r). set_solver. }
    iApply (trap_handler_ok_no_handler with "Hno_handler"); [done | done |].
    iIntros (n rmap' Hfull_rmap' Hca0' Hca1') "HPC Hrmap' Hcstk _ Hna".
    rewrite /registers_pointsto.
    getRegValList [csp].
    iExtractList "Hrmap'" [csp;ca0;ca1] as ["Hcsp";"Hca0";"Hca1"].
    iEval (rewrite -(interp_cont_set_top_count cstk Ws Cs n)) in "HK".
    iApply (switcher_ret_specification _ _ _ _ _ _ _ _ (cstack_set_top_count cstk n) with
             "[$Hswitcher $Hstatic $Hstk $Hcstk $HK $Hworld_interp $Hna $HPC
               $Hclose_list_res $Hrmap' $Hca0 $Hca1 $Hcsp]"); try done.
    { rewrite !dom_delete_L (lregmap_full_dom _ Hfull_rmap'). set_solver. }
    { by apply frame_match_set_top_count. }
    { by apply csp_sync_set_top_count. }
    iSplit; iApply interp_int.
  Qed.

End Switcher.
