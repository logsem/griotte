From iris.proofmode Require Import proofmode.
From griotte Require Import logrel memory_region rules proofmode monotone.
From griotte Require Import map_simpl register_tactics.
From griotte Require Export switcher_spec_return_gen.
From griotte Require Import switcher_exception.

(** * Functional specification of the switcher's return routine

    [switcher_ret_specification_gen], instantiated with the trap safety of
    the switcher ([switcher_trap_safety_intro]), and the safety of a fault
    in a trusted callee without handler. *)

Section Switcher.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
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
    na_inv cerise_nais Nswitcher switcher_inv
    ∗ switcher_static
    ∗ interp Wfixed C wca0
    ∗ interp Wfixed C wca1
    ∗ [[csp_b,csp_e]]↦ₐ[[stk_mem]]
    ∗ cstack_frag cstk
    ∗ interp_continuation cstk Ws Cs
    ∗ world_interp Wcur C
    ∗ na_own cerise_nais ⊤
    ∗ PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_return
    ∗ RevokedResources Wfixed C l
    ∗ ([∗ map] k↦y ∈ rmap, k ↦ᵣ y)
    ∗ ca0 ↦ᵣ wca0
    ∗ ca1 ↦ᵣ wca1
    ∗ csp ↦ᵣ wcsp
    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros Wfixed.
    iIntros (Hrelated_pub_W0_Wfixed Hrmap Hframe Hcsp_sync Hnodup_revoked Htemp_revoked)
      "(#Hswitcher & #Hstatic & Hres)".
    iPoseProof (switcher_trap_safety_intro with "[$Hswitcher $Hstatic]") as "#Hsafety".
    by iApply (switcher_ret_specification_gen with "[$Hsafety $Hres]").
  Qed.

  (** A fault in a trusted callee whose table declares no handler is safe:
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

    na_inv cerise_nais Nswitcher switcher_inv -∗
    switcher_static -∗
    no_handler (top_export_tbl cstk) -∗
    (|={⊤}=>
       [[csp_b,csp_e]]↦ₐ[[stk_mem]] ∗
       cstack_frag cstk ∗
       interp_continuation cstk Ws Cs ∗
       world_interp Wcur C ∗
       na_own cerise_nais ⊤ ∗
       RevokedResources Wfixed C l ∗
       ([∗ map] k↦y ∈ rmap, k ↦ᵣ y) ∗
       ca0 ↦ᵣ - ∗
       ca1 ↦ᵣ - ∗
       csp ↦ᵣ -) -∗
    trap_safe w ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I.
  Proof.
    intros Wfixed.
    iIntros (Hrelated_pub_W0_Wfixed Hrmap Hframe Hcsp_sync Hnodup_revoked Htemp_revoked
               Hno_resume)
      "#Hswitcher #Hstatic #Hno_handler Hres".
    iApply (trap_safe_exception_entry ⊤ with "Hswitcher Hstatic");
      [set_solver | set_solver |].
    iMod "Hres" as "(Hstk & Hcstk & HK & Hworld_interp & Hna & Hclose_list_res & Hrmap
                     & [%wca0 Hca0] & [%wca1 Hca1] & [%wcsp Hcsp])".
    iModIntro.
    iInsertList "Hrmap" [csp;ca0;ca1].
    iExists _, cstk. iFrame "Hna Hrmap Hcstk".
    iSplit.
    { iPureIntro. intros r. apply elem_of_dom. rewrite !dom_insert_L Hrmap.
      pose proof (all_registers_s_correct r). set_solver. }
    iApply (trap_handler_ok_no_handler with "Hno_handler"); first done.
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
