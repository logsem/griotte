From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From griotte Require Import sts_multiple_updates.
From griotte Require Import ftlr_base_binary interp_weakening_binary.
From griotte Require Import logrel_binary fundamental_binary memory_region memory_region_binary.
From griotte Require Import rules proofmode proofmode_binary monotone_binary.
From griotte Require Import region_invariants_revocation_binary.
From griotte Require Export switcher switcher_preamble_binary.
From stdpp Require Import base.
From griotte Require Import map_simpl register_tactics register_tactics_binary.
From griotte Require Export world_ghost_theory_binary world_interp_stack_binary switcher_helpers_binary.
From griotte Require Import switcher_return_states_binary switcher_return_blocks_1_binary
  switcher_return_blocks_2_binary.

Section Switcher.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (** Specification of the return-to-switcher routine, for a trusted callee
      returning in both runs (lockstep). Both runs return with the same stack
      pointer: the callee was given the same stack frame in both runs. The
      return values are related, and the stack contents may differ. *)
  Lemma switcher_ret_specification_gen
    (Nswitcher : namespace)
    (W0 Wcur : WORLD)
    (C : CmptName)
    (rmap smap : Reg)
    (csp_e csp_b: Addr)
    (l : list Addr)
    (stk_mem stk_mem_spec : list Word)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName)
    (wca0 wca1 : Word * Word)
    :
    let Wfixed := (close_list (l ++ finz.seq_between csp_b csp_e) Wcur) in
    related_sts_pub_world W0 Wfixed ->
    dom rmap = all_registers_s ∖ ({[ PC ; csp ; ca0 ; ca1 ]} ) ->
    dom smap = all_registers_s ∖ ({[ PC ; csp ; ca0 ; ca1 ]} ) ->
    frame_match Ws Cs stk W0 C ->
    csp_sync stk (csp_b ^+ -4)%a csp_e ->
    NoDup (l ++ finz.seq_between csp_b csp_e) ->
    (∀ a : finz MemNum, std W0 !! a = Some Temporary -> a ∈ l ++ finz.seq_between csp_b csp_e) ->

    na_inv cerise_nais Nswitcher switcher_inv_binary
    ∗ spec_ctx
    ∗ interp Wfixed C wca0
    ∗ interp Wfixed C wca1
    ∗ [[csp_b,csp_e]]↦ₐ[[stk_mem]]
    ∗ [[csp_b,csp_e]]↣ₐ[[stk_mem_spec]]
    ∗ cstack_frag (map fst stk)
    ∗ cstack_frag_spec (map snd stk)
    ∗ interp_continuation stk Ws Cs
    ∗ world_interp Wcur C
    ∗ na_own cerise_nais ⊤
    ∗ ⤇ Seq (Instr Executable)
    ∗ PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_return
    ∗ PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_return
    ∗ close_list_resources_gen C Wcur (l ++ finz.seq_between csp_b csp_e) l false
    ∗ ([∗ map] k↦y ∈ rmap, k ↦ᵣ y)
    ∗ ([∗ map] k↦y ∈ smap, k ↣ᵣ y)
    ∗ ca0 ↦ᵣ wca0.1
    ∗ ca0 ↣ᵣ wca0.2
    ∗ ca1 ↦ᵣ wca1.1
    ∗ ca1 ↣ᵣ wca1.2
    ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
    ∗ csp ↣ᵣ WCap RWL Local csp_b csp_e csp_b
    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }}.
  Proof.
    (* Outline of the proof:
       - open the switcher invariant of both runs;
       - when the call-stack is empty: [switcher_return_blocks_1_empty_spec];
       - [switcher_return_blocks_1_spec]: pop both trusted stacks;
       - [open_world_interp_cframe_gen]: obtain the callee-save area;
       - [switcher_return_blocks_2_spec]: restore the callee-save registers,
         clear the stack frame and the registers, and jump to the caller;
       - close the switcher invariant and fix the world
         ([world_interp_stack_fixing]);
       - when the caller is trusted, use the continuation;
       - when the caller is untrusted, [switcher_jump_to_caller_spec]. *)
    intros Wfixed.
    iIntros (Hrelated_pub_W0_Wfixed Hrmap Hsmap Hframe Hcsp_sync Hnodup_revoked Htemp_revoked)
      "(#Hswitcher & #Hspec & #Hinterp_Wfixed_wca0 & #Hinterp_Wfixed_wca1 & Hstk & Hsstk
       & Hcstk & Hcstk_spec & HK & Hworld_interp & Hna & Hj
       & HPC & HsPC & Hclose_list_res & Hrmap & Hsmap & Hca0 & Hsca0 & Hca1 & Hsca1 & Hcsp & Hscsp)".

    (* Open the switcher invariant *)
    iMod (na_inv_acc with "Hswitcher Hna")
      as "([Hswitcher_inv Hswitcher_inv_spec] & Hna & Hclose_switcher_inv)" ; auto.
    iDestruct "Hswitcher_inv"
      as (a_tstk cstk' tstk_next)
           "(>Hmtdc & >%Hot_bounds & >Hcode & >Hb_switcher & >Htstk & >[%Hbounds_tstk_b %Hbounds_tstk_e]
           & >Hcstk_full & >%Hlen_cstk & Hstk_interp & #Hp_ot_switcher)".
    iDestruct "Hswitcher_inv_spec"
      as (sa_tstk scstk' ststk_next)
           "(>Hsmtdc & >Hscode & >Hsb_switcher & >Hststk & >[%Hsbounds_tstk_b %Hsbounds_tstk_e]
           & >Hcstk_full_spec & >%Hslen_cstk & Hsstk_interp)".
    iDestruct (cstack_agree with "Hcstk_full Hcstk") as %->.
    iDestruct (cstack_agree_spec with "Hcstk_full_spec Hcstk_spec") as %->.
    assert (sa_tstk = a_tstk) as ->.
    { eapply a_tstk_eq; [|exact Hslen_cstk|exact Hlen_cstk]. by rewrite !length_map. }
    clear Hslen_cstk Hsbounds_tstk_b Hsbounds_tstk_e.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hswitcher" as hinv_switcher.

    assert (is_Some (rmap !! cra)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    assert (is_Some (rmap !! cgp)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    assert (is_Some (rmap !! ctp)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    assert (is_Some (rmap !! ca2)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    assert (is_Some (rmap !! cs1)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    assert (is_Some (rmap !! cs0)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    assert (is_Some (rmap !! ct0)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    assert (is_Some (rmap !! ct1)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    iExtractList "Hrmap" [cra;cgp;ctp;ca2;cs1;cs0;ct0;ct1]
      as ["Hcra";"Hcgp";"Hctp";"Hca2";"Hcs1";"Hcs0";"Hct0";"Hct1"].
    assert (is_Some (smap !! cra)) as [??];[apply elem_of_dom;rewrite Hsmap;set_solver-|].
    assert (is_Some (smap !! cgp)) as [??];[apply elem_of_dom;rewrite Hsmap;set_solver-|].
    assert (is_Some (smap !! ctp)) as [??];[apply elem_of_dom;rewrite Hsmap;set_solver-|].
    assert (is_Some (smap !! ca2)) as [??];[apply elem_of_dom;rewrite Hsmap;set_solver-|].
    assert (is_Some (smap !! cs1)) as [??];[apply elem_of_dom;rewrite Hsmap;set_solver-|].
    assert (is_Some (smap !! cs0)) as [??];[apply elem_of_dom;rewrite Hsmap;set_solver-|].
    assert (is_Some (smap !! ct0)) as [??];[apply elem_of_dom;rewrite Hsmap;set_solver-|].
    assert (is_Some (smap !! ct1)) as [??];[apply elem_of_dom;rewrite Hsmap;set_solver-|].
    iExtractList "Hsmap" [cra;cgp;ctp;ca2;cs1;cs0;ct0;ct1]
      as ["Hscra";"Hscgp";"Hsctp";"Hsca2";"Hscs1";"Hscs0";"Hsct0";"Hsct1"].

    destruct stk as [|[frm1 frm2] stk]
    ; iEval (cbn) in "Hstk_interp"; iEval (cbn) in "Hsstk_interp"; cbn in Hlen_cstk.
    { (* No caller: the return fails *)
      replace a_tstk with (b_trusted_stack)%a by solve_addr.
      iMod "Hstk_interp".
      iApply (switcher_return_blocks_1_empty_spec with
        "[$HPC $Hctp $Hcsp $Hmtdc $Hstk_interp $Hcode]").
    }

    destruct Ws as [|Wprev Ws],Cs;try done. simpl in Hframe.
    destruct Hframe as [Hrelated_pub_Wprev_W0 [<- [Hccrel_known_to_known Hframe] ] ].

    iDestruct "Hstk_interp" as "(Hstk_interp_next & Hcframe_interp)".
    iDestruct "Hsstk_interp" as "(Hsstk_interp_next & Hscframe_interp)".
    iDestruct (interp_monotone_continuation with "HK") as "HK"; eauto.
    rewrite /interp_continuation /interp_cont.
    iEval (cbn) in "HK".
    iDestruct "HK" as "(Hcont_K & %Hframe_pair & HK)".
    rewrite Hccrel_known_to_known.
    iDestruct "HK" as "(#Hinterp_callee_wstk & Hexec_topmost_frm)".
    destruct (Hframe_pair (or_introl Hccrel_known_to_known)) as (Hccrel_eq & Hb_eq & Ha_eq & He_eq).
    destruct frm1 as [wret wcgp0 wcs2 wcs3 b_stk a_stk' e_stk ccrel].
    destruct frm2 as [swret swcgp0 swcs2 swcs3 sb_stk sa_stk se_stk sccrel].
    cbn in Hccrel_eq, Hb_eq, Ha_eq, He_eq, Hccrel_known_to_known, Hframe, Hcsp_sync.
    subst sccrel sb_stk sa_stk se_stk.
    destruct Hcsp_sync as (Ha & He & _ & _); simplify_eq.
    rewrite /cframe_interp /cframe_interp_spec.
    iEval (cbn) in "Hcframe_interp".
    iEval (cbn) in "Hscframe_interp".
    iDestruct "Hcframe_interp" as "[>Ha_tstk (>%HWF & Hcframe_interp)]".
    iDestruct "Hscframe_interp" as "[>Hsa_tstk (_ & Hscframe_interp)]".
    destruct HWF as (Hb_a4 & He_a1 & [a_stk4 Ha_stk4]).
    set (a_stk := (csp_b ^+ -4)%a).
    pose proof (switcher_stk_bounds_frame b_stk csp_e a_stk Hb_a4 He_a1 (ex_intro _ _ Ha_stk4))
      as Hstk_bounds.
    pose proof Hstk_bounds as (_ & _ & Ha4).
    iEval (cbn) in "Hinterp_callee_wstk".
    rewrite /is_untrusted_caller_frm /=.

    (* Block 12: pop both trusted stacks *)
    iApply (switcher_return_blocks_1_spec with
      "[- $Hspec $Hj $HPC $HsPC $Hctp $Hsctp $Hcsp $Hscsp $Hmtdc $Hsmtdc $Ha_tstk $Hsa_tstk
        $Hcode $Hscode]"); [done|done|].
    iNext; iIntros (a_tstk1)
      "(%Ha_tstk1 & %Htstk_ae & Hj & HPC & HsPC & Hctp & Hsctp & Hcsp & Hscsp & Hmtdc & Hsmtdc
      & Ha_tstk & Hsa_tstk & Hcode & Hscode & Hlc)".

    (* Obtain the callee-save area *)
    iMod (open_world_interp_cframe_gen
           with "Hinterp_callee_wstk Hcframe_interp Hscframe_interp Hclose_list_res Hlc")
      as "(%wastk & %wastk1 & %wastk2 & %wastk3 & %swastk & %swastk1 & %swastk2 & %swastk3 &
            Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & Hsa_stk & Hsa_stk1 & Hsa_stk2 & Hsa_stk3
            & %Hwastks & #Hinterp_wfrm & Hrevoked)";eauto.

    (* Blocks 12-15: restore, clear and return *)
    assert (csp_b = (a_stk ^+ 4)%a) as Hcsp_b by (subst a_stk; solve_addr+Ha_stk4).
    iEval (rewrite {1}Hcsp_b) in "Hstk".
    iEval (rewrite {1}Hcsp_b) in "Hsstk".
    iApply (switcher_return_blocks_2_spec with
      "[- $Hspec $Hj $HPC $HsPC $Hcgp $Hscgp $Hcra $Hscra $Hcs1 $Hscs1 $Hcs0 $Hscs0
        $Hct0 $Hsct0 $Hct1 $Hsct1 $Hca2 $Hsca2 $Hctp $Hsctp $Hcsp $Hscsp
        $Ha_stk $Ha_stk1 $Ha_stk2 $Ha_stk3 $Hsa_stk $Hsa_stk1 $Hsa_stk2 $Hsa_stk3
        $Hstk $Hsstk $Hrmap $Hsmap $Hcode $Hscode]"); first done.
    { repeat (rewrite dom_delete_L). rewrite Hrmap. set_solver. }
    { repeat (rewrite dom_delete_L). rewrite Hsmap. set_solver. }
    iNext; iIntros (arg_rmap')
      "(%Harg_rmap' & Hj & HPC & HsPC & Hcra & Hscra & Hcgp & Hscgp & Hcs0 & Hscs0 & Hcs1 & Hscs1
      & Hcsp & Hscsp & Hstk' & Hsstk' & Hstk & Hsstk & Hrmap & Hcode & Hscode & Hlc)".
    iDestruct "Hlc" as "(Hlc & Hlc'' & _)".
    assert ((a_stk ^+ 4)%a = a_stk4) as Ha_stk4_eq by (subst a_stk; solve_addr+Ha_stk4).
    iEval (rewrite Ha_stk4_eq) in "Hstk' Hsstk' Hstk Hsstk".

    iHide "Hcode" as hcode.
    iHide "Hscode" as hscode.
    (* Update both call stacks: pop the topmost frames *)
    iDestruct (cstack_update _ _ (map fst stk) with "Hcstk_full Hcstk") as ">[Hcstk_full Hcstk_frag]".
    iDestruct (cstack_update_spec _ _ (map snd stk) with "Hcstk_full_spec Hcstk_spec")
      as ">[Hcstk_full_spec Hcstk_frag_spec]".

    (* Close the switcher's invariant *)
    iDestruct (region_pointsto_cons with "[$Ha_tstk $Htstk]") as "Htstk"; [solve_addr| solve_addr| ].
    iDestruct (spec_region_pointsto_cons with "[$Hsa_tstk $Hststk]") as "Hststk"; [solve_addr| solve_addr| ].
    iMod ("Hclose_switcher_inv"
           with "[Hstk_interp_next Hsstk_interp_next $Hna $Hmtdc $Hsmtdc $Hcode $Hscode
                  $Hb_switcher $Hsb_switcher Htstk Hststk $Hcstk_full $Hcstk_full_spec $Hp_ot_switcher]")
      as "Hna".
    {
      replace (a_tstk1 ^+ 1)%a with a_tstk by solve_addr.
      replace (a_tstk ^+ -1)%a with a_tstk1 by solve_addr.
      iFrame.
      iNext.
      rewrite !length_map in Hlen_cstk |- *.
      repeat iSplit; iPureIntro; try done.
      all: solve_addr+Hbounds_tstk_b Hbounds_tstk_e Hlen_cstk Ha_tstk1.
    }

    (* Fix the world *)
    iMod (world_interp_stack_fixing
           with "Hinterp_callee_wstk Hworld_interp Hstk' Hsstk' Hstk Hsstk Hrevoked Hlc''") as
      "(Hworld_interp & Hstk')"; eauto.

    iDestruct (interp_monotone with "[] [$Hinterp_callee_wstk]") as "Hinterp_callee_wstk'" ; first done.

    rewrite /is_untrusted_caller_frm /=
    ; rewrite /is_untrusted_caller_frm /= in Hframe
    ; destruct (is_untrusted_caller ccrel); cycle 1.
    - (* Case where caller is trusted, we use the continuation *)
      destruct Hwastks as (-> & -> & -> & -> & -> & -> & -> & ->).
      iDestruct "Hstk'" as "[Hstk' Hsstk']".

      iEval (rewrite open_world_interp_empty) in "Hworld_interp".
      iDestruct (open_world_interp_opening_resources _ _ (finz.seq_between a_stk4 csp_e) []
                  with "[$Hinterp_callee_wstk' $Hworld_interp]")
        as "(Hworld_interp & (%lv & %slv & Hstk & Hsstk & Hres))"; auto.
      { apply finz_seq_between_NoDup. }
      { apply Forall_forall; intros y Hy.
        rewrite elem_of_finz_seq_between in Hy.
        subst a_stk.
        solve_addr+Ha_stk4 Hb_a4 He_a1 Hy.
      }
      { set_solver+. }
      iMod (lc_fupd_elim_later with "Hlc Hres") as "Hres".

      rewrite app_nil_r.
      replace a_stk4 with csp_b by solve_addr+Ha_stk4 Hb_a4 He_a1.
      replace csp_b with (a_stk ^+ 4)%a by (subst a_stk ; solve_addr+Ha_stk4 Hb_a4 He_a1).
      replace ((a_stk ^+ 4) ^+ -4)%a with a_stk by (subst a_stk ; solve_addr+Ha_stk4 Hb_a4 He_a1).

      iApply ("Hexec_topmost_frm" $! Wfixed _ wca0 wca1 arg_rmap' with
               "[$Hspec $HPC $HsPC $Hcra $Hscra $Hcsp $Hscsp $Hcgp $Hscgp $Hcs0 $Hscs0 $Hcs1 $Hscs1
                 $Hca0 $Hsca0 $Hca1 $Hsca1 $Hinterp_Wfixed_wca0 $Hinterp_Wfixed_wca1
                 $Hworld_interp $Hstk $Hsstk $Hstk' $Hsstk' $Hres $Hcont_K $Hcstk_frag $Hcstk_frag_spec
                 $Hj $Hna $Hrmap]").
      iPureIntro; rewrite Harg_rmap'; set_solver.
      Unshelve. done.

    - (* Case where caller is untrusted, we jump to the return address *)
      iDestruct "Hinterp_wfrm" as "#(Hinterp_wstk0 & Hinterp_wstk1 & Hinterp_wstk2 & Hinterp_wstk3)".
      iClear "Hexec_topmost_frm".
      iApply (switcher_jump_to_caller_spec Wfixed C stk Ws Cs arg_rmap'
                (wastk2, swastk2) (wastk3, swastk3) (wastk, swastk) (wastk1, swastk1)
                (WCap RWL Local b_stk csp_e a_stk, WCap RWL Local b_stk csp_e a_stk) wca0 wca1 with
               "Hspec Hinterp_wstk2 Hinterp_wstk3 Hinterp_wstk0 Hinterp_wstk1 Hinterp_callee_wstk'
                Hinterp_Wfixed_wca0 Hinterp_Wfixed_wca1 HPC HsPC Hcra Hscra Hcgp Hscgp Hcs0 Hscs0
                Hcs1 Hscs1 Hcsp Hscsp Hca0 Hsca0 Hca1 Hsca1
                Hrmap Hworld_interp Hcont_K Hcstk_frag Hcstk_frag_spec Hj Hna Hlc"); first done.
      eapply frame_match_mono; eauto.
  Qed.

  Lemma switcher_ret_specification
    (Nswitcher : namespace)
    (W0 Wcur : WORLD)
    (C : CmptName)
    (rmap smap : Reg)
    (csp_e csp_b: Addr)
    (l : list Addr)
    (stk_mem stk_mem_spec : list Word)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName)
    (wca0 wca1 : Word * Word)
    :
    let Wfixed := (close_list (l ++ finz.seq_between csp_b csp_e) Wcur) in
    related_sts_pub_world W0 Wfixed ->
    dom rmap = all_registers_s ∖ ({[ PC ; csp ; ca0 ; ca1 ]} ) ->
    dom smap = all_registers_s ∖ ({[ PC ; csp ; ca0 ; ca1 ]} ) ->
    frame_match Ws Cs stk W0 C ->
    csp_sync stk (csp_b ^+ -4)%a csp_e ->
    NoDup (l ++ finz.seq_between csp_b csp_e) ->
    (∀ a : finz MemNum, std W0 !! a = Some Temporary -> a ∈ l ++ finz.seq_between csp_b csp_e) ->

    na_inv cerise_nais Nswitcher switcher_inv_binary
    ∗ spec_ctx
    ∗ interp Wfixed C wca0
    ∗ interp Wfixed C wca1
    ∗ [[csp_b,csp_e]]↦ₐ[[stk_mem]]
    ∗ [[csp_b,csp_e]]↣ₐ[[stk_mem_spec]]
    ∗ cstack_frag (map fst stk)
    ∗ cstack_frag_spec (map snd stk)
    ∗ interp_continuation stk Ws Cs
    ∗ world_interp Wcur C
    ∗ na_own cerise_nais ⊤
    ∗ ⤇ Seq (Instr Executable)
    ∗ PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_return
    ∗ PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_return
    ∗ RevokedResources W0 C l
    ∗ ([∗ map] k↦y ∈ rmap, k ↦ᵣ y)
    ∗ ([∗ map] k↦y ∈ smap, k ↣ᵣ y)
    ∗ ca0 ↦ᵣ wca0.1
    ∗ ca0 ↣ᵣ wca0.2
    ∗ ca1 ↦ᵣ wca1.1
    ∗ ca1 ↣ᵣ wca1.2
    ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
    ∗ csp ↣ᵣ WCap RWL Local csp_b csp_e csp_b
    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }}.
  Proof.
    intros Wfixed.
    iIntros (Hrelated_pub_W0_Wfixed Hrmap Hsmap Hframe Hcsp_sync Hnodup_revoked Htemp_revoked)
      "(#Hswitcher & #Hspec & #Hinterp_Wfixed_wca0 & #Hinterp_Wfixed_wca1 & Hstk & Hsstk
       & Hcstk & Hcstk_spec & HK & Hworld_interp & Hna & Hj
       & HPC & HsPC & Hclose_list_res & Hrmap & Hsmap & Hca0 & Hsca0 & Hca1 & Hsca1 & Hcsp & Hscsp)".
    iApply (switcher_ret_specification_gen _ _ _ _ rmap smap); eauto.
    iFrame "∗#".
    iApply close_list_resources_gen_eq; eauto.
    rewrite /close_list_resources /close_addr_resources /RevokedResources.
    iApply (big_sepL_impl with "Hclose_list_res").
    iModIntro; iIntros (k ka Hka) "(%pa & %Pa & $ & $ & (%va & ($ & $ & $ & $ & ?)))".
    by rewrite mono_temporary_eq.
  Qed.

End Switcher.
