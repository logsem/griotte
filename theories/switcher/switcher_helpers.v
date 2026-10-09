From iris.proofmode Require Import proofmode.
From griotte Require Import logrel monotone interp_weakening fundamental.
From griotte Require Import region_invariants_revocation.
From griotte Require Export world_ghost_theory world_interp_stack.
From griotte Require Import switcher_preamble.
From griotte Require Import map_simpl.
From griotte Require Export switcher_helpers_cframe.

Section switcher_helper.

  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
  .
  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation K := (CSTK -n> list WORLD -n> leibnizO (list CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (V).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

    Lemma world_interp_stack_fixing
      (Wcur W0 : WORLD) (C : CmptName)
      (a_stk4 b_stk csp_b csp_e : Addr) (l : list Addr)
      ccrel
      :

      let a_stk := (csp_b ^+ -4)%a in
      let Wfixed := close_list (l ++ finz.seq_between csp_b csp_e) Wcur in
      let closing_region := finz.seq_between csp_b csp_e in

      ((csp_b ^+ -4) ^+ 3 < csp_e)%a ->
      (b_stk <= csp_b ^+ -4)%a ->
      (csp_b ^+ -4 + 4)%a = Some a_stk4 ->

      related_sts_pub_world W0 Wfixed ->
      interp W0 C
        (WCap RWL Local
           (if is_untrusted_caller ccrel then b_stk else (a_stk ^+ 4)%a) csp_e
           a_stk) -∗
      world_interp Wcur C -∗
      [[a_stk,a_stk4]]↦ₐ[[region_addrs_zeroes a_stk a_stk4]] -∗
      [[a_stk4,csp_e]]↦ₐ[[region_addrs_zeroes a_stk4 csp_e]] -∗

      CloseRes_gen Wcur Wfixed C csp_b csp_e a_stk l ccrel -∗

      £ 1 -∗
      |={⊤}=>
            world_interp Wfixed C
            ∗ (if (is_untrusted_caller ccrel)
               then True
               else [[a_stk,a_stk4]]↦ₐ[[region_addrs_zeroes a_stk a_stk4]]
              )
    .
    Proof.
      intros a_stk Wfixed closing_region.
      iIntros (He_a1 Hb_a4 Ha_stk4 Hrelated_pub_W0_Wfixed)
        "#Hinterp_callee_wstk Hworld_interp Hstk' Hstk Hrevoked Hlc''".

      iAssert ( ▷( close_list_resources_gen C Wcur (l++(finz.seq_between csp_b csp_e)) (finz.seq_between csp_b csp_e) false) )%I with "[Hstk]" as "Hstk".
      {
        replace a_stk4 with (a_stk ^+4)%a by (subst a_stk; solve_addr+Ha_stk4 He_a1).
        replace (a_stk ^+4)%a with csp_b by (subst a_stk; solve_addr+Ha_stk4 He_a1).
        iAssert (interp W0 C (WCap RWL Local csp_b csp_e a_stk)) as "Hvalid".
        {
          rewrite /is_untrusted_caller_frm /=; destruct (is_untrusted_caller ccrel); auto.
          iApply (interp_weakening _ _ _ _ _ _ b_stk csp_b with "[]Hinterp_callee_wstk"); auto.
          + subst a_stk; solve_addr+Ha_stk4 He_a1 Hb_a4.
          + subst a_stk; solve_addr+Ha_stk4 He_a1 Hb_a4.
          + iApply fundamental_ih.
        }

        iDestruct (write_allowed_inv_full_cap with "Hvalid") as "-#H"; auto.
        iClear "#";clear-Hrelated_pub_W0_Wfixed.
        rewrite /region_pointsto.
        rewrite big_sepL2_replicate_r; last by rewrite finz_seq_between_length.
        iDestruct (big_sepL_sep with "[$Hstk $H]") as "H".
        iNext.
        iApply (big_sepL_impl with "H").
        iIntros "!> %%% [Hv (%&%&%&%&Hrel&#Hzcond&#Hrcond&#Hwcond&Hmono)]".
        iExists x0, (safeC x1). iFrame.
        iSplit.
        { iPureIntro; intros W. rewrite /persistent_cond in H1.
          specialize (H1 W).
          apply _.
        }
        iFrame "%".
        iSplit; first (iPureIntro; eapply notisO_flowsfrom; eauto).
        iSplit.
        { erewrite isWL_flowsto;eauto.
          rewrite /future_pub_mono.
          iIntros "!> %%% H".
          iApply "Hzcond"; auto.
        }
        iApply "Hwcond"; iApply interp_int.
      }
      iDestruct (lc_fupd_elim_later with "[$] [$Hstk]") as ">Hstk".

      rewrite /CloseRes_gen.
      destruct (is_untrusted_caller ccrel).
      - (* caller is untrusted, we need to re-instate the whole stack frame *)
        iMod (reinstate_close_list_gen _ _ (l++closing_region) with
               "[$Hworld_interp Hrevoked Hstk Hstk']") as "Hworld_interp"; last by iFrame.
        iDestruct "Hrevoked" as (l') "(%Hl & Hclose_list_res & (Hrev0 & Hrev1 & Hrev2 & Hrev3 & _) )".
        rewrite /close_list_resources_gen.
        rewrite big_sepL_app.
        iSplitR "Hstk"; last done.
        iApply big_opL_permutation; first (symmetry; done).
        rewrite big_sepL_app.
        iFrame.
        cbn in *.
        replace a_stk4 with (a_stk ^+4)%a by (subst a_stk; solve_addr+Ha_stk4 He_a1).
        rewrite /region_addrs_zeroes.
        replace (finz.dist a_stk (a_stk ^+ 4)%a) with 4; first cbn.
        2: { do 4 (rewrite finz_dist_S; last (subst a_stk; solve_addr+Ha_stk4)).
             rewrite finz_dist_0; last (subst a_stk; solve_addr+Ha_stk4).
             done.
        }
        iDestruct (region_pointsto_cons with "Hstk'") as "[Ha_stk0 Hstk']"
        ; [ transitivity ( Some (a_stk ^+ 1)%a ); subst a_stk; solve_addr+Ha_stk4
          | subst a_stk; solve_addr+Ha_stk4 He_a1
          |].
        iDestruct (region_pointsto_cons with "Hstk'") as "[Ha_stk1 Hstk']"
        ; [ transitivity ( Some (a_stk ^+ 2)%a ); subst a_stk; solve_addr+Ha_stk4
          | subst a_stk; solve_addr+Ha_stk4 He_a1
          |].
        iDestruct (region_pointsto_cons with "Hstk'") as "[Ha_stk2 Hstk']"
        ; [ transitivity ( Some (a_stk ^+ 3)%a ); subst a_stk; solve_addr+Ha_stk4
          | subst a_stk; solve_addr+Ha_stk4 He_a1
          |].
        iDestruct (region_pointsto_cons with "Hstk'") as "[Ha_stk3 _]"
        ; [ transitivity ( Some (a_stk ^+ 4)%a ); subst a_stk; solve_addr+Ha_stk4
          | subst a_stk; solve_addr+Ha_stk4 He_a1
          |].
        rewrite /close_addr_resources_gen.
        iSplitL "Hrev0 Ha_stk0".
        { iFrame "Ha_stk0".
          iDestruct "Hrev0" as " (%p & %P & $ & ($ & $ & $) & $)".
        }
        iSplitL "Hrev1 Ha_stk1".
        { iFrame "Ha_stk1".
          iDestruct "Hrev1" as " (%p & %P & $ & ($ & $ & $) & $)".
        }
        iSplitL "Hrev2 Ha_stk2".
        { iFrame "Ha_stk2".
          iDestruct "Hrev2" as " (%p & %P & $ & ($ & $ & $) & $)".
        }
        iSplitL "Hrev3 Ha_stk3".
        { iFrame "Ha_stk3".
          iDestruct "Hrev3" as " (%p & %P & $ & ($ & $ & $) & $)".
        }
        done.

      - (* caller is trusted, we need only need re-instate callee's stack frame *)
        iFrame "Hstk'".
        iMod (reinstate_close_list_gen _ _ (l++closing_region) with
               "[$Hworld_interp Hrevoked Hstk]") as "Hworld_interp"; last by iFrame.
        rewrite /close_list_resources_gen big_sepL_app.
        iFrame.
    Qed.

    (** Jump to a safe return address [wret], with safe callee-save
        registers [cgp], [cs0], [cs1], [csp], safe return values [ca0],
        [ca1], and cleared registers. *)
    Lemma switcher_jump_to_caller_spec
      (W : WORLD) (C : CmptName) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
      (rmap : Reg) (wret wcgp wcs0 wcs1 wcsp wca0 wca1 : Word) :
      dom rmap = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ->
      frame_match Ws Cs cstk W C ->

      interp W C wret -∗
      interp W C wcgp -∗
      interp W C wcs0 -∗
      interp W C wcs1 -∗
      interp W C wcsp -∗
      interp W C wca0 -∗
      interp W C wca1 -∗
      PC ↦ᵣ updatePcPerm wret -∗
      cra ↦ᵣ wret -∗
      cgp ↦ᵣ wcgp -∗
      cs0 ↦ᵣ wcs0 -∗
      cs1 ↦ᵣ wcs1 -∗
      csp ↦ᵣ wcsp -∗
      ca0 ↦ᵣ wca0 -∗
      ca1 ↦ᵣ wca1 -∗
      ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝) -∗
      world_interp W C -∗
      interp_continuation cstk Ws Cs -∗
      cstack_frag cstk -∗
      na_own cerise_nais ⊤ -∗
      £ 1 -∗
      WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
    Proof.
      iIntros (Hdom Hframe) "#Hwret #Hwcgp #Hwcs0 #Hwcs1 #Hwcsp #Hwca0 #Hwca1
        HPC Hcra Hcgp Hcs0 Hcs1 Hcsp Hca0 Hca1 Hrmap Hworld_interp HK Hcstk Hna Hlc".
      iDestruct (jmp_or_fail_spec with "Hwret") as "Hcont".
      destruct (decide (isCorrectPC (updatePcPerm wret))); cycle 1.
      { iApply "Hcont"; iFrame. by iIntros (?). }

      iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap %Hrmap_zeroes]".
      iDestruct (big_sepM_insert with "[$Hrmap $Hca0]") as "Hrmap".
      { apply not_elem_of_dom; rewrite Hdom; set_solver+. }
      iDestruct (big_sepM_insert with "[$Hrmap $Hca1]") as "Hrmap".
      { apply not_elem_of_dom; repeat (rewrite dom_insert_L); rewrite Hdom; set_solver+. }
      iDestruct (big_sepM_insert with "[$Hrmap $Hcs0]") as "Hrmap".
      { apply not_elem_of_dom; repeat (rewrite dom_insert_L); rewrite Hdom; set_solver+. }
      iDestruct (big_sepM_insert with "[$Hrmap $Hcs1]") as "Hrmap".
      { apply not_elem_of_dom; repeat (rewrite dom_insert_L); rewrite Hdom; set_solver+. }
      iDestruct (big_sepM_insert with "[$Hrmap $Hcgp]") as "Hrmap".
      { apply not_elem_of_dom; repeat (rewrite dom_insert_L); rewrite Hdom; set_solver+. }
      iDestruct (big_sepM_insert with "[$Hrmap $Hcra]") as "Hrmap".
      { apply not_elem_of_dom; repeat (rewrite dom_insert_L); rewrite Hdom; set_solver+. }
      iDestruct (big_sepM_insert with "[$Hrmap $Hcsp]") as "Hrmap".
      { apply not_elem_of_dom; repeat (rewrite dom_insert_L); rewrite Hdom; set_solver+. }
      set (regs := <[csp := _]> _ ).
      set (regs' := <[PC := WInt 0]> regs).

      iDestruct "Hcont" as "(%&%&%&%&%&Hcont)".
      iDestruct "Hcont" as "(%Hwret & #Hcont)".
      iAssert (future_world g W W) as "Hfuture".
      { destruct g; cbn; iPureIntro; [ apply related_sts_priv_refl_world
                                     | apply related_sts_pub_refl_world].
      }
      iSpecialize ("Hcont" $! W with "Hfuture").
      iDestruct (lc_fupd_elim_later with "[$] [$Hcont]") as ">Hcont'".

      iApply ("Hcont'" $! cstk Ws Cs regs'); iFrame.
      iSplit.
      { iSplit.
        + iIntros (r); iPureIntro.
          rewrite -elem_of_dom.
          subst regs regs'.
          repeat (rewrite dom_insert_L).
          rewrite Hdom.
          set_solver+.
        + iIntros (r v) "%HrPC %Hr".
          subst regs' regs.
          clear -Hr HrPC Hrmap_zeroes.
          rewrite lookup_insert_ne in Hr; last done.
          destruct (decide (r = csp)); simplify_map_eq; first done.
          destruct (decide (r = cra)); simplify_map_eq; first done.
          destruct (decide (r = cgp)); simplify_map_eq; first done.
          destruct (decide (r = cs1)); simplify_map_eq; first done.
          destruct (decide (r = cs0)); simplify_map_eq; first done.
          destruct (decide (r = ca1)); simplify_map_eq; first done.
          destruct (decide (r = ca0)); simplify_map_eq; first done.
          eapply map_Forall_lookup_1 in Hr; eauto; cbn in Hr; simplify_eq.
          iApply interp_int.
      }
      iSplit; last done.
      rewrite /registers_pointsto.
      subst regs'.
      rewrite insert_insert_eq.
      iApply big_sepM_insert; last iFrame.
      subst regs.
      simplify_map_eq.
      rewrite -not_elem_of_dom Hdom.
      set_solver+.
    Qed.

End switcher_helper.
