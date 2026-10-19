From iris.proofmode Require Import proofmode.
From griotte Require Import logrel monotone interp_weakening fundamental wp_rules_interp.
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
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
  .
  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).
  Notation K := (CSTK -n> list WORLD -n> leibnizO (list CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LReg) -n> iPropO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

    Lemma world_interp_stack_fixing
      (Wcur W0 : WORLD) (C : CmptName)
      (a_stk4 b_stk csp_b csp_e : Addr) (l : list LAddr)
      ccrel
      :

      let a_stk := (csp_b ^+ -4)%a in
      let Wfixed := close_list (l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) Wcur in
      let closing_region := LNonHeap <$> finz.seq_between csp_b csp_e in

      ((csp_b ^+ -4) ^+ 3 < csp_e)%a ->
      (b_stk <= csp_b ^+ -4)%a ->
      (csp_b ^+ -4 + 4)%a = Some a_stk4 ->

      related_sts_pub_world W0 Wfixed ->
      interp W0 C
        (WCap true RWL Local
           (if is_untrusted_caller ccrel then b_stk else (a_stk ^+ 4)%a) csp_e
           a_stk) -∗
      world_interp Wcur C -∗
      [[a_stk,a_stk4]]↦ₐ[[region_addrs_zeroes a_stk a_stk4]] -∗
      [[a_stk4,csp_e]]↦ₐ[[region_addrs_zeroes a_stk4 csp_e]] -∗

      CloseRes Wfixed C a_stk l ccrel -∗

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


      iAssert (▷ close_list_resources C W0 (LNonHeap <$> finz.seq_between csp_b csp_e) false)%I
        with "[Hstk]" as "Hstk".
      {
        replace a_stk4 with (a_stk ^+4)%a by (subst a_stk; solve_addr+Ha_stk4 He_a1).
        replace (a_stk ^+4)%a with csp_b by (subst a_stk; solve_addr+Ha_stk4 He_a1).
        iAssert (interp W0 C (WCap true RWL Local csp_b csp_e a_stk)) as "Hvalid".
        {
          rewrite /is_untrusted_caller_frm /=; destruct (is_untrusted_caller ccrel); auto.
          iApply (interp_weakening _ _ true _ _ _ _ b_stk csp_b with "[]Hinterp_callee_wstk"); auto using subseg_heap_base_noid.
          + subst a_stk; solve_addr+Ha_stk4 He_a1 Hb_a4.
          + subst a_stk; solve_addr+Ha_stk4 He_a1 Hb_a4.
          + iApply fundamental_ih.
        }

        iDestruct (interp_WL_addr_key with "Hvalid") as %Hkeys; first done.
        iDestruct (write_allowed_inv_full_cap with "Hvalid") as "-#H"; auto.
        iClear "#"; clear -Hrelated_pub_W0_Wfixed Hkeys.
        rewrite /region_pointsto /close_list_resources big_sepL_fmap.
        rewrite big_sepL2_replicate_r; last by rewrite finz_seq_between_length.
        iDestruct (big_sepL_sep with "[$Hstk $H]") as "H".
        iNext.
        iApply (big_sepL_impl with "H").
        iIntros "!> %%% [Hv (%&%&%&%&Hrel&#Hzcond&#Hrcond&#Hwcond&Hmono)]".
        assert (addr_key None x = LNonHeap x) as Hkey_x by done.
        rewrite Hkey_x.
        iExists x0, (safeC x1). iFrame.
        iSplit.
        { iPureIntro; intros W. rewrite /persistent_cond in H1.
          specialize (H1 W).
          apply _.
        }
        rewrite /heap_key_status /if_later_P /temp_resources /=.
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

      iDestruct (world_interp_close_resources_to_RevokedResources Wcur W0 C
        (l ++ closing_region) closing_region Hrelated_pub_W0_Wfixed
        with "Hworld_interp Hstk")
        as "[Hworld_interp Hstk]".
      rewrite /CloseRes.
      destruct (is_untrusted_caller ccrel).
      - iDestruct "Hrevoked" as (l')
          "(%Hl & Hclose_list_res & (Hrev0 & Hrev1 & Hrev2 & Hrev3 & _))".
        iDestruct "Hrev0" as (p0 P0 Hpers0) "(Hdata0 & #Hrel0)".
        iDestruct "Hrev1" as (p1 P1 Hpers1) "(Hdata1 & #Hrel1)".
        iDestruct "Hrev2" as (p2 P2 Hpers2) "(Hdata2 & #Hrel2)".
        iDestruct "Hrev3" as (p3 P3 Hpers3) "(Hdata3 & #Hrel3)".
        iAssert (close_list_resources C Wfixed
          (LNonHeap <$> [a_stk; (a_stk ^+ 1)%a; (a_stk ^+ 2)%a; (a_stk ^+ 3)%a]) false)
          with "[Hstk' Hdata0 Hdata1 Hdata2 Hdata3]" as "Hframe".
        {
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
        rewrite /close_list_resources /= /close_addr_resources.
        iSplitL "Hdata0 Ha_stk0".
        { iExists p0, P0. iFrame "Hrel0". iSplit; first done.
          iDestruct "Hdata0" as "(%Hp & #Hmono & Hsrc)".
          iDestruct "Hsrc" as (Wsrc Hrelated) "Hφ".
          iApply (temp_resources_mono_pub Wsrc Wfixed C P0 a_stk p0
            Hrelated with "[Ha_stk0 Hφ]").
          iExists (WInt 0). iFrame "Ha_stk0 Hmono Hφ %".
        }
        iSplitL "Hdata1 Ha_stk1".
        { iExists p1, P1. iFrame "Hrel1". iSplit; first done.
          iDestruct "Hdata1" as "(%Hp & #Hmono & Hsrc)".
          iDestruct "Hsrc" as (Wsrc Hrelated) "Hφ".
          iApply (temp_resources_mono_pub Wsrc Wfixed C P1 (a_stk ^+ 1)%a p1
            Hrelated with "[Ha_stk1 Hφ]").
          iExists (WInt 0). iFrame "Ha_stk1 Hmono Hφ %".
        }
        iSplitL "Hdata2 Ha_stk2".
        { iExists p2, P2. iFrame "Hrel2". iSplit; first done.
          iDestruct "Hdata2" as "(%Hp & #Hmono & Hsrc)".
          iDestruct "Hsrc" as (Wsrc Hrelated) "Hφ".
          iApply (temp_resources_mono_pub Wsrc Wfixed C P2 (a_stk ^+ 2)%a p2
            Hrelated with "[Ha_stk2 Hφ]").
          iExists (WInt 0). iFrame "Ha_stk2 Hmono Hφ %".
        }
        iSplitL "Hdata3 Ha_stk3".
        { iExists p3, P3. iFrame "Hrel3". iSplit; first done.
          iDestruct "Hdata3" as "(%Hp & #Hmono & Hsrc)".
          iDestruct "Hsrc" as (Wsrc Hrelated) "Hφ".
          iApply (temp_resources_mono_pub Wsrc Wfixed C P3 (a_stk ^+ 3)%a p3
            Hrelated with "[Ha_stk3 Hφ]").
          iExists (WInt 0). iFrame "Ha_stk3 Hmono Hφ %".
        }
        done.
        }
        assert (related_sts_pub_world Wfixed Wfixed) as Hrelated_refl
          by apply related_sts_pub_refl_world.
        iDestruct (world_interp_close_resources_to_RevokedResources Wcur Wfixed C
          (l ++ closing_region)
          (LNonHeap <$> [a_stk; (a_stk ^+ 1)%a; (a_stk ^+ 2)%a; (a_stk ^+ 3)%a])
          Hrelated_refl with "Hworld_interp Hframe") as "[Hworld_interp Hframe]".
        iMod (world_interp_restore Wcur C (l ++ closing_region)
          with "[$Hworld_interp Hclose_list_res Hframe Hstk]") as "$"; last done.
        rewrite /RevokedResources big_sepL_app.
        iSplitR "Hstk"; last done.
        iApply (big_opL_permutation (o := bi_sep) _
          ((LNonHeap <$> [a_stk; (a_stk ^+ 1)%a; (a_stk ^+ 2)%a; (a_stk ^+ 3)%a]) ++ l') l);
          first (symmetry; exact Hl).
        rewrite big_sepL_app. iFrame.
      - iFrame "Hstk'".
        iMod (world_interp_restore Wcur C (l ++ closing_region)
          with "[$Hworld_interp Hrevoked Hstk]") as "$"; last done.
        rewrite /RevokedResources big_sepL_app. iFrame.
    Qed.

    (** Jump to a safe return address [wret], with safe callee-save
        registers [cgp], [cs0], [cs1], [csp], safe return values [ca0],
        [ca1], and cleared registers. *)
    Lemma switcher_jump_to_caller_spec
      (W : WORLD) (C : CmptName) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
      (rmap : LReg) (wret wcgp wcs0 wcs1 wcsp wca0 wca1 : LWord) :
      dom rmap = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ->
      frame_match Ws Cs cstk W C ->

      interp W C wret -∗
      interp W C wcgp -∗
      interp W C wcs0 -∗
      interp W C wcs1 -∗
      interp W C wcsp -∗
      interp W C wca0 -∗
      interp W C wca1 -∗
      PC ↦ₚ lupdatePcPerm wret -∗
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
      destruct (decide (isCorrectPC (updatePcPerm wret.(lw)))); cycle 1.
      { iApply "Hcont"; iFrame.
        iApply trap_safe_intro.
        by iIntros "!>" (?). }

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

      iDestruct "Hcont" as "(%&%&%&%&%&%&Hcont)".
      iDestruct "Hcont" as "(%Hwret & #Hcont)".
      iAssert (future_world g W W) as "Hfuture".
      { destruct g; cbn; iPureIntro; [ apply related_sts_priv_refl_world
                                     | apply related_sts_pub_refl_world].
      }
      iSpecialize ("Hcont" $! W with "Hfuture").
      iDestruct (lc_fupd_elim_later with "[$] [$Hcont]") as ">Hcont'".

      iApply ("Hcont'" $! cstk Ws Cs regs); iFrame.
      iSplit.
      { iSplit.
        + iIntros (r); iPureIntro.
          rewrite -elem_of_dom.
          subst regs.
          repeat (rewrite dom_insert_L).
          rewrite Hdom.
          set_solver+.
        + iIntros (r v) "%Hr".
          iApply interp_filter_heap.
          subst regs.
          clear -Hr Hrmap_zeroes.
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
      done.
    Qed.

End switcher_helper.
