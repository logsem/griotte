From iris.proofmode Require Import proofmode.
From griotte Require Import logrel monotone interp_weakening fundamental wp_rules_interp.
From griotte Require Import world_interp_revocation.
From griotte Require Export world_ghost_theory world_interp_stack.
From griotte Require Import switcher_preamble.
From griotte Require Import map_simpl.
From griotte Require Export switcher_helpers_cframe.

Section switcher_helper.

  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
  .
  #[local] Notation E := (interpO Σ).
  #[local] Notation V := (interpO Σ).
  #[local] Notation K := (contO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

    #[local] Lemma world_interp_stack_fixing_aux
      (Wcur W0 : WORLD) (C : CmptName)
      (a_stk a_stk4 b_stk e_stk cur : Addr) (l : list LAddr)
      ccrel
      :

      let Wfixed := close_list (l ++ (LNonHeap <$> finz.seq_between b_stk a_stk)) Wcur in
      let closing_region := LNonHeap <$> finz.seq_between b_stk a_stk in

      (a_stk ^+ (SpillSlot_size - 1) < e_stk)%a ->
      (b_stk <= a_stk)%a ->
      (a_stk + SpillSlot_size)%a = Some a_stk4 ->

      related_sts_pub_world W0 Wfixed ->
      interp W0 C
        (Cap RWL Local b_stk
           (if is_untrusted_caller ccrel then e_stk else a_stk) cur) -∗
      world_interp Wcur C -∗
      [[ a_stk , a_stk4 ]] ↦ₐ [[ 0…0 ]] -∗
      [[ b_stk , a_stk ]] ↦ₐ [[ 0…0 ]] -∗

      CloseRes Wfixed C a_stk l ccrel -∗

      £ 1 -∗
      |={⊤}=>
            world_interp Wfixed C
            ∗ (if (is_untrusted_caller ccrel)
               then True
               else [[ a_stk , a_stk4 ]] ↦ₐ [[ 0…0 ]]
              )
    .
    Proof.
      intros Wfixed closing_region.
      iIntros (He_a1 Hb_a4 Ha_stk4 Hrelated_pub_W0_Wfixed)
        "#Hinterp_callee_wstk Hworld_interp Hstk' Hstk Hrevoked Hlc''".
      rewrite /SpillSlot_size in He_a1 Ha_stk4. change (4 - 1)%Z with 3%Z in He_a1.


      iAssert (▷ RevokedResources W0 C (LNonHeap <$> finz.seq_between b_stk a_stk))%I
        with "[Hstk]" as "Hstk".
      {
        iAssert (interp W0 C (Cap RWL Local b_stk a_stk cur)) as "Hvalid".
        {
          rewrite /is_untrusted_caller_frm /=; destruct (is_untrusted_caller ccrel); auto.
          iApply (interp_weakeningEO_gen _ _ true RWL RWL Local Local b_stk b_stk e_stk a_stk
                   with "[] Hinterp_callee_wstk"); auto using subseg_heap_base_noid.
          + solve_addr+.
          + solve_addr+Ha_stk4 He_a1 Hb_a4.
          + iIntros "!>" (Hg _); discriminate Hg.
        }

        iDestruct (interp_WL_addr_key with "Hvalid") as %Hkeys; first done.
        iDestruct (write_allowed_inv_full_cap with "Hvalid") as "-#H"; auto.
        iClear "#"; clear -Hrelated_pub_W0_Wfixed Hkeys.
        rewrite /region_pointsto /RevokedResources big_sepL_fmap.
        rewrite big_sepL2_replicate_r; last by rewrite finz_seq_between_length.
        iDestruct (big_sepL_sep with "[$Hstk $H]") as "H".
        iNext.
        iApply (big_sepL_impl with "H").
        iIntros "!> %k %x %Hx [Hv (%p' & %P & %Hflows & %Hpers & Hrel & #Hzcond & #Hrcond & #Hwcond)]".
        rewrite (Forall_lookup_1 _ _ _ _ Hkeys Hx).
        rewrite /region_rel /=.
        iDestruct "Hrel" as "(#Hrel & _ & #Hmono)".
        iExists p', (safeC P). iFrame "Hrel".
        iSplit; first (iPureIntro; intros [ [W C'] w]; apply Hpers).
        rewrite /temp_res /heap_key_resource /TmpRes /=.
        iExists (WInt 0). iFrame "Hv".
        iSplit; first (iPureIntro; eapply notisO_flowsfrom; eauto).
        iSplitR; [|iNext; iApply "Hmono"].
        iNext. iApply "Hwcond"; iApply interp_int.
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
        iAssert (RevokedResources Wfixed C
          (LNonHeap <$> [a_stk; (a_stk ^+ 1); (a_stk ^+ 2); (a_stk ^+ 3)]))
          with "[Hstk' Hdata0 Hdata1 Hdata2 Hdata3]" as "Hframe".
        {
        cbn in *.
        replace a_stk4 with (a_stk ^+4) by solve_addr+Ha_stk4 He_a1.
        rewrite /region_addrs_zeroes.
        replace (finz.dist a_stk (a_stk ^+ 4)) with 4; first cbn.
        2: { do 4 (rewrite finz_dist_S; last (solve_addr+Ha_stk4)).
             rewrite finz_dist_0; last (solve_addr+Ha_stk4).
             done.
        }
        iDestruct (region_pointsto_cons with "Hstk'") as "[Ha_stk0 Hstk']"
        ; [ transitivity ( Some (a_stk ^+ 1) ); solve_addr+Ha_stk4
          | solve_addr+Ha_stk4 He_a1
          |].
        iDestruct (region_pointsto_cons with "Hstk'") as "[Ha_stk1 Hstk']"
        ; [ transitivity ( Some (a_stk ^+ 2) ); solve_addr+Ha_stk4
          | solve_addr+Ha_stk4 He_a1
          |].
        iDestruct (region_pointsto_cons with "Hstk'") as "[Ha_stk2 Hstk']"
        ; [ transitivity ( Some (a_stk ^+ 3) ); solve_addr+Ha_stk4
          | solve_addr+Ha_stk4 He_a1
          |].
        iDestruct (region_pointsto_cons with "Hstk'") as "[Ha_stk3 _]"
        ; [ transitivity ( Some (a_stk ^+ 4) ); solve_addr+Ha_stk4
          | solve_addr+Ha_stk4 He_a1
          |].
        rewrite /RevokedResources /=.
        iSplitL "Hdata0 Ha_stk0".
        { iExists p0, P0. iFrame "Hrel0". iSplit; first done.
          iDestruct "Hdata0" as "(%Hp & #Hmono & Hsrc)".
          iDestruct "Hsrc" as (Wsrc Hrelated) "Hφ".
          rewrite /temp_res /heap_key_resource /TmpRes /=.
          iExists (WInt 0). iFrame "Ha_stk0 Hmono %".
          iNext. iApply ("Hmono" with "[] Hφ"). iPureIntro; exact Hrelated.
        }
        iSplitL "Hdata1 Ha_stk1".
        { iExists p1, P1. iFrame "Hrel1". iSplit; first done.
          iDestruct "Hdata1" as "(%Hp & #Hmono & Hsrc)".
          iDestruct "Hsrc" as (Wsrc Hrelated) "Hφ".
          rewrite /temp_res /heap_key_resource /TmpRes /=.
          iExists (WInt 0). iFrame "Ha_stk1 Hmono %".
          iNext. iApply ("Hmono" with "[] Hφ"). iPureIntro; exact Hrelated.
        }
        iSplitL "Hdata2 Ha_stk2".
        { iExists p2, P2. iFrame "Hrel2". iSplit; first done.
          iDestruct "Hdata2" as "(%Hp & #Hmono & Hsrc)".
          iDestruct "Hsrc" as (Wsrc Hrelated) "Hφ".
          rewrite /temp_res /heap_key_resource /TmpRes /=.
          iExists (WInt 0). iFrame "Ha_stk2 Hmono %".
          iNext. iApply ("Hmono" with "[] Hφ"). iPureIntro; exact Hrelated.
        }
        iSplitL "Hdata3 Ha_stk3".
        { iExists p3, P3. iFrame "Hrel3". iSplit; first done.
          iDestruct "Hdata3" as "(%Hp & #Hmono & Hsrc)".
          iDestruct "Hsrc" as (Wsrc Hrelated) "Hφ".
          rewrite /temp_res /heap_key_resource /TmpRes /=.
          iExists (WInt 0). iFrame "Ha_stk3 Hmono %".
          iNext. iApply ("Hmono" with "[] Hφ"). iPureIntro; exact Hrelated.
        }
        done.
        }
        iMod (world_interp_restore Wcur C (l ++ closing_region)
          with "[$Hworld_interp Hclose_list_res Hframe Hstk]") as "$"; last done.
        rewrite /RevokedResources big_sepL_app.
        iSplitR "Hstk"; last done.
        iApply (big_opL_permutation (o := bi_sep) _
          ((LNonHeap <$> [a_stk; (a_stk ^+ 1); (a_stk ^+ 2); (a_stk ^+ 3)]) ++ l') l);
          first (symmetry; exact Hl).
        rewrite big_sepL_app. iFrame.
      - iFrame "Hstk'".
        iMod (world_interp_restore Wcur C (l ++ closing_region)
          with "[$Hworld_interp Hrevoked Hstk]") as "$"; last done.
        rewrite /RevokedResources big_sepL_app. iFrame.
    Qed.

    (** At the return, fix the world on the callee's stack and on the spill
        area of the topmost frame, whose caller's cursor is [a_stk], once
        both are zeroed. *)
    Lemma world_interp_stack_fixing
      (Wcur W0 : WORLD) (C : CmptName)
      (b_stk e_stk a_stk : Addr) (l : list LAddr)
      ccrel
      :
      let s := stk_spill_a a_stk in
      let Wfixed := close_list (l ++ (LNonHeap <$> callee_stk_region b_stk e_stk a_stk)) Wcur in

      switcher_stk_bounds b_stk e_stk a_stk ->
      related_sts_pub_world W0 Wfixed ->
      interp W0 C
        (Cap RWL Local
           (if is_untrusted_caller ccrel then b_stk else stk_callee_b b_stk a_stk)
           (if is_untrusted_caller ccrel then e_stk else stk_callee_e e_stk a_stk)
           a_stk) -∗
      world_interp Wcur C -∗
      [[ s , s ^+ SpillSlot_size ]] ↦ₐ [[ 0…0 ]] -∗
      [[ stk_callee_b b_stk a_stk , stk_callee_e e_stk a_stk ]] ↦ₐ [[ 0…0 ]] -∗

      CloseRes Wfixed C s l ccrel -∗

      £ 1 -∗
      |={⊤}=>
            world_interp Wfixed C
            ∗ (if (is_untrusted_caller ccrel)
               then True
               else [[ s , s ^+ SpillSlot_size ]] ↦ₐ [[ 0…0 ]]
              )
    .
    Proof.
      intros s Wfixed Hbounds; subst s Wfixed.
      destruct Hbounds as (Hb & Hb3 & Ha4).
      stk_unfold. change (4 - 1)%Z with 3%Z in Hb3.
      replace (if is_untrusted_caller ccrel then b_stk else b_stk) with b_stk
        by (by destruct (is_untrusted_caller ccrel)).
      intros Hrelated.
      iApply (world_interp_stack_fixing_aux Wcur W0 C (stk_spill_a a_stk));
        [stk_unfold; solve_addr+Hb3 Ha4 | done | stk_unfold; solve_addr+Ha4 | done].
    Qed.

    (** The register file of a return to the caller is safe: the return
        address, the callee-save registers, the stack pointer and the return
        values are safe, and the other registers are cleared. *)
    #[local] Lemma switcher_caller_regs_interp
      (W : WORLD) (C : CmptName) (rmap : LReg)
      (wret wcgp wcs0 wcs1 wcsp wca0 wca1 : LWord) :
      let regs :=
        <[csp := wcsp]> (<[cra := wret]> (<[cgp := wcgp]> (<[cs1 := wcs1]>
          (<[cs0 := wcs0]> (<[ca1 := wca1]> (<[ca0 := wca0]> rmap)))))) in
      (∀ r, is_Some (regs !! r)) ->
      map_Forall (λ _ w, w = WInt 0) rmap ->
      interp W C wret -∗
      interp W C wcgp -∗
      interp W C wcs0 -∗
      interp W C wcs1 -∗
      interp W C wcsp -∗
      interp W C wca0 -∗
      interp W C wca1 -∗
      interp_reg interp W C regs.
    Proof.
      intros regs Hfull Hzeroes.
      iIntros "#Hwret #Hwcgp #Hwcs0 #Hwcs1 #Hwcsp #Hwca0 #Hwca1".
      iApply interp_reg_intro; first done.
      iIntros (r v) "%Hr".
      subst regs.
      destruct (decide (r = csp)); simplify_map_eq; first done.
      destruct (decide (r = cra)); simplify_map_eq; first done.
      destruct (decide (r = cgp)); simplify_map_eq; first done.
      destruct (decide (r = cs1)); simplify_map_eq; first done.
      destruct (decide (r = cs0)); simplify_map_eq; first done.
      destruct (decide (r = ca1)); simplify_map_eq; first done.
      destruct (decide (r = ca0)); simplify_map_eq; first done.
      eapply map_Forall_lookup_1 in Hr; eauto; cbn in Hr; simplify_eq.
      iApply interp_int.
    Qed.

    (** Jump to a safe return address [wret], with safe callee-save
        registers [cgp], [cs0], [cs1], [csp], safe return values [ca0],
        [ca1], and cleared registers. *)
    Lemma switcher_jump_to_caller_spec (trusted_fault : CSTK → LWord → LReg → iProp Σ)
      (W : WORLD) (C : CmptName) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
      (rmap : LReg) (wret wcgp wcs0 wcs1 wcsp wca0 wca1 : LWord) :
      dom rmap = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ->
      frame_match Ws Cs cstk W C ->

      trap_vector_safe trusted_fault (lword_of_word mtcc_vec) -∗
      thread_in th C -∗
      interp W C wret -∗
      interp W C wcgp -∗
      interp W C wcs0 -∗
      interp W C wcs1 -∗
      interp W C wcsp -∗
      interp W C wca0 -∗
      interp W C wca1 -∗
      top_cmpt_untrusted interp W C cstk -∗
      PC ↦ₚ[th] lupdatePcPerm wret -∗
      cra ↦ᵣ[th] wret -∗
      cgp ↦ᵣ[th] wcgp -∗
      cs0 ↦ᵣ[th] wcs0 -∗
      cs1 ↦ᵣ[th] wcs1 -∗
      csp ↦ᵣ[th] wcsp -∗
      ca0 ↦ᵣ[th] wca0 -∗
      ca1 ↦ᵣ[th] wca1 -∗
      regs₀[th] rmap -∗
      world_interp W C -∗
      interp_continuation cstk Ws Cs -∗
      ◯(CSTK)[th] cstk -∗
      na_own (tpool th) ⊤ -∗
      £ 1 -∗
      safe[th].
    Proof.
      iIntros (Hdom Hframe) "#Htrap #Hthread #Hwret #Hwcgp #Hwcs0 #Hwcs1 #Hwcsp #Hwca0 #Hwca1 #Htop
        HPC Hcra Hcgp Hcs0 Hcs1 Hcsp Hca0 Hca1 Hrmap Hworld_interp HK Hcstk Hna Hlc".
      iDestruct (trap_vector_safe_untrusted with "Htrap") as "#Htv".
      iEval (rewrite -world_resources_exclusive) in "Hworld_interp".
      iPoseProof (shared_credit_exclusive C) as "Hcred".
      iDestruct (jmp_or_fail_spec with "Hwret") as "Hcont".
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
      assert (∀ r, is_Some (regs !! r)) as Hfull_regs.
      { intros r.
        rewrite -elem_of_dom.
        subst regs.
        repeat (rewrite dom_insert_L).
        rewrite Hdom.
        set_solver+. }
      iPoseProof (switcher_caller_regs_interp with "Hwret Hwcgp Hwcs0 Hwcs1 Hwcsp Hwca0 Hwca1")
        as "#Hregs_interp"; [exact Hfull_regs | exact Hrmap_zeroes |].
      destruct (decide (isCorrectPC (updatePcPerm wret.(lw)))); cycle 1.
      { (* The return address is not a valid PC: the jump faults *)
        iApply "Hcont"; iFrame "HPC".
        iApply (interp_trap_safe_untrusted with
                 "Htrap Hthread Hregs_interp Htop [$Hrmap $Hworld_interp $Hcred $HK $Hna $Hcstk]");
          done. }

      iDestruct "Hcont" as "(%&%&%&%&%&%&Hcont)".
      iDestruct "Hcont" as "(%Hwret & #Hcont)".
      iAssert (future_world g W W) as "Hfuture".
      { destruct g; cbn; iPureIntro; [ done
                                     | apply related_sts_pub_refl_world].
      }
      iSpecialize ("Hcont" $! W with "Hfuture").
      iDestruct (lc_fupd_elim_later with "[$] [$Hcont]") as ">Hcont'".

      iApply ("Hcont'" $! cstk Ws Cs regs); iFrame "∗ #".
      done.
    Qed.

    (** The jump to the return address [wret], or its fault when [wret] is
        not a valid target of [Jalr cnull cra]: the fault unwinds the frame
        of the caller. The world, the token and the call stack are only
        needed after the jump or the exception entry. *)
    Lemma switcher_jump_to_caller_cases_spec (trusted_fault : CSTK → LWord → LReg → iProp Σ)
      (W : WORLD) (C : CmptName) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
      (rmap : LReg) (wret wcgp wcs0 wcs1 wcsp wca0 wca1 w : LWord) :
      dom rmap = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ->
      frame_match Ws Cs cstk W C ->

      trap_vector_safe trusted_fault (lword_of_word mtcc_vec) -∗
      thread_in th C -∗
      interp W C wret -∗
      interp W C wcgp -∗
      interp W C wcs0 -∗
      interp W C wcs1 -∗
      interp W C wcsp -∗
      interp W C wca0 -∗
      interp W C wca1 -∗
      top_cmpt_untrusted interp W C cstk -∗
      cra ↦ᵣ[th] wret -∗
      cgp ↦ᵣ[th] wcgp -∗
      cs0 ↦ᵣ[th] wcs0 -∗
      cs1 ↦ᵣ[th] wcs1 -∗
      csp ↦ᵣ[th] wcsp -∗
      ca0 ↦ᵣ[th] wca0 -∗
      ca1 ↦ᵣ[th] wca1 -∗
      regs₀[th] rmap -∗
      interp_continuation cstk Ws Cs -∗
      (|={⊤}=>
         world_interp W C ∗
         na_own (tpool th) ⊤ ∗
         ◯(CSTK)[th] cstk) -∗
      ( PC ↦ₚ[th] lupdatePcPerm wret ∗
        £ 1 -∗
        safe[th] ) ∧
      ( ⌜ jalr_target_ok cnull cra wret.(lw) = false ⌝ -∗
        trap_safe w ⊤ (HO th) ).
    Proof.
      iIntros (Hdom Hframe) "#Htrap #Hthread #Hwret #Hwcgp #Hwcs0 #Hwcs1 #Hwcsp #Hwca0 #Hwca1 #Htop
        Hcra Hcgp Hcs0 Hcs1 Hcsp Hca0 Hca1 Hrmap HK Hres".
      iSplit.
      - iIntros "[HPC Hlc]".
        iMod "Hres" as "(Hworld_interp & Hna & Hcstk)".
        iApply (switcher_jump_to_caller_spec with
                 "Htrap Hthread Hwret Hwcgp Hwcs0 Hwcs1 Hwcsp Hwca0 Hwca1 Htop HPC Hcra Hcgp Hcs0 Hcs1 Hcsp
                  Hca0 Hca1 Hrmap Hworld_interp HK Hcstk Hna Hlc"); done.
      - iIntros "_".
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
        assert (∀ r, is_Some (regs !! r)) as Hfull_regs.
        { intros r. rewrite -elem_of_dom. subst regs. repeat (rewrite dom_insert_L).
          rewrite Hdom. set_solver+. }
        iPoseProof (switcher_caller_regs_interp with "Hwret Hwcgp Hwcs0 Hwcs1 Hwcsp Hwca0 Hwca1")
          as "#Hregs_interp"; [exact Hfull_regs | exact Hrmap_zeroes |].
        iApply (interp_trap_safe_untrusted _ _ _ cstk Ws Cs regs with
                 "Htrap Hthread Hregs_interp Htop [Hrmap HK Hres]");
          [done | done |].
        iMod "Hres" as "(Hworld_interp & Hna & Hcstk)".
        iEval (rewrite -world_resources_exclusive) in "Hworld_interp".
        iPoseProof (shared_credit_exclusive C) as "Hcred".
        by iFrame.
    Qed.

End switcher_helper.
