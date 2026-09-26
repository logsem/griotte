From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From griotte Require Import ftlr_base interp_weakening interp_switcher_return.
From griotte Require Import logrel fundamental interp_weakening memory_region rules proofmode monotone.
From griotte Require Import sts_multiple_updates region_invariants_revocation.
From griotte Require Export switcher switcher_preamble switcher_macros_spec switcher_helpers.
From griotte Require Import switcher_spec_call_blocks world_ghost_theory world_interp_stack.
From griotte Require Import map_simpl register_tactics proofmode.
From griotte Require Import switcher_spec_call_gen.


Section Switcher.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).


  (* This specification unifies the two possible outcomes of the switcher call.
     It closes the world, and then revokes it.
   *)
  Lemma switcher_cc_specification_gen_revoked
    (Nswitcher : namespace)
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller : Word)
    (b_stk e_stk a_stk : Addr)
    (stk_mem : list Word)
    (arg_rmap rmap : Reg)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (is_entry_point_known : bool)
    :
    let a_stk4 := (a_stk ^+ 4)%a in
    let callee_stk_region := finz.seq_between a_stk4 e_stk in
    disjoint_from_shadow b_stk e_stk ->
    disjoint_from_heap b_stk e_stk ->
    dom rmap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->

    (* Switcher Invariant *)
    allocator_ctx ∗ na_inv cerise_nais Nswitcher switcher_inv

    (* PRE-CONDITION *)
    ∗ na_own cerise_nais ⊤
    (* Registers *)
    ∗ PC ↦ᵣ WCap true XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ wcgp_caller
    ∗ cra ↦ᵣ wcra_caller
    (* Stack register *)
    ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ wct1_caller
    ∗ (if is_sealed_with_o wct1_caller ot_switcher then interp W C wct1_caller else True)
    ∗ (if is_entry_point_known
       then ∃ nargs, wct1_caller ↦□ₑ nargs
                     (* Argument registers, need to be safe-to-share *)
                     ∗ ( [∗ map] rarg↦warg ∈ arg_rmap,
                           rarg ↦ᵣ warg
                           ∗ if decide (rarg ∈ dom_arg_rmap nargs)
                             then interp W C warg
                             else True )
       else ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg ∗ interp W C warg )
      )
    ∗ cs0 ↦ᵣ wcs0_caller
    ∗ cs1 ↦ᵣ wcs1_caller
    (* All the other registers *)
    ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

    (* Stack frame *)
    ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ world_interp W C
    ∗ StackRevokedResources W C (finz.seq_between a_stk e_stk)
    ∗ ⌜ revoked_addresses W (finz.seq_between a_stk e_stk) ⌝
    ∗ cstack_frag cstk
    ∗ interp_continuation cstk Ws Cs


    (* POST-CONDITION *)
    ∗ ▷ ( ∀ (W2 : WORLD) (rmap' : Reg) (stk_mem : list Word) l' rcgp rcra rcs0 rcs1,
              (* We receive a public future world of the world pre switcher call *)
            ⌜ extract_temporaries_condition W2 (l' ++ finz.seq_between (a_stk ^+ 4)%a e_stk) ⌝
            ∗ RevokedResources W2 C l'
            ∗ ⌜ revoked_addresses (revoke W2) l' ⌝
            ∗ ⌜ related_sts_pub_world (std_update_multiple W callee_stk_region Temporary) W2 ⌝
            ∗ ([∗ list] a ∈ callee_stk_region, ⌜ std W2 !! a = Some Temporary ⌝ )
            ∗ ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
            ∗ StackRevokedResources W2 C (finz.seq_between a_stk e_stk)
            ∗ ⌜ revoked_addresses (revoke W2) (finz.seq_between a_stk e_stk) ⌝
            ∗ na_own cerise_nais ⊤
            ∗ ⌜ (b_stk <= a_stk4 ∧ a_stk4 <= e_stk ∧ (a_stk + 4) = Some a_stk4)%a ⌝
            (* Interpretation of the world *)
            ∗ world_interp (revoke W2) C
            ∗ cstack_frag cstk
            ∗ PC ↦ᵣ updatePcPerm (rcra)
            (* cgp is restored, cra points to the next  *)
            ∗ cgp ↦ᵣ rcgp
            ∗ cra ↦ᵣ rcra
            ∗ cs0 ↦ᵣ rcs0
            ∗ cs1 ↦ᵣ rcs1
            ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
            ∗ (∃ warg0, ca0 ↦ᵣ warg0 ∗ interp W2 C warg0)
            ∗ (∃ warg1, ca1 ↦ᵣ warg1 ∗ interp W2 C warg1)
            ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
            ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]
            ∗ interp_continuation cstk Ws Cs
              ∗ ⌜load_heap wcgp_caller rcgp ∧ load_heap wcra_caller rcra ∧
                load_heap wcs0_caller rcs0 ∧ load_heap wcs1_caller rcs1⌝
              ∗ ⌜filter_heap W2 rcs1 = rcs1⌝
              -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})


    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (a_stk4 callee_stk_region Hstk_shadow Hstk_heap Hdom Hrdom) "(#Halloc & #Hswitcher & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & #Htarget_v
    & Hargs & Hcs0 & Hcs1 & Hregs & Hstk & Hworld_interp & #Hstk_val & %Hrevoked_stk & Hcstk & Hcont & Hpost)".
    subst a_stk4.
    subst callee_stk_region.
    iApply (switcher_cc_specification_gen Nswitcher W C
      wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller
      b_stk e_stk a_stk stk_mem arg_rmap rmap cstk Ws Cs is_entry_point_known);
      eauto; iFrame "∗#%".
    iIntros (W' rmap' stk_mem_l stk_mem_h rcgp rcra rcs0 rcs1).
    iNext; iIntros "[H|H]".
    + clear stk_mem.
      iDestruct "H" as
        "(%Hrelated_pub_Wext_W2 & %Hdom_rmap
      & Hna & #Hinterp_W2_csp & %Hcsp_bounds & %Hstack_heap
      & Hworld_interp_C & Hstack_revoked_W2
      & Hcstk_frag & Hrel_stk_C
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 #Hinterp_wca0] ] & [%warg1 [Hca1 #Hinterp_wca1] ]
      & Hrmap & Hstk_l & Hstk_h & HK & %Hrestored & %Hretained & [Hlc Hlc'])".

      iDestruct ( big_sepL2_length with "Hstk_h" ) as "%Hlen_stk_h".
      iDestruct ( big_sepL2_length with "Hstk_l" ) as "%Hlen_stk_l".
      iEval (rewrite <- (app_nil_r (finz.seq_between (a_stk ^+ 4)%a e_stk))) in "Hworld_interp_C".

      iDestruct (close_world_interp_opening_resources
                  with "[$Hworld_interp_C $Hstack_revoked_W2 $Hstk_h]")
        as "Hworld_interp_C".
      { apply finz_seq_between_NoDup. }
      { set_solver+. }
      { by rewrite finz_seq_between_length in Hlen_stk_l. }
      { apply Forall_forall; intros x Hx.
        apply heap_cell_live_nonheap.
        apply not_true_is_false; intros Hxheap.
        apply withinBounds_true_iff in Hxheap.
        rewrite /disjoint_from_heap elem_of_disjoint in Hstk_heap.
        eapply (Hstk_heap x); apply elem_of_finz_seq_between.
        - rewrite elem_of_finz_seq_between in Hx.
          solve_addr+Hcsp_bounds Hx.
        - exact Hxheap. }
      rewrite -open_world_interp_empty.

      iMod (world_interp_revoked_by_separation_many with "[$Hworld_interp_C $Hstk_l]")
        as "(Hworld_interp_C & Hstk_l & %Hstk_l_revoked)".
      { apply Forall_forall; intros x Hx.
        apply heap_cell_live_nonheap.
        apply not_true_is_false; intros Hxheap.
        apply withinBounds_true_iff in Hxheap.
        rewrite /disjoint_from_heap elem_of_disjoint in Hstack_heap.
        eapply (Hstack_heap x); apply elem_of_finz_seq_between.
        - rewrite elem_of_finz_seq_between in Hx.
          solve_addr+Hx Hcsp_bounds.
        - exact Hxheap. }
      {
        apply Forall_forall; intros a Ha.
        eapply elem_of_mono_pub;eauto.
        rewrite elem_of_dom.
        rewrite std_sta_update_multiple_lookup_same_i; cycle 1.
        { intro Hcontra.
          apply elem_of_finz_seq_between in Ha, Hcontra.
          solve_addr.
        }
        assert ( a ∈ finz.seq_between a_stk e_stk).
        { rewrite elem_of_finz_seq_between.
          rewrite elem_of_finz_seq_between in Ha.
          solve_addr.
        }
        rewrite /revoked_addresses Forall_forall in Hrevoked_stk.
        apply Hrevoked_stk in H.
        done.
    }

    iMod (world_interp_revoke_stack with "[$Hinterp_W2_csp $Hworld_interp_C]")
      as (l') "(%Hl_unk' & Hworld_interp_C & Hstack_revoked_W2 & Hrevoked_W2 & >[%stk_mem_h' Hstk_h] & [Hrevoked_l' %Hrevoked_W2_l'])".
    iDestruct (region_pointsto_split with "[$Hstk_l $Hstk_h]") as "Hstk"; auto.
    { solve_addr+ Hcsp_bounds. }
    { by rewrite finz_seq_between_length in Hlen_stk_l. }
    iCombine "Hstack_revoked_W2 Hrevoked_W2" as "Hstack_revoked_W2".
    iDestruct (lc_fupd_elim_later with "[$] [$Hrevoked_l']") as ">Hrevoked_l'".
    iDestruct (lc_fupd_elim_later with "[$] [$Hstack_revoked_W2]") as ">[Hstack_revoked_W2 %]".
    iApply "Hpost"; iFrame "∗%#".
    iSplitL "Hstack_revoked_W2"; cycle 1.
    { iPureIntro.
      rewrite (finz_seq_between_split a_stk (a_stk^+4)%a); last (split; solve_addr).
      rewrite !/revoked_addresses !Forall_forall in H,Hstk_l_revoked |- *.
      intros x Hx; cbn.
      apply elem_of_app in Hx; destruct Hx as [Hx|Hx].
      + apply revoke_lookup_Revoked; apply Hstk_l_revoked; done.
      + apply H; done.
    }
    iApply (StackRevokedResources_mono_priv with "Hstk_val").
    eapply related_sts_priv_pub_trans_world; eauto.
    apply related_sts_pub_priv_world.
    eapply related_sts_pub_update_multiple_temp.
    rewrite (finz_seq_between_split a_stk (a_stk^+4)%a) in Hrevoked_stk; last (split; solve_addr).
    apply revoked_addresses_app in Hrevoked_stk as [? ?]; auto.

    + clear W' stk_mem_l stk_mem_h.
      set (stk_mem_l := [wcs0_caller; wcs1_caller; wcra_caller; wcgp_caller]).
      set (stk_mem_h := drop 4 stk_mem).
      iDestruct "H" as
        "( %Hdom_rmap & %Hcsp_bounds
           & Hna
           & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp & Hca0 & Hca1
           & Hrmap & Hstk_l & Hstk_h
           & Hworld_interp_C & Hclose
           & Hcstk_frag & HK & %Hrestored & %Hretained & [Hlc Hlc'])".
      iDestruct (wp_rules_interp.world_interp_heap_wf with "Hworld_interp_C") as %Hheap_wf_W.
      assert (heap_wf (heap_std (std_update_multiple W
        (finz.seq_between (a_stk ^+ 4)%a e_stk) Temporary))) as Hheap_wf_Wext.
      { rewrite std_update_multiple_heap. exact Hheap_wf_W. }
      pose proof (extract_temps W) as [l_unk [Hlunk_nodup Hlunk] ].

      iMod ( world_interp_revoke _ _ l_unk with "[$Hworld_interp_C]") as
        "(Hworld_interp_C & Hrevoked_l & %Hrevoked_l)"; auto.
      { split; auto. }
      iDestruct (lc_fupd_elim_later with "[$] [$Hrevoked_l]") as ">Hrevoked_l".

      iSpecialize ("Hpost" $! (std_update_multiple W (finz.seq_between (a_stk ^+ 4)%a e_stk)
                                 Temporary) rmap' (stk_mem_l++stk_mem_h) l_unk).
      rewrite revoke_std_update_multiple_eq.
      2: { apply Forall_forall.
           intros a Ha.
           assert (a ∈ finz.seq_between a_stk e_stk) as Ha'.
           { rewrite elem_of_finz_seq_between.
             rewrite elem_of_finz_seq_between in Ha.
             solve_addr.
           }
           rewrite list_elem_of_lookup in Ha'; destruct Ha' as [? ?].
           rewrite /revoked_addresses Forall_forall in Hrevoked_stk.
           eapply Hrevoked_stk; eauto.
           by apply list_elem_of_lookup_2 in H.
      }
      assert (filter_heap (std_update_multiple W
        (finz.seq_between (a_stk ^+ 4)%a e_stk) Temporary) rcs1 = rcs1)
        as Hretained_Wext.
      { rewrite /filter_heap std_update_multiple_heap. exact Hretained. }
      iApply "Hpost"; iFrame "∗%#".
      iSplit.
      { iPureIntro.
        split.
        - apply NoDup_app; split; auto.
          split; last by apply finz_seq_between_NoDup.
          intros a Ha. apply Hlunk in Ha.
          intro Ha'.
          rewrite /revoked_addresses  Forall_forall in Hrevoked_stk.
           assert (a ∈ finz.seq_between a_stk e_stk) as Ha''.
           { rewrite elem_of_finz_seq_between.
             rewrite elem_of_finz_seq_between in Ha'.
             solve_addr.
           }
           apply Hrevoked_stk in Ha''.
           simplify_eq.
        - intros a; cbn.
          rewrite elem_of_app.
          split; intro Ha.
          + destruct ( decide ( a ∈ finz.seq_between (a_stk ^+ 4)%a e_stk )); first (right; done).
            rewrite std_sta_update_multiple_lookup_same_i in Ha; auto.
            apply Hlunk in Ha.
            left; done.
          + destruct Ha as [Ha|Ha]; cycle 1.
            * rewrite std_sta_update_multiple_lookup_in_i; auto.
            * destruct ( decide ( a ∈ finz.seq_between (a_stk ^+ 4)%a e_stk )); first (rewrite std_sta_update_multiple_lookup_in_i; auto).
              rewrite std_sta_update_multiple_lookup_same_i; auto.
              apply Hlunk in Ha; done.
      }
      iSplitL "Hrevoked_l".
      {
        iApply (RevokedResources_mono_pub with "Hrevoked_l"); auto.
        eapply related_sts_pub_update_multiple_temp.
        rewrite (finz_seq_between_split a_stk (a_stk^+4)%a) in Hrevoked_stk; last (split; solve_addr).
        apply revoked_addresses_app in Hrevoked_stk as [? ?]; auto.
      }
      iSplit.
      {
        iPureIntro.
        apply related_sts_pub_refl_world.
      }
      iSplit.
      {
        iPureIntro.
        intros k a Ha; cbn.
        apply std_sta_update_multiple_lookup_in_i.
        apply list_elem_of_lookup; eauto.
      }
      iSplitL "Hclose".
      { iApply (StackRevokedResources_mono_priv with "Hclose"); auto.
        apply related_sts_pub_priv_world.
        eapply related_sts_pub_update_multiple_temp.
        rewrite (finz_seq_between_split a_stk (a_stk^+4)%a) in Hrevoked_stk; last (split; solve_addr).
        apply revoked_addresses_app in Hrevoked_stk as [? ?]; auto.
      }
      iSplit; first iPureIntro.
      { eapply Forall_impl; eauto.
        cbn; intros a Ha.
        apply revoke_lookup_Revoked; done.
      }
      iSplit; first iApply interp_int.
      iSplit; first iApply interp_int.
      iApply (region_pointsto_split _ _ (a_stk ^+4)%a); last iFrame.
      { solve_addr+ Hcsp_bounds. }
      { subst stk_mem_l. cbn.
        destruct Hcsp_bounds as (?&?&Ha4).
        pose proof (finz_incr_iff_dist a_stk (a_stk ^+ 4)%a 4) as [Hdist _].
        by apply Hdist in Ha4 as [? ?].
      }
  Qed.

End Switcher.
