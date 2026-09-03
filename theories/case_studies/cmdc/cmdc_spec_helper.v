From iris.proofmode Require Import proofmode.
From griotte Require Import logrel rules monotone interp_weakening.
From griotte Require Import switcher_spec_call cmdc.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import proofmode register_tactics map_simpl.

Section CMDC_Call_Phase.
  Context
    {Σ : gFunctors}
    {ceriseg : ceriseG Σ} {sealsg : sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP : MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}
  .

  (** The common semantic phase of a one-argument Cmdc call. The caller has
      already executed [Jalr], so the switcher owns [PC]. This lemma turns the
      argument address into a permanent shared region, performs the switcher
      call, and returns all caller registers and stack resources to the
      supplied continuation. In doing so it relinquishes [shared_addr] into
      the world: the caller gives up its points-to resource and receives the
      permanent shared relation back. Keeping the instruction-specific [Jalr],
      loads, and moves outside this contract lets both Cmdc calls share the
      expensive world and register-map reasoning without hiding their concrete
      code. *)
  Lemma cmdc_call_adv_block_spec
      (Nswitcher : namespace)
      (W0 : WORLD) (C : CmptName)
      (shared_addr shared_addr_e : Addr) (target : Sealable)
      (wcgp wcra wcs0 wcs1 : Word)
      (wca1 wca2 wca3 wca4 wca5 : Word)
      (b_stk e_stk a_stk : Addr)
      (stk_mem : list Word) (rmap : Reg)
      (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    let Wcall := <s[shared_addr := Permanent]s>W0 in
    let shared_addr_cap :=
      WCap RW Global shared_addr shared_addr_e shared_addr in
    let target_word := WSealed ot_switcher target in
    let arg_rmap : Reg :=
      {[ ca0 := shared_addr_cap;
         ca1 := wca1;
         ca2 := wca2;
         ca3 := wca3;
         ca4 := wca4;
         ca5 := wca5;
         ct0 := WInt 0 ]} in
    let callee_stk_region := finz.seq_between (a_stk ^+ 4)%a e_stk in
    (shared_addr + 1)%a = Some shared_addr_e ->
    shared_addr ∉ dom (std W0) ->
    shared_addr ∉ finz.seq_between b_stk e_stk ->
    revoked_addresses W0 (finz.seq_between b_stk e_stk) ->
    (b_stk <= a_stk)%a ->
    dom rmap =
      all_registers_s ∖
        ({[ PC; cgp; cra; csp; ct1; cs0; cs1 ]} ∪ dom_arg_rmap 8) ->

    (na_inv cerise_nais Nswitcher switcher_inv
    ∗ na_own cerise_nais ⊤
    ∗ PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ wcgp
    ∗ cra ↦ᵣ wcra
    ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
    ∗ ct1 ↦ᵣ target_word
    ∗ cs0 ↦ᵣ wcs0
    ∗ cs1 ↦ᵣ wcs1
    ∗ ca0 ↦ᵣ shared_addr_cap
    ∗ ca1 ↦ᵣ wca1
    ∗ ca2 ↦ᵣ wca2
    ∗ ca3 ↦ᵣ wca3
    ∗ ca4 ↦ᵣ wca4
    ∗ ca5 ↦ᵣ wca5
    ∗ ct0 ↦ᵣ WInt 0
    ∗ ([∗ map] r ↦ w ∈ rmap, r ↦ᵣ w)
    ∗ shared_addr ↦ₐ WInt 0
    ∗ [[a_stk, e_stk]] ↦ₐ [[stk_mem]]
    ∗ world_interp W0 C
    ∗ StackRevokedResources W0 C (finz.seq_between a_stk e_stk)
    ∗ cstack_frag cstk
    ∗ interp_continuation cstk Ws Cs
    ∗ interp W0 C target_word
    ∗ target_word ↦□ₑ 1)%I

    ∗ ▷ (∀
          (Wret : WORLD) (rmap' : Reg)
          (stk_mem' : list Word) (l' : list Addr),
        (⌜extract_temporaries_condition Wret (l' ++ callee_stk_region)⌝
        ∗ RevokedResources Wret C l'
        ∗ ⌜revoked_addresses (revoke Wret) l'⌝
        ∗ ⌜related_sts_pub_world (std_update_multiple Wcall callee_stk_region Temporary) Wret⌝
        ∗ ([∗ list] a ∈ callee_stk_region, ⌜std Wret !! a = Some Temporary⌝)
        ∗ ⌜std (revoke Wret) !! shared_addr = Some Permanent⌝
        ∗ rel C shared_addr RW interpC
        ∗ ⌜dom rmap' = all_registers_s ∖ {[ PC; cgp; cra; csp; ca0; ca1; cs0; cs1 ]}⌝
        ∗ StackRevokedResources Wret C (finz.seq_between a_stk e_stk)
        ∗ ⌜revoked_addresses (revoke Wret) (finz.seq_between a_stk e_stk)⌝
        ∗ na_own cerise_nais ⊤
        ∗ ⌜(b_stk <= (a_stk ^+ 4)%a
             ∧ (a_stk ^+ 4)%a <= e_stk
             ∧ (a_stk + 4)%a = Some (a_stk ^+ 4)%a)%a⌝
        ∗ world_interp (revoke Wret) C
        ∗ cstack_frag cstk
        ∗ PC ↦ᵣ updatePcPerm wcra
        ∗ cgp ↦ᵣ wcgp
        ∗ cra ↦ᵣ wcra
        ∗ cs0 ↦ᵣ wcs0
        ∗ cs1 ↦ᵣ wcs1
        ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
        ∗ (∃ warg0, ca0 ↦ᵣ warg0 ∗ interp Wret C warg0)
        ∗ (∃ warg1, ca1 ↦ᵣ warg1 ∗ interp Wret C warg1)
        ∗ ([∗ map] r ↦ w ∈ rmap', r ↦ᵣ w ∗ ⌜w = WInt 0⌝)
        ∗ [[a_stk, e_stk]] ↦ₐ [[stk_mem']]
        ∗ interp_continuation cstk Ws Cs)%I
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Wcall shared_addr_cap target_word arg_rmap callee_stk_region
      Hshared_addr_e Hshared_addr_fresh Hshared_addr_stk Hrevoked_stk
      Hstk_lower Hrmap_dom).
    iIntros "(Hpre & Hcont)".
    iDestruct "Hpre" as
      "(#Hswitcher & Hna & HPC & Hcgp & Hcra & Hcsp
      & Hct1 & Hcs0 & Hcs1
      & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & Hct0 & Hrmap
      & Hshared_addr & Hstk & Hworld & Hstack_revoked & Hcstk & HK
      & #Htarget & #Hentry)".

    (* Relinquish [shared_addr] and prove that its capability is safe to share.
       Install the singleton as a permanent region and retain its relation for
       the caller's subsequent access through the shared address. *)
    iDestruct (init_PermRes W0 C shared_addr RW interpC
      with "[] [$Hshared_addr] []") as "Hshared_addr".
    { done. }
    { iApply future_priv_mono_interp_z. }
    { iApply interp_int. }
    iMod (world_interp_extend_perm with "Hworld Hshared_addr")
      as "(Hworld & Hrel_shared_addr)"; auto.

    assert (related_sts_priv_world W0 Wcall) as HW0_priv_Wcall.
    { subst Wcall. by eapply related_sts_priv_world_fresh_Permanent. }

    iAssert (interp Wcall C shared_addr_cap) as "#Hshared_addr_cap".
    { subst shared_addr_cap.
      iEval (cbn). iEval (rewrite fixpoint_interp1_eq). iEval (cbn).
      rewrite (finz_seq_between_cons shared_addr); last solve_addr.
      rewrite (finz_seq_between_empty (shared_addr ^+ 1)%a);
        last solve_addr+Hshared_addr_e.
      iApply big_sepL_singleton.
      iExists RW, interp.
      iEval (cbn).
      iSplit; first done.
      iSplit; first (iPureIntro; by apply persistent_cond_interp).
      iSplit; first iFrame "Hrel_shared_addr".
      iSplit; first (iNext; by iApply zcond_interp).
      iSplit; first (iNext; by iApply rcond_interp).
      iSplit; first (iNext; by iApply wcond_interp).
      subst Wcall.
      iSplit.
      - iApply (monoReq_interp _ _ _ _ Permanent); last done.
        rewrite /std_update. by rewrite lookup_insert_eq.
      - iPureIntro. by rewrite lookup_insert_eq.
    }

    (* Prove that the callee's entry point is safe to share. Private-world
       monotonicity preserves the sealed entry point. *)
    iAssert (interp Wcall C target_word) as "#Htarget_call".
    { iApply interp_monotone_sd; eauto. }

    (* Prepare the argument registers for the call. Only [ca0] is semantically
       live for a one-argument call; the complete seven-register map is still
       supplied because that is the switcher's calling convention. *)
    iAssert
      ([∗ map] rarg ↦ warg ∈ arg_rmap,
        rarg ↦ᵣ warg ∗
          if decide (rarg ∈ dom_arg_rmap 1)
          then interp Wcall C warg else True)%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hargs".
    { subst arg_rmap.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done.
    }

    (* Prepare the stack resources required by the cross-compartment call
       specification. *)
    assert (revoked_addresses Wcall (finz.seq_between b_stk e_stk))
      as Hrevoked_stk_call.
    { rewrite /revoked_addresses Forall_forall.
      rewrite /revoked_addresses Forall_forall in Hrevoked_stk.
      intros a Ha. subst Wcall. cbn.
      rewrite lookup_insert_ne;
        last (intros ->; set_solver+Hshared_addr_stk Ha).
      by apply Hrevoked_stk.
    }
    assert (revoked_addresses Wcall (finz.seq_between a_stk e_stk))
      as Hrevoked_call_frame.
    { eapply revoked_addresses_weaken; last exact Hrevoked_stk_call.
      intros a Ha.
      rewrite !elem_of_finz_seq_between in Ha |- *.
      solve_addr+Hstk_lower Ha.
    }
    iDestruct (StackRevokedResources_mono_priv with "Hstack_revoked")
      as "Hstack_revoked"; eauto.

    iApply (switcher_cc_specification _ Wcall with
      "[- $Hswitcher $Hna $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1
       $Hargs $Hrmap $Hstk $Hworld $Hstack_revoked $Hcstk $HK
       $Htarget_call $Hentry]").
    - exact Hrmap_dom.
    - subst arg_rmap. by rewrite /is_arg_rmap.
    - iSplit; first done.

      iNext.
      iIntros (Wret rmap' stk_mem' l')
      "(%Hextract & Hrevoked_l & %Hrevoked_l_revoke
      & %HWcall_pub_Wret & Hcallee_temporary
      & %Hrmap'_dom & Hstack_revoked & %Hrevoked_stk_revoke
      & Hna & %Hstk_bounds & Hworld & Hcstk
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & Hca0 & Hca1 & Hrmap & Hstk & HK)".

      assert (shared_addr ∉ callee_stk_region) as Hshared_addr_callee.
      { subst callee_stk_region.
        intro Hshared_addr_range. apply Hshared_addr_stk.
        rewrite !elem_of_finz_seq_between in Hshared_addr_range |- *.
        solve_addr+Hstk_lower Hshared_addr_range.
      }
      assert (std Wret !! shared_addr = Some Permanent)
        as Hshared_addr_perm.
      { eapply region_state_pub_perm; first exact HWcall_pub_Wret.
        subst Wcall callee_stk_region.
        rewrite std_update_multiple_insert_commute;
          last exact Hshared_addr_callee.
        by rewrite lookup_insert_eq.
      }
      assert (std (revoke Wret) !! shared_addr = Some Permanent)
        as Hshared_addr_perm_revoke.
      { by apply revoke_lookup_Perm. }

      iApply ("Hcont" $! Wret rmap' stk_mem' l' with "[-]").
      iFrame "∗#%".
  Qed.
End CMDC_Call_Phase.
