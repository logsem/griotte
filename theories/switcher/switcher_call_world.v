From iris.proofmode Require Import proofmode.
From griotte Require Import logrel monotone interp_weakening memory_region rules proofmode.
From griotte Require Import sts_multiple_updates region_invariants_revocation.
From griotte Require Import world_ghost_theory world_interp_stack stack_world_resources.
From griotte Require Import map_simpl register_tactics.
From griotte Require Import switcher_call_states.

(** * Logical steps of the call routine of the switcher

    The lemmas of this file do not execute code. They are used between the
    block groups of [switcher_call_blocks_n] by the proofs of
    [switcher_cc_specification_gen] and [interp_expr_switcher_call]. *)

Section Switcher_Call_World.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (** ** Stack frame of an untrusted caller

      When the caller is untrusted, its stack is shared in the world. The
      switcher opens the part [[a, e)] of the stack above the stack pointer
      to spill the callee-save registers and to clear the callee's frame,
      and then closes it with safe words. *)

  Lemma StackWorldResource_update W C a v v' :
    interp W C v' -∗
    StackWorldResource interp W C a v -∗
    StackWorldResource interp W C a v'.
  Proof.
    iIntros "#Hv' (%φ & %p & _ & _ & Hrel & Hvalid & %Hflow)".
    iDestruct "Hvalid" as "(#Hmono & #Hzcond & #Hrcond & #Hwcond & %Hpers)".
    iExists φ, p; iFrame "∗ # %".
    iSplit; first (iApply "Hwcond"; done).
    rewrite /mono_temporary.
    assert (isWL p = true) as HWL by (eapply isWL_flowsto; eauto).
    rewrite decide_True; last (left; done).
    iApply "Hmono".
  Qed.

  Lemma StackWorldResources_update W C (la : list Addr) (lv lv' : list Word) :
    length lv' = length lv ->
    StackWorldResources interp W C la lv -∗
    ([∗ list] w ∈ lv', interp W C w) -∗
    StackWorldResources interp W C la lv'.
  Proof.
    iIntros (Hlen) "H Hlv'".
    iStopProof.
    revert lv lv' Hlen.
    induction la as [|a la IH]; iIntros (lv lv' Hlen) "[H Hlv']".
    - iDestruct (StackWorldResources_length with "H") as %Hlen_la.
      destruct lv; last done.
      destruct lv'; last done.
      done.
    - iDestruct (StackWorldResources_length with "H") as %Hlen_la.
      destruct lv as [|v lv]; first done.
      destruct lv' as [|v' lv']; first done.
      iDestruct "H" as "[Ha H]".
      iDestruct "Hlv'" as "[Hv' Hlv']".
      iSplitL "Ha Hv'"; first (iApply (StackWorldResource_update with "Hv' Ha")).
      iApply (IH lv lv' with "[$H $Hlv']"); cbn in *; lia.
  Qed.

  (** The opened part [[a, e)] of the stack, containing [lv]. *)
  Definition switcher_stk_opened W C (a e : Addr) (lv : list Word) : iProp Σ :=
    world_interp_open W C (finz.seq_between a e) ∗
    StackOpenWorldResources interp W C (finz.seq_between a e) lv.

  Lemma switcher_call_stk_open W C (b e a : Addr) :
    (b <= a)%a ->
    interp W C (WCap RWL Local b e a) -∗
    world_interp W C -∗
    ∃ lv,
      [[ a , e ]] ↦ₐ [[ lv ]] ∗
      ▷ switcher_stk_opened W C a e lv ∗
      ▷ ([∗ list] w ∈ lv, interp W C w).
  Proof.
    iIntros (Hba) "#Hinterp Hworld".
    iEval (rewrite open_world_interp_empty) in "Hworld".
    iDestruct (open_world_interp_opening_resources _ _ (finz.seq_between a e) []
                with "[$Hinterp $Hworld]")
      as "(Hworld & %lv & Hstk & Hres)".
    { apply finz_seq_between_NoDup. }
    { apply Forall_forall; intros a' Ha'.
      apply elem_of_finz_seq_between in Ha'; solve_addr. }
    { set_solver+. }
    rewrite app_nil_r.
    iDestruct "Hres" as "[#Hsw Hst]".
    iExists lv; iFrame.
    iFrame "Hsw". iNext.
    iDestruct (big_sepL2_impl _ (λ _ _ v, interp W C v) with "Hsw []") as "Hlv".
    { iIntros "!>" (k a' v Ha' Hv) "Hr". iApply (StackWorldResource_interp with "Hr"). }
    iDestruct (big_sepL2_const_sepL_r with "Hlv") as "[_ $]".
  Qed.

  Lemma switcher_call_stk_close W C (a e : Addr) (lv lv' : list Word) :
    length lv' = length lv ->
    switcher_stk_opened W C a e lv -∗
    [[ a , e ]] ↦ₐ [[ lv' ]] -∗
    ([∗ list] w ∈ lv', interp W C w) -∗
    world_interp W C.
  Proof.
    iIntros (Hlen) "[Hworld [Hsw Hst]] Hstk #Hlv'".
    iDestruct (StackWorldResources_length with "Hsw") as "%Hlen_la".
    iDestruct (StackWorldResources_update with "Hsw Hlv'") as "Hsw"; first done.
    iEval (rewrite -(app_nil_r (finz.seq_between a e))) in "Hworld".
    iDestruct (close_world_interp_opening_resources _ _ lv' (finz.seq_between a e) []
                with "[$Hworld $Hstk $Hsw $Hst]") as "Hworld".
    { apply finz_seq_between_NoDup. }
    { set_solver+. }
    { by rewrite Hlen -Hlen_la. }
    by rewrite -open_world_interp_empty.
  Qed.

  (** ** Entry point of the callee *)

  (** The sealing predicate of [ot_switcher] describes the entry point of
      the callee, once unsealed. *)
  Lemma switcher_entry_point_prop W C (wct1 : Word) :
    seal_pred ot_switcher ot_switcher_propC -∗
    (if is_sealed_with_o wct1 ot_switcher then interp W C wct1 else True) -∗
    ▷ (∀ wsb, ⌜ wct1 = WSealed ot_switcher wsb ⌝ -∗ ot_switcher_prop W C (WSealable wsb)).
  Proof.
    iIntros "#Hp_ot_switcher #Htarget_v".
    destruct (is_sealed_with_o wct1 ot_switcher) eqn:Hsealed; cycle 1.
    { iIntros "!>" (wsb ->); cbn in Hsealed.
      by rewrite Z.eqb_refl in Hsealed. }
    assert (∃ wsb0, wct1 = WSealed ot_switcher wsb0) as [wsb0 ->].
    { destruct wct1 as [ | [] | |]; cbn in Hsealed; try discriminate.
      exists sb. apply Z.eqb_eq in Hsealed.
      replace ot with ot_switcher by solve_addr.
      done.
    }
    rewrite (fixpoint_interp1_eq _ _ (WSealed ot_switcher wsb0)).
    iDestruct "Htarget_v" as (P HpersP) "(_ & HPseal & HP & _)".
    iDestruct (seal_pred_agree with "Hp_ot_switcher HPseal") as "Hagree".
    iSpecialize ("Hagree" $! (W,C,WSealable wsb0)).
    iNext; iIntros (wsb Hwsb); simplify_eq.
    iSimpl in "Hagree".
    iRewrite -"Hagree" in "HP".
    done.
  Qed.

  (** The registers when entering the callee. *)
  Lemma switcher_call_entry_registers W W' C (nargs : nat)
    (arg_rmap' rmap' : Reg) (wpcc wcgp wstk : Word) :
    related_sts_pub_world W W' ->
    is_arg_rmap arg_rmap' 8 ->
    dom rmap' = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ PC ; cra ; cgp ; csp ]}) ->

    PC ↦ᵣ wpcc ∗
    cgp ↦ᵣ wcgp ∗
    cra ↦ᵣ WSentry XSRW_ Local b_switcher e_switcher a_switcher_return ∗
    csp ↦ᵣ wstk ∗
    interp W' C wstk ∗
    ( [∗ map] r↦w ∈ arg_rmap',
        r ↦ᵣ w ∗ if decide (r ∈ dom_arg_rmap nargs) then interp W C w else ⌜ w = WInt 0 ⌝ ) ∗
    ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
    -∗
    ∃ regs,
      registers_pointsto regs ∗
      execute_entry_point_register wpcc wcgp wstk nargs W' C regs.
  Proof.
    iIntros (Hrelated Harg_rmap' Hrmap')
      "(HPC & Hcgp & Hcra & Hcsp & #Hstk & Hargs & Hregs)".
    iDestruct (big_sepM_sep with "Hregs") as "[Hregs #Hnil]".
    iDestruct (big_sepM_sep with "Hargs") as "[Hargs #Hval]".
    iDestruct (big_sepM_union with "[$Hargs $Hregs]") as "Hregs".
    { apply map_disjoint_dom. rewrite Hrmap' Harg_rmap'.
      set_solver+. }
    iDestruct (big_sepM_insert_2 with "[Hcsp] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hcra] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hcgp] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[HPC] Hregs") as "Hregs";[iFrame|].
    iExists _; iFrame "Hregs".
    cbn.
    iSplit.
    { iPureIntro. intros rr. clear -Harg_rmap' Hrmap'.
      destruct (decide (rr = PC));simplify_map_eq;[eauto|].
      destruct (decide (rr = cgp));simplify_map_eq;[eauto|].
      destruct (decide (rr = cra));simplify_map_eq;[eauto|].
      destruct (decide (rr = csp));simplify_map_eq;[eauto|].
      apply elem_of_dom. rewrite dom_union_L Hrmap' Harg_rmap'.
      rewrite difference_union_distr_r_L union_intersection_l.
      rewrite -union_difference_L;[|apply all_registers_subseteq].
      apply elem_of_intersection. split;[apply all_registers_s_correct|].
      apply elem_of_union. right.
      apply elem_of_difference. split;[apply all_registers_s_correct|set_solver]. }
    repeat iSplit.
    - iPureIntro. simplify_map_eq. reflexivity.
    - iPureIntro. clear. simplify_map_eq. auto.
    - iPureIntro. clear. simplify_map_eq. auto.
    - iPureIntro. clear. simplify_map_eq. done.
    - done.
    - iIntros (r v Hr Hv).
      assert (r ∉ ({[ PC ; cgp ; cra ; csp ]} : gset RegName)) as Hr'.
      {
        clear -Hr.
        do 8 (destruct nargs; first set_solver).
        induction nargs.
        + set_solver+Hr.
        + apply IHnargs; set_solver+Hr.
      }
      repeat (rewrite lookup_insert_ne in Hv;[|set_solver+Hr Hr']).
      apply lookup_union_Some in Hv.
      2: {
        apply map_disjoint_dom_2.
        rewrite Harg_rmap' Hrmap' /=; set_solver+.
      }
      destruct Hv as [Hv|Hv].
      + iDestruct (big_sepM_lookup with "Hval") as "Hv";[apply Hv|].
        destruct (decide (r ∈ _)) as [|Hcontra]; last set_solver+Hcontra Hr.
        iApply (interp_monotone with "[] Hv").
        iPureIntro; done.
      + iDestruct (big_sepM_lookup with "Hnil") as "%";eauto; simplify_eq.
        iApply interp_int.
    - iIntros (r v Hr Hv).
      repeat (rewrite lookup_insert_ne in Hv;[|set_solver+Hr]).
      apply lookup_union_Some in Hv.
      2: {
        apply map_disjoint_dom_2.
        rewrite Harg_rmap' Hrmap' /=; set_solver+.
      }
      destruct Hv.
      + iDestruct (big_sepM_lookup with "Hval") as "?";eauto.
        destruct (decide (r ∈ _)) as [Hcontra|]; last iFrame "#".
        set_solver+Hcontra Hr.
      + iDestruct (big_sepM_lookup with "Hnil") as "%";eauto; simplify_eq.
  Qed.

  (** ** Switcher invariant *)

  (** Close the switcher invariant after pushing the frame [frm] on the
      trusted stack. *)
  Lemma switcher_inv_push_frame
    (frm : cframe) (cstk cstk' : CSTK) (a_tstk : Addr) (tstk_next : list Word) :
    (b_trusted_stack <= a_tstk)%a ->
    ((a_tstk ^+ 1) + 1)%a = Some (a_tstk ^+ 2)%a ->
    (a_tstk ^+ 1 < e_trusted_stack)%a ->
    (b_trusted_stack + length cstk')%a = Some a_tstk ->
    (ot_switcher < ot_switcher ^+ 1)%ot ->
    switcher_stk_bounds frm.(b_stk) frm.(e_stk) frm.(a_stk) ->

    cstack_full cstk' -∗
    cstack_frag cstk -∗
    mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack (a_tstk ^+ 1)%a -∗
    (a_tstk ^+ 1)%a ↦ₐ WCap RWL Local frm.(b_stk) frm.(e_stk) (frm.(a_stk) ^+ 4)%a -∗
    [[ (a_tstk ^+ 2)%a , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] -∗
    cstack_interp cstk' a_tstk -∗
    cframe_stk_own frm -∗
    switcher_code -∗
    b_switcher ↦ₐ WSealRange (true,true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher -∗
    seal_pred ot_switcher ot_switcher_propC
    ==∗
    switcher_inv ∗ cstack_frag (frm :: cstk).
  Proof.
    iIntros (Htstk_b Ha_tstk2 Ha_tstk1 Hlen_cstk Hot (Hba & Hba3 & Ha4))
      "Hcstk_full Hcstk Hmtdc Ha_tstk1 Htstk Hstk_interp Hframe Hcode Hb_switcher #Hp_ot_switcher".
    iDestruct (cstack_agree with "Hcstk_full Hcstk") as %->.
    iMod (cstack_update _ _ (frm :: cstk) with "Hcstk_full Hcstk") as "[Hcstk_full $]".
    iModIntro.
    iExists (a_tstk ^+ 1)%a, (frm :: cstk), tstk_next.
    iFrame "Hmtdc Hcode Hb_switcher Hcstk_full Hp_ot_switcher".
    rewrite (finz_incr_eq Ha_tstk2).
    iFrame "Htstk".
    cbn.
    replace ((a_tstk ^+ 1) ^+ -1)%a with a_tstk by solve_addr.
    iFrame.
    iPureIntro.
    repeat split; try done; try solve_addr.
  Qed.

  (** ** Functional specification *)

  (** Reinstate the callee's stack frame in the world, once cleared. *)
  Lemma switcher_cc_world_reinstate E W C (a e : Addr) :
    revoked_addresses W (finz.seq_between a e) ->
    (a + 4)%a = Some (a ^+ 4)%a ->
    (a ^+ 4 <= e)%a ->
    let W' := std_update_multiple W (finz.seq_between (a ^+ 4)%a e) Temporary in
    world_interp W C -∗
    StackRevokedResources W C (finz.seq_between a e) -∗
    [[ (a ^+ 4)%a , e ]] ↦ₐ [[ region_addrs_zeroes (a ^+ 4)%a e ]]
    ={E}=∗
    world_interp W' C ∗
    interp W' C (WCap RWL Local (a ^+ 4)%a e (a ^+ 4)%a) ∗
    ⌜ related_sts_pub_world W W' ⌝ ∗
    ⌜ revoked_addresses W (finz.seq_between (a ^+ 4)%a e) ⌝.
  Proof.
    iIntros (Hstk_revoked Ha4 He W') "Hworld_interp Hstk_val Hstk".
    rewrite (finz_seq_between_split a (a ^+ 4)%a);[|solve_addr].
    iDestruct (StackRevokedResources_app with "Hstk_val") as "[_ #Hstk_val']".
    assert (revoked_addresses W (finz.seq_between (a ^+ 4)%a e)) as Hrev.
    { clear-Hstk_revoked Ha4.
      rewrite /revoked_addresses Forall_forall in Hstk_revoked.
      rewrite /revoked_addresses Forall_forall.
      intros a' Ha'.
      apply Hstk_revoked.
      rewrite !elem_of_finz_seq_between in Ha' |- *.
      solve_addr.
    }
    iMod (world_interp_reinstate_stack with "Hworld_interp Hstk_val' Hstk") as "Hworld_interp"; auto.
    { apply finz_seq_between_NoDup. }
    { apply Forall_replicate_eq. }
    iModIntro.
    iFrame "Hworld_interp".
    iSplit; last (iPureIntro; split; [apply related_sts_pub_update_multiple_temp|]; done).
    iApply fixpoint_interp1_eq. iSimpl.
    rewrite /StackRevokedResources /StackWorldResources big_sepL2_replicate_r; last done.
    iApply (big_sepL_impl with "Hstk_val'").
    iIntros "!>" (k a' Ha') "Hr".
    iDestruct "Hr" as (φ p) "(Hφ & Hmono & Hrel & (HmonoR & Hzcond & Hrcond & Hwcond & Hpers) & %Hperm_flow)".
    iExists p,φ.
    iFrame "∗#%".
    iSplit.
    { erewrite readAllowed_flowsto; eauto. }
    iSplit.
    { erewrite writeAllowed_flowsto; eauto. }
    iSplitL "Hmono HmonoR".
    {
      rewrite /monoReq /monotonicity_guarantees_region.
      erewrite isWL_flowsto; eauto.
      subst W'.
      rewrite std_sta_update_multiple_lookup_in_i.
      2: { apply list_elem_of_lookup. eauto. }
      done.
    }
    iPureIntro. apply std_sta_update_multiple_lookup_in_i. apply list_elem_of_lookup. eauto.
  Qed.

  (** Collect the registers cleared on the exhausted path of the
      functional specification. *)
  Lemma switcher_cc_exhausted_regs (arg_rmap rmap : Reg) (wct1 wct2 wctp : Word) :
    is_arg_rmap arg_rmap 8 ->
    dom rmap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    ( [∗ map] r↦w ∈ arg_rmap, r ↦ᵣ w ) -∗
    ( [∗ map] r↦w ∈ delete ctp (delete ct2 rmap), r ↦ᵣ w ) -∗
    ct1 ↦ᵣ wct1 -∗
    ct2 ↦ᵣ wct2 -∗
    ctp ↦ᵣ wctp -∗
    ∃ (wca0 wca1 : Word) (rmap0 : Reg),
      ca0 ↦ᵣ wca0 ∗
      ca1 ↦ᵣ wca1 ∗
      ⌜ dom rmap0 = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
      ( [∗ map] r↦w ∈ rmap0, r ↦ᵣ w ).
  Proof.
    iIntros (Hrdom Hdom) "Hargs Hregs Hct1 Hct2 Hctp".
    iExtractList "Hargs" [ca0; ca1] as ["Hca0"; "Hca1"].
    iExtractList "Hargs" [ca2; ca3; ca4; ca5; ct0]
      as ["Hca2"; "Hca3"; "Hca4"; "Hca5"; "Hct0"].
    iClear "Hargs".
    iExists _, _, _; iFrame "Hca0 Hca1".
    iDestruct (big_sepM_insert_2 with "[Hctp] Hregs") as "Hregs";[iFrame|].
    rewrite insert_delete_eq.
    rewrite -delete_insert_ne; last done.
    iDestruct (big_sepM_insert_2 with "[Hct2] Hregs") as "Hregs";[iFrame|].
    rewrite insert_delete_eq.
    iDestruct (big_sepM_insert_2 with "[Hct1] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hca2] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hca3] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hca4] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hca5] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hct0] Hregs") as "Hregs";[iFrame|].
    iFrame "Hregs".
    iPureIntro.
    clear -Hdom Hrdom.
    repeat (rewrite dom_insert_L).
    rewrite Hdom /=.
    set_solver.
  Qed.

  (** Revoke the world after the callee returned: close the callee's stack
      frame in the world, and revoke the temporary addresses, including the
      caller's stack frame. *)
  Lemma switcher_cc_revoke_returned E W W2 C (b_stk e_stk a_stk : Addr)
    (stk_mem_l stk_mem_h : list Word) :
    revoked_addresses W (finz.seq_between a_stk e_stk) ->
    related_sts_pub_world
      (std_update_multiple W (finz.seq_between (a_stk ^+ 4)%a e_stk) Temporary) W2 ->
    (b_stk <= a_stk ^+ 4 ∧ a_stk ^+ 4 <= e_stk ∧ (a_stk + 4) = Some (a_stk ^+ 4))%a ->

    interp W2 C (WCap RWL Local (a_stk ^+ 4)%a e_stk (a_stk ^+ 4)%a) -∗
    StackRevokedResources W C (finz.seq_between a_stk e_stk) -∗
    world_interp_open W2 C (finz.seq_between (a_stk ^+ 4)%a e_stk) -∗
    StackOpenWorldResources interp W2 C (finz.seq_between (a_stk ^+ 4)%a e_stk) stk_mem_h -∗
    [[ a_stk , (a_stk ^+ 4)%a ]] ↦ₐ [[ stk_mem_l ]] -∗
    [[ (a_stk ^+ 4)%a , e_stk ]] ↦ₐ [[ stk_mem_h ]] -∗
    £ 2
    ={E}=∗
    ∃ (stk_mem : list Word) (l' : list Addr),
      ⌜ extract_temporaries_condition W2 (l' ++ finz.seq_between (a_stk ^+ 4)%a e_stk) ⌝ ∗
      RevokedResources W2 C l' ∗
      ⌜ revoked_addresses (revoke W2) l' ⌝ ∗
      StackRevokedResources W2 C (finz.seq_between a_stk e_stk) ∗
      ⌜ revoked_addresses (revoke W2) (finz.seq_between a_stk e_stk) ⌝ ∗
      world_interp (revoke W2) C ∗
      [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]].
  Proof.
    iIntros (Hrevoked_stk Hrelated_pub_Wext_W2 Hcsp_bounds)
      "#Hinterp_W2_csp #Hstk_val Hworld_interp_C Hstack_revoked_W2 Hstk_l Hstk_h [Hlc Hlc']".
    iDestruct ( big_sepL2_length with "Hstk_h" ) as "%Hlen_stk_h".
    iDestruct ( big_sepL2_length with "Hstk_l" ) as "%Hlen_stk_l".
    iEval (rewrite <- (app_nil_r (finz.seq_between (a_stk ^+ 4)%a e_stk))) in "Hworld_interp_C".

    iDestruct (close_world_interp_opening_resources
                with "[$Hworld_interp_C $Hstack_revoked_W2 $Hstk_h]")
      as "Hworld_interp_C".
    { apply finz_seq_between_NoDup. }
    { set_solver+. }
    { by rewrite finz_seq_between_length in Hlen_stk_l. }
    rewrite -open_world_interp_empty.

    iMod (world_interp_revoked_by_separation_many with "[$Hworld_interp_C $Hstk_l]")
      as "(Hworld_interp_C & Hstk_l & %Hstk_l_revoked)".
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
    iModIntro.
    iExists _, l'; iFrame "∗ %".
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
  Qed.

  (** Revoke the world after the trusted stack was exhausted. The world is
      the one of the call, where the callee's stack frame is [Temporary]. *)
  Lemma switcher_cc_revoke_exhausted E W C (b_stk e_stk a_stk : Addr)
    (stk_mem_l stk_mem_h : list Word) :
    let W2 := std_update_multiple W (finz.seq_between (a_stk ^+ 4)%a e_stk) Temporary in
    revoked_addresses W (finz.seq_between a_stk e_stk) ->
    (b_stk <= a_stk ^+ 4 ∧ a_stk ^+ 4 <= e_stk ∧ (a_stk + 4) = Some (a_stk ^+ 4))%a ->
    length stk_mem_l = 4 ->

    world_interp W C -∗
    StackRevokedResources W C (finz.seq_between a_stk e_stk) -∗
    [[ a_stk , (a_stk ^+ 4)%a ]] ↦ₐ [[ stk_mem_l ]] -∗
    [[ (a_stk ^+ 4)%a , e_stk ]] ↦ₐ [[ stk_mem_h ]] -∗
    £ 2
    ={E}=∗
    ∃ (l' : list Addr),
      ⌜ extract_temporaries_condition W2 (l' ++ finz.seq_between (a_stk ^+ 4)%a e_stk) ⌝ ∗
      RevokedResources W2 C l' ∗
      ⌜ revoked_addresses (revoke W2) l' ⌝ ∗
      ⌜ related_sts_pub_world W2 W2 ⌝ ∗
      ([∗ list] a ∈ finz.seq_between (a_stk ^+ 4)%a e_stk, ⌜ std W2 !! a = Some Temporary ⌝) ∗
      StackRevokedResources W2 C (finz.seq_between a_stk e_stk) ∗
      ⌜ revoked_addresses (revoke W2) (finz.seq_between a_stk e_stk) ⌝ ∗
      world_interp (revoke W2) C ∗
      [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem_l ++ stk_mem_h ]].
  Proof.
    intros W2.
    iIntros (Hrevoked_stk Hcsp_bounds Hlen_l)
      "Hworld_interp_C #Hclose Hstk_l Hstk_h [Hlc Hlc']".
    pose proof (extract_temps W) as [l_unk [Hlunk_nodup Hlunk] ].

    iMod ( world_interp_revoke _ _ l_unk with "[$Hworld_interp_C]") as
      "(Hworld_interp_C & Hrevoked_l & %Hrevoked_l)"; auto.
    { split; auto. }
    iDestruct (lc_fupd_elim_later with "[$] [$Hrevoked_l]") as ">Hrevoked_l".
    iModIntro.
    subst W2.
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
    iExists l_unk; iFrame "∗%#".
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
    iSplitR "Hstk_l Hstk_h".
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
    iApply (region_pointsto_split _ _ (a_stk ^+4)%a); last iFrame.
    { solve_addr+ Hcsp_bounds. }
    { rewrite Hlen_l.
      destruct Hcsp_bounds as (?&?&Ha4).
      pose proof (finz_incr_iff_dist a_stk (a_stk ^+ 4)%a 4) as [Hdist _].
      by apply Hdist in Ha4 as [? ?].
    }
  Qed.

End Switcher_Call_World.
