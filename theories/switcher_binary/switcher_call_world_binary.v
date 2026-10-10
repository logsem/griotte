From iris.proofmode Require Import proofmode.
From griotte Require Import sts_multiple_updates.
From griotte Require Import logrel_binary monotone_binary interp_weakening_binary.
From griotte Require Import memory_region memory_region_binary rules proofmode proofmode_binary.
From griotte Require Import region_invariants_revocation_binary.
From griotte Require Import world_ghost_theory_binary world_interp_stack_binary stack_world_resources_binary.
From griotte Require Import map_simpl register_tactics register_tactics_binary.
From griotte Require Import switcher_call_states_binary.

(** * Logical steps of the call routine of the switcher, binary model

    The lemmas of this file do not execute code. They are used between the
    block groups of [switcher_call_blocks_n_binary] by the proofs of
    [switcher_cc_specification_gen] and [interp_expr_switcher_call]. *)

Section Switcher_Call_World.
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

  (** ** Stack frame of an untrusted caller

      When the caller is untrusted, its stack is shared in the world. The
      switcher opens the part [[a, e)] of the stack above the stack pointer,
      in both runs, to spill the callee-save registers and to clear the
      callee's frame, and then closes it with related words. *)

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

  Lemma StackWorldResources_update W C (la : list Addr) (lv slv lv' slv' : list Word) :
    length lv' = length lv ->
    length slv' = length lv' ->
    StackWorldResources interp W C la lv slv -∗
    ([∗ list] w;sw ∈ lv';slv', interp W C (w, sw)) -∗
    StackWorldResources interp W C la lv' slv'.
  Proof.
    iIntros (Hlen Hslen) "[%Hlen0 H] Hlv'".
    iSplit; first (iPureIntro; lia).
    iDestruct (big_sepL2_length with "H") as %Hl.
    rewrite length_zip Hlen0 Nat.min_id in Hl.
    iInduction la as [|a la] "IH" forall (lv slv lv' slv' Hlen Hslen Hlen0 Hl).
    - destruct slv as [|]; last (cbn in Hl; lia).
      destruct lv as [|]; last (cbn in Hlen0; lia).
      destruct lv' as [|]; last (cbn in Hlen; lia).
      destruct slv' as [|]; last (cbn in Hslen; lia).
      done.
    - destruct slv as [|sv slv]; first (cbn in Hl; lia).
      destruct lv as [|v lv]; first (cbn in Hlen0; lia).
      destruct lv' as [|v' lv']; first (cbn in Hlen; lia).
      destruct slv' as [|sv' slv']; first (cbn in Hslen; lia).
      iDestruct "H" as "[Ha H]".
      iDestruct "Hlv'" as "[Hv' Hlv']".
      iSplitL "Ha Hv'"; first (iApply (StackWorldResource_update with "Hv' Ha")).
      iApply ("IH" with "[] [] [] [] H Hlv'"); iPureIntro; cbn in *; lia.
  Qed.

  (** The opened part [[a, e)] of the stack, containing [lv] and [slv]. *)
  Definition switcher_stk_opened W C (a e : Addr) (lv slv : list Word) : iProp Σ :=
    world_interp_open W C (finz.seq_between a e) ∗
    StackOpenWorldResources interp W C (finz.seq_between a e) lv slv.

  Lemma switcher_call_stk_open W C (b e a : Addr) :
    (b <= a)%a ->
    interp W C (WCap RWL Local b e a, WCap RWL Local b e a) -∗
    world_interp W C -∗
    ∃ lv slv,
      [[ a , e ]] ↦ₐ [[ lv ]] ∗
      [[ a , e ]] ↣ₐ [[ slv ]] ∗
      ▷ switcher_stk_opened W C a e lv slv ∗
      ▷ ([∗ list] w;sw ∈ lv;slv, interp W C (w, sw)).
  Proof.
    iIntros (Hba) "#Hinterp Hworld".
    iEval (rewrite open_world_interp_empty) in "Hworld".
    iDestruct (open_world_interp_opening_resources _ _ (finz.seq_between a e) []
                with "[$Hinterp $Hworld]")
      as "(Hworld & %lv & %slv & Hstk & Hsstk & Hres)".
    { apply finz_seq_between_NoDup. }
    { apply Forall_forall; intros a' Ha'.
      apply elem_of_finz_seq_between in Ha'; solve_addr. }
    { set_solver+. }
    rewrite app_nil_r.
    iDestruct "Hres" as "[#Hsw Hst]".
    iExists lv, slv; iFrame "Hstk Hsstk Hworld Hsw Hst".
    iNext.
    iDestruct "Hsw" as "[%Hlen Hsw]".
    iDestruct (big_sepL2_impl _ (λ _ _ v, interp W C v) with "Hsw []") as "Hlv".
    { iIntros "!>" (k a' v Ha' Hv) "Hr". iApply (StackWorldResource_interp with "Hr"). }
    iDestruct (big_sepL2_const_sepL_r with "Hlv") as "[_ Hlv2]".
    iApply big_sepL2_alt.
    iSplit; first done.
    iApply (big_sepL_impl with "Hlv2").
    iIntros "!>" (k [w sw] _) "$".
  Qed.

  Lemma switcher_call_stk_close W C (a e : Addr) (lv slv lv' slv' : list Word) :
    length lv' = length lv ->
    length slv' = length lv' ->
    switcher_stk_opened W C a e lv slv -∗
    [[ a , e ]] ↦ₐ [[ lv' ]] -∗
    [[ a , e ]] ↣ₐ [[ slv' ]] -∗
    ([∗ list] w;sw ∈ lv';slv', interp W C (w, sw)) -∗
    world_interp W C.
  Proof.
    iIntros (Hlen Hslen) "[Hworld [Hsw Hst]] Hstk Hsstk #Hlv'".
    iDestruct (StackWorldResources_length with "Hsw") as "%Hlen_la".
    iDestruct (StackWorldResources_update with "Hsw Hlv'") as "Hsw"; [done|done|].
    iEval (rewrite -(app_nil_r (finz.seq_between a e))) in "Hworld".
    iDestruct (close_world_interp_opening_resources _ _ lv' slv' (finz.seq_between a e) []
                with "[$Hworld $Hstk $Hsstk $Hsw $Hst]") as "Hworld".
    { apply finz_seq_between_NoDup. }
    { set_solver+. }
    { destruct Hlen_la; lia. }
    by rewrite -open_world_interp_empty.
  Qed.

  (** ** Entry point of the callee *)

  (** The sealing predicate of [ot_switcher] describes the entry point of
      the callee, once unsealed. It relates identical entry points, hence
      the spec run unseals the same entry point. *)
  Lemma switcher_entry_point_prop W C (wct1 swct1 : Word) :
    seal_pred ot_switcher ot_switcher_propC -∗
    (if is_sealed_with_o wct1 ot_switcher then interp W C (wct1, swct1) else True) -∗
    ▷ (⌜ ∀ wsb, wct1 = WSealed ot_switcher wsb → swct1 = WSealed ot_switcher wsb ⌝ ∗
       ∀ wsb, ⌜ wct1 = WSealed ot_switcher wsb ⌝ -∗
              ot_switcher_prop W C (WSealable wsb, WSealable wsb)).
  Proof.
    iIntros "#Hp_ot_switcher #Htarget_v".
    destruct (is_sealed_with_o wct1 ot_switcher) eqn:Hsealed; cycle 1.
    { iNext; iSplit.
      - iPureIntro; intros wsb ->; cbn in Hsealed.
        by rewrite Z.eqb_refl in Hsealed.
      - iIntros (wsb ->); cbn in Hsealed.
        by rewrite Z.eqb_refl in Hsealed. }
    assert (∃ wsb0, wct1 = WSealed ot_switcher wsb0) as [wsb0 ->].
    { destruct wct1 as [ | [] | |]; cbn in Hsealed; try discriminate.
      exists sb. apply Z.eqb_eq in Hsealed.
      replace ot with ot_switcher by solve_addr.
      done.
    }
    iDestruct (interp_eq_unless_sealed with "Htarget_v") as %Heq.
    assert (∃ swsb0, swct1 = WSealed ot_switcher swsb0) as [swsb0 ->].
    { destruct Heq as [<-|(o & sb1 & sb2 & Heq1 & ->)]; eauto.
      inversion Heq1; subst; eauto. }
    iDestruct (interp_sealed_inv with "Htarget_v") as "[_ Hsb]".
    iDestruct "Hsb" as (P HpersP) "(HmonoP & HPseal & %Hloc & HP & HPborrow)".
    iDestruct (seal_pred_agree with "Hp_ot_switcher HPseal") as "Hagree".
    iSpecialize ("Hagree" $! (W,C,(WSealable wsb0, WSealable swsb0))).
    iNext.
    iSimpl in "Hagree".
    iRewrite -"Hagree" in "HP".
    iPoseProof "HP" as "HP'".
    iDestruct "HP'" as (??????????? Heq1 Heq2) "_".
    cbn in Heq1, Heq2; simplify_eq.
    iSplit.
    - iPureIntro; intros wsb Hwsb; simplify_eq; done.
    - iIntros (wsb Hwsb); simplify_eq.
      iExact "HP".
  Qed.

  (** The registers when entering the callee, in both runs. *)
  Lemma switcher_call_entry_registers W W' C (nargs : nat)
    (arg_rmap' arg_smap' rmap' smap' : Reg) (wpcc wcgp wstk : Word) :
    related_sts_pub_world W W' ->
    is_arg_rmap arg_rmap' 8 ->
    is_arg_rmap arg_smap' 8 ->
    dom rmap' = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ PC ; cra ; cgp ; csp ]}) ->
    dom smap' = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ PC ; cra ; cgp ; csp ]}) ->

    PC ↦ᵣ wpcc ∗
    PC ↣ᵣ wpcc ∗
    cgp ↦ᵣ wcgp ∗
    cgp ↣ᵣ wcgp ∗
    cra ↦ᵣ WSentry XSRW_ Local b_switcher e_switcher a_switcher_return ∗
    cra ↣ᵣ WSentry XSRW_ Local b_switcher e_switcher a_switcher_return ∗
    csp ↦ᵣ wstk ∗
    csp ↣ᵣ wstk ∗
    interp W' C (wstk, wstk) ∗
    ( [∗ map] r↦w;s ∈ arg_rmap';arg_smap',
        r ↦ᵣ w ∗ r ↣ᵣ s ∗
        if decide (r ∈ dom_arg_rmap nargs)
        then interp W C (w, s)
        else ⌜ w = WInt 0 ∧ s = WInt 0 ⌝ ) ∗
    ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ ) ∗
    ( [∗ map] r↦w ∈ smap', r ↣ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
    -∗
    ∃ regs1 regs2,
      registers_pointsto regs1 ∗
      spec_registers_pointsto regs2 ∗
      execute_entry_point_register (wpcc, wpcc) (wcgp, wcgp) wstk nargs W' C (regs1, regs2).
  Proof.
    iIntros (Hrelated Hisarg_rmap' Hisarg_smap' Hrmap'' Hsmap'')
      "(HPC & HsPC & Hcgp & Hscgp & Hcra & Hscra & Hcsp & Hscsp & #Hstk & Hparams & Hrest & Hsrest)".
    iDestruct (big_sepM_sep with "Hrest") as "[Hrest #Hnil]".
    iDestruct (big_sepM_sep with "Hsrest") as "[Hsrest #Hsnil]".
    iDestruct (big_sepM2_sep with "Hparams") as "[Hparams Hparams']".
    iDestruct (big_sepM2_sep with "Hparams'") as "[Hsparams #Hval]".
    iDestruct (big_sepM2_sep_2 with "Hparams Hsparams") as "Hparams".
    iDestruct (big_sepM2_sepM with "Hparams") as "[Hparams Hsparams]".
    { intros k. rewrite -!elem_of_dom Hisarg_rmap' Hisarg_smap'. done. }
    iDestruct (big_sepM_union with "[$Hparams $Hrest]") as "Hregs".
    { apply map_disjoint_dom. rewrite Hrmap'' Hisarg_rmap'.
      rewrite /dom_arg_rmap. clear. set_solver. }
    iDestruct (big_sepM_union with "[$Hsparams $Hsrest]") as "Hsregs".
    { apply map_disjoint_dom. rewrite Hsmap'' Hisarg_smap'.
      rewrite /dom_arg_rmap. clear. set_solver. }
    iDestruct (big_sepM_insert_2 with "[Hcsp] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hcra] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hcgp] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[HPC] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hscsp] Hsregs") as "Hsregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hscra] Hsregs") as "Hsregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hscgp] Hsregs") as "Hsregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[HsPC] Hsregs") as "Hsregs";[iFrame|].
    iExists _, _; iFrame "Hregs Hsregs".
    rewrite /execute_entry_point_register.
    cbn.
    iSplit.
    { iPureIntro. intros rr. clear -Hisarg_rmap' Hrmap''.
      destruct (decide (rr = PC));simplify_map_eq;[eauto|].
      destruct (decide (rr = cgp));simplify_map_eq;[eauto|].
      destruct (decide (rr = cra));simplify_map_eq;[eauto|].
      destruct (decide (rr = csp));simplify_map_eq;[eauto|].
      apply elem_of_dom. rewrite dom_union_L Hrmap'' Hisarg_rmap'.
      rewrite difference_union_distr_r_L union_intersection_l.
      rewrite -union_difference_L;[|apply all_registers_subseteq].
      apply elem_of_intersection. split;[apply all_registers_s_correct|].
      apply elem_of_union. right.
      apply elem_of_difference. split;[apply all_registers_s_correct|set_solver].
    }
    iSplit.
    { iPureIntro. intros rr. clear -Hisarg_smap' Hsmap''.
      destruct (decide (rr = PC));simplify_map_eq;[eauto|].
      destruct (decide (rr = cgp));simplify_map_eq;[eauto|].
      destruct (decide (rr = cra));simplify_map_eq;[eauto|].
      destruct (decide (rr = csp));simplify_map_eq;[eauto|].
      apply elem_of_dom. rewrite dom_union_L Hsmap'' Hisarg_smap'.
      rewrite difference_union_distr_r_L union_intersection_l.
      rewrite -union_difference_L;[|apply all_registers_subseteq].
      apply elem_of_intersection. split;[apply all_registers_s_correct|].
      apply elem_of_union. right.
      apply elem_of_difference. split;[apply all_registers_s_correct|set_solver].
    }
    repeat iSplit.
    - iPureIntro. clear. simplify_map_eq. done.
    - iPureIntro. clear. simplify_map_eq. done.
    - iPureIntro. clear. simplify_map_eq. done.
    - iPureIntro. clear. simplify_map_eq. done.
    - iPureIntro. clear. simplify_map_eq. done.
    - iPureIntro. clear. simplify_map_eq. done.
    - iPureIntro. clear. simplify_map_eq. done.
    - iPureIntro. clear. simplify_map_eq. done.
    - done.
    - iIntros (r v1 v2 Hr Hv1 Hv2).
      assert (r ∉ ({[ PC ; cgp ; cra ; csp ]} : gset RegName)) as Hr'.
      {
        clear -Hr.
        do 8 (destruct nargs; first set_solver).
        induction nargs.
        + set_solver+Hr.
        + apply IHnargs; set_solver+Hr.
      }
      repeat (rewrite lookup_insert_ne in Hv1;[|set_solver+Hr Hr']).
      repeat (rewrite lookup_insert_ne in Hv2;[|set_solver+Hr Hr']).
      apply lookup_union_Some in Hv1.
      2: {
        apply map_disjoint_dom_2.
        rewrite Hisarg_rmap' Hrmap'' /=; set_solver+.
      }
      apply lookup_union_Some in Hv2.
      2: {
        apply map_disjoint_dom_2.
        rewrite Hisarg_smap' Hsmap'' /=; set_solver+.
      }
      destruct Hv1 as [Hv1|Hv1]; cycle 1.
      { apply elem_of_dom_2 in Hv1; rewrite Hrmap'' in Hv1.
        exfalso; clear -Hr Hv1. do 8 (destruct nargs; first set_solver).
        induction nargs; [set_solver+Hr Hv1|apply IHnargs; set_solver+Hr]. }
      destruct Hv2 as [Hv2|Hv2]; cycle 1.
      { apply elem_of_dom_2 in Hv2; rewrite Hsmap'' in Hv2.
        exfalso; clear -Hr Hv2. do 8 (destruct nargs; first set_solver).
        induction nargs; [set_solver+Hr Hv2|apply IHnargs; set_solver+Hr]. }
      iDestruct (big_sepM2_lookup with "Hval") as "Hv"; eauto.
      destruct (decide (r ∈ _)) as [|Hcontra].
      + iApply (interp_monotone with "[] Hv"); done.
      + set_solver+Hcontra Hr.
    - iIntros (r v Hr Hv).
      repeat (rewrite lookup_insert_ne in Hv;[|set_solver+Hr]).
      apply lookup_union_Some in Hv.
      2: {
        apply map_disjoint_dom_2.
        rewrite Hisarg_rmap' Hrmap'' /=; set_solver+.
      }
      destruct Hv as [Hv|Hv].
      + assert (is_Some (arg_smap' !! r)) as [v2 Hv2].
        { apply elem_of_dom; rewrite Hisarg_smap' -Hisarg_rmap'. by apply elem_of_dom_2 in Hv. }
        iDestruct (big_sepM2_lookup with "Hval") as "Hv"; eauto.
        destruct (decide (r ∈ _)) as [Hcontra|]; last (iDestruct "Hv" as "[$ _]").
        set_solver+Hcontra Hr.
      + iDestruct (big_sepM_lookup with "Hnil") as "%";eauto; simplify_eq.
    - iIntros (r v Hr Hv).
      repeat (rewrite lookup_insert_ne in Hv;[|set_solver+Hr]).
      apply lookup_union_Some in Hv.
      2: {
        apply map_disjoint_dom_2.
        rewrite Hisarg_smap' Hsmap'' /=; set_solver+.
      }
      destruct Hv as [Hv|Hv].
      + assert (is_Some (arg_rmap' !! r)) as [v1 Hv1].
        { apply elem_of_dom; rewrite Hisarg_rmap' -Hisarg_smap'. by apply elem_of_dom_2 in Hv. }
        iDestruct (big_sepM2_lookup with "Hval") as "Hv"; eauto.
        destruct (decide (r ∈ _)) as [Hcontra|]; last (iDestruct "Hv" as "[_ $]").
        set_solver+Hcontra Hr.
      + iDestruct (big_sepM_lookup with "Hsnil") as "%";eauto; simplify_eq.
  Qed.

  (** ** Switcher invariant *)

  (** Close the switcher invariant of each run after pushing the frame
      [frm] on its trusted stack. *)
  Lemma switcher_inv_push_frame
    (frm : cframe) (cstk cstk' : cstack) (a_tstk : Addr) (tstk_next : list Word) :
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

  Lemma switcher_inv_spec_push_frame
    (frm : cframe) (cstk cstk' : cstack) (a_tstk : Addr) (tstk_next : list Word) :
    (b_trusted_stack <= a_tstk)%a ->
    ((a_tstk ^+ 1) + 1)%a = Some (a_tstk ^+ 2)%a ->
    (a_tstk ^+ 1 < e_trusted_stack)%a ->
    (b_trusted_stack + length cstk')%a = Some a_tstk ->
    switcher_stk_bounds frm.(b_stk) frm.(e_stk) frm.(a_stk) ->

    cstack_full_spec cstk' -∗
    cstack_frag_spec cstk -∗
    mtdc ↣ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack (a_tstk ^+ 1)%a -∗
    (a_tstk ^+ 1)%a ↣ₐ WCap RWL Local frm.(b_stk) frm.(e_stk) (frm.(a_stk) ^+ 4)%a -∗
    [[ (a_tstk ^+ 2)%a , e_trusted_stack ]] ↣ₐ [[ tstk_next ]] -∗
    cstack_interp_spec cstk' a_tstk -∗
    cframe_stk_own_spec frm -∗
    switcher_spec_code -∗
    b_switcher ↣ₐ WSealRange (true,true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher
    ==∗
    switcher_inv_spec ∗ cstack_frag_spec (frm :: cstk).
  Proof.
    iIntros (Htstk_b Ha_tstk2 Ha_tstk1 Hlen_cstk (Hba & Hba3 & Ha4))
      "Hcstk_full Hcstk Hmtdc Ha_tstk1 Htstk Hstk_interp Hframe Hcode Hb_switcher".
    iDestruct (cstack_agree_spec with "Hcstk_full Hcstk") as %->.
    iMod (cstack_update_spec _ _ (frm :: cstk) with "Hcstk_full Hcstk") as "[Hcstk_full $]".
    iModIntro.
    iExists (a_tstk ^+ 1)%a, (frm :: cstk), tstk_next.
    iFrame "Hmtdc Hcode Hb_switcher Hcstk_full".
    rewrite (finz_incr_eq Ha_tstk2).
    iFrame "Htstk".
    cbn.
    replace ((a_tstk ^+ 1) ^+ -1)%a with a_tstk by solve_addr.
    iFrame.
    iPureIntro.
    repeat split; try done; try solve_addr.
  Qed.

  (** ** Functional specification *)

  (** A revoked and cleared stack region becomes safe-to-share once it is
      reinstated as temporary. *)
  Lemma StackRevokedResources_interp (W : WORLD) (C : CmptName) (b e a : Addr) :
    StackRevokedResources W C (finz.seq_between b e) -∗
    interp (std_update_multiple W (finz.seq_between b e) Temporary) C
      (WCap RWL Local b e a, WCap RWL Local b e a).
  Proof.
    rewrite /StackRevokedResources /StackWorldResources zip_with_replicate big_sepL2_replicate_r; last done.
    iIntros "[_ Hres]".
    rewrite /interp fixpoint_interp1_eq interp1_eq /=.
    iSplit; last done.
    iApply (big_sepL_impl with "Hres").
    iIntros "!>" (k a' Ha) "Hr".
    iDestruct "Hr" as (φ p) "(Hφ & Hmono & Hrel & (HmonoR & Hzcond & Hrcond & Hwcond & Hpers) & %Hperm_flow)".
    iExists p,φ.
    iFrame "∗#%".
    iSplit.
    { erewrite readAllowed_flowsto; eauto. }
    iSplit.
    { erewrite writeAllowed_flowsto; eauto. }
    iSplitL "HmonoR".
    { rewrite /monoReq.
      erewrite isWL_flowsto; eauto.
      rewrite std_sta_update_multiple_lookup_in_i; first done.
      apply list_elem_of_lookup. eauto. }
    iPureIntro. apply std_sta_update_multiple_lookup_in_i. apply list_elem_of_lookup. eauto.
  Qed.

  (** Reinstate the callee's stack frame in the world, once cleared in both
      runs. *)
  Lemma switcher_cc_world_reinstate E W C (a e : Addr) :
    revoked_addresses W (finz.seq_between a e) ->
    (a + 4)%a = Some (a ^+ 4)%a ->
    (a ^+ 4 <= e)%a ->
    let W' := std_update_multiple W (finz.seq_between (a ^+ 4)%a e) Temporary in
    world_interp W C -∗
    StackRevokedResources W C (finz.seq_between a e) -∗
    [[ (a ^+ 4)%a , e ]] ↦ₐ [[ region_addrs_zeroes (a ^+ 4)%a e ]] -∗
    [[ (a ^+ 4)%a , e ]] ↣ₐ [[ region_addrs_zeroes (a ^+ 4)%a e ]]
    ={E}=∗
    world_interp W' C ∗
    interp W' C (WCap RWL Local (a ^+ 4)%a e (a ^+ 4)%a, WCap RWL Local (a ^+ 4)%a e (a ^+ 4)%a) ∗
    ⌜ related_sts_pub_world W W' ⌝ ∗
    ⌜ revoked_addresses W (finz.seq_between (a ^+ 4)%a e) ⌝.
  Proof.
    iIntros (Hstk_revoked Ha4 He W') "Hworld_interp Hstk_val Hstk Hsstk".
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
    iMod (world_interp_reinstate_stack with "Hworld_interp Hstk_val' Hstk Hsstk") as "Hworld_interp".
    { apply finz_seq_between_NoDup. }
    { apply Forall_replicate_eq. }
    { apply Forall_replicate_eq. }
    { done. }
    iModIntro.
    iFrame "Hworld_interp".
    iSplit; last (iPureIntro; split; [apply related_sts_pub_update_multiple_temp|]; done).
    iApply (StackRevokedResources_interp with "Hstk_val'").
  Qed.

  (** Collect the registers of one run cleared on the exhausted path of the
      functional specification. *)
  Local Lemma switcher_cc_exhausted_regs_aux (P : RegName → Word → iProp Σ)
    (arg_rmap rmap : Reg) (wct1 wct2 wctp : Word) :
    is_arg_rmap arg_rmap 8 ->
    dom rmap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    ( [∗ map] r↦w ∈ arg_rmap, P r w ) -∗
    ( [∗ map] r↦w ∈ delete ctp (delete ct2 rmap), P r w ) -∗
    P ct1 wct1 -∗
    P ct2 wct2 -∗
    P ctp wctp -∗
    ∃ (wca0 wca1 : Word) (rmap0 : Reg),
      P ca0 wca0 ∗
      P ca1 wca1 ∗
      ⌜ dom rmap0 = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
      ( [∗ map] r↦w ∈ rmap0, P r w ).
  Proof.
    iIntros (Hrdom Hdom) "Hargs Hregs Hct1 Hct2 Hctp".
    destruct (is_arg_rmap_8_inv _ Hrdom) as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & ->).
    rewrite !big_sepM_insert; [|by simplify_map_eq..].
    iDestruct "Hargs" as "(Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & Hct0 & _)".
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
    clear -Hdom.
    repeat (rewrite dom_insert_L).
    rewrite Hdom /dom_arg_rmap /=.
    set_solver.
  Qed.

  (** Collect the registers cleared on the exhausted path of the functional
      specification, in both runs. *)
  Lemma switcher_cc_exhausted_regs (arg_rmap arg_smap rmap smap : Reg)
    (wct1 swct1 wct2 swct2 wctp swctp : Word) :
    is_arg_rmap arg_rmap 8 ->
    is_arg_rmap arg_smap 8 ->
    dom rmap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    dom smap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    ( [∗ map] r↦w ∈ arg_rmap, r ↦ᵣ w ) -∗
    ( [∗ map] r↦w ∈ arg_smap, r ↣ᵣ w ) -∗
    ( [∗ map] r↦w ∈ delete ctp (delete ct2 rmap), r ↦ᵣ w ) -∗
    ( [∗ map] r↦w ∈ delete ctp (delete ct2 smap), r ↣ᵣ w ) -∗
    ct1 ↦ᵣ wct1 -∗
    ct1 ↣ᵣ swct1 -∗
    ct2 ↦ᵣ wct2 -∗
    ct2 ↣ᵣ swct2 -∗
    ctp ↦ᵣ wctp -∗
    ctp ↣ᵣ swctp -∗
    ∃ (wca0 swca0 wca1 swca1 : Word) (rmap0 smap0 : Reg),
      ca0 ↦ᵣ wca0 ∗
      ca0 ↣ᵣ swca0 ∗
      ca1 ↦ᵣ wca1 ∗
      ca1 ↣ᵣ swca1 ∗
      ⌜ dom rmap0 = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
      ⌜ dom smap0 = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
      ( [∗ map] r↦w ∈ rmap0, r ↦ᵣ w ) ∗
      ( [∗ map] r↦w ∈ smap0, r ↣ᵣ w ).
  Proof.
    iIntros (Hrdom Hsrdom Hdom Hsdom) "Hargs Hsargs Hregs Hsregs Hct1 Hsct1 Hct2 Hsct2 Hctp Hsctp".
    iDestruct (switcher_cc_exhausted_regs_aux (λ r w, r ↦ᵣ w)%I with "Hargs Hregs Hct1 Hct2 Hctp")
      as (wca0 wca1 rmap0) "(Hca0 & Hca1 & %Hrmap0 & Hrmap0)"; [done|done|].
    iDestruct (switcher_cc_exhausted_regs_aux (λ r w, r ↣ᵣ w)%I with "Hsargs Hsregs Hsct1 Hsct2 Hsctp")
      as (swca0 swca1 smap0) "(Hsca0 & Hsca1 & %Hsmap0 & Hsmap0)"; [done|done|].
    iExists _, _, _, _, _, _; iFrame "∗ %".
  Qed.

  (** Revoke the world after the callee returned: close the callee's stack
      frame in the world, and revoke the temporary addresses, including the
      caller's stack frame. *)
  Lemma switcher_cc_revoke_returned E W W2 C (b_stk e_stk a_stk : Addr)
    (stk_mem_l stk_mem_h stk_mem_l_spec stk_mem_h_spec : list Word) :
    revoked_addresses W (finz.seq_between a_stk e_stk) ->
    related_sts_pub_world
      (std_update_multiple W (finz.seq_between (a_stk ^+ 4)%a e_stk) Temporary) W2 ->
    (b_stk <= a_stk ^+ 4 ∧ a_stk ^+ 4 <= e_stk ∧ (a_stk + 4) = Some (a_stk ^+ 4))%a ->

    interp W2 C (WCap RWL Local (a_stk ^+ 4)%a e_stk (a_stk ^+ 4)%a,
                 WCap RWL Local (a_stk ^+ 4)%a e_stk (a_stk ^+ 4)%a) -∗
    StackRevokedResources W C (finz.seq_between a_stk e_stk) -∗
    world_interp_open W2 C (finz.seq_between (a_stk ^+ 4)%a e_stk) -∗
    StackOpenWorldResources interp W2 C (finz.seq_between (a_stk ^+ 4)%a e_stk)
      stk_mem_h stk_mem_h_spec -∗
    [[ a_stk , (a_stk ^+ 4)%a ]] ↦ₐ [[ stk_mem_l ]] -∗
    [[ a_stk , (a_stk ^+ 4)%a ]] ↣ₐ [[ stk_mem_l_spec ]] -∗
    [[ (a_stk ^+ 4)%a , e_stk ]] ↦ₐ [[ stk_mem_h ]] -∗
    [[ (a_stk ^+ 4)%a , e_stk ]] ↣ₐ [[ stk_mem_h_spec ]] -∗
    £ 2
    ={E}=∗
    ∃ (stk_mem stk_mem_spec : list Word) (l' : list Addr),
      ⌜ extract_temporaries_condition W2 (l' ++ finz.seq_between (a_stk ^+ 4)%a e_stk) ⌝ ∗
      RevokedResources W2 C l' ∗
      ⌜ revoked_addresses (revoke W2) l' ⌝ ∗
      StackRevokedResources W2 C (finz.seq_between a_stk e_stk) ∗
      ⌜ revoked_addresses (revoke W2) (finz.seq_between a_stk e_stk) ⌝ ∗
      world_interp (revoke W2) C ∗
      [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]] ∗
      [[ a_stk , e_stk ]] ↣ₐ [[ stk_mem_spec ]].
  Proof.
    iIntros (Hrevoked_stk Hrelated_pub_Wext_W2 Hcsp_bounds)
      "#Hinterp_W2_csp #Hstk_val Hworld_interp_C Hstack_revoked_W2 Hstk_l Hsstk_l Hstk_h Hsstk_h
      [Hlc Hlc']".
    iDestruct ( big_sepL2_length with "Hstk_h" ) as "%Hlen_stk_h".
    iDestruct ( big_sepL2_length with "Hstk_l" ) as "%Hlen_stk_l".
    iDestruct ( big_sepL2_length with "Hsstk_l" ) as "%Hslen_stk_l".
    iEval (rewrite <- (app_nil_r (finz.seq_between (a_stk ^+ 4)%a e_stk))) in "Hworld_interp_C".

    iDestruct (close_world_interp_opening_resources
                with "[$Hworld_interp_C $Hstack_revoked_W2 $Hstk_h $Hsstk_h]")
      as "Hworld_interp_C".
    { apply finz_seq_between_NoDup. }
    { set_solver+. }
    { by rewrite Hlen_stk_h. }
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
      as (l') "(%Hl_unk' & Hworld_interp_C & Hstack_revoked_W2 & Hrevoked_W2
               & >(%stk_mem_h' & %stk_mem_h_spec' & Hstk_h & Hsstk_h)
               & [Hrevoked_l' %Hrevoked_W2_l'])".
    iDestruct (region_pointsto_split with "[$Hstk_l $Hstk_h]") as "Hstk"; auto.
    { solve_addr+ Hcsp_bounds. }
    { by rewrite finz_seq_between_length in Hlen_stk_l. }
    iDestruct (spec_region_pointsto_split with "[$Hsstk_l $Hsstk_h]") as "Hsstk"; auto.
    { solve_addr+ Hcsp_bounds. }
    { by rewrite finz_seq_between_length in Hslen_stk_l. }
    iCombine "Hstack_revoked_W2 Hrevoked_W2" as "Hstack_revoked_W2".
    iDestruct (lc_fupd_elim_later with "[$] [$Hrevoked_l']") as ">Hrevoked_l'".
    iDestruct (lc_fupd_elim_later with "[$] [$Hstack_revoked_W2]") as ">[Hstack_revoked_W2 %]".
    iModIntro.
    iExists _, _, l'; iFrame "∗ %".
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
    (stk_mem_l stk_mem_h stk_mem_l_spec stk_mem_h_spec : list Word) :
    let W2 := std_update_multiple W (finz.seq_between (a_stk ^+ 4)%a e_stk) Temporary in
    revoked_addresses W (finz.seq_between a_stk e_stk) ->
    (b_stk <= a_stk ^+ 4 ∧ a_stk ^+ 4 <= e_stk ∧ (a_stk + 4) = Some (a_stk ^+ 4))%a ->
    length stk_mem_l = 4 ->
    length stk_mem_l_spec = 4 ->

    world_interp W C -∗
    StackRevokedResources W C (finz.seq_between a_stk e_stk) -∗
    [[ a_stk , (a_stk ^+ 4)%a ]] ↦ₐ [[ stk_mem_l ]] -∗
    [[ a_stk , (a_stk ^+ 4)%a ]] ↣ₐ [[ stk_mem_l_spec ]] -∗
    [[ (a_stk ^+ 4)%a , e_stk ]] ↦ₐ [[ stk_mem_h ]] -∗
    [[ (a_stk ^+ 4)%a , e_stk ]] ↣ₐ [[ stk_mem_h_spec ]] -∗
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
      [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem_l ++ stk_mem_h ]] ∗
      [[ a_stk , e_stk ]] ↣ₐ [[ stk_mem_l_spec ++ stk_mem_h_spec ]].
  Proof.
    intros W2.
    iIntros (Hrevoked_stk Hcsp_bounds Hlen_l Hslen_l)
      "Hworld_interp_C #Hclose Hstk_l Hsstk_l Hstk_h Hsstk_h [Hlc Hlc']".
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
    assert (length stk_mem_l = finz.dist a_stk (a_stk ^+ 4)%a) as Hdist.
    { rewrite Hlen_l.
      destruct Hcsp_bounds as (?&?&Ha4).
      pose proof (finz_incr_iff_dist a_stk (a_stk ^+ 4)%a 4) as [Hdist _].
      by apply Hdist in Ha4 as [? ?].
    }
    iDestruct (region_pointsto_split _ _ (a_stk ^+4)%a with "[$Hstk_l $Hstk_h]") as "Hstk".
    { solve_addr+ Hcsp_bounds. }
    { done. }
    iDestruct (spec_region_pointsto_split _ _ (a_stk ^+4)%a with "[$Hsstk_l $Hsstk_h]") as "Hsstk".
    { solve_addr+ Hcsp_bounds. }
    { by rewrite Hslen_l -Hlen_l. }
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
    iSplit.
    { iApply (StackRevokedResources_mono_priv with "Hclose"); auto.
      apply related_sts_pub_priv_world.
      eapply related_sts_pub_update_multiple_temp.
      rewrite (finz_seq_between_split a_stk (a_stk^+4)%a) in Hrevoked_stk; last (split; solve_addr).
      apply revoked_addresses_app in Hrevoked_stk as [? ?]; auto.
    }
    iPureIntro.
    eapply Forall_impl; eauto.
    cbn; intros a Ha.
    apply revoke_lookup_Revoked; done.
  Qed.

End Switcher_Call_World.
