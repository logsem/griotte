From iris.proofmode Require Import proofmode.
From griotte Require Import logrel monotone interp_weakening memory_region rules proofmode.
From griotte Require Import sts_multiple_updates region_invariants_revocation.
From griotte Require Import world_ghost_theory world_interp_stack stack_world_resources.
From griotte Require Import map_simpl register_tactics.
From griotte Require Import switcher_call_states.

(** * Logical steps of the call routine of the switcher

    The lemmas of this file do not execute code. They are used between the
    paths of the call routine ([call_path]) by the proofs of
    [switcher_cc_specification_gen] and [interp_expr_switcher_call]. *)

Section Switcher_Call_World.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (** ** Stack frame of an untrusted caller

      When the caller is untrusted, its stack is shared in the world. The
      switcher opens a part of the stack, the free part below the stack
      pointer, to spill the callee-save registers and to clear the callee's
      frame, and then closes it with safe words. *)

  Lemma StackWorldResource_update W C a v v' :
    interp W C v' -∗
    StackWorldResource interp W C a v -∗
    StackWorldResource interp W C a v'.
  Proof.
    iIntros "#Hv' (%φ & %p & _ & _ & Hrel & Hvalid & %Hflow)".
    iDestruct "Hvalid" as "(#Hmono & #Hzcond & #Hrcond & #Hwcond & %Hpers)".
    iExists φ, p.
    iSplitR; first iApply ("Hwcond" with "Hv'").
    iSplitR.
    { rewrite /mono_temporary decide_True; first iApply "Hmono".
      left; by eapply isWL_flowsto. }
    iSplitL "Hrel"; first iExact "Hrel".
    iSplitR; last (iPureIntro; exact Hflow).
    iFrame "Hmono Hzcond Hrcond Hwcond"; iPureIntro; exact Hpers.
  Qed.

  (** The words of [lv'] are either unchanged from [lv], or safe. *)
  Lemma StackWorldResources_update W C (la : list Addr) (lv lv' : list LWord) :
    length lv' = length lv ->
    StackWorldResources interp W C la lv -∗
    ([∗ list] k ↦ w ∈ lv', ⌜ lv !! k = Some w ⌝ ∨ interp W C w) -∗
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
      iSplitL "Ha Hv'".
      { iDestruct "Hv'" as "[%Heq | Hv']".
        - cbn in Heq; simplify_eq; iFrame.
        - iApply (StackWorldResource_update with "Hv' Ha"). }
      iApply (IH lv lv' with "[$H $Hlv']"); cbn in *; lia.
  Qed.

  (** The opened part [[a, e)] of the stack, containing [lv]. *)
  Definition switcher_stk_opened W C (a e : Addr) (lv : list LWord) : iProp Σ :=
    world_interp_open W C (LNonHeap <$> finz.seq_between a e) ∗
    StackOpenWorldResources interp W C (finz.seq_between a e) lv.

  (** Open the part [[x, y)] of a safe stack [[b, e)]. *)
  Lemma switcher_call_stk_open W C (b e a x y : Addr) :
    (b <= x)%a ->
    (y <= e)%a ->
    interp W C (WCap true RWL Local b e a) -∗
    world_interp W C -∗
    ∃ lv,
      [[ x , y ]] ↦ₐ [[ lv ]] ∗
      ▷ switcher_stk_opened W C x y lv.
  Proof.
    iIntros (Hbx Hye) "#Hinterp Hworld".
    iEval (rewrite open_world_interp_empty -(fmap_nil LNonHeap)) in "Hworld".
    iDestruct (open_world_interp_opening_resources _ _ (finz.seq_between x y) []
                with "[$Hinterp $Hworld]")
      as "(Hworld & %lv & Hstk & Hres)".
    { apply finz_seq_between_NoDup. }
    { apply Forall_forall; intros a' Ha'.
      apply elem_of_finz_seq_between in Ha'; solve_addr. }
    { set_solver+. }
    rewrite app_nil_r.
    iExists lv; iFrame.
  Qed.

  Lemma switcher_call_stk_close W C (a e : Addr) (lv lv' : list LWord) :
    length lv' = length lv ->
    switcher_stk_opened W C a e lv -∗
    [[ a , e ]] ↦ₐ [[ lv' ]] -∗
    ([∗ list] k ↦ w ∈ lv', ⌜ lv !! k = Some w ⌝ ∨ interp W C w) -∗
    world_interp W C.
  Proof.
    iIntros (Hlen) "[Hworld [Hsw Hst]] Hstk Hlv'".
    iDestruct (StackWorldResources_length with "Hsw") as "%Hlen_la".
    iDestruct (StackWorldResources_update with "Hsw Hlv'") as "Hsw"; first done.
    iEval (rewrite -(app_nil_r (finz.seq_between a e))) in "Hworld".
    iDestruct (close_world_interp_opening_resources _ _ lv' (finz.seq_between a e) []
                with "[$Hworld $Hstk $Hsw $Hst]") as "Hworld".
    { apply finz_seq_between_NoDup. }
    { set_solver+. }
    { by rewrite Hlen -Hlen_la. }
    by rewrite fmap_nil -open_world_interp_empty.
  Qed.

  (** A safe write-local capability with a non-empty range carries no
      identifier: heap authority is never write-local. *)
  Lemma interp_wl_noid W C p g b e a π :
    isWL p = true → (b < e)%a →
    interp W C (WCap true p g b e a @@? π) -∗ ⌜π = None⌝.
  Proof.
    iIntros (Hwl Hbe) "Hinterp".
    iDestruct (interp_cap_regions with "Hinterp") as %[_ Hheap];
      first (apply isWL_nonO; exact Hwl).
    iPureIntro. specialize (Hheap Hbe). destruct π as [ι|]; last done.
    destruct Hheap as (_ & o & _ & _ & _ & _ & _ & Hnotwl). congruence.
  Qed.

  (** Loading a safe word gives a safe word. *)
  Lemma interp_load_heap W C (w w' : LWord) :
    load_heap w w' →
    interp W C w -∗ interp W C w'.
  Proof.
    iIntros ([-> | [_ ->] ]) "#Hw"; first done.
    iApply interp_clear_tag.
  Qed.

  (** ** Entry point of the callee *)

  (** Since [Po] is persistent, the world interpretation is given back
      immediately: only the sealing predicate is under a later. *)
  Lemma world_interp_seal_pred_singleton_persistent
    (W : WORLD) (C : CmptName) (o : OType) Po `{Hpers: ∀ WCv, Persistent (Po WCv)} (w : LWord) :
    seal_pred o Po -∗
    sts_seals_std C o {[ w ]} -∗
    world_interp W C -∗
    world_interp W C ∗ ▷ Po (W, C, lforce_global w).
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros "#Hspred Hseal ($ & Hsts & Hseals)".
    iDestruct (sealing_map_seal_pred_persistent with "Hspred Hseal Hseals Hsts")
      as "($ & $ & H)"; eauto.
    by rewrite normalise_sealed_words_singleton big_sepS_singleton.
  Qed.

  (** The sealing predicate of [ot_switcher] describes the entry point of
      the callee, once unsealed. *)
  Lemma switcher_entry_point_prop W C (wct1 : LWord) :
    seal_pred ot_switcher ot_switcher_propC -∗
    (if is_sealed_with_o wct1.(lw) ot_switcher then interp W C wct1 else True) -∗
    world_interp W C -∗
    world_interp W C ∗
    ▷ (∀ wsb π,
         ⌜ wct1 = WSealed ot_switcher wsb @@? π ⌝ -∗
         ⌜ get_tag_sealable wsb = true ⌝ -∗
         ot_switcher_prop W C (WSealable wsb @@? π)).
  Proof.
    iIntros "#Hp_ot_switcher #Htarget_v Hworld_interp".
    destruct (is_sealed_with_o wct1.(lw) ot_switcher) eqn:Hsealed; cycle 1.
    { iFrame; iIntros "!>" (wsb π -> ?); cbn in Hsealed.
      by rewrite Z.eqb_refl in Hsealed. }
    assert (∃ wsb0 π0, wct1 = WSealed ot_switcher wsb0 @@? π0) as (wsb0 & π0 & ->).
    { destruct wct1 as [ [ | [] | |] π0]; cbn in Hsealed; try discriminate.
      exists sb, π0. apply Z.eqb_eq in Hsealed.
      replace ot with ot_switcher by solve_addr.
      done.
    }
    destruct (get_tag_sealable wsb0) eqn:Htag; cycle 1.
    { iFrame; iIntros "!>" (wsb π Hwsb Htag'); simplify_eq; congruence. }
    rewrite (interp_unfold _ _ (WSealed ot_switcher wsb0 @@? π0)).
    iEval (cbn; rewrite Htag) in "Htarget_v".
    rewrite /interp_sb.
    iDestruct "Htarget_v" as "[#Htarget_v _]".
    iAssert (sts_seals_std C ot_switcher {[WSealable wsb0 @@? π0]}) as "#Htarget_v'".
    { iApply sts_seals_std_weaken; last iFrame "Htarget_v"; last set_solver+. }
    iDestruct (world_interp_seal_pred_singleton_persistent with
                "Hp_ot_switcher Htarget_v' Hworld_interp") as "($ & HP)".
    iNext; iIntros (wsb π Hwsb _); simplify_eq.
    destruct wsb as [t p g b e a | t sp g b e a]; cycle 1.
    { iEval (cbn) in "HP".
      iNamed "HP".
      rewrite /lforce_global /lift_word /lword_of_word /= in Hw; discriminate. }
    cbn in Htag; subst t.
    destruct g; first done.
    iDestruct (ot_switcher_prop_borrow _ _ (WCap true p Global b e a @@? π) with "HP") as "HP'".
    done.
  Qed.

  (** The registers when entering the callee. *)
  Lemma switcher_call_entry_registers W W' C (nargs : nat)
    (arg_rmap' rmap' : LReg) (wcgp wstk : LWord) (mie : InterruptStatus) :
    related_sts_pub_world W W' ->
    heap_std W = heap_std W' ->
    is_arg_rmap arg_rmap' 8 ->
    dom rmap' = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ cra ; cgp ; csp ]}) ->

    cgp ↦ᵣ wcgp ∗
    cra ↦ᵣ WSentry (ret_kind mie) true XSRW_ Local b_switcher e_switcher a_switcher_return ∗
    csp ↦ᵣ wstk ∗
    interp W' C wstk ∗
    ( [∗ map] r↦w ∈ arg_rmap',
        r ↦ᵣ w ∗ if decide (r ∈ dom_arg_rmap nargs) then interp W C w else ⌜ w = WInt 0 ⌝ ) ∗
    ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
    -∗
    ∃ regs,
      registers_pointsto regs ∗
      execute_entry_point_register wcgp wstk nargs W' C regs.
  Proof.
    iIntros (Hrelated Hheap Harg_rmap' Hrmap')
      "(Hcgp & Hcra & Hcsp & #Hstk & Hargs & Hregs)".
    iDestruct (big_sepM_sep with "Hregs") as "[Hregs #Hnil]".
    iDestruct (big_sepM_sep with "Hargs") as "[Hargs #Hval]".
    iDestruct (big_sepM_union with "[$Hargs $Hregs]") as "Hregs".
    { apply map_disjoint_dom. rewrite Hrmap' Harg_rmap'.
      set_solver+. }
    iDestruct (big_sepM_insert_2 with "[Hcsp] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hcra] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hcgp] Hregs") as "Hregs";[iFrame|].
    iExists _; iFrame "Hregs".
    cbn.
    iSplit.
    { iPureIntro. intros rr. clear -Harg_rmap' Hrmap'.
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
    - iPureIntro. clear. simplify_map_eq. auto.
    - iPureIntro. exists mie. simplify_map_eq. auto.
    - iPureIntro. clear. simplify_map_eq. done.
    - done.
    - iIntros (r v Hr Hv).
      assert (r ∉ ({[ cgp ; cra ; csp ]} : gset RegName)) as Hr'.
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
        iApply (interp_monotone_same_heap with "[] Hv"); first done.
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
      trusted stack, above the topmost frame at [a_tstk]. *)
  Lemma switcher_inv_push_frame
    (frm : cframe) (cstk cstk' : CSTK) (a_tstk : Addr) (save_area tstk_next : list LWord)
    (wtbl : LWord) (b_stk e_stk a_stk : Addr) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    let a_save_end := (b_trusted_stack ^+ TSTACK_REGFRAME_SZ)%a in
    let a_threadID := (b_trusted_stack ^+ TrustedStack_offset_threadID)%a in
    let a_next := (a_tstk ^+ TrustedStackFrame_size)%a in
    let a_free := (a_next ^+ TrustedStackFrame_size)%a in
    let a_csp := (a_next ^+ TrustedStackFrame_offset_csp)%a in
    let a_export_table := (a_next ^+ TrustedStackFrame_offset_calleeExportTable)%a in
    let a_error_count := (a_next ^+ TrustedStackFrame_offset_errorHandlerCount)%a in
    (b_trusted_stack + tstack_frame_offset (length cstk'.(cstk_frames)))%a = Some a_tstk ->
    (b_trusted_stack + tstack_frame_offset (S (length cstk'.(cstk_frames))))%a = Some a_next ->
    (a_next + TrustedStackFrame_size <= e_trusted_stack)%Z ->
    (ot_switcher < ot_switcher ^+ 1)%ot ->
    frm.(cf_tframe).(tf_csp) = lword_of_word (WCap true RWL Local b_stk e_stk (stk_saved_a a_stk)) ->
    switcher_stk_bounds b_stk e_stk a_stk ->
    disjoint_from_mmio b_stk e_stk ->
    disjoint_from_heap b_stk e_stk ->
    (is_untrusted_caller_frm frm = false →
     jalr_target_ok cnull cra frm.(cf_saved).(cs_cra).(lw) = true ∧
     is_heap_cap frm.(cf_saved).(cs_cra).(lw) = false) ->
    frm.(cf_tframe).(tf_export_tbl) = lword_of_word (WInt 0) ∨
      (wtbl = frm.(cf_tframe).(tf_export_tbl) ∧ tf_export_tbl_ok frm.(cf_tframe)) ->
    save_area !! Z.to_nat TrustedStack_offset_hazardPointers = Some (lword_of_word hazard_slots_cap) ->

    cstack_full cstk' -∗
    cstack_frag cstk -∗
    mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack -∗
    [[ b_trusted_stack, a_save_end ]] ↦ₐ [[ save_area ]] -∗
    (∃ ws, [[ b_hazard_slots, e_hazard_slots ]] ↦ₐ [[ ws ]]) -∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset (S (length cstk'.(cstk_frames)))) -∗
    (∃ w, a_threadID ↦ₐ w) -∗
    a_csp ↦ₐ WCap true RWL Local b_stk e_stk (stk_saved_a a_stk) -∗
    a_export_table ↦ₐ wtbl -∗
    a_error_count ↦ₐ WInt frm.(cf_tframe).(tf_error_count) -∗
    [[ a_free , e_trusted_stack ]]
      ↦ₐ [[ tstk_next ]] -∗
    cstack_interp cstk' a_tstk -∗
    cframe_stk_own (stk_spill_a a_stk) frm.(cf_saved) frm.(ccrel) -∗
    seal_pred ot_switcher ot_switcher_propC
    ==∗
    switcher_inv ∗ cstack_frag (cstack_push frm cstk).
  Proof.
    intros a_frameoffset a_save_end a_threadID a_next a_free a_csp a_export_table a_error_count.
    subst a_frameoffset a_save_end a_threadID a_next a_free a_csp a_export_table a_error_count.
    iIntros (Hlen_cstk Hlen_cstk' Htstk_e Hot Hcsp (Hba & Hba3 & Ha4) Hstk_mmio Hstk_heap Hret
             Htbl Hsave_hazard)
      "Hcstk_full Hcstk Hmtdc Hsave_area Hhazard_slots Hframeoffset HthreadID Hframe_csp
       Hframe_tbl Hframe_cnt Htstk Hstk_interp Hframe #Hp_ot_switcher".
    iDestruct (cstack_agree with "Hcstk_full Hcstk") as %->.
    iMod (cstack_update _ _ (cstack_push frm cstk) with "Hcstk_full Hcstk") as "[Hcstk_full $]".
    iModIntro.
    iExists (a_tstk ^+ TrustedStackFrame_size)%a, (cstack_push frm cstk), save_area, tstk_next.
    iFrame "Hmtdc Hsave_area Hhazard_slots Hframeoffset HthreadID Htstk Hcstk_full Hp_ot_switcher".
    rewrite /cstack_interp.
    cbn.
    replace ((a_tstk ^+ TrustedStackFrame_size) ^+ - TrustedStackFrame_size)%a with a_tstk
      by (tstack_unfold; solve_addr).
    rewrite /cframe_interp /trusted_frame_interp Hcsp.
    iFrame "Hstk_interp Hframe_csp Hframe_cnt".
    iSplit; first done.
    iSplit; first done.
    iSplit; first (iPureIntro; split; done).
    iSplitL "Hframe_tbl"; first (iExists wtbl; by iFrame).
    iExists b_stk, e_stk, a_stk.
    iFrame "Hframe".
    iPureIntro.
    repeat split; try done; try solve_addr; try (by destruct Hstk_mmio); naive_solver.
  Qed.

  (** The switcher invariant, open during the call routine: the resources
      of the invariant that the call path does not use, and what closes
      the invariant. The trusted stack pointer, the frame offset and the
      unused part of the trusted stack go through the call path. *)
  Definition switcher_inv_opened (cstk' : CSTK) (a_tstk : Addr) : iProp Σ :=
    let a_save_end := (b_trusted_stack ^+ TSTACK_REGFRAME_SZ)%a in
    let a_threadID := (b_trusted_stack ^+ TrustedStack_offset_threadID)%a in
    "Hclose_switcher_inv" ∷
      (▷ switcher_inv ∗ na_own cerise_nais (⊤ ∖ ↑Nswitcher) ={⊤}=∗ na_own cerise_nais ⊤) ∗
    "Hna" ∷ na_own cerise_nais (⊤ ∖ ↑Nswitcher) ∗
    "Hsave_area" ∷
      (∃ save_area,
        ⌜save_area !! Z.to_nat TrustedStack_offset_hazardPointers
         = Some (lword_of_word hazard_slots_cap)⌝ ∗
        (tstack_hazard_cell ↦ₐ hazard_slots_cap -∗
         [[ b_trusted_stack, a_save_end ]] ↦ₐ [[ save_area ]])) ∗
    "HthreadID" ∷ (∃ w, a_threadID ↦ₐ w) ∗
    "Hcstk_full" ∷ cstack_full cstk' ∗
    "Hstk_interp" ∷ cstack_interp cstk' a_tstk ∗
    "#Hp_ot_switcher" ∷ seal_pred ot_switcher ot_switcher_propC ∗
    "%Hlen_cstk" ∷ ⌜ (b_trusted_stack + tstack_frame_offset (length cstk'.(cstk_frames)))%a
                     = Some a_tstk ⌝ ∗
    "%Ha_tstk_e" ∷ ⌜ (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z ⌝ ∗
    "%Hot_bounds" ∷ ⌜ (ot_switcher < ot_switcher ^+ 1)%ot ⌝.

  (** Open the switcher invariant for the call routine. The resources come
      under a later, which the first instruction removes. *)
  Lemma switcher_inv_open_call :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    na_inv cerise_nais Nswitcher switcher_inv -∗
    na_own cerise_nais ⊤
    ={⊤}=∗
    ∃ (a_tstk : Addr) (cstk' : CSTK) (tstk_next : list LWord),
      let a_next := (a_tstk ^+ TrustedStackFrame_size)%a in
      ⌜ (b_trusted_stack + tstack_frame_offset (length cstk'.(cstk_frames)))%a = Some a_tstk ⌝ ∗
      ⌜ (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z ⌝ ∗
      ▷ switcher_inv_opened cstk' a_tstk ∗
      mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
      a_frameoffset ↦ₐ WInt (tstack_frameoffset (length cstk'.(cstk_frames))) ∗
      switcher_hazard ∗
      [[ a_next, e_trusted_stack ]] ↦ₐ [[ tstk_next ]].
  Proof.
    intros a_frameoffset; subst a_frameoffset.
    iIntros "#Hinv Hna".
    iMod (na_inv_acc with "Hinv Hna") as "(Hswitcher_inv & Hna & Hclose)"; [done|done|].
    iMod (switcher_inv_open with "Hswitcher_inv") as
      (a_tstk cstk' save_area tstk_next)
      "(Hmtdc & %Hot & Hsave_area & %Hsave_hazard & Hhazard_slots & Hframeoffset & HthreadID
       & Htstk & Hcstk_full & %Hlen & Hstk_interp & #Hp_ot_switcher)".
    destruct Hlen as [Hlen Ha_tstk_e].
    iDestruct (switcher_hazard_open with "Hsave_area Hhazard_slots") as "[Hhazard Hsave_area]";
      first done.
    iModIntro.
    iExists a_tstk, cstk', tstk_next.
    iFrame "Hmtdc Hframeoffset Hhazard Htstk".
    iSplit; first done.
    iSplit; first done.
    iNext.
    iFrame "Hclose Hna Hsave_area HthreadID Hcstk_full Hstk_interp Hp_ot_switcher".
    done.
  Qed.

  (** Close the switcher invariant, with the trusted stack unchanged. *)
  Lemma switcher_inv_opened_close (cstk' : CSTK) (a_tstk : Addr) (tstk_next : list LWord) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    let a_next := (a_tstk ^+ TrustedStackFrame_size)%a in
    switcher_inv_opened cstk' a_tstk -∗
    mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack -∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset (length cstk'.(cstk_frames))) -∗
    switcher_hazard -∗
    [[ a_next, e_trusted_stack ]] ↦ₐ [[ tstk_next ]]
    ={⊤}=∗
    na_own cerise_nais ⊤.
  Proof.
    intros a_frameoffset a_next; subst a_frameoffset a_next.
    iIntros "Hopened Hmtdc Hframeoffset Hhazard Htstk".
    iNamed "Hopened".
    iDestruct "Hsave_area" as (save_area Hsave_hazard) "Hsave_area".
    iDestruct "Hhazard" as "[Hhazard_cell Hhazard_slots]".
    iSpecialize ("Hsave_area" with "Hhazard_cell").
    iApply ("Hclose_switcher_inv" with "[- $Hna]").
    iNext. iExists a_tstk, cstk', save_area, tstk_next.
    iFrame "Hmtdc Hsave_area Hhazard_slots Hframeoffset HthreadID Htstk Hcstk_full Hstk_interp
      Hp_ot_switcher".
    iPureIntro; done.
  Qed.

  (** Close the switcher invariant after pushing the frame [frm] on the
      trusted stack. *)
  Lemma switcher_inv_opened_push
    (frm : cframe) (cstk cstk' : CSTK) (a_tstk : Addr) (tstk_next : list LWord)
    (wtbl : LWord) (b_stk e_stk a_stk : Addr) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    let a_next := (a_tstk ^+ TrustedStackFrame_size)%a in
    let a_free := (a_next ^+ TrustedStackFrame_size)%a in
    let a_csp := (a_next ^+ TrustedStackFrame_offset_csp)%a in
    let a_export_table := (a_next ^+ TrustedStackFrame_offset_calleeExportTable)%a in
    let a_error_count := (a_next ^+ TrustedStackFrame_offset_errorHandlerCount)%a in
    (b_trusted_stack + tstack_frame_offset (S (length cstk'.(cstk_frames))))%a = Some a_next ->
    (a_next + TrustedStackFrame_size <= e_trusted_stack)%Z ->
    frm.(cf_tframe).(tf_csp) = lword_of_word (WCap true RWL Local b_stk e_stk (stk_saved_a a_stk)) ->
    switcher_stk_bounds b_stk e_stk a_stk ->
    disjoint_from_mmio b_stk e_stk ->
    disjoint_from_heap b_stk e_stk ->
    (is_untrusted_caller_frm frm = false →
     jalr_target_ok cnull cra frm.(cf_saved).(cs_cra).(lw) = true ∧
     is_heap_cap frm.(cf_saved).(cs_cra).(lw) = false) ->
    frm.(cf_tframe).(tf_export_tbl) = lword_of_word (WInt 0) ∨
      (wtbl = frm.(cf_tframe).(tf_export_tbl) ∧ tf_export_tbl_ok frm.(cf_tframe)) ->

    switcher_inv_opened cstk' a_tstk -∗
    cstack_frag cstk -∗
    mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack -∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset (S (length cstk'.(cstk_frames)))) -∗
    switcher_hazard -∗
    a_csp ↦ₐ WCap true RWL Local b_stk e_stk (stk_saved_a a_stk) -∗
    a_export_table ↦ₐ wtbl -∗
    a_error_count ↦ₐ WInt frm.(cf_tframe).(tf_error_count) -∗
    [[ a_free , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] -∗
    cframe_stk_own (stk_spill_a a_stk) frm.(cf_saved) frm.(ccrel)
    ={⊤}=∗
    na_own cerise_nais ⊤ ∗ cstack_frag (cstack_push frm cstk).
  Proof.
    intros a_frameoffset a_next a_free a_csp a_export_table a_error_count.
    subst a_frameoffset a_next a_free a_csp a_export_table a_error_count.
    iIntros (Ha_next Ha_next_e Hcsp Hbounds Hstk_mmio Hstk_heap Hret Htbl)
      "Hopened Hcstk Hmtdc Hframeoffset Hhazard Hframe_csp Hframe_tbl Hframe_cnt Htstk Hframe".
    iNamed "Hopened".
    iDestruct "Hsave_area" as (save_area Hsave_hazard) "Hsave_area".
    iDestruct "Hhazard" as "[Hhazard_cell Hhazard_slots]".
    iSpecialize ("Hsave_area" with "Hhazard_cell").
    iMod (switcher_inv_push_frame frm cstk with
           "Hcstk_full Hcstk Hmtdc Hsave_area Hhazard_slots Hframeoffset HthreadID Hframe_csp
            Hframe_tbl Hframe_cnt Htstk Hstk_interp Hframe Hp_ot_switcher")
      as "[Hinv $]"; [done..|].
    iApply ("Hclose_switcher_inv" with "[$Hinv $Hna]").
  Qed.

  (** The sealing predicate of [ot_switcher], from the open invariant. *)
  Lemma switcher_inv_opened_seal_pred (cstk' : CSTK) (a_tstk : Addr) :
    switcher_inv_opened cstk' a_tstk ⊢ seal_pred ot_switcher ot_switcher_propC.
  Proof. iIntros "Hopened"; iNamed "Hopened"; iExact "Hp_ot_switcher". Qed.

  (** ** Functional specification *)

  (** The callee's stack and the spill area of a caller whose cursor is
      [a] are disjoint parts of its free part. *)
  #[local] Lemma callee_stk_region_free_split (b e a : Addr) :
    callee_stk_bounds b e a →
    stk_free b e a =
      callee_stk_region b e a ++
        finz.seq_between (stk_spill_a a) (stk_spill_a a ^+ SpillSlot_size)%a.
  Proof.
    intros (_ & He & Hbe & Ha).
    rewrite stk_spill_a_end //. stk_unfold.
    apply finz_seq_between_split; solve_addr.
  Qed.

  (** The spill area and the callee's stack make the free part. *)
  #[local] Lemma stk_free_join_callee (b e a : Addr) (ls lc : list LWord) :
    callee_stk_bounds b e a →
    length ls = Z.to_nat SpillSlot_size →
    [[ stk_spill_a a , (stk_spill_a a ^+ SpillSlot_size)%a ]] ↦ₐ [[ ls ]] ∗
    [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ [[ lc ]] ⊢
    [[ stk_free_b b a , stk_free_e e a ]] ↦ₐ [[ stk_mem_join ls lc ]].
  Proof.
    intros (_ & He & Hbe & Ha) Hls.
    rewrite stk_spill_a_end //. stk_unfold.
    rewrite region_pointsto_split_r; [by rewrite bi.sep_comm|solve_addr|].
    rewrite Hls /finz.dist. solve_addr.
  Qed.

  (** Reinstate the callee's stack in the world, once cleared. *)
  Lemma switcher_cc_world_reinstate E W C (b e a : Addr) :
    revoked_addresses W (stk_free b e a) ->
    callee_stk_bounds b e a ->
    disjoint_from_mmio (stk_free_b b a) (stk_free_e e a) ->
    disjoint_from_heap (stk_free_b b a) (stk_free_e e a) ->
    let W' := std_update_multiple W (callee_stk_region b e a) Temporary in
    world_interp W C -∗
    StackRevokedResources W C (stk_free b e a) -∗
    [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ
      [[ region_addrs_zeroes (stk_callee_b b a) (stk_callee_e e a) ]]
    ={E}=∗
    world_interp W' C ∗
    interp W' C (callee_csp b e a) ∗
    ⌜ related_sts_pub_world W W' ⌝ ∗
    ⌜ revoked_addresses W (callee_stk_region b e a) ⌝.
  Proof.
    iIntros (Hstk_revoked Hbounds Hstk_mmio Hstk_heap W') "Hworld_interp Hstk_val Hstk".
    rewrite (callee_stk_region_free_split _ _ _ Hbounds) in Hstk_revoked |- *.
    iDestruct (StackRevokedResources_app with "Hstk_val") as "[#Hstk_val' _]".
    apply revoked_addresses_app in Hstk_revoked as [Hrev _].
    iMod (world_interp_reinstate_stack with "Hworld_interp Hstk_val' Hstk") as "Hworld_interp"; auto.
    { apply finz_seq_between_NoDup. }
    { apply Forall_replicate_eq. }
    iModIntro.
    iFrame "Hworld_interp".
    iSplit; last (iPureIntro; split; [apply related_sts_pub_update_multiple_temp|]; done).
    revert Hbounds Hstk_mmio Hstk_heap; stk_unfold; intros (_ & He & Hbe & Ha) Hstk_mmio Hstk_heap.
    assert (disjoint_from_mmio b (a ^+ - (4))%a ∧ disjoint_from_heap b (a ^+ - (4))%a)
      as [Hshadow Hheap].
    { eapply switcher_disjoint_subseg; [reflexivity| |split; eassumption]. solve_addr. }
    iApply interp_unfold. iSimpl.
    iSplit; last first.
    { iPureIntro. split; first exact Hshadow. by apply heap_cap_valid_disjoint. }
    rewrite /StackRevokedResources /StackWorldResources big_sepL2_replicate_r; last done.
    iApply (big_sepL_impl with "Hstk_val'").
    iIntros "!>" (k a' Ha') "Hr".
    rewrite ?addr_key_None.
    iDestruct "Hr" as (φ p) "(Hφ & Hmono & Hrel & (HmonoR & Hzcond & Hrcond & Hwcond & Hpers) & %Hperm_flow)".
    iExists p,φ.
    iSplit; first (iPureIntro; exact Hperm_flow).
    iFrame "Hpers Hrel Hzcond".
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
  Lemma switcher_cc_exhausted_regs (arg_rmap rmap : LReg) (wct1 wct2 wctp : LWord) :
    is_arg_rmap arg_rmap 8 ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    ( [∗ map] r↦w ∈ arg_rmap, r ↦ᵣ w ) -∗
    ( [∗ map] r↦w ∈ delete ctp (delete ct2 rmap), r ↦ᵣ w ) -∗
    ct1 ↦ᵣ wct1 -∗
    ct2 ↦ᵣ wct2 -∗
    ctp ↦ᵣ wctp -∗
    ∃ (wca0 wca1 : LWord) (rmap0 : LReg),
      ca0 ↦ᵣ wca0 ∗
      ca1 ↦ᵣ wca1 ∗
      ⌜ dom rmap0 = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
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
    (stk_mem_l stk_mem_h : list LWord) :
    revoked_addresses W (stk_free b_stk e_stk a_stk) ->
    related_sts_pub_world
      (std_update_multiple W (callee_stk_region b_stk e_stk a_stk) Temporary) W2 ->
    callee_stk_bounds b_stk e_stk a_stk ->

    interp W2 C (callee_csp b_stk e_stk a_stk) -∗
    StackRevokedResources W C (stk_free b_stk e_stk a_stk) -∗
    world_interp_open W2 C (LNonHeap <$> callee_stk_region b_stk e_stk a_stk) -∗
    StackOpenWorldResources interp W2 C (callee_stk_region b_stk e_stk a_stk) stk_mem_h -∗
    [[ stk_spill_a a_stk , (stk_spill_a a_stk ^+ SpillSlot_size)%a ]] ↦ₐ [[ stk_mem_l ]] -∗
    [[ stk_callee_b b_stk a_stk , stk_callee_e e_stk a_stk ]] ↦ₐ [[ stk_mem_h ]] -∗
    £ 2
    ={E}=∗
    ∃ (stk_mem : list LWord) (l' : list LAddr),
      ⌜ extract_temporaries_condition W2
          (l' ++ (LNonHeap <$> callee_stk_region b_stk e_stk a_stk)) ⌝ ∗
      RevokedResources W2 C l' ∗
      ⌜ revoked_keys (revoke W2) l' ⌝ ∗
      StackRevokedResources W2 C (stk_free b_stk e_stk a_stk) ∗
      ⌜ revoked_addresses (revoke W2) (stk_free b_stk e_stk a_stk) ⌝ ∗
      world_interp (revoke W2) C ∗
      [[ stk_free_b b_stk a_stk , stk_free_e e_stk a_stk ]] ↦ₐ [[ stk_mem ]].
  Proof.
    iIntros (Hrevoked_stk Hrelated_pub_Wext_W2 Hcsp_bounds)
      "#Hinterp_W2_csp #Hstk_val Hworld_interp_C Hstack_revoked_W2 Hstk_l Hstk_h [Hlc Hlc']".
    pose proof (callee_stk_region_free_split _ _ _ Hcsp_bounds) as Hsplit.
    iDestruct ( big_sepL2_length with "Hstk_h" ) as "%Hlen_stk_h".
    iDestruct ( big_sepL2_length with "Hstk_l" ) as "%Hlen_stk_l".
    iEval (rewrite <- (app_nil_r (callee_stk_region b_stk e_stk a_stk))) in "Hworld_interp_C".

    iDestruct (close_world_interp_opening_resources
                with "[$Hworld_interp_C $Hstack_revoked_W2 $Hstk_h]")
      as "Hworld_interp_C".
    { apply finz_seq_between_NoDup. }
    { set_solver+. }
    { by rewrite /callee_stk_region finz_seq_between_length in Hlen_stk_l. }
    rewrite fmap_nil -open_world_interp_empty.

    assert (NoDup (stk_free b_stk e_stk a_stk)) as Hnodup by apply finz_seq_between_NoDup.
    rewrite Hsplit in Hrevoked_stk Hnodup.
    apply revoked_addresses_app in Hrevoked_stk as [Hrev_callee Hrev_spill].
    apply NoDup_app in Hnodup as (_ & Hdisj & _).

    iMod (world_interp_revoked_by_separation_many with "[$Hworld_interp_C $Hstk_l]")
      as "(Hworld_interp_C & Hstk_l & %Hstk_l_revoked)".
    { apply Forall_forall; intros x Hx. apply heap_key_live_nonheap. }
    {
      apply Forall_forall; intros a Ha.
      eapply elem_of_mono_pub;eauto.
      rewrite elem_of_dom.
      rewrite std_sta_update_multiple_lookup_same_i; cycle 1.
      { intro Hcontra. by apply (Hdisj a). }
      rewrite /revoked_addresses Forall_forall in Hrev_spill.
      apply Hrev_spill in Ha.
      done.
    }

    iMod (world_interp_revoke_stack with "[$Hinterp_W2_csp $Hworld_interp_C]")
      as (l') "(%Hl_unk' & Hworld_interp_C & Hstack_revoked_W2 & Hrevoked_W2 & >[%stk_mem_h' Hstk_h] & [Hrevoked_l' %Hrevoked_W2_l'])".
    iDestruct (stk_free_join_callee with "[$Hstk_l $Hstk_h]") as "Hstk"; first done.
    { rewrite finz_seq_between_length in Hlen_stk_l. rewrite -Hlen_stk_l.
      revert Hcsp_bounds; stk_unfold. intros (_ & He & Hbe & Ha).
      rewrite /finz.dist. solve_addr. }
    iCombine "Hstack_revoked_W2 Hrevoked_W2" as "Hstack_revoked_W2".
    iDestruct (lc_fupd_elim_later with "[$] [$Hrevoked_l']") as ">Hrevoked_l'".
    iDestruct (lc_fupd_elim_later with "[$] [$Hstack_revoked_W2]") as ">[Hstack_revoked_W2 %Hrevoked_callee]".
    iModIntro.
    iExists _, l'; iFrame (Hl_unk' Hrevoked_W2_l') "Hrevoked_l' Hworld_interp_C Hstk".
    rewrite Hsplit.
    iSplitL "Hstack_revoked_W2"; cycle 1.
    { iPureIntro.
      rewrite !/revoked_addresses !Forall_forall in Hrevoked_callee, Hstk_l_revoked |- *.
      intros x Hx; cbn.
      apply elem_of_app in Hx; destruct Hx as [Hx|Hx].
      + apply Hrevoked_callee; done.
      + apply revoke_lookup_Revoked; apply Hstk_l_revoked; done.
    }
    iDestruct (StackRevokedResources_app with "Hstk_val") as "[_ Hstk_val_l]".
    iApply StackRevokedResources_app; iFrame "Hstack_revoked_W2".
    iApply (StackRevokedResources_mono_priv with "Hstk_val_l").
    eapply related_sts_priv_pub_trans_world; eauto.
    apply related_sts_pub_priv_world.
    eapply related_sts_pub_update_multiple_temp.
    done.
  Qed.

  (** Revoke the world after the trusted stack was exhausted. The world is
      the one of the call, where the callee's stack frame is [Temporary]. *)
  Lemma switcher_cc_revoke_exhausted E W C (b_stk e_stk a_stk : Addr)
    (stk_mem_l stk_mem_h : list LWord) :
    let W2 := std_update_multiple W (callee_stk_region b_stk e_stk a_stk) Temporary in
    revoked_addresses W (stk_free b_stk e_stk a_stk) ->
    callee_stk_bounds b_stk e_stk a_stk ->
    length stk_mem_l = Z.to_nat SpillSlot_size ->

    world_interp W C -∗
    StackRevokedResources W C (stk_free b_stk e_stk a_stk) -∗
    [[ stk_spill_a a_stk , (stk_spill_a a_stk ^+ SpillSlot_size)%a ]] ↦ₐ [[ stk_mem_l ]] -∗
    [[ stk_callee_b b_stk a_stk , stk_callee_e e_stk a_stk ]] ↦ₐ [[ stk_mem_h ]] -∗
    £ 2
    ={E}=∗
    ∃ (l' : list LAddr),
      ⌜ extract_temporaries_condition W2
          (l' ++ (LNonHeap <$> callee_stk_region b_stk e_stk a_stk)) ⌝ ∗
      RevokedResources W2 C l' ∗
      ⌜ revoked_keys (revoke W2) l' ⌝ ∗
      ⌜ related_sts_pub_world W2 W2 ⌝ ∗
      ([∗ list] a ∈ callee_stk_region b_stk e_stk a_stk,
         ⌜ std W2 !! LNonHeap a = Some Temporary ⌝) ∗
      StackRevokedResources W2 C (stk_free b_stk e_stk a_stk) ∗
      ⌜ revoked_addresses (revoke W2) (stk_free b_stk e_stk a_stk) ⌝ ∗
      world_interp (revoke W2) C ∗
      [[ stk_free_b b_stk a_stk , stk_free_e e_stk a_stk ]] ↦ₐ
        [[ stk_mem_join stk_mem_l stk_mem_h ]].
  Proof.
    intros W2.
    iIntros (Hrevoked_stk Hcsp_bounds Hlen_l)
      "Hworld_interp_C #Hclose Hstk_l Hstk_h [Hlc Hlc']".
    pose proof (callee_stk_region_free_split _ _ _ Hcsp_bounds) as Hsplit.
    pose proof (extract_temps W) as [l_unk [Hlunk_nodup Hlunk] ].
    assert (revoked_addresses W (callee_stk_region b_stk e_stk a_stk)) as Hrev_callee.
    { rewrite Hsplit in Hrevoked_stk. by apply revoked_addresses_app in Hrevoked_stk as [? ?]. }

    iMod ( world_interp_revoke _ _ l_unk with "[$Hworld_interp_C]") as
      "(Hworld_interp_C & Hrevoked_l & %Hrevoked_l)"; auto.
    { split; auto. }
    iDestruct (lc_fupd_elim_later with "[$] [$Hrevoked_l]") as ">Hrevoked_l".
    iModIntro.
    subst W2.
    rewrite revoke_std_update_multiple_eq.
    2: { apply Forall_forall.
         intros a Ha.
         rewrite /revoked_addresses Forall_forall in Hrev_callee.
         by apply Hrev_callee.
    }
    iExists l_unk; iFrame (Hrevoked_l) "Hworld_interp_C".
    iSplit.
    { iPureIntro.
      split.
      - apply NoDup_app; split; auto.
        split; last by apply NoDup_LNonHeap_fmap, finz_seq_between_NoDup.
        intros a Ha. apply Hlunk in Ha.
        intro Ha'.
        apply list_elem_of_fmap in Ha' as [a' [-> Ha'] ].
        rewrite /revoked_addresses Forall_forall in Hrev_callee.
        apply Hrev_callee in Ha'.
        simplify_eq.
      - intros a; cbn.
        rewrite elem_of_app.
        split; intro Ha.
        + destruct ( decide ( a ∈ LNonHeap <$> callee_stk_region b_stk e_stk a_stk )); first (right; done).
          rewrite std_sta_update_multiple_lookup_same_k in Ha; auto.
          apply Hlunk in Ha.
          left; done.
        + destruct Ha as [Ha|Ha]; cycle 1.
          * rewrite std_sta_update_multiple_lookup_in_k; auto.
          * destruct ( decide ( a ∈ LNonHeap <$> callee_stk_region b_stk e_stk a_stk )); first (rewrite std_sta_update_multiple_lookup_in_k; auto).
            rewrite std_sta_update_multiple_lookup_same_k; auto.
            apply Hlunk in Ha; done.
    }
    iSplitL "Hrevoked_l".
    {
      iApply (RevokedResources_mono_pub with "Hrevoked_l"); auto.
      by eapply related_sts_pub_update_multiple_temp.
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
      by eapply related_sts_pub_update_multiple_temp.
    }
    iSplit; first iPureIntro.
    { eapply Forall_impl; eauto.
      cbn; intros a Ha.
      apply revoke_lookup_Revoked; done.
    }
    iApply stk_free_join_callee; [done | done |].
    iFrame.
  Qed.

End Switcher_Call_World.
