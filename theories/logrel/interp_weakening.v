From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Import memory_region monotone.
From griotte Require Export logrel.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {cthreads : CmptThreads} {CL : CritLink Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation E := (CSTK -n> list WORLD -n> WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).
  #[local] Notation V := (interpO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

  (** A Local copy of a Global sentry runs at the running thread: the thread
      is in the compartment whenever the copy runs. *)
  Lemma enter_cond_weakening_global W C p b e a π :
    (□ ∀ t', thread_in t' C -∗
       enter_cond (th := t') W C p Global b e a π (interp (th := t'))) -∗
     □ enter_cond W C p Local b e a π interp.
  Proof.
    iIntros "#Hinterp !>". rewrite /enter_cond.
    iIntros (W') "_". iIntros (g' Hflows).
    iApply later_interp_expr_thread_in. iIntros "#Hth".
    assert (LocalityFlowsTo g' Global) as Hflow' by (destruct g'; auto).
    iSpecialize ("Hinterp" $! th with "Hth").
    iApply ("Hinterp" $! W' with "[//] [%]"). done.
  Qed.

  (** The read condition of a capability, through a lesser locality: from
      Global to Local at the running thread. *)
  Lemma rcond_sel_weakening g g' P C p'' :
    LocalityFlowsTo g' g →
    □ (⌜g = Global⌝ → ⌜g' = Local⌝ → thread_in th C) -∗
    ▷ (if isGlobal g then rcond_g P C p'' (λ t, interp (th := t)) else rcond P C p'' interp) -∗
    ▷ (if isGlobal g' then rcond_g P C p'' (λ t, interp (th := t)) else rcond P C p'' interp).
  Proof.
    iIntros (Hl) "#Hth H". destruct g, g'; cbn in Hl |- *; try done.
    iApply (rcond_sel_here Global with "[] H"). by iApply "Hth".
  Qed.

  (** The write condition of a capability, through a lesser permission. *)
  Lemma wcond_sel_weakening p p' P C :
    PermFlowsTo p' p →
    ▷ (if isWL p then wcond P C interp else wcond_nwl P C interp) -∗
    ▷ (if isWL p' then wcond P C interp else wcond_nwl P C interp).
  Proof.
    iIntros (Hp) "H".
    destruct (isWL p') eqn:Hwl'.
    { by rewrite (isWL_flowsto p' p Hp Hwl'). }
    destruct (isWL p); last done.
    iNext. by iApply wcond_wcond_nwl.
  Qed.

  (** The region of a key, read through a lesser capability. *)
  Lemma region_rel_weakening W C k p'' P p p' g g' :
    PermFlowsTo p' p →
    LocalityFlowsTo g' g →
    (isWL p = true → g = Local) →
    region_rel W C k p'' P p g -∗ region_rel W C k p'' P p' g'.
  Proof.
    iIntros (Hp Hg Hwl) "Hrel". rewrite /region_rel.
    destruct (isWL p') eqn:Hwl'.
    { rewrite (isWL_flowsto p' p Hp Hwl'). done. }
    destruct (isWL p) eqn:Hpwl.
    { rewrite (Hwl eq_refl) in Hg. destruct g'; cbn in Hg; [done|]. by iRight. }
    destruct g, g'; cbn in Hg; try done; by iLeft.
  Qed.

  Lemma heap_cap_O_key_weakening W C g g' k :
    LocalityFlowsTo g' g →
    heap_cap_O_key W C g k -∗ heap_cap_O_key W C g' k.
  Proof.
    iIntros (Hg) "[H|H]"; [by iLeft|].
    destruct g, g'; cbn in Hg; try done; by iRight.
  Qed.

  Lemma interp_weakening_from_sentry W C sk t p g b e a π :
      interp W C (WSentry sk t p g b e a @@? π)
      -∗ interp W C (WSentry sk t p Local b e a @@? π).
  Proof.
    iIntros "#Hinterp".
    destruct t; last (iApply interp_untagged; done).
    rewrite !interp_unfold /=.
    iDestruct "Hinterp" as "[$ Hinterp]".
    destruct g; cbn; last done.
    by iApply enter_cond_weakening_global.
  Qed.

  Lemma heap_cap_ok_perm p p' b e π :
    PermFlowsTo p' p -> heap_cap_ok p b e π -∗ heap_cap_ok p' b e π.
  Proof.
    iIntros (Hflow) "#Hok %Hnonempty". iSpecialize ("Hok" with "[//]").
    destruct π as [ι|]; last done.
    iDestruct "Hok" as "[%Hconds $]". iPureIntro.
    destruct Hconds as (Hheap & Hexec & HnotWL).
    repeat split; eauto using notexecuteAllowed_flowsfrom, notisWL_flowsfrom.
  Qed.

  Lemma interp_weakening_O_same_bounds W C t p p' g g' b e a a' π :
    isO p' = true ->
    PermFlowsTo p' p ->
    LocalityFlowsTo g' g ->
    interp W C (WCap t p g b e a @@? π) -∗
    interp W C (WCap t p' g' b e a' @@? π).
  Proof.
    intros HpO Hp Hg. iIntros "Hinterp".
    destruct t; last (iApply interp_untagged; done).
    iDestruct (interp_cap_heap_conditions with "Hinterp") as "[#Hvalid #Hcoverage]".
    iEval (rewrite interp_unfold interp1_eq HpO).
    iSplit; first by iApply (heap_cap_ok_perm with "Hvalid").
    iApply (big_sepL_impl with "Hcoverage"). iIntros "!>" (k x Hx) "Hx %Hheap".
    iApply (heap_cap_O_key_weakening with "(Hx [//])"); done.
  Qed.

  Lemma interp_weakening_same_bounds_gen W C t p p' g g' b e a a' π :
    isO p = false →
    isO p' = false →
    PermFlowsTo p' p ->
    LocalityFlowsTo g' g ->
    □ (⌜g = Global⌝ → ⌜g' = Local⌝ → thread_in th C) -∗
    interp W C (WCap t p g b e a @@? π) -∗
    interp W C (WCap t p' g' b e a' @@? π).
  Proof.
    intros HpnotO HpnotO' Hp Hl. iIntros "#Hth HA".
    destruct t; last (iApply interp_untagged; done).
    rewrite !interp_unfold !interp1_eq.
    rewrite HpnotO HpnotO'.
    destruct (has_sreg_access p) eqn:HpXSR; auto.
    replace (has_sreg_access p')
      with false by (symmetry; eapply nothas_sreg_access_flowsfrom; eauto).
    iDestruct "HA" as "[#A [%Hconditions #Hheap] ]".
    destruct Hconditions as [Hpwl_cond Hshadow].
    iSplit; cycle 1.
    { iSplit; last by iApply (heap_cap_ok_perm with "Hheap").
      iPureIntro. split; last done.
      case_eq (isWL p'); intros Hpwl'; auto.
      pose proof (isWL_flowsto p' p Hp Hpwl') as Hpwl.
      rewrite Hpwl in Hpwl_cond.
      destruct g; try congruence.
      destruct g'; simpl in Hl; tauto.
    }

    iApply (big_sepL_impl with "A"); auto.
    iModIntro; iIntros (k x Hx) "Hw".
    iDestruct "Hw" as (p'' φ Hflp'' Hpersφ) "(Hrel & Hzcond & Hrcond & Hwcond)".
    iExists p'', φ. iFrame "Hzcond".
    iSplit; first (iPureIntro; eapply PermFlowsToTransitive; eauto).
    iSplit; first done.
    iSplitL "Hrel".
    { iApply (region_rel_weakening with "Hrel"); eauto.
      intros Hpwl. by rewrite Hpwl in Hpwl_cond. }
    iSplitL "Hrcond".
    { destruct (readAllowed p''); last done.
      iApply (rcond_sel_weakening with "Hth Hrcond"); done. }
    destruct (writeAllowed p''); last done.
    iApply (wcond_sel_weakening with "Hwcond"); done.
  Qed.

  Lemma interp_weakening_same_bounds W C t p p' g g' b e a a' π :
    isO p = false →
    isO p' = false →
    PermFlowsTo p' p ->
    LocalityFlowsTo g' g ->
    thread_in th C -∗
    interp W C (WCap t p g b e a @@? π) -∗
    interp W C (WCap t p' g' b e a' @@? π).
  Proof.
    intros HpnotO HpnotO' Hp Hl. iIntros "#Hth HA".
    iApply (interp_weakening_same_bounds_gen with "[] HA"); [done..|].
    by iIntros "!> _ _".
  Qed.

  (** The same at the same locality: no thread premise. *)
  Lemma interp_weakening_same_bounds_same_loc W C t p p' g b e a a' π :
    isO p = false →
    isO p' = false →
    PermFlowsTo p' p ->
    interp W C (WCap t p g b e a @@? π) -∗
    interp W C (WCap t p' g b e a' @@? π).
  Proof.
    intros HpnotO HpnotO' Hp. iIntros "HA".
    iApply (interp_weakening_same_bounds_gen with "[] HA"); [done|done|done|apply LocalityFlowsToReflexive|].
    iIntros "!>" (Hg1 Hg2). congruence.
  Qed.

  Lemma interp_next_PC W C t p g b e a a' π :
    isCorrectPC (WCap t p g b e a) ->
    interp W C (WCap t p g b e a @@? π) -∗
    interp W C (WCap t p g b e a' @@? π).
  Proof.
    iIntros (HcorrectPC) "#Hinterp".
    destruct t; last by inversion HcorrectPC.
    inversion HcorrectPC as [p' g' b' e' a'' Hb' Hexec']; subst.
    assert (isO p = false) by (by eapply executeAllowed_nonO).
    iApply interp_weakening_same_bounds_same_loc; eauto; try solve_addr; try done.
  Qed.

  Lemma interp_lea W C t p g b e a a' π :
    isO p = false ->
    interp W C (WCap t p g b e a @@? π) -∗
    interp W C (WCap t p g b e a' @@? π).
  Proof.
    iIntros (Hisno) "#Hi".
    iApply interp_weakening_same_bounds_same_loc; eauto; try solve_addr; try done.
  Qed.

  Lemma safe_to_unseal_weakening W C b e b' e':
    (b <= b')%ot ->
    (e' <= e)%ot ->
    safe_to_unseal W C (λ t, interp (th := t)) b e -∗
    safe_to_unseal W C (λ t, interp (th := t)) b' e'.
  Proof.
    iIntros (Hb He) "HA".
    rewrite /safe_to_unseal.
    destruct (decide (b' <= e')%ot).
    - rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr].
      rewrite !big_sepL_app; iDestruct "HA" as "[_ [$ _] ]".
    - iClear "HA"; rewrite !finz_seq_between_empty;[done |solve_addr].
  Qed.

  Lemma safe_to_seal_weakening W C b e b' e':
    (b <= b')%ot ->
    (e' <= e)%ot ->
    safe_to_seal W C (λ t, interp (th := t)) b e -∗
    safe_to_seal W C (λ t, interp (th := t)) b' e'.
  Proof.
    iIntros (Hb He) "HA".
    rewrite /safe_to_seal.
    destruct (decide (b' <= e')%ot).
    - rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr].
      rewrite !big_sepL_app; iDestruct "HA" as "[_ [$ _] ]".
    - iClear "HA"; rewrite !finz_seq_between_empty;[done |solve_addr].
  Qed.

  Lemma interp_weakening_ot W C t p p' g g' b b' e e' a a' π :
    (b <= b')%ot ->
    (e' <= e)%ot ->
    SealPermFlowsTo p' p ->
    LocalityFlowsTo g' g ->
    interp W C (WSealRange t p g b e a @@? π) -∗
    interp W C (WSealRange t p' g' b' e' a' @@? π).
  Proof.
  intros Hb He Hp Hg. iIntros "#HA".
  destruct t; last (iApply interp_untagged; done).
  rewrite !interp_unfold. cbn.
  destruct (permit_seal p') eqn:Hseal; [eapply (permit_seal_flowsto _ p) in Hseal as ->; auto | ].
  all: destruct (permit_unseal p') eqn:Hunseal; [eapply (permit_unseal_flowsto _ p) in Hunseal as ->; auto | ]; iDestruct "HA" as "[Hs Hus]".
  all: iSplitL "Hs";
  [try iApply (safe_to_seal_weakening with "Hs") | try iApply (safe_to_unseal_weakening with "Hus")]; auto.
  Unshelve. all: exact W.
  Qed.

  Lemma interp_borrowed_sealed (W : WORLD) (C : CmptName) (ot : OType) (sb : Sealable) π :
    interp W C (WSealed ot sb @@? π) -∗ interp W C (WSealed ot (borrow_sb sb) @@? π).
  Proof.
    iIntros "Hinterp".
    destruct sb as [t p g b e a | t p g b e a]; destruct t;
      rewrite !interp_unfold /= /interp_sb /=; try done.
    all: iDestruct "Hinterp" as "[(%κ & %P & #Hs & #Hok & HP) $]".
    all: iExists κ, P; iFrame "Hs Hok".
    all: destruct κ; cbn; [done|by iDestruct "Hok" as "[_ [] ]"].
  Qed.

  Lemma interp_deeplocal_word W C w : interp W C w ⊢ interp W C (ldeeplocal w).
  Proof.
    iIntros "Hw".
    destruct w as [w π].
    destruct (get_tag w) eqn:Htag.
    2: { iApply interp_untagged. by rewrite /= get_tag_deeplocal Htag. }
    rewrite /ldeeplocal /lift_word /=.
    destruct w; try done.
    destruct sb as [t p g b e a | t p g b e a];
      destruct t; cbn in Htag; try discriminate; try done; cbn; cycle 1.
    destruct p;try done; cbn; cycle 1.
    destruct (isO (BPerm rx w dl dro)) eqn:HpO.
    { destruct rx,w; cbn in *; try done.
      rewrite !interp_unfold //=.
    }
    iApply interp_weakening_same_bounds_same_loc; eauto; try done; try solve_addr.
    apply DL_flowsto.
  Qed.

  Lemma interp_borrow_word W C w : thread_in th C -∗ interp W C w -∗ interp W C (lborrow w).
  Proof.
    iIntros "#Hth Hw".
    destruct w as [w π].
    destruct (get_tag w) eqn:Htag.
    2: { iApply interp_untagged. by rewrite /= get_tag_borrow Htag. }
    rewrite /lborrow /lift_word /=.
    destruct w; try done.
    - destruct sb as [t p g b e a | t p g b e a];
      destruct t; cbn in Htag; try discriminate; try done; cbn; cycle 1.
      { by rewrite !interp_unfold. }
      {
        destruct p.
        destruct (isO (BPerm rx w dl dro)) eqn:HpO.
        { destruct rx,w; cbn in *; try done.
          rewrite !interp_unfold /=.
          iDestruct "Hw" as "[#Hvalid #Hcoverage]".
          iFrame "Hvalid".
          iApply (big_sepL_impl with "Hcoverage"). iIntros "!>" (k x Hx) "Hx %Hheap".
          iApply (heap_cap_O_key_weakening with "(Hx [//])"). by destruct g.
        }
        iApply (interp_weakening_same_bounds with "Hth"); eauto; try done; try solve_addr.
      }
    - by iApply interp_weakening_from_sentry.
    - by iApply (interp_borrowed_sealed with "Hw").
  Qed.

  Lemma interp_readonly_word W C w : interp W C w ⊢ interp W C (lreadonly w).
  Proof.
    iIntros "Hw".
    destruct w as [w π].
    destruct (get_tag w) eqn:Htag.
    2: { iApply interp_untagged. by rewrite /= get_tag_readonly Htag. }
    rewrite /lreadonly /lift_word /=.
    destruct w; try done.
    destruct sb as [t p g b e a | t p g b e a];
      destruct t; cbn in Htag; try discriminate; try done; cbn; cycle 1.
    destruct p;try done; cbn; cycle 1.
    destruct (isO (BPerm rx w dl dro)) eqn:HpO.
    { destruct rx,w; cbn in *; try done.
      rewrite !interp_unfold //=.
    }
    destruct (isO (BPerm rx Ow dl DRO)) eqn:HpO'.
    { iApply (interp_weakening_O_same_bounds with "Hw"); auto.
      - apply DRO_flowsto.
      - by destruct g.
    }
    iApply (interp_weakening_same_bounds_same_loc with "Hw"); eauto; try done; try solve_addr.
    apply DRO_flowsto.
  Qed.

  Lemma lload_word_eq p w :
    lload_word p w =
      if isDRO p
      then if isDL p then lreadonly (ldeeplocal (lborrow w)) else lreadonly w
      else if isDL p then ldeeplocal (lborrow w) else w.
  Proof.
    destruct w as [w π].
    rewrite /lload_word /lreadonly /ldeeplocal /lborrow /lift_word /load_word /=.
    by destruct (isDRO p), (isDL p).
  Qed.

  Lemma interp_load_word W C p w :
    thread_in th C -∗ interp W C w -∗ interp W C (lload_word p w).
  Proof.
    iIntros "#Hth Hinterp".
    rewrite lload_word_eq.
    destruct (isDRO p),(isDL p); auto.
    - iApply interp_readonly_word ; iApply interp_deeplocal_word.
      by iApply (interp_borrow_word with "Hth").
    - by iApply interp_readonly_word.
    - iApply interp_deeplocal_word. by iApply (interp_borrow_word with "Hth").
  Qed.

  (** A load through a permission that is not deep-local needs no thread
      premise. *)
  Lemma interp_load_word_nodl W C p w :
    isDL p = false → interp W C w -∗ interp W C (lload_word p w).
  Proof.
    iIntros (Hdl) "Hinterp".
    rewrite lload_word_eq Hdl.
    destruct (isDRO p); auto.
    by iApply interp_readonly_word.
  Qed.

  Lemma interp_in_mem_load_word W C p w :
    thread_in th C -∗ interp_in_mem RWL W C w -∗ interp_in_mem p W C w.
  Proof.
    change (⊢ thread_in th C -∗ interp W C (lload_word RWL w) -∗
      interp W C (lload_word p w))%I.
    replace (lload_word RWL w) with w by (destruct w; done).
    iIntros "#Hth H". by iApply (interp_load_word with "Hth").
  Qed.



  Lemma interp_in_mem_readonly_word W C w :
    interp_in_mem RWL W C w -∗ interp_in_mem RWL W C (lreadonly w).
  Proof.
    change (⊢ interp W C (lload_word RWL w) -∗
              interp W C (lload_word RWL (lreadonly w)))%I.
    replace (lload_word RWL w) with w by (destruct w; done).
    replace (lload_word RWL (lreadonly w)) with (lreadonly w) by (destruct w; done).
    iIntros "H". by iApply interp_readonly_word.
  Qed.

  Lemma persistent_cond_interp_in_mem : persistent_cond (interp_in_mem RWL).
  Proof. intros WCw; apply _. Qed.

  Lemma zcond_interp_in_mem C : ⊢ zcond (interp_in_mem RWL) C.
  Proof. iIntros "!> %W1 %W2 %z %π _". iApply interp_untagged; done. Qed.

  Lemma wcond_interp_in_mem C : ⊢ wcond (interp_in_mem RWL) C interp.
  Proof. iIntros "!> %W %w H". by iApply interp_to_in_mem. Qed.

  Lemma rcond_interp_in_mem C p : thread_in th C -∗ rcond (interp_in_mem RWL) C p interp.
  Proof. iIntros "#Hth !> %W %w H". by iApply (interp_in_mem_load_word with "Hth"). Qed.

  Lemma rcond_interp_in_mem_nodl C p :
    isDL p = false → ⊢ rcond (interp_in_mem RWL) C p interp.
  Proof.
    iIntros (Hdl) "!> %W %w H".
    rewrite /interp_in_mem_pre.
    iEval (rewrite interp_in_mem_eq) in "H".
    replace (lload_word RWL w) with w by (destruct w; done).
    by iApply interp_load_word_nodl.
  Qed.

  (* Lemmas about interp  *)

  Lemma mono_pub_interp_in_mem (C : CmptName) :
    ⊢ mono_pub C interp_in_memC.
  Proof.
    iIntros (w W0 W1 Hrelated) "!> Hinterp".
    iApply interp_in_mem_monotone; eauto.
  Qed.

  Lemma future_pub_mono_interp_in_mem_z C z :
    ⊢ future_pub_mono C interp_in_memC (WInt z).
  Proof. iIntros "!> %W %W' %Hrelated _". iApply interp_int. Qed.

  (* interp_in_mem_dl *)
  Program Definition interp_in_mem_dl : V :=
    (λne (W : WORLD) (B : leibnizO CmptName) (v : leibnizO LWord)
     , (interp_in_mem RWL W B (ldeeplocal (lborrow v)))%I).
  Solve All Obligations with solve_proper.

  Lemma future_pub_mono_interp_in_mem_dl C w:
    ⊢ future_pub_mono C (safeC interp_in_mem_dl) w.
  Proof.
    iIntros "!>" (W W' Hrelated) "H"; cbn.
    iApply interp_in_mem_monotone; eauto.
  Qed.

  Lemma persistent_cond_interp_in_mem_dl : persistent_cond interp_in_mem_dl.
  Proof. intros W; apply _. Qed.

  Lemma zcond_interp_in_mem_dl C : ⊢ zcond interp_in_mem_dl C.
  Proof. by iModIntro; iIntros (W1 W2 w π) "_"; iApply interp_int. Qed.

  Lemma wcond_interp_in_mem_dl C : thread_in th C -∗ wcond interp_in_mem_dl C interp.
  Proof.
    iIntros "#Hth !> %W %w H". iApply interp_to_in_mem.
    iApply interp_deeplocal_word. by iApply (interp_borrow_word with "Hth").
  Qed.

  Lemma rcond_interp_in_mem_dl C p : isDL p = true -> ⊢ rcond interp_in_mem_dl C p interp.
  Proof.
    iIntros (Hp) "!> %W %w H".
    rewrite /interp_in_mem_pre /= lload_word_eq Hp.
    replace (lload_word RWL (ldeeplocal (lborrow w))) with (ldeeplocal (lborrow w)) by (destruct w; done).
    destruct (isDRO p); last done.
    iPoseProof (interp_in_mem_readonly_word with "H") as "H'".
    rewrite /interp_in_mem /= /interp_in_mem_pre.
    by replace (lload_word RWL (lreadonly (ldeeplocal (lborrow w))))
      with (lreadonly (ldeeplocal (lborrow w))) by (destruct w; done).
  Qed.

  Lemma mono_pub_interp_in_mem_dl C : ⊢ mono_pub C (safeC interp_in_mem_dl).
  Proof. iIntros (w) "!> %W %W' %Hrelated H"; cbn.
    iApply (interp_in_mem_monotone W W' C RWL (ldeeplocal (lborrow w)) with "H"); done. Qed.

  Program Definition interp_in_mem_dro_eq (w : LWord) : V :=
    (λne (W : WORLD) (B : leibnizO CmptName) (v : leibnizO LWord)
     , (⌜ v = w ⌝ ∗ interp_in_mem RWL W B (lreadonly w))%I).
  Solve All Obligations with solve_proper.

  (* Proving the meaning of sealing in the LR sane. The sealed word keeps the
     payload's identifier. Sealing needs no ghost update. *)
  Lemma sealing_preserves_interp W C sb π p g b e a πr :
    permit_seal p = true ->
    withinBounds b e a = true ->
    thread_in th C -∗
    interp W C (WSealable sb @@? π) -∗
    interp W C (SealRange p g b e a @@? πr) -∗
    interp W C (WSealed a sb @@? π).
  Proof.
    iIntros (Hseal Hwb) "#Hth #HVsb #HVsr".
    destruct (get_tag_sealable sb) eqn:Htag.
    2: { iApply interp_untagged. done. }
    rewrite (interp_unfold W C (SealRange _ _ _ _ _ @@? _)).
    iDestruct "HVsr" as "[Hss _]"; rewrite /= Hseal.
    apply seq_between_dist_Some in Hwb.
    iDestruct (big_sepL_elem_of_acc with "Hss") as "[HSa0 _]"; eauto.
    { rewrite list_elem_of_lookup; eauto. }
    iDestruct "HSa0" as "(%κ & %Po & #Hsealpred & #Hok & #Hwcond_Po)".
    iEval (rewrite interp_unfold /= Htag /interp_sb).
    iSplit.
    - iExists κ, Po. iFrame "Hsealpred Hok". iNext.
      iApply ("Hwcond_Po" $! th with "Hth HVsb").
    - rewrite /sealed_payload_ok.
      destruct sb as [t q l b' e' a'|t q l b' e' a']; destruct t;
        cbn in Htag; try discriminate; last done.
      by iDestruct (interp_cap_heap_conditions with "HVsb") as "[$ _]".
  Qed.

  (* Proving the meaning of unsealing in the LR sane. Note the use of the later in the result. *)
  Lemma unsealing_preserves_interp W C sb π p0 g0 b0 e0 a0 π0 o s:
        permit_unseal p0 = true →
        withinBounds b0 e0 o = true →
        thread_in th C -∗
        interp W C (WSealed o sb @@? π) -∗
        interp W C (SealRange p0 g0 b0 e0 a0 @@? π0) -∗
        world_interp_open W C s
        -∗
        ▷ (interp W C (WSealable (unseal_sb g0 sb) @@? π) ∗
           world_interp_open W C s).
  Proof.
    iIntros (Hpseal Hwb) "#Hth #HVsd #HVsr Hworld_interp".
    destruct (get_tag_sealable sb) eqn:Htag.
    2: { iNext. iFrame. iApply interp_untagged. by rewrite /= get_tag_unseal Htag. }
    rewrite
      (interp_unfold W C (SealRange _ _ _ _ _ @@? _))
      (interp_unfold W C (WSealed _ _ @@? _)) /= Htag Hpseal /interp_sb.
    iDestruct "HVsr" as "[_ Hss]".
    iDestruct "HVsd" as "[(%κ1 & %P1 & #Hs1 & _ & #HP1) _]".
    apply seq_between_dist_Some in Hwb.
    iDestruct (big_sepL_delete with "Hss") as "[HSa0 _]"; eauto.
    iDestruct "HSa0" as "(%κ2 & %P2 & #Hs2 & _ & #Hrcond)".
    iDestruct (seal_pred_agree with "Hs1 Hs2") as "[-> #Heq]".
    iNext. iFrame "Hworld_interp".
    iAssert (interp W C (WSealable sb @@? π)) as "#Hpayload".
    { iApply ("Hrcond" $! th with "Hth").
      iRewrite -("Heq" $! (th, W, C, norm κ2 (WSealable sb @@? π))). done. }
    destruct g0.
    - by rewrite unseal_global.
    - rewrite unseal_local.
      iApply (interp_borrow_word W C (WSealable sb @@? π) with "Hth Hpayload").
  Qed.

  (** A narrowed capability with an identifier keeps a heap base. The world
      does not record that objects lie in the heap, so this is a premise:
      trivial when the base is kept, and otherwise obtained from erasure at
      the narrowing step (see [observe_prov_heap]). *)
  Definition subseg_heap_base (π : option AId) (b b' e' : Addr) : Prop :=
    ∀ ι, π = Some ι → b ≠ b' → (b' < e')%a → is_heap_address b' = true.

  Lemma subseg_heap_base_same π b e' : subseg_heap_base π b b e'.
  Proof. by intros ι _ []. Qed.

  Lemma subseg_heap_base_noid b b' e' : subseg_heap_base None b b' e'.
  Proof. by intros ι ?. Qed.

  Lemma heap_cap_ok_subseg p b e b' e' π :
    (b <= b')%a -> (e' <= e)%a ->
    subseg_heap_base π b b' e' ->
    heap_cap_ok p b e π -∗ heap_cap_ok p b' e' π.
  Proof.
    iIntros (Hb He Hgate) "#Hvalid %Hnonempty".
    iSpecialize ("Hvalid" with "[%]"); first solve_addr.
    destruct π as [ι|].
    - iDestruct "Hvalid" as "[%Hconds (%bo & %eo & #Hobj & %Hbo)]".
      destruct Hconds as (Hbheap & Hexec & Hwl).
      iSplit.
      + iPureIntro. split; last done.
        destruct (decide (b = b')) as [<-|Hne]; first done.
        by apply (Hgate ι).
      + iExists bo, eo. iFrame "Hobj". iPureIntro. solve_addr.
    - iDestruct "Hvalid" as %Hvalid. iPureIntro.
      rewrite /disjoint_from_heap elem_of_disjoint in Hvalid |- *.
      intros a Ha Hheap. eapply Hvalid; last exact Hheap.
      apply elem_of_finz_seq_between in Ha.
      apply elem_of_finz_seq_between. solve_addr.
  Qed.

  Lemma interp_weakeningEO_gen W C t p p' g g' b b' e e' a a' π :
    isO p = false →
    isO p' = false →
    (b <= b')%a ->
    (e' <= e)%a ->
    subseg_heap_base π b b' e' ->
    PermFlowsTo p' p ->
    LocalityFlowsTo g' g ->
    □ (⌜g = Global⌝ → ⌜g' = Local⌝ → thread_in th C) -∗
    interp W C (WCap t p g b e a @@? π) -∗
    interp W C (WCap t p' g' b' e' a' @@? π).
  Proof.
    intros HpnotO HpnotO' Hb He Hgate Hp Hl. iIntros "#Hth HA".
    destruct t; last (iApply interp_untagged; done).
    rewrite !interp_unfold !interp1_eq.
    rewrite HpnotO HpnotO'.
    destruct (has_sreg_access p) eqn:HpXSR; auto.
    replace (has_sreg_access p')
      with false by (symmetry; eapply nothas_sreg_access_flowsfrom; eauto).
    iDestruct "HA" as "[A [%Hconditions #Hok] ]".
    destruct Hconditions as [Hpwl_cond Hshadow].
    assert (Hshadow' : disjoint_from_mmio b' e').
    { eapply (disjoint_from_mmio_weaken b e); [solve_addr | solve_addr | exact Hshadow]. }
    iSplitL "A"; cycle 1.
    { iSplit.
      2: { iApply (heap_cap_ok_perm with "[]"); first exact Hp.
           by iApply (heap_cap_ok_subseg with "Hok"). }
      iPureIntro. split; last exact Hshadow'.
      case_eq (isWL p'); intros Hpwl'; auto.
      pose proof (isWL_flowsto p' p Hp Hpwl') as Hpwl.
      rewrite Hpwl in Hpwl_cond.
      destruct g; try congruence.
      destruct g'; simpl in Hl; tauto.
    }

    destruct (decide (b' < e')%a) as [Hbe'|Hbe']; cycle 1.
    { rewrite (finz_seq_between_empty b' e'); auto; solve_addr. }
    rewrite (isWithin_finz_seq_between_decomposition b' e' b e); last solve_addr.
    iEval (rewrite !big_sepL_app) in "A". iDestruct "A" as "[_ [A _] ]".
    iApply (big_sepL_impl with "A").
    iIntros "!>" (k x Hx) "Hw".
    iDestruct "Hw" as (p'' φ Hflp'' Hpersφ) "(Hrel & Hzcond & Hrcond & Hwcond)".
    iExists p'', φ. iFrame "Hzcond".
    iSplit; first (iPureIntro; eapply PermFlowsToTransitive; eauto).
    iSplit; first done.
    iSplitL "Hrel".
    { iApply (region_rel_weakening with "Hrel"); eauto.
      intros Hpwl. by rewrite Hpwl in Hpwl_cond. }
    iSplitL "Hrcond".
    { destruct (readAllowed p''); last done.
      iApply (rcond_sel_weakening with "Hth Hrcond"); done. }
    destruct (writeAllowed p''); last done.
    iApply (wcond_sel_weakening with "Hwcond"); done.
  Qed.

  Lemma interp_weakeningEO W C t p p' g g' b b' e e' a a' π :
    isO p = false →
    isO p' = false →
    (b <= b')%a ->
    (e' <= e)%a ->
    subseg_heap_base π b b' e' ->
    PermFlowsTo p' p ->
    LocalityFlowsTo g' g ->
    thread_in th C -∗
    interp W C (WCap t p g b e a @@? π) -∗
    interp W C (WCap t p' g' b' e' a' @@? π).
  Proof.
    intros HpnotO HpnotO' Hb He Hgate Hp Hl. iIntros "#Hth HA".
    iApply (interp_weakeningEO_gen with "[] HA"); [done..|].
    by iIntros "!> _ _".
  Qed.

  Lemma interp_weakening_word_load (W : WORLD) (C : CmptName) (p p' : Perm) v :
    PermFlowsTo p p'
    -> thread_in th C
    -∗ interp W C (lload_word p' v)
    -∗ interp W C (lload_word p v).
  Proof.
    iIntros (Hfl) "#Hth #Hinterp".
    destruct v as [v π].
    destruct (get_tag v) eqn:Htag.
    2: { iApply interp_untagged. by rewrite /= get_tag_load_word Htag. }
    iEval (rewrite /lload_word /lift_word /=) in "Hinterp".
    rewrite /lload_word /lift_word /=.
    destruct v.
    - rewrite !load_word_int; done.
    - destruct sb as [t p0 g b e a | t p0 g b e a]; destruct t; cbn in Htag; try discriminate; cycle 1.
      { rewrite !load_word_sealrange; cbn.
        by rewrite !interp_unfold /=.
      }
      destruct p0 as [ rx0 w0 dl0 dro0 ].

      rewrite !load_word_cap.
      destruct (isO (load_word_perm p (BPerm rx0 w0 dl0 dro0))) eqn:HnO.
      { iApply (interp_weakening_O_same_bounds with "Hinterp"); auto.
        - apply load_word_perm_load_flows; auto.
        - destruct (isDL p) eqn:Hdl; auto.
          eapply notisDL_flowsfrom in Hfl; eauto.
          by rewrite Hfl.
      }
      iApply (interp_weakening_same_bounds with "Hth Hinterp"); auto; try solve_addr.
      + eapply notisO_flowsfrom ; eauto.
        apply load_word_perm_load_flows;auto.
      + apply load_word_perm_load_flows;auto.
      + destruct (isDL p) eqn:Hdl; auto.
        eapply notisDL_flowsfrom in Hfl; eauto.
        by rewrite Hfl.
    - rewrite !load_word_sentry.
      destruct (isDL p') eqn:Hdl
      ; [ eapply isDL_flowsto in Hfl; eauto ; rewrite Hfl |]
      ; auto.
      destruct (isDL p); auto.
        by iApply interp_weakening_from_sentry.
    - rewrite !load_word_sealed.
      destruct (isDL p') eqn:Hdl'; cbn.
      + pose proof (isDL_flowsto p p' Hfl Hdl') as Hdl; rewrite Hdl.
        done.
      + iDestruct (interp_borrowed_sealed with "Hinterp") as "Hinterp'".
        destruct (isDL p); auto.
  Qed.


End fundamental.

Section region_alloc_cmpt.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    {cthreads : CmptThreads}
    `{MP: MachineParameters}
  .
  #[local] Notation V := (interpO Σ).

  (** The read condition of the PCC range, at every thread, through a
      permission that is not deep-local. *)
  Lemma rcond_g_interp_cmpt_threads C p :
    isDL p = false → ⊢ rcond_g interp_cmpt_threads C p (λ t, interp (th := t)).
  Proof.
    intros Hdl. iIntros "!>" (t') "#Ht'". iIntros "!>" (W w) "Hw".
    iEval (rewrite /interp_cmpt_threads /=) in "Hw". iDestruct "Hw" as "#Hw".
    rewrite /interp_in_mem_pre.
    iApply (interp_load_word_nodl (th := t')); first done.
    iApply ("Hw" $! t' with "Ht'").
  Qed.

  Lemma rcond_g_interp_nonlocal C p :
    isDL p = false → ⊢ rcond_g interp_nonlocal C p (λ t, interp (th := t)).
  Proof.
    intros Hdl. iIntros "!>" (t') "_". iIntros "!>" (W w) "Hw".
    iEval (rewrite /interp_nonlocal /=) in "Hw". iDestruct "Hw" as "[%Hloc #Hw]".
    rewrite /interp_in_mem_pre.
    iApply (interp_load_word_nodl (th := t')); first done.
    by iApply (interp_global_thread_world_free th t' W W C w Hloc).
  Qed.

End region_alloc_cmpt.
