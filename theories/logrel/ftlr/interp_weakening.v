From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Import memory_region monotone.
From griotte Require Export logrel ftlr_base.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {CL : CritLink Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation E := (CSTK -n> list WORLD -n> WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).
  #[local] Notation V := (interpO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).
  Lemma enter_cond_weakening W C p b e a π :
    (□ enter_cond W C p Global b e a π interp) -∗
     □ enter_cond W C p Local b e a π interp.
  Proof.
    iIntros "#Hinterp".
    rewrite /enter_cond /interp_expr /=.
    iIntros (W' Hrelated) "!> %g' %Hflows".
    assert (LocalityFlowsTo g' Global) as Hflow' by (destruct g'; auto).
    iApply ("Hinterp" $! W' with "[//] [//]").
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
    destruct g; auto.
    iApply enter_cond_weakening;auto.
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

  Lemma interp_weakening_same_bounds W C t p p' g g' b e a a' π :
    isO p = false →
    isO p' = false →
    PermFlowsTo p' p ->
    LocalityFlowsTo g' g ->
    interp W C (WCap t p g b e a @@? π) -∗
    interp W C (WCap t p' g' b e a' @@? π).
  Proof.
    intros HpnotO HpnotO' Hp Hl. iIntros "HA".
    destruct t; last (iApply interp_untagged; done).
    rewrite !interp_unfold !interp1_eq.
    rewrite HpnotO HpnotO'.
    destruct (has_sreg_access p) eqn:HpXSR; auto.
    replace (has_sreg_access p')
      with false by (symmetry; eapply nothas_sreg_access_flowsfrom; eauto).
    iDestruct "HA" as "[#A [%Hconditions #Hheap]]".
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
    iExists p'', φ. iFrame "Hzcond Hrcond Hwcond".
    iSplit; first (iPureIntro; eapply PermFlowsToTransitive; eauto).
    iSplit; first done.
    iApply (region_rel_weakening with "Hrel"); eauto.
    intros Hpwl. by rewrite Hpwl in Hpwl_cond.
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
    iApply interp_weakening_same_bounds; eauto; try solve_addr; try done.
  Qed.

  Lemma interp_lea W C t p g b e a a' π :
    isO p = false ->
    interp W C (WCap t p g b e a @@? π) -∗
    interp W C (WCap t p g b e a' @@? π).
  Proof.
    iIntros (Hisno) "#Hi".
    iApply interp_weakening_same_bounds; eauto; try solve_addr; try done.
  Qed.

  Lemma safe_to_unseal_weakening W C b e b' e':
    (b <= b')%ot ->
    (e' <= e)%ot ->
    safe_to_unseal W C interp b e -∗
    safe_to_unseal W C interp b' e'.
  Proof.
    iIntros (Hb He) "HA".
    rewrite /safe_to_unseal.
    destruct (decide (b' <= e')%ot).
    - rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr].
      rewrite !big_sepL_app; iDestruct "HA" as "[_ [$ _]]".
    - iClear "HA"; rewrite !finz_seq_between_empty;[done |solve_addr].
  Qed.

  Lemma safe_to_seal_weakening W C b e b' e':
    (b <= b')%ot ->
    (e' <= e)%ot ->
    safe_to_seal W C interp b e -∗
    safe_to_seal W C interp b' e'.
  Proof.
    iIntros (Hb He) "HA".
    rewrite /safe_to_seal.
    destruct (decide (b' <= e')%ot).
    - rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr].
      rewrite !big_sepL_app; iDestruct "HA" as "[_ [$ _]]".
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
    all: destruct κ; cbn; [done|by iDestruct "Hok" as "[_ []]"].
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
    iApply interp_weakening_same_bounds; eauto; try done; try solve_addr.
    apply DL_flowsto.
  Qed.

  Lemma interp_borrow_word W C w : interp W C w ⊢ interp W C (lborrow w).
  Proof.
    iIntros "Hw".
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
        iApply interp_weakening_same_bounds; eauto; try done; try solve_addr.
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
    iApply (interp_weakening_same_bounds with "Hw"); eauto; try done; try solve_addr.
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

  Lemma interp_load_word W C p w : interp W C w ⊢ interp W C (lload_word p w).
  Proof.
    iIntros "Hinterp".
    rewrite lload_word_eq.
    destruct (isDRO p),(isDL p); auto.
    - by iApply interp_readonly_word ; iApply interp_deeplocal_word ; iApply interp_borrow_word.
    - by iApply interp_readonly_word.
    - by iApply interp_deeplocal_word ; iApply interp_borrow_word.
  Qed.

  Lemma interp_in_mem_load_word W C p w :
    interp_in_mem RWL W C w -∗ interp_in_mem p W C w.
  Proof.
    change (⊢ interp W C (lload_word RWL w) -∗
      interp W C (lload_word p w))%I.
    replace (lload_word RWL w) with w by (destruct w; done).
    iIntros "H". by iApply interp_load_word.
  Qed.

  Lemma interp_in_mem_unseal_payload W C ot sb π :
    interp W C (WSealed ot sb @@? π) -∗
    interp_in_mem RWL W C (WSealable sb @@? π) -∗ interp W C (WSealable sb @@? π).
  Proof.
    iIntros "#Hsealed Hmem".
    iEval (rewrite interp_in_mem_eq) in "Hmem".
    by replace (lload_word RWL (WSealable sb @@? π)) with (WSealable sb @@? π)
      by (by destruct sb).
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

  Lemma rcond_interp_in_mem C p : ⊢ rcond (interp_in_mem RWL) C p interp.
  Proof. iIntros "!> %W %w H". by iApply interp_in_mem_load_word. Qed.

  (* Lemmas about interp  *)

  Lemma mono_pub_interp_in_mem (C : CmptName) :
    ⊢ mono_pub C interp_in_memC.
  Proof.
    iIntros (w W0 W1 Hrelated) "!> Hinterp".
    iApply interp_in_mem_monotone; eauto.
  Qed.

  Lemma future_priv_mono_interp_in_mem_z C z :
    ⊢ future_priv_mono C interp_in_memC (WInt z).
  Proof. iIntros "!> %W %W' %Hrelated _". iApply interp_int. Qed.

  Lemma future_pub_mono_interp_in_mem_z C z :
    ⊢ future_pub_mono C interp_in_memC (WInt z).
  Proof. iIntros "!> %W %W' %Hrelated _". iApply interp_int. Qed.

  Lemma future_priv_mono_interp_in_mem_global (C : CmptName) (t : bool) (p : Perm) (b e a : Addr) :
    ⊢ future_priv_mono C interp_in_memC (WCap t p Global b e a).
  Proof.
    iModIntro.
    iIntros (W W') "%Hrelated Hinterp".
    rewrite /=.
    iApply (interp_in_mem_monotone_nl W W' C RWL (WCap t p Global b e a) with "Hinterp"); [exact Hrelated|].
    by destruct t.
  Qed.

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

  Lemma wcond_interp_in_mem_dl C : ⊢ wcond interp_in_mem_dl C interp.
  Proof. iIntros "!> %W %w H". iApply interp_to_in_mem. by iApply interp_deeplocal_word; iApply interp_borrow_word. Qed.

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
    interp W C (WSealable sb @@? π) -∗
    interp W C (SealRange p g b e a @@? πr) -∗
    interp W C (WSealed a sb @@? π).
  Proof.
    iIntros (Hseal Hwb) "#HVsb #HVsr".
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
    - iExists κ, Po. iFrame "Hsealpred Hok". iNext. by iApply "Hwcond_Po".
    - rewrite /sealed_payload_ok.
      destruct sb as [t q l b' e' a'|t q l b' e' a']; destruct t;
        cbn in Htag; try discriminate; last done.
      by iDestruct (interp_cap_heap_conditions with "HVsb") as "[$ _]".
  Qed.

  (* Proving the meaning of unsealing in the LR sane. Note the use of the later in the result. *)
  Lemma unsealing_preserves_interp W C sb π p0 g0 b0 e0 a0 π0 o s:
        permit_unseal p0 = true →
        withinBounds b0 e0 o = true →
        interp W C (WSealed o sb @@? π) -∗
        interp W C (SealRange p0 g0 b0 e0 a0 @@? π0) -∗
        world_interp_open W C s
        -∗
        ▷ (interp W C (WSealable (unseal_sb g0 sb) @@? π) ∗
           world_interp_open W C s).
  Proof.
    iIntros (Hpseal Hwb) "#HVsd #HVsr Hworld_interp".
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
    { iApply "Hrcond". iRewrite -("Heq" $! (th, W, C, norm κ2 (WSealable sb @@? π))). done. }
    destruct g0.
    - by rewrite unseal_global.
    - rewrite unseal_local.
      iApply (interp_borrow_word W C (WSealable sb @@? π) with "Hpayload").
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

  Lemma interp_weakeningEO W C t p p' g g' b b' e e' a a' π :
    isO p = false →
    isO p' = false →
    (b <= b')%a ->
    (e' <= e)%a ->
    subseg_heap_base π b b' e' ->
    PermFlowsTo p' p ->
    LocalityFlowsTo g' g ->
    interp W C (WCap t p g b e a @@? π) -∗
    interp W C (WCap t p' g' b' e' a' @@? π).
  Proof.
    intros HpnotO HpnotO' Hb He Hgate Hp Hl. iIntros "HA".
    destruct t; last (iApply interp_untagged; done).
    rewrite !interp_unfold !interp1_eq.
    rewrite HpnotO HpnotO'.
    destruct (has_sreg_access p) eqn:HpXSR; auto.
    replace (has_sreg_access p')
      with false by (symmetry; eapply nothas_sreg_access_flowsfrom; eauto).
    iDestruct "HA" as "[A [%Hconditions #Hok]]".
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
    iEval (rewrite !big_sepL_app) in "A". iDestruct "A" as "[_ [A _]]".
    iApply (big_sepL_mono with "A").
    iIntros (k x Hx) "Hw".
    iDestruct "Hw" as (p'' φ Hflp'' Hpersφ) "(Hrel & Hzcond & Hrcond & Hwcond)".
    iExists p'', φ. iFrame "Hzcond Hrcond Hwcond".
    iSplit; first (iPureIntro; eapply PermFlowsToTransitive; eauto).
    iSplit; first done.
    iApply (region_rel_weakening with "Hrel"); eauto.
    intros Hpwl. by rewrite Hpwl in Hpwl_cond.
  Qed.

  Lemma interp_weakening W C t p p' g g' b b' e e' a a' π :
    (b <= b')%a ->
    (e' <= e)%a ->
    subseg_heap_base π b b' e' ->
    PermFlowsTo p' p ->
    LocalityFlowsTo g' g ->
    ftlr_IH -∗
    interp W C (WCap t p g b e a @@? π) -∗
    interp W C (WCap t p' g' b' e' a' @@? π).
  Proof.
    intros Hb He Hgate Hp Hl. iIntros "#IH HA".
    destruct t; last (iApply interp_untagged; done).
    destruct (isO p') eqn:HpO'.
    { iDestruct (interp_cap_heap_conditions with "HA") as "[#Hvalid #Hcoverage]".
      iEval (rewrite interp_unfold interp1_eq HpO').
      iSplit.
      - iApply (heap_cap_ok_perm with "[]"); first exact Hp.
        by iApply (heap_cap_ok_subseg with "Hvalid").
      - destruct (decide (b' < e')%a) as [Hbe'|Hbe']; cycle 1.
        { rewrite (finz_seq_between_empty b' e'); auto; solve_addr. }
        rewrite (isWithin_finz_seq_between_decomposition b' e' b e); last solve_addr.
        iEval (rewrite !big_sepL_app) in "Hcoverage". iDestruct "Hcoverage" as "[_ [Hcov _]]".
        iApply (big_sepL_impl with "Hcov"). iIntros "!>" (k x Hx) "Hx %Hheap".
        iApply (heap_cap_O_key_weakening with "(Hx [//])"); done. }
    destruct (isO p) eqn:HpO.
    { eapply notisO_flowsfrom in Hp ; eauto; congruence. }
    { iApply (interp_weakeningEO _ _ true p p' g g'); eauto. }
  Qed.

  Lemma interp_weakeningSentry W C sk t p g g' b b' e e' a a' :
      not_heap_range b' e' ->
      isO p = false ->
      (b <= b')%a ->
      (e' <= e)%a ->
      LocalityFlowsTo g' g ->
      ftlr_IH -∗
      interp W C (WCap t p g b e a) -∗
      interp W C (WSentry sk t p g' b' e' a').
  Proof.
    intros Hsentry HpnotO Hb He Hl.
    iIntros "#IH #HA".
    destruct t; last (iApply interp_untagged; done).
    iEval (rewrite interp_unfold /=).
    iEval (rewrite interp_unfold interp1_eq) in "HA".
    rewrite HpnotO.
    destruct (has_sreg_access p) eqn:HpXSR; auto.
    iDestruct "HA" as "[A [%Hconditions #Hok]]".
    destruct Hconditions as [Hpwl_cond Hshadow].
    assert (Hregions' : disjoint_from_mmio b' e' ∧ disjoint_from_heap b' e').
    { split; last exact (proj2 Hsentry).
      eapply (disjoint_from_mmio_weaken b e); [solve_addr | solve_addr | exact Hshadow]. }
    iSplit; first done.
    iModIntro.
    rewrite /enter_cond /interp_expr /=.
    iIntros (W') "#Hfuture %g'' %Hflows !>".
    iApply "IH".
    iEval (rewrite interp_unfold interp1_eq HpnotO HpXSR).
    iSplitR; cycle 1.
    {
      iSplit; last (iApply heap_cap_ok_disjoint; exact (proj2 Hregions')).
      iPureIntro. split; last exact (proj1 Hregions').
      destruct (isWL p) eqn:Hpwl; auto.
      simplify_eq.
      destruct g',g''; inversion Hl; inversion Hflows; auto.
    }
    destruct (decide (b' < e'))%a; cycle 1.
    { rewrite (finz_seq_between_empty b' e'); auto; solve_addr. }
    rewrite (isWithin_finz_seq_between_decomposition b' e' b e); try solve_addr.
    rewrite !big_sepL_app. iDestruct "A" as "[_ [A2 _]]".
    iClear "IH".
    iApply (big_sepL_impl with "A2").
    iModIntro; iIntros (k x Hx) "Hw".
    iDestruct "Hw" as (p'' φ Hflp'' Hpersφ) "(#Hrel & #Hzcond & #Hrcond & #Hwcond)".
    iExists p'',φ.
    iFrame "Hzcond Hrcond Hwcond".
    iSplitR; first done. iSplitR; first done.
    assert (isWL p = true → g = Local) as Hwl by (intros Hpwl; by rewrite Hpwl in Hpwl_cond).
    (* The region at the future world, through the sentry's locality. *)
    iAssert (region_rel W' C (addr_key None x) p'' φ p g')%I as "#Hrel'".
    { destruct g'.
      - destruct g; cbn in Hl; last done.
        destruct (isWL p) eqn:Hpwl; [by specialize (Hwl eq_refl)|].
        by rewrite /region_rel Hpwl.
      - iDestruct "Hfuture" as "%Hfuture".
        iApply (region_rel_mono_pub with "[Hrel]"); first done.
        iApply (region_rel_weakening with "Hrel"); [apply PermFlowsToReflexive|done|done]. }
    iApply (region_rel_weakening with "Hrel'"); [apply PermFlowsToReflexive|done|].
    intros Hpwl. specialize (Hwl Hpwl). subst g.
    destruct g'; cbn in Hl; done.
  Qed.


  Lemma interp_weakening_word_load (W : WORLD) (C : CmptName) (p p' : Perm) v :
    PermFlowsTo p p'
    -> interp W C (lload_word p' v)
    -∗ interp W C (lload_word p v).
  Proof.
    iIntros (Hfl) "#Hinterp".
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
      iApply (interp_weakening_same_bounds with "Hinterp"); auto; try solve_addr.
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
