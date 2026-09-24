From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From iris.base_logic Require Export invariants na_invariants saved_prop.
From griotte Require Export logrel region_invariants.
Import uPred.

Section monotone.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation K := (CSTK -n> list WORLD -n> leibnizO (list CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (V).

  Lemma region_state_pub_perm W W' a :
    related_sts_pub_world W W'
    → (std W) !! a = Some Permanent
    -> (std W') !! a = Some Permanent.
  Proof.
    intros Hrelated Hstate.
    destruct Hrelated as [ [ Hdom_sta Hrelated] _]. simpl in *.
    assert (is_Some ((std W') !! a)) as [y Hy].
    { rewrite -elem_of_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. rewrite elem_of_dom;eauto. }
    specialize (Hrelated a Permanent y Hstate Hy).
    apply std_rel_pub_rtc_Permanent in Hrelated; subst; auto.
  Qed.

  Lemma region_state_pub_temp W W' a :
    related_sts_pub_world W W'
    → (std W) !! a = Some Temporary
    -> (std W') !! a = Some Temporary.
  Proof.
    intros Hrelated Hstate.
    destruct Hrelated as [ [Hdom_sta Hrelated ] _]. simpl in *.
    assert (is_Some ((std W') !! a)) as [y Hy].
    { rewrite -elem_of_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. rewrite elem_of_dom;eauto. }
    specialize (Hrelated _ Temporary y Hstate Hy).
    apply std_rel_pub_rtc_Temporary in Hrelated; subst; auto.
  Qed.

  Lemma region_state_priv_perm W W' a :
    related_sts_priv_world W W'
    → (std W) !! a = Some Permanent
    -> (std W') !! a = Some Permanent.
  Proof.
    intros Hrelated Hstate.
    destruct Hrelated as [ [Hdom_sta Hrelated ] _]. simpl in *.
    assert (is_Some ((std W') !! a)) as [y Hy].
{ rewrite -elem_of_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. rewrite elem_of_dom;eauto. }
    specialize (Hrelated a Permanent y Hstate Hy).
    eapply std_rel_rtc_Permanent in Hrelated;subst;auto.
  Qed.

  Lemma region_state_nwl_monotone W W' a l :
    related_sts_pub_world W W' →
    region_state_nwl W a l -> region_state_nwl W' a l.
  Proof.
    rewrite /region_state_nwl.
    intros  Hrelated Hstate; simplify_eq.
    destruct l.
    - eapply region_state_pub_perm; eauto.
    - destruct Hstate as [Hstate|Hstate].
      + eapply region_state_pub_perm in Hstate; eauto.
      + eapply region_state_pub_temp in Hstate; eauto.
  Qed.

  Lemma region_state_nwl_monotone_nl W W' a :
    related_sts_priv_world W W' →
    region_state_nwl W a Global -> region_state_nwl W' a Global.
  Proof.
    rewrite /region_state_nwl.
    intros Hrelated Hstate; simplify_eq.
    eapply region_state_priv_perm;eauto.
  Qed.

  Lemma region_state_pwl_monotone W W' a :
    related_sts_pub_world W W' →
    region_state_pwl W a -> region_state_pwl W' a.
  Proof.
    rewrite /region_state_pwl /region_state_nwl.
    intros Hrelated Hstate; simplify_eq.
    eapply region_state_pub_temp in Hstate; eauto.
  Qed.

  Lemma region_state_nwl_future W W' l l' p a:
    LocalityFlowsTo l' l ->
    (if isWL p then l = Local else True) ->
    (@future_world Σ l' W W') -∗
    ⌜if isWL p then region_state_pwl W a else region_state_nwl W a l⌝ -∗
    ⌜region_state_nwl W' a l'⌝.
  Proof.
    intros Hlflows Hloc. iIntros "Hfuture %".
    rewrite /future_world.
    destruct l'; simpl; iDestruct "Hfuture" as %Hf; iPureIntro.
    - assert (l = Global) as -> by (destruct l; simpl in Hlflows; tauto).
      destruct (isWL p) eqn:HpwlU; try congruence.
      eapply region_state_nwl_monotone_nl; last eauto; eauto.
    - destruct (isWL p).
      + subst l.
        rewrite /region_state_nwl.
        right; eapply region_state_pub_temp; eauto.
      + generalize (region_state_nwl_monotone _ _ _ _ Hf H).
        destruct l; auto.
  Qed.

  Lemma region_state_future W W' l l' p p' a:
    PermFlowsTo p' p ->
    LocalityFlowsTo l' l ->
    (if isWL p then l = Local else True) ->
    (@future_world Σ l' W W') -∗
    ⌜if isWL p then region_state_pwl W a else region_state_nwl W a l⌝ -∗
    ⌜if isWL p' then region_state_pwl W' a else region_state_nwl W' a l'⌝.
  Proof.
    intros Hpflows Hlflows Hloc. iIntros "Hfuture %Hstate".
    case_eq (isWL p'); intros Hpwlp'.
    - assert (isWL p = true) as Hpwl.
      { destruct_perm p; destruct_perm p'; simpl in Hpwlp'; try congruence; simpl in Hpflows; try tauto. }
      rewrite Hpwl in Hstate, Hloc; subst l.
      destruct l'; simpl in Hlflows; try tauto.
      rewrite /future_world.
      simpl; iDestruct "Hfuture" as "%"; iPureIntro.
      eapply region_state_pwl_monotone; last eauto; eauto.
    - iApply (region_state_nwl_future with "Hfuture"); eauto.
  Qed.

  Lemma region_state_Revoked_monotone (W W' : WORLD) (a : Addr) :
    related_sts_pub_world W W' →
    (std W) !! a = Some Revoked ->
    (std W') !! a = Some Revoked ∨
    (std W') !! a = Some Temporary ∨
    (std W') !! a = Some Permanent.
  Proof.
    rewrite /region_state_pwl.
    intros Hrelated Hstate.
    destruct Hrelated as [ [Hdom_sta Hrelated ] _]. simpl in *.
    assert (is_Some (std W' !! a)) as [y Hy].
    { rewrite -elem_of_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. rewrite elem_of_dom ;eauto. }
    specialize (Hrelated _ Revoked y Hstate Hy).
    apply std_rel_pub_rtc_Revoked in Hrelated; auto.
    destruct Hrelated as [Hperm | [Hmono | Hrev] ]; subst; auto.
  Qed.

  Lemma monoReq_mono_pub_nwl W W' C (P : V) a p g:
    related_sts_pub_world W W'
    -> region_state_nwl W a g
    -> monoReq W C a p P
    -∗ monoReq W' C a p P.
  Proof.
    intros Hrelated Hstate; simplify_eq.
    iIntros "HmonoW"; rewrite /monoReq.
    destruct g.
    - pose proof (region_state_pub_perm _ _ _ Hrelated Hstate) as Hnext_state.
      by rewrite Hstate Hnext_state.
    - destruct Hstate as [Hstate|Hstate].
      + pose proof (region_state_pub_perm _ _ _ Hrelated Hstate) as Hnext_state.
        by rewrite Hstate Hnext_state.
      + pose proof (region_state_pub_temp _ _ _ Hrelated Hstate) as Hnext_state.
        by rewrite Hstate Hnext_state.
  Qed.

  Lemma monoReq_mono_pub_pwl W W' C (P : V) a p:
    related_sts_pub_world W W'
    -> region_state_pwl W a
    -> monoReq W C a p P
    -∗ monoReq W' C a p P.
  Proof.
    intros Hrelated Hstate; simplify_eq.
    iIntros "HmonoW"; rewrite /monoReq.
    pose proof (region_state_pub_temp _ _ _ Hrelated Hstate) as Hnext_state.
    by rewrite Hstate Hnext_state.
  Qed.

  Lemma monoReq_mono_priv_nwl W W' C (P : V) a p:
    related_sts_priv_world W W'
    -> region_state_nwl W a Global
    -> monoReq W C a p P
    -∗ monoReq W' C a p P.
  Proof.
    intros Hrelated Hstate; simplify_eq.
    iIntros "HmonoW"; rewrite /monoReq.
    pose proof (region_state_priv_perm _ _ _ Hrelated Hstate) as Hnext_state.
    by rewrite Hstate Hnext_state.
  Qed.

  Lemma monoReq_nwl_future W W' C l l' p p' a P:
    LocalityFlowsTo l' l
    -> PermFlowsTo p p'
    -> (if isWL p then l = Local else True)
    -> (@future_world Σ l' W W')
    -∗ ⌜if isWL p then region_state_pwl W a else region_state_nwl W a l⌝
    -∗ monoReq W C a p' P
    -∗ monoReq W' C a p' P.
  Proof.
    intros Hlflows Hflp Hloc. iIntros "Hfuture %Hstate HmonoR".
    rewrite /future_world.
    destruct l'; simpl
    ; iDestruct "Hfuture" as %Hrelated
    ; destruct (isWL p) eqn:Hpwl
    ; simplify_map_eq
    ; try done.
    - destruct l ; try done.
      iDestruct (monoReq_mono_priv_nwl with "HmonoR") as "HmonoR'"; eauto.
    - iDestruct (monoReq_mono_pub_pwl with "HmonoR") as "HmonoR'"; eauto.
    - iDestruct (monoReq_mono_pub_nwl with "HmonoR") as "HmonoR'"; eauto.
  Qed.

  Lemma filter_heap_quarantined_future W W' w b base obj :
    heap_wf (heap_std W') ->
    related_sts_heap_std (heap_std W) (heap_std W') ->
    heap_authority_base w = Some b ->
    heap_lookup_addr (heap_std W) b = Some (base,obj) ->
    alloc_object_status obj = AllocObjectQuarantined ->
    filter_heap W' w = clear_tag w.
  Proof.
    intros Hwf Hfuture Hb Hlookup Hstatus.
    destruct (heap_lookup_addr_future _ _ _ _ _ Hwf Hfuture Hlookup)
      as (obj' & Hlookup' & _ & _ & Hstatus').
    eapply filter_heap_quarantined; eauto.
  Qed.

  Lemma filter_heap_future W W' w :
    heap_wf (heap_std W') ->
    related_sts_heap_std (heap_std W) (heap_std W') ->
    filter_heap W' (filter_heap W w) = filter_heap W' w.
  Proof.
    intros Hwf Hfuture.
    destruct (heap_authority_base w) as [b|] eqn:Hb.
    2: { by rewrite (filter_heap_nonheap W w Hb). }
    destruct (heap_lookup_addr (heap_std W) b) as [ [base obj] | ] eqn:Hlookup.
    2: { by rewrite /filter_heap Hb Hlookup Hb. }
    destruct (alloc_object_status obj) eqn:Hstatus.
    - by rewrite (filter_heap_live W w b base obj Hb Hlookup Hstatus).
    - rewrite (filter_heap_quarantined W w b base obj Hb Hlookup Hstatus).
      rewrite filter_heap_untagged; last apply get_tag_clear_tag.
      symmetry. eapply filter_heap_quarantined_future; eauto.
  Qed.

  Lemma heap_cap_live_future_retained W W' w p b e :
    heap_wf (heap_std W') ->
    related_sts_heap_std (heap_std W) (heap_std W') ->
    (is_heap_address b = true -> heap_authority_base w = Some b) ->
    get_tag w = true -> filter_heap W' w = w ->
    heap_cap_live W p b e -> heap_cap_live W' p b e.
  Proof.
    intros Hwf Hfuture Hb Htag Hfilter.
    rewrite /heap_cap_live.
    destruct (is_heap_address b) eqn:Hheap; last done.
    destruct (heap_lookup_addr (heap_std W) b) as [ [base obj] | ] eqn:Hlookup;
      last done.
    destruct (heap_lookup_addr_future _ _ _ _ _ Hwf Hfuture Hlookup)
      as (obj' & Hlookup' & _ & Hend & Hstatus).
    rewrite Hlookup'.
    destruct (alloc_object_status obj); last done.
    destruct (alloc_object_status obj') eqn:Hstatus'; first by rewrite -Hend.
    have Hclear := filter_heap_quarantined W' w b base obj' (Hb eq_refl) Hlookup' Hstatus'.
    have := get_tag_clear_tag w. rewrite -Hclear Hfilter Htag. discriminate.
  Qed.

  Lemma heap_cap_valid_future_retained W W' w p b e :
    heap_wf (heap_std W') ->
    related_sts_heap_std (heap_std W) (heap_std W') ->
    ((b < e)%a -> is_heap_address b = true -> heap_authority_base w = Some b) ->
    get_tag w = true -> filter_heap W' w = w ->
    heap_cap_valid W p b e -> heap_cap_valid W' p b e.
  Proof.
    intros Hwf Hfuture Hb Htag Hfilter Hvalid Hnonempty.
    eapply heap_cap_live_future_retained; eauto.
  Qed.

  Lemma interp_monotone_sd_same_heap W W' C ot sb :
    heap_std W = heap_std W' ->
    ⌜related_sts_priv_world W W'⌝
    -∗ interp W C (WSealed ot sb) -∗ interp W' C (WSealed ot sb).
  Proof.
    iIntros (Hheap Hrelated) "#Hinterp".
    destruct sb as [t p g b e a | t p g b e a]; destruct t;
      rewrite !fixpoint_interp1_eq /= /interp_sb /heap_cap_valid /heap_cap_live; try done.
    by rewrite -Hheap.
  Qed.

  Lemma interp_monotone_sentry W W' C t p g b e a :
    ⌜related_sts_pub_world W W'⌝
    -∗ interp W C (WSentry t p g b e a) -∗ interp W' C (WSentry t p g b e a).
  Proof.
    iIntros (Hrelated) "#Hw".
    destruct t; last (iApply interp_untagged; done).
    rewrite !fixpoint_interp1_eq /=.
    iDestruct "Hw" as "[$ Hw]".
    iModIntro. iIntros (W'').
    destruct g.
    + iIntros "#Hrelated'".
      rewrite /future_world.
      iDestruct "Hrelated'" as "%Hrelated'".
      iAssert (future_world Global W W'')%I as "Hrelated".
      { rewrite /future_world.
        iPureIntro. apply related_sts_pub_priv_trans_world with W'; auto. }
      iSpecialize ("Hw" $! W'' with "Hrelated").
      iApply "Hw".
    + iIntros "#Hrelated'".
      rewrite /future_world.
      iDestruct "Hrelated'" as "%Hrelated'".
      iAssert (future_world Local W W'')%I as "Hrelated".
      { rewrite /future_world.
        iPureIntro. apply related_sts_pub_trans_world with W'; auto. }
      iSpecialize ("Hw" $! W'' with "Hrelated").
      iApply "Hw".
  Qed.

  Lemma interp_addr_mono_pub
      (W W' : WORLD) (C : CmptName) (p : Perm) (g : Locality) (a : Addr) :
    related_sts_pub_world W W' ->
    (∃ (p' : Perm) (P : V),
        ⌜PermFlowsTo p p'⌝ ∗ ⌜persistent_cond P⌝ ∗
        rel C a p' (safeC P) ∗ ▷ zcond P C ∗
        (if readAllowed p' then ▷ rcond P C p' interp else True) ∗
        (if writeAllowed p' then ▷ wcond P C interp else True) ∗
        monoReq W C a p' P ∗
        ⌜if isWL p then region_state_pwl W a else region_state_nwl W a g⌝)
    -∗
    (∃ (p' : Perm) (P : V),
        ⌜PermFlowsTo p p'⌝ ∗ ⌜persistent_cond P⌝ ∗
        rel C a p' (safeC P) ∗ ▷ zcond P C ∗
        (if readAllowed p' then ▷ rcond P C p' interp else True) ∗
        (if writeAllowed p' then ▷ wcond P C interp else True) ∗
        monoReq W' C a p' P ∗
        ⌜if isWL p then region_state_pwl W' a else region_state_nwl W' a g⌝).
  Proof.
    iIntros (Hrelated) "Hw".
    iDestruct "Hw" as (p' P Hpfl' Hpers)
      "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate)".
    destruct (isWL p) eqn:Hwl.
    - iPoseProof (monoReq_mono_pub_pwl with "HmonoR") as "HmonoR'"; eauto.
      pose proof (region_state_pwl_monotone W W' a Hrelated Hstate) as Hstate'.
      iExists p', P.
      iSplit; first done. iSplit; first done.
      iSplitL "Hrel"; first iExact "Hrel".
      iSplitL "Hzcond"; first iExact "Hzcond".
      iSplitL "Hrcond"; first iExact "Hrcond".
      iSplitL "Hwcond"; first iExact "Hwcond".
      iSplitL "HmonoR'"; first iExact "HmonoR'".
      iPureIntro; exact Hstate'.
    - iPoseProof (monoReq_mono_pub_nwl with "HmonoR") as "HmonoR'"; eauto.
      pose proof (region_state_nwl_monotone W W' a g Hrelated Hstate) as Hstate'.
      iExists p', P.
      iSplit; first done. iSplit; first done.
      iSplitL "Hrel"; first iExact "Hrel".
      iSplitL "Hzcond"; first iExact "Hzcond".
      iSplitL "Hrcond"; first iExact "Hrcond".
      iSplitL "Hwcond"; first iExact "Hwcond".
      iSplitL "HmonoR'"; first iExact "HmonoR'".
      iPureIntro; exact Hstate'.
  Qed.

  Lemma interp_addr_mono_priv_nwl
      (W W' : WORLD) (C : CmptName) (p : Perm) (a : Addr) :
    related_sts_priv_world W W' ->
    (∃ (p' : Perm) (P : V),
        ⌜PermFlowsTo p p'⌝ ∗ ⌜persistent_cond P⌝ ∗
        rel C a p' (safeC P) ∗ ▷ zcond P C ∗
        (if readAllowed p' then ▷ rcond P C p' interp else True) ∗
        (if writeAllowed p' then ▷ wcond P C interp else True) ∗
        monoReq W C a p' P ∗ ⌜region_state_nwl W a Global⌝)
    -∗
    (∃ (p' : Perm) (P : V),
        ⌜PermFlowsTo p p'⌝ ∗ ⌜persistent_cond P⌝ ∗
        rel C a p' (safeC P) ∗ ▷ zcond P C ∗
        (if readAllowed p' then ▷ rcond P C p' interp else True) ∗
        (if writeAllowed p' then ▷ wcond P C interp else True) ∗
        monoReq W' C a p' P ∗ ⌜region_state_nwl W' a Global⌝).
  Proof.
    iIntros (Hrelated) "Hw".
    iDestruct "Hw" as (p' P Hpfl' Hpers)
      "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate)".
    iPoseProof (monoReq_mono_priv_nwl with "HmonoR") as "HmonoR'"; eauto.
    pose proof (region_state_nwl_monotone_nl W W' a Hrelated Hstate) as Hstate'.
    iExists p', P.
    iSplit; first done. iSplit; first done.
    iSplitL "Hrel"; first iExact "Hrel".
    iSplitL "Hzcond"; first iExact "Hzcond".
    iSplitL "Hrcond"; first iExact "Hrcond".
    iSplitL "Hwcond"; first iExact "Hwcond".
    iSplitL "HmonoR'"; first iExact "HmonoR'".
    iPureIntro; exact Hstate'.
  Qed.

  Lemma interp_monotone_cap_valid (W W' : WORLD) C t p g b e a :
    (heap_cap_valid W p b e -> heap_cap_valid W' p b e) ->
    ⌜related_sts_pub_world W W'⌝
    -∗ interp W C (WCap t p g b e a) -∗ interp W' C (WCap t p g b e a).
  Proof.
    iIntros (Hheap Hrelated) "#Hw".
    destruct t; last (iApply interp_untagged; done).
    rewrite !fixpoint_interp1_eq !interp1_eq.
    destruct (isO p); first done.
    destruct (has_sreg_access p); first done.
    iDestruct "Hw" as "[Hw %Hlocal]".
    iSplit; last (iPureIntro; naive_solver).
    iApply (big_sepL_mono with "Hw").
    iIntros (n y Hsome) "Hy".
    iApply (interp_addr_mono_pub W W' C p g y with "Hy").
    exact Hrelated.
  Qed.

  Lemma safe_to_seal_monotone C W W' b e :
    related_sts_priv_world W W' ->
    safe_to_seal W C interp b e -∗
    safe_to_seal W' C interp b e.
  Proof.
    iIntros (Hrelated) "#Hw"; rewrite /safe_to_seal.
    generalize (finz.seq_between b e) as l; intros l.
    iApply big_sepL_mono; last done.
    iIntros (k o Hk) "(%P & HP_pers & Hseal & %Hdom & Hwcond)".
    iExists P; iFrame.
    iPureIntro.
    destruct Hrelated as (_ & _ & [ Hrelated_dom _ ] & _).
    by apply Hrelated_dom.
  Qed.

  Lemma safe_to_unseal_monotone C W W' b e :
    related_sts_priv_world W W' ->
    safe_to_unseal W C interp b e -∗
    safe_to_unseal W' C interp b e.
  Proof.
    iIntros (Hrelated) "#Hw"; rewrite /safe_to_seal.
    generalize (finz.seq_between b e) as l; intros l.
    iApply big_sepL_mono; last done.
    iIntros (k o Hk) "(%P & HP_pers & Hseal & %Hdom & Hwcond)".
    iExists P; iFrame.
    iPureIntro.
    destruct Hrelated as (_ & _ & [ Hrelated_dom _ ] & _).
    by apply Hrelated_dom.
  Qed.

  Lemma interp_monotone_sealrange (W W' : WORLD) C t p g b e a :
    ⌜related_sts_priv_world W W'⌝
    -∗ interp W C (WSealRange t p g b e a) -∗ interp W' C (WSealRange t p g b e a).
  Proof.
    iIntros (Hrelated) "#Hw".
    destruct t; last (iApply interp_untagged; done).
    rewrite !fixpoint_interp1_eq /=; auto.
    iDestruct "Hw" as "[Hw_seal Hw_unseal]".
    iSplitL "Hw_seal".
    - destruct (permit_seal p); last done.
      iApply safe_to_seal_monotone; eauto.
    - destruct (permit_unseal p); last done.
      iApply safe_to_unseal_monotone; eauto.
  Qed.

  Lemma interp_monotone_same_heap (W W' : WORLD) C w :
    heap_std W = heap_std W' ->
    ⌜related_sts_pub_world W W'⌝
    -∗ interp W C w -∗ interp W' C w.
  Proof.
    iIntros (Hheap Hrelated) "#Hw".
    pose proof (related_sts_pub_priv_world _ _ Hrelated) as Hrelated'.
    destruct w; [ | destruct sb | | ].
    - rewrite !fixpoint_interp1_eq /=; auto.
    - iApply (interp_monotone_cap_valid with "[] [$]"); eauto.
      by rewrite /heap_cap_valid /heap_cap_live -Hheap.
    - iApply (interp_monotone_sealrange with "[] [$]"); eauto.
    - iApply (interp_monotone_sentry with "[] [$]"); eauto.
    - iApply (interp_monotone_sd_same_heap with "[] [$]"); eauto.
  Qed.

  Lemma interp_monotone_nl_sentry W W' C t p g b e a :
    ⌜related_sts_priv_world W W'⌝
    -∗ ⌜isLocalWord (WSentry t p g b e a) = false⌝
    -∗ interp W C (WSentry t p g b e a) -∗ interp W' C (WSentry t p g b e a).
  Proof.
    iIntros (Hrelated Hnl) "#Hw".
    destruct t; last (iApply interp_untagged; done).
    rewrite !fixpoint_interp1_eq /=.
    iDestruct "Hw" as "[$ Hw]".
    destruct g ; cbn in Hnl ; try done.
    iModIntro. iIntros (W'').
    iIntros "#Hrelated'".
    rewrite /future_world.
    iDestruct "Hrelated'" as "%Hrelated'".
    iAssert (future_world Global W W'')%I as "Hrelated".
    { rewrite /future_world.
      iPureIntro. apply related_sts_priv_trans_world with W'; auto. }
    iSpecialize ("Hw" $! W'' with "Hrelated").
    iApply "Hw".
  Qed.

  Lemma interp_monotone_nl_cap_valid (W W' : WORLD) C t p g b e a :
    (heap_cap_valid W p b e -> heap_cap_valid W' p b e) ->
    ⌜related_sts_priv_world W W'⌝
    -∗ ⌜isLocalWord (WCap t p g b e a) = false⌝
    -∗ interp W C (WCap t p g b e a) -∗ interp W' C (WCap t p g b e a).
  Proof.
    iIntros (Hheap Hrelated Hnl) "#Hw".
    destruct t; last (iApply interp_untagged; done).
    destruct g; cbn in Hnl; try done.
    rewrite !fixpoint_interp1_eq !interp1_eq.
    destruct (isO p); first done.
    destruct (has_sreg_access p); first done.
    iDestruct "Hw" as "[Hw %Hconditions]".
    pose proof (proj1 Hconditions) as Hlocal.
    destruct (isWL p) eqn:Hwl; first congruence.
    iSplit; last (iPureIntro; naive_solver).
    iApply (big_sepL_mono with "Hw").
    iIntros (n y Hsome) "Hy".
    iApply (interp_addr_mono_priv_nwl W W' C p y with "Hy").
    exact Hrelated.
  Qed.

 Lemma interp_monotone_nl_same_heap W W' C w :
    heap_std W = heap_std W' ->
    ⌜related_sts_priv_world W W'⌝
    -∗ ⌜isLocalWord w = false⌝
    -∗ interp W C w -∗ interp W' C w.
  Proof.
    iIntros (Hheap Hrelated Hnl) "#Hw".
    destruct w; [ | destruct sb | | ].
    - rewrite !fixpoint_interp1_eq /=; auto.
    - iApply (interp_monotone_nl_cap_valid with "[] [] [$]"); eauto.
      by rewrite /heap_cap_valid /heap_cap_live -Hheap.
    - iApply (interp_monotone_sealrange with "[] [$]"); eauto.
    - iApply (interp_monotone_nl_sentry with "[] [] [$]"); eauto.
    - iApply (interp_monotone_sd_same_heap with "[] [$]"); eauto.
  Qed.

  Lemma interp_monotone_sd_retained W W' C ot sb :
    heap_wf (heap_std W') ->
    related_sts_priv_world W W' ->
    get_tag (WSealed ot sb) = true ->
    filter_heap W' (WSealed ot sb) = WSealed ot sb ->
    interp W C (WSealed ot sb) -∗ interp W' C (WSealed ot sb).
  Proof.
    intros Hwf Hrelated Htag Hfilter. iIntros "#Hw".
    destruct sb as [t p g b e a | t p g b e a]; destruct t;
      cbn in Htag; try discriminate;
      rewrite !fixpoint_interp1_eq /= /interp_sb; last done.
    iDestruct "Hw" as "[$ %Hvalid]". iPureIntro.
    destruct (isO p); first done.
    eapply (heap_cap_valid_future_retained _ _ (WSealed ot (SCap true p g b e a))); eauto.
    - exact (proj2 (proj2 (proj2 Hrelated))).
    - intros Hnonempty Hb. by rewrite /heap_authority_base /= decide_True // /heap_cap_base /memory_cap_base Hb.
  Qed.

  Lemma interp_monotone_retained W W' C w :
    heap_wf (heap_std W') -> related_sts_pub_world W W' ->
    get_tag w = true -> filter_heap W' w = w ->
    interp W C w -∗ interp W' C w.
  Proof.
    intros Hwf Hrelated Htag Hfilter. iIntros "#Hw".
    destruct w as [z|[t p g b e a|t p g b e a]|t p g b e a|ot sb].
    - discriminate.
    - iApply (interp_monotone_cap_valid with "[] Hw"); last done.
      intros Hvalid. eapply (heap_cap_valid_future_retained _ _ (WCap t p g b e a)); eauto.
      + exact (proj2 (proj2 (proj2 Hrelated))).
      + intros Hnonempty Hb. by rewrite /heap_authority_base /= decide_True // /heap_cap_base /memory_cap_base Hb.
    - iApply (interp_monotone_sealrange with "[] Hw").
      iPureIntro. by apply related_sts_pub_priv_world.
    - by iApply (interp_monotone_sentry with "[] Hw").
    - iApply (interp_monotone_sd_retained with "Hw"); eauto.
      by apply related_sts_pub_priv_world.
  Qed.

  Lemma interp_monotone_nl_retained W W' C w :
    heap_wf (heap_std W') -> related_sts_priv_world W W' ->
    isLocalWord w = false -> get_tag w = true -> filter_heap W' w = w ->
    interp W C w -∗ interp W' C w.
  Proof.
    intros Hwf Hrelated Hnl Htag Hfilter. iIntros "#Hw".
    destruct w as [z|[t p g b e a|t p g b e a]|t p g b e a|ot sb].
    - discriminate.
    - iApply (interp_monotone_nl_cap_valid with "[] [] Hw"); try done.
      intros Hvalid. eapply (heap_cap_valid_future_retained _ _ (WCap t p g b e a)); eauto.
      + exact (proj2 (proj2 (proj2 Hrelated))).
      + intros Hnonempty Hb. by rewrite /heap_authority_base /= decide_True // /heap_cap_base /memory_cap_base Hb.
    - by iApply (interp_monotone_sealrange with "[] Hw").
    - by iApply (interp_monotone_nl_sentry with "[] [] Hw").
    - iApply (interp_monotone_sd_retained with "Hw"); eauto.
  Qed.

  Lemma filter_heap_retained_past W W' w :
    heap_wf (heap_std W') ->
    related_sts_heap_std (heap_std W) (heap_std W') ->
    get_tag w = true -> filter_heap W' w = w -> filter_heap W w = w.
  Proof.
    intros Hwf Hrelated Htag Hfilter.
    destruct (filter_heap_result W w) as [Hraw|Hclear]; first done.
    have Hfuture := filter_heap_future W W' w Hwf Hrelated.
    rewrite Hclear filter_heap_untagged in Hfuture; last apply get_tag_clear_tag.
    rewrite Hfilter in Hfuture.
    have := get_tag_clear_tag w. rewrite Hfuture Htag. discriminate.
  Qed.

  Lemma interp_in_mem_monotone_raw W W' C w :
    heap_wf (heap_std W') -> related_sts_pub_world W W' ->
    interp_in_mem RWL W C w -∗ interp_in_mem RWL W' C w.
  Proof.
    intros Hwf Hrelated.
    change (⊢ interp W C (filter_heap W w) -∗ interp W' C (filter_heap W' w))%I.
    destruct (get_tag w) eqn:Htag.
    2: { rewrite !filter_heap_untagged //.
         iIntros "_". by iApply interp_untagged. }
    destruct (filter_heap_result W' w) as [Hraw|Hclear].
    - have Hpast := filter_heap_retained_past W W' w Hwf
        (proj2 (proj2 (proj2 Hrelated))) Htag Hraw.
      rewrite Hpast Hraw. by apply interp_monotone_retained.
    - rewrite Hclear. iIntros "_". iApply interp_clear_tag.
  Qed.

  Lemma interp_in_mem_monotone_nl_raw W W' C w :
    heap_wf (heap_std W') -> related_sts_priv_world W W' ->
    isLocalWord w = false ->
    interp_in_mem RWL W C w -∗ interp_in_mem RWL W' C w.
  Proof.
    intros Hwf Hrelated Hnl.
    change (⊢ interp W C (filter_heap W w) -∗ interp W' C (filter_heap W' w))%I.
    destruct (get_tag w) eqn:Htag.
    2: { rewrite !filter_heap_untagged //.
         iIntros "_". by iApply interp_untagged. }
    destruct (filter_heap_result W' w) as [Hraw|Hclear].
    - have Hpast := filter_heap_retained_past W W' w Hwf
        (proj2 (proj2 (proj2 Hrelated))) Htag Hraw.
      rewrite Hpast Hraw. by apply interp_monotone_nl_retained.
    - rewrite Hclear. iIntros "_". iApply interp_clear_tag.
  Qed.

  Lemma interp_in_mem_monotone W W' C p w :
    heap_wf (heap_std W') -> related_sts_pub_world W W' ->
    interp_in_mem p W C w -∗ interp_in_mem p W' C w.
  Proof.
    intros Hwf Hrelated.
    change (⊢ interp_in_mem RWL W C (load_word p w) -∗
      interp_in_mem RWL W' C (load_word p w))%I.
    by apply interp_in_mem_monotone_raw.
  Qed.

  Lemma interp_in_mem_monotone_nl W W' C p w :
    heap_wf (heap_std W') -> related_sts_priv_world W W' ->
    isLocalWord (load_word p w) = false ->
    interp_in_mem p W C w -∗ interp_in_mem p W' C w.
  Proof.
    intros Hwf Hrelated Hnl.
    change (⊢ interp_in_mem RWL W C (load_word p w) -∗
      interp_in_mem RWL W' C (load_word p w))%I.
    by apply interp_in_mem_monotone_nl_raw.
  Qed.

  Lemma interp_monotone_cap_nonheap W W' C t p g b e a :
    is_heap_address b = false -> disjoint_from_heap b e ->
    related_sts_pub_world W W' ->
    interp W C (WCap t p g b e a) -∗ interp W' C (WCap t p g b e a).
  Proof.
    intros Hb Hdisj Hrelated.
    iApply interp_monotone_cap_valid; last done.
    by rewrite /heap_cap_valid /heap_cap_live Hb.
  Qed.

  Lemma interp_monotone_nl_cap_nonheap W W' C t p g b e a :
    is_heap_address b = false -> disjoint_from_heap b e ->
    related_sts_priv_world W W' -> isLocalWord (WCap t p g b e a) = false ->
    interp W C (WCap t p g b e a) -∗ interp W' C (WCap t p g b e a).
  Proof.
    intros Hb Hdisj Hrelated Hnl.
    iApply interp_monotone_nl_cap_valid; try done.
    by rewrite /heap_cap_valid /heap_cap_live Hb.
  Qed.

Lemma interp_monotone_continuation
  (W W' : WORLD) (C : CmptName)
  (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
  related_sts_pub_world W W' ->
  interp_continuation cstk (W :: Ws) (C :: Cs) -∗ interp_continuation cstk (W' :: Ws) (C :: Cs).
Proof.
  revert Ws Cs; induction cstk;intros Ws Cs; simpl;auto.
  iIntros (Hrel) "[Hic Hk]".
  destruct (is_known_to_known_frm a); first (by iFrame).
  iDestruct "Hk" as "[Hcallee Hrestore]".
  iSplitL "Hic"; [|iSplitL "Hcallee"].
  - iFrame.
  - iDestruct "Hcallee" as "[%Hheap Hcallee]".
    iSplit; first done.
    iApply (interp_monotone_cap_nonheap with "Hcallee"); naive_solver.
  - destruct (is_untrusted_caller_frm a); first done.
    iIntros (W'' Hrel'). iApply "Hrestore". iPureIntro.
    eapply related_sts_pub_trans_world; eauto.
Qed.

Lemma elem_of_mono_pub W W' a :
  related_sts_pub_world W W' -> a ∈ dom (std W) -> a ∈ dom (std W').
Proof.
  intros [ [ Hdom_sta Hrelated] _] Ha.
  rewrite elem_of_dom in Ha; destruct Ha as [? Ha].
  cbn in *.
  apply Hdom_sta; rewrite elem_of_dom;eauto.
Qed.


End monotone.
