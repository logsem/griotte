From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From iris.base_logic Require Export invariants na_invariants saved_prop.
From griotte Require Export logrel region_invariants.
Import uPred.

Section monotone.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {CL : CritLink Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  #[local] Notation E := (interpO Σ).
  #[local] Notation V := (interpO Σ).
  #[local] Notation K := (contO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
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

  Lemma interp_monotone_sd_same_heap W W' C ot sb π :
    ⌜related_sts_priv_world W W'⌝
    -∗ interp W C (WSealed ot sb @@? π) -∗ interp W' C (WSealed ot sb @@? π).
  Proof.
    iIntros (Hrelated) "#Hinterp".
    destruct sb as [t p g b e a | t p g b e a]; destruct t;
      rewrite !interp_unfold /= /interp_sb; done.
  Qed.

  Lemma interp_monotone_sentry W W' C k t p g b e a π :
    ⌜related_sts_pub_world W W'⌝
    -∗ interp W C (WSentry k t p g b e a @@? π) -∗ interp W' C (WSentry k t p g b e a @@? π).
  Proof.
    iIntros (Hrelated) "#Hw".
    destruct t; last (iApply interp_untagged; done).
    rewrite !interp_unfold /=.
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
      (W W' : WORLD) (C : CmptName) (p : Perm) (g : Locality) (k : LAddr) :
    related_sts_pub_world W W' ->
    (∃ (p' : Perm) (P : V),
        ⌜PermFlowsTo p p'⌝ ∗ ⌜persistent_cond P⌝ ∗
        rel C k p' (safeC P) ∗ ▷ zcond P C ∗
        (if readAllowed p' then ▷ rcond P C p' interp else True) ∗
        (if writeAllowed p' then ▷ wcond P C interp else True) ∗
        monoReq W C k p' P ∗
        ⌜if isWL p then region_state_pwl W k else region_state_nwl W k g⌝)
    -∗
    (∃ (p' : Perm) (P : V),
        ⌜PermFlowsTo p p'⌝ ∗ ⌜persistent_cond P⌝ ∗
        rel C k p' (safeC P) ∗ ▷ zcond P C ∗
        (if readAllowed p' then ▷ rcond P C p' interp else True) ∗
        (if writeAllowed p' then ▷ wcond P C interp else True) ∗
        monoReq W' C k p' P ∗
        ⌜if isWL p then region_state_pwl W' k else region_state_nwl W' k g⌝).
  Proof.
    iIntros (Hrelated) "Hw".
    iDestruct "Hw" as (p' P Hpfl' Hpers)
      "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate)".
    destruct (isWL p) eqn:Hwl.
    - iPoseProof (monoReq_mono_pub_pwl with "HmonoR") as "HmonoR'"; eauto.
      pose proof (region_state_pwl_monotone W W' k Hrelated Hstate) as Hstate'.
      iExists p', P. iFrame "∗%".
    - iPoseProof (monoReq_mono_pub_nwl with "HmonoR") as "HmonoR'"; eauto.
      pose proof (region_state_nwl_monotone W W' k g Hrelated Hstate) as Hstate'.
      iExists p', P. iFrame "∗%".
  Qed.

  Lemma interp_addr_mono_priv_nwl
      (W W' : WORLD) (C : CmptName) (p : Perm) (k : LAddr) :
    related_sts_priv_world W W' ->
    (∃ (p' : Perm) (P : V),
        ⌜PermFlowsTo p p'⌝ ∗ ⌜persistent_cond P⌝ ∗
        rel C k p' (safeC P) ∗ ▷ zcond P C ∗
        (if readAllowed p' then ▷ rcond P C p' interp else True) ∗
        (if writeAllowed p' then ▷ wcond P C interp else True) ∗
        monoReq W C k p' P ∗ ⌜region_state_nwl W k Global⌝)
    -∗
    (∃ (p' : Perm) (P : V),
        ⌜PermFlowsTo p p'⌝ ∗ ⌜persistent_cond P⌝ ∗
        rel C k p' (safeC P) ∗ ▷ zcond P C ∗
        (if readAllowed p' then ▷ rcond P C p' interp else True) ∗
        (if writeAllowed p' then ▷ wcond P C interp else True) ∗
        monoReq W' C k p' P ∗ ⌜region_state_nwl W' k Global⌝).
  Proof.
    iIntros (Hrelated) "Hw".
    iDestruct "Hw" as (p' P Hpfl' Hpers)
      "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate)".
    iPoseProof (monoReq_mono_priv_nwl with "HmonoR") as "HmonoR'"; eauto.
    pose proof (region_state_nwl_monotone_nl W W' k Hrelated Hstate) as Hstate'.
    iExists p', P. iFrame "∗%".
  Qed.

  (** The region keys of a capability do not depend on the world: only the
      heap validity needs a premise. *)
  Lemma interp_monotone_cap_valid (W W' : WORLD) C t p g b e a π :
    ⌜related_sts_pub_world W W'⌝
    -∗ interp W C (WCap t p g b e a @@? π) -∗ interp W' C (WCap t p g b e a @@? π).
  Proof.
    iIntros (Hrelated) "#Hw".
    destruct t; last (iApply interp_untagged; done).
    rewrite !interp_unfold !interp1_eq.
    destruct (isO p).
    { iDestruct "Hw" as "[#Hok %Hcoverage]".
      iFrame "Hok". iPureIntro.
      intros x Hx Hxheap.
      eapply region_state_nwl_monotone; eauto. }
    destruct (has_sreg_access p); first done.
    iDestruct "Hw" as "[Hw [%Hlocal #Hok]]".
    iFrame "Hok". iSplit; last (iPureIntro; naive_solver).
    iApply (big_sepL_mono with "Hw").
    iIntros (n y Hsome) "Hy".
    iApply (interp_addr_mono_pub W W' C p g (addr_key π y) with "Hy").
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
    destruct Hrelated as (_ & _ & [ Hrelated_dom _ ]).
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
    destruct Hrelated as (_ & _ & [ Hrelated_dom _ ]).
    by apply Hrelated_dom.
  Qed.

  Lemma interp_monotone_sealrange (W W' : WORLD) C t p g b e a π :
    ⌜related_sts_priv_world W W'⌝
    -∗ interp W C (WSealRange t p g b e a @@? π) -∗ interp W' C (WSealRange t p g b e a @@? π).
  Proof.
    iIntros (Hrelated) "#Hw".
    destruct t; last (iApply interp_untagged; done).
    rewrite !interp_unfold /=; auto.
    iDestruct "Hw" as "[Hw_seal Hw_unseal]".
    iSplitL "Hw_seal".
    - destruct (permit_seal p); last done.
      iApply safe_to_seal_monotone; eauto.
    - destruct (permit_unseal p); last done.
      iApply safe_to_unseal_monotone; eauto.
  Qed.

  Lemma interp_monotone_same_heap (W W' : WORLD) C w :
    ⌜related_sts_pub_world W W'⌝
    -∗ interp W C w -∗ interp W' C w.
  Proof.
    iIntros (Hrelated) "#Hw".
    pose proof (related_sts_pub_priv_world _ _ Hrelated) as Hrelated'.
    destruct w as [w π].
    destruct w; [ | destruct sb | | ].
    - rewrite !interp_unfold /=; auto.
    - iApply (interp_monotone_cap_valid with "[] [$]"); eauto.
    - iApply (interp_monotone_sealrange with "[] [$]"); eauto.
    - iApply (interp_monotone_sentry with "[] [$]"); eauto.
    - iApply (interp_monotone_sd_same_heap with "[] [$]"); eauto.
  Qed.

  Lemma interp_monotone_nl_sentry W W' C k t p g b e a π :
    ⌜related_sts_priv_world W W'⌝
    -∗ ⌜isLocalWord (WSentry k t p g b e a) = false⌝
    -∗ interp W C (WSentry k t p g b e a @@? π) -∗ interp W' C (WSentry k t p g b e a @@? π).
  Proof.
    iIntros (Hrelated Hnl) "#Hw".
    destruct t; last (iApply interp_untagged; done).
    rewrite !interp_unfold /=.
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

  Lemma interp_monotone_nl_cap_valid (W W' : WORLD) C t p g b e a π :
    ⌜related_sts_priv_world W W'⌝
    -∗ ⌜isLocalWord (WCap t p g b e a) = false⌝
    -∗ interp W C (WCap t p g b e a @@? π) -∗ interp W' C (WCap t p g b e a @@? π).
  Proof.
    iIntros (Hrelated Hnl) "#Hw".
    destruct t; last (iApply interp_untagged; done).
    destruct g; cbn in Hnl; try done.
    rewrite !interp_unfold !interp1_eq.
    destruct (isO p).
    { iDestruct "Hw" as "[#Hok %Hcoverage]".
      iFrame "Hok". iPureIntro.
      intros x Hx Hxheap.
      eapply region_state_nwl_monotone_nl; eauto. }
    destruct (has_sreg_access p); first done.
    iDestruct "Hw" as "[Hw [%Hconditions #Hok]]".
    pose proof (proj1 Hconditions) as Hlocal.
    destruct (isWL p) eqn:Hwl; first congruence.
    iFrame "Hok". iSplit; last (iPureIntro; naive_solver).
    iApply (big_sepL_mono with "Hw").
    iIntros (n y Hsome) "Hy".
    iApply (interp_addr_mono_priv_nwl W W' C p (addr_key π y) with "Hy").
    exact Hrelated.
  Qed.

 Lemma interp_monotone_nl_same_heap W W' C w :
    ⌜related_sts_priv_world W W'⌝
    -∗ ⌜isLocalWord w.(lw) = false⌝
    -∗ interp W C w -∗ interp W' C w.
  Proof.
    iIntros (Hrelated Hnl) "#Hw".
    destruct w as [w π].
    destruct w; [ | destruct sb | | ].
    - rewrite !interp_unfold /=; auto.
    - iApply (interp_monotone_nl_cap_valid with "[] [] [$]"); eauto.
    - iApply (interp_monotone_sealrange with "[] [$]"); eauto.
    - iApply (interp_monotone_nl_sentry with "[] [] [$]"); eauto.
    - iApply (interp_monotone_sd_same_heap with "[] [$]"); eauto.
  Qed.

  Lemma interp_in_mem_monotone W W' C p w :
    related_sts_pub_world W W' ->
    interp_in_mem p W C w -∗ interp_in_mem p W' C w.
  Proof.
    intros Hrelated.
    change (⊢ interp W C (lload_word p w) -∗ interp W' C (lload_word p w))%I.
    iIntros "Hw". by iApply (interp_monotone_same_heap with "[] Hw").
  Qed.

  Lemma interp_in_mem_monotone_nl W W' C p w :
    related_sts_priv_world W W' ->
    isLocalWord (load_word p w.(lw)) = false ->
    interp_in_mem p W C w -∗ interp_in_mem p W' C w.
  Proof.
    intros Hrelated Hnl.
    change (⊢ interp W C (lload_word p w) -∗ interp W' C (lload_word p w))%I.
    iIntros "Hw". iApply (interp_monotone_nl_same_heap with "[] [] Hw"); first done.
    by rewrite lw_lload_word.
  Qed.

  Lemma interp_monotone_cap_nonheap W W' C t p g b e a :
    disjoint_from_heap b e ->
    related_sts_pub_world W W' ->
    interp W C (WCap t p g b e a) -∗ interp W' C (WCap t p g b e a).
  Proof.
    intros Hdisj Hrelated. iIntros "Hw".
    by iApply (interp_monotone_cap_valid with "[] Hw").
  Qed.

  Lemma interp_monotone_nl_cap_nonheap W W' C t p g b e a :
    disjoint_from_heap b e ->
    related_sts_priv_world W W' ->
    isLocalWord (WCap t p g b e a) = false ->
    interp W C (WCap t p g b e a) -∗ interp W' C (WCap t p g b e a).
  Proof.
    intros Hdisj Hrelated Hnl. iIntros "Hw".
    by iApply (interp_monotone_nl_cap_valid with "[] [] Hw").
  Qed.

  (** [top_cmpt_untrusted] is monotone along public transitions: the table
      facts hold in every private future world, and the thread's stack, at
      depth 0, lies outside the heap. *)
  Lemma top_cmpt_untrusted_mono_pub W W' C cstk :
    related_sts_pub_world W W' →
    top_cmpt_untrusted interp W C cstk -∗ top_cmpt_untrusted interp W' C cstk.
  Proof.
    iIntros (Hrelated) "[Htbl Hstk]".
    iSplitL "Htbl".
    { iDestruct "Htbl" as (pcc cgp eh ehs) "(Hpcc & Hcgp & Heh & Hehs & #Hinterp & %Htbl_set)".
      iExists pcc, cgp, eh, ehs. iFrame "Hpcc Hcgp Heh Hehs". iSplit; last done.
      iIntros "!>" (W'' Hrelated').
      iApply "Hinterp". iPureIntro.
      eapply related_sts_priv_trans_world; last exact Hrelated'.
      by apply related_sts_pub_priv_world. }
    destruct (cstk_frames cstk); last done.
    iDestruct "Hstk" as (p g b e a Hcsp Hheap) "#Hcsp".
    iExists p, g, b, e, a. do 2 (iSplit; first done).
    rewrite Hcsp. iModIntro.
    by iApply (interp_monotone_cap_nonheap with "Hcsp").
  Qed.

Lemma interp_monotone_continuation
  (W W' : WORLD) (C : CmptName)
  (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
  related_sts_pub_world W W' ->
  interp_continuation cstk (W :: Ws) (C :: Cs) -∗ interp_continuation cstk (W' :: Ws) (C :: Cs).
Proof.
  destruct cstk as [ef frms].
  revert Ws Cs; induction frms as [|frm frms IH];intros Ws Cs; simpl;auto.
  iIntros (Hrel) "[Hic Hk]".
  destruct (is_known_to_known_frm frm); first (by iFrame).
  iDestruct "Hk" as "[Hcallee Htopmost_frm]".
  iSplitL "Hic"; [|iSplitL "Hcallee"].
  - iFrame.
  - iDestruct "Hcallee" as "[%Hheap Hcallee]".
    iSplit; first done.
    iApply (interp_monotone_cap_nonheap with "Hcallee"); naive_solver.
  - destruct (is_untrusted_caller_frm frm).
    { by iApply (top_cmpt_untrusted_mono_pub with "Htopmost_frm"). }
    iIntros (W'' Hrel'). iApply "Htopmost_frm". iPureIntro.
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

  (** The safe registers, in a public future world. *)
  Lemma interp_reg_monotone W W' C (regs : LReg) :
    related_sts_pub_world W W' →
    interp_reg interp W C regs -∗ interp_reg interp W' C regs.
  Proof.
    iIntros (Hrel) "[Hfull #Hregs]". iSplit; first done.
    iIntros (r v Hv). iApply (interp_monotone_same_heap with "[] (Hregs [//])"); done.
  Qed.

  (** A safe word without identifier is safe in a public future world. *)
  Lemma interp_monotone_noid W W' C w :
    related_sts_pub_world W W' →
    w.(lprov) = None →
    interp W C w -∗ interp W' C w.
  Proof.
    iIntros (Hrel Hnoid) "Hw".
    by iApply (interp_monotone_same_heap with "[] Hw").
  Qed.

End monotone.
