From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From iris.base_logic Require Export invariants na_invariants saved_prop.
From griotte Require Export logrel region_invariants.
Import uPred.

Section monotone.
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

  #[local] Notation E := (interpO Σ).
  #[local] Notation V := (interpO Σ).
  #[local] Notation K := (contO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

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

  Lemma region_state_pwl_monotone W W' a :
    related_sts_pub_world W W' →
    region_state_pwl W a -> region_state_pwl W' a.
  Proof.
    rewrite /region_state_pwl.
    intros Hrelated Hstate; simplify_eq.
    eapply region_state_pub_temp in Hstate; eauto.
  Qed.

  (** Every world is a public future of the empty world. *)
  (* TODO: move to sts.v *)
  Lemma related_sts_pub_world_empty W : related_sts_pub_world ∅ W.
  Proof.
    split; cbn.
    - split; [rewrite dom_empty_L; set_solver|]. intros i x y Hx. by rewrite lookup_empty in Hx.
    - split_and!; [rewrite dom_empty_L; set_solver|rewrite dom_empty_L; set_solver|].
      intros i rpub rpriv rpub' rpriv' Hr. by rewrite lookup_empty in Hr.
  Qed.

  (** A sealed word under a Global-kind otype is valid in every world. *)
  Lemma interp_monotone_sd W W' C ot sb π P :
    ⌜related_sts_priv_world W W'⌝ -∗
    ot ↪ₒ{SealGlobal} P -∗
    interp W C (WSealed ot sb @@? π) -∗
    interp W' C (WSealed ot sb @@? π).
  Proof.
    iIntros (Hrelated) "#Hspred #Hinterp".
    destruct sb as [t p g b e a | t p g b e a]; destruct t;
      rewrite !interp_unfold /= /interp_sb; try done.
    all: iDestruct "Hinterp" as "[(%κ & %P' & #Hs & #Hok & #HP) $]";
      iDestruct (seal_pred_agree with "Hspred Hs") as "[<- _]";
      iExists SealGlobal, P'; iFrame "Hs Hok";
      iDestruct "Hok" as "[_ #Hc]"; iNext; by iApply ("Hc" $! th th W W').
  Qed.

  (** A sealed word with a Global payload is valid in every world. *)
  Lemma interp_monotone_sd_nl W W' C ot sb π :
    ⌜related_sts_priv_world W W'⌝ -∗
    ⌜isLocalSealable sb = false⌝ -∗
    interp W C (WSealed ot sb @@? π) -∗
    interp W' C (WSealed ot sb @@? π).
  Proof.
    iIntros (Hrelated Hnl) "#Hinterp".
    by iApply (interp_global_world_free with "Hinterp").
  Qed.

  Lemma interp_monotone_sd_pub W W' C ot sb π :
    ⌜related_sts_pub_world W W'⌝ -∗
    interp W C (WSealed ot sb @@? π) -∗
    interp W' C (WSealed ot sb @@? π).
  Proof.
    iIntros (Hrelated) "#Hinterp".
    destruct sb as [t p g b e a | t p g b e a]; destruct t;
      rewrite !interp_unfold /= /interp_sb; try done.
    all: iDestruct "Hinterp" as "[(%κ & %P & #Hs & #Hok & #HP) $]";
      iExists κ, P; iFrame "Hs Hok";
      (destruct κ; cbn;
       [iDestruct "Hok" as "[_ #Hc]"; iNext; by iApply ("Hc" $! th th W W')
       |by iDestruct "Hok" as "[_ []]"]).
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
    + iIntros "_". iApply "Hw". done.
    + iIntros "#Hrelated'".
      rewrite /future_world.
      iDestruct "Hrelated'" as "%Hrelated'".
      iAssert (future_world Local W W'')%I as "Hrelated".
      { rewrite /future_world.
        iPureIntro. apply related_sts_pub_trans_world with W'; auto. }
      iSpecialize ("Hw" $! W'' with "Hrelated").
      iApply "Hw".
  Qed.

  Lemma region_rel_mono_pub W W' C k p' P p g :
    related_sts_pub_world W W' ->
    region_rel W C k p' P p g -∗ region_rel W' C k p' P p g.
  Proof.
    iIntros (Hrelated) "Hrel".
    iAssert (□ (region_rel_l W C k p' P -∗ region_rel_l W' C k p' P))%I as "#Hl".
    { iIntros "!> (Hr & %HT & Hm)". iFrame. iPureIntro. by eapply region_state_pub_temp. }
    rewrite /region_rel. destruct (isWL p); [by iApply "Hl"|].
    destruct g; [done|]. iDestruct "Hrel" as "[$|Hrel]". iRight. by iApply "Hl".
  Qed.

  Lemma interp_addr_mono_pub
      (W W' : WORLD) (C : CmptName) (p : Perm) (g : Locality) (k : LAddr) :
    related_sts_pub_world W W' ->
    (∃ (p' : Perm) (P : V),
        ⌜PermFlowsTo p p'⌝ ∗ ⌜persistent_cond P⌝ ∗
        region_rel W C k p' P p g ∗ ▷ zcond P C ∗
        (if readAllowed p' then ▷ rcond P C p' interp else True) ∗
        (if writeAllowed p' then ▷ wcond P C interp else True))
    -∗
    (∃ (p' : Perm) (P : V),
        ⌜PermFlowsTo p p'⌝ ∗ ⌜persistent_cond P⌝ ∗
        region_rel W' C k p' P p g ∗ ▷ zcond P C ∗
        (if readAllowed p' then ▷ rcond P C p' interp else True) ∗
        (if writeAllowed p' then ▷ wcond P C interp else True)).
  Proof.
    iIntros (Hrelated) "Hw".
    iDestruct "Hw" as (p' P Hpfl' Hpers) "(Hrel & Hzcond & Hrcond & Hwcond)".
    iDestruct (region_rel_mono_pub with "Hrel") as "Hrel"; first done.
    iExists p', P. iFrame "∗%".
  Qed.

  Lemma heap_cap_O_key_mono_pub W W' C g k :
    related_sts_pub_world W W' ->
    heap_cap_O_key W C g k -∗ heap_cap_O_key W' C g k.
  Proof.
    iIntros (Hrelated) "[H|H]"; [by iLeft|iRight].
    destruct g; [done|].
    iDestruct "H" as (p φ Hpers) "[Hr %HT]".
    iExists p, φ. iFrame "Hr %". iPureIntro. by eapply region_state_pub_temp.
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
    { iDestruct "Hw" as "[#Hok #Hcoverage]".
      iFrame "Hok". iApply (big_sepL_impl with "Hcoverage").
      iIntros "!>" (n x Hx) "Hx %Hheap".
      iApply heap_cap_O_key_mono_pub; [done|]. by iApply "Hx". }
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
  Proof. by iIntros (Hrelated) "#Hw". Qed.

  Lemma safe_to_unseal_monotone C W W' b e :
    related_sts_priv_world W W' ->
    safe_to_unseal W C interp b e -∗
    safe_to_unseal W' C interp b e.
  Proof. by iIntros (Hrelated) "#Hw". Qed.

  Lemma interp_monotone_sealrange (W W' : WORLD) C t p g b e a π :
    ⌜related_sts_priv_world W W'⌝
    -∗ interp W C (WSealRange t p g b e a @@? π) -∗ interp W' C (WSealRange t p g b e a @@? π).
  Proof.
    iIntros (Hrelated) "#Hw".
    rewrite !interp_unfold /=; auto.
  Qed.

  Lemma interp_monotone (W W' : WORLD) C w :
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
    - iApply (interp_monotone_sd_pub with "[] [$]"); eauto.
  Qed.

  Lemma interp_monotone_nl_sentry W W' C k t p g b e a π :
    ⌜related_sts_priv_world W W'⌝
    -∗ ⌜isLocalWord (WSentry k t p g b e a) = false⌝
    -∗ interp W C (WSentry k t p g b e a @@? π) -∗ interp W' C (WSentry k t p g b e a @@? π).
  Proof.
    iIntros (Hrelated Hnl) "#Hw".
    by iApply (interp_global_world_free with "Hw").
  Qed.

  Lemma interp_monotone_nl_cap_valid (W W' : WORLD) C t p g b e a π :
    ⌜related_sts_priv_world W W'⌝
    -∗ ⌜isLocalWord (WCap t p g b e a) = false⌝
    -∗ interp W C (WCap t p g b e a @@? π) -∗ interp W' C (WCap t p g b e a @@? π).
  Proof.
    iIntros (Hrelated Hnl) "#Hw".
    by iApply (interp_global_world_free with "Hw").
  Qed.

  (** A word valid in every world is valid in [W]. *)
  Lemma interp_g_any_world W C w :
    interp_g C w -∗ interp W C w.
  Proof.
    iIntros "Hw". iApply (interp_monotone with "[] Hw").
    iPureIntro. apply related_sts_pub_world_empty.
  Qed.

 Lemma interp_monotone_nl W W' C w :
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
    - iApply (interp_monotone_sd_nl with "[] [] [$]"); eauto.
  Qed.

  Lemma interp_in_mem_monotone W W' C p w :
    related_sts_pub_world W W' ->
    interp_in_mem p W C w -∗ interp_in_mem p W' C w.
  Proof.
    intros Hrelated.
    change (⊢ interp W C (lload_word p w) -∗ interp W' C (lload_word p w))%I.
    iIntros "Hw". by iApply (interp_monotone with "[] Hw").
  Qed.

  Lemma interp_in_mem_monotone_nl W W' C p w :
    related_sts_priv_world W W' ->
    isLocalWord (load_word p w.(lw)) = false ->
    interp_in_mem p W C w -∗ interp_in_mem p W' C w.
  Proof.
    intros Hrelated Hnl.
    change (⊢ interp W C (lload_word p w) -∗ interp W' C (lload_word p w))%I.
    iIntros "Hw". iApply (interp_monotone_nl with "[] [] Hw"); first done.
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
    iIntros (r v Hv). iApply (interp_monotone with "[] (Hregs [//])"); done.
  Qed.

  (** A safe word without identifier is safe in a public future world. *)
  Lemma interp_monotone_noid W W' C w :
    related_sts_pub_world W W' →
    w.(lprov) = None →
    interp W C w -∗ interp W' C w.
  Proof.
    iIntros (Hrel Hnoid) "Hw".
    by iApply (interp_monotone with "[] Hw").
  Qed.

End monotone.
