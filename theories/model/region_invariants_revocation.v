From iris.proofmode Require Import proofmode.
From griotte Require Export stdpp_extra iris_extra region_invariants world_std_revocation.

  (*** REVOCATION OF THE WORLD INTERPRETATION *)

  (** * Disclaimer to the users of Griotte:

      All the lemmas and definitions in this file are internal to the Griotte model.
      To manipulate the world in the proofs, see [world_ghost_theory.v].

  *)

Section region_invariant_revocation.

  Context {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {relg : relGS Σ}
    `{MP: MachineParameters}.
  Implicit Types W : WORLD.

  (* The following lemma takes a revoked region and makes it Temporary. *)

  (* In the following variant, we only require monotonicity of the updated world *)
  Lemma update_region_revoked_temp_quarantined_heap E W C a ι p φ o :
    heap_std W !! ι = Some o ->
    alloc_object_status o = AllocObjectQuarantined ->
    std W !! LHeap a ι = Some Revoked ->
    sts_full_world W C -∗ region W C -∗ rel C (LHeap a ι) p φ
    ={E}=∗ region (<s[LHeap a ι:=Temporary]s>W) C ∗ sts_full_world (<s[LHeap a ι:=Temporary]s>W) C.
  Proof.
    iIntros (Hι Hstatus Hrev) "Hsts Hreg #Hrel".
    rewrite region_eq /region_def.
    iNamed "Hreg"; simplify_eq.
    iDestruct "Hmap" as "[%Hknown [Hheapfrag Hpreds]]".
    rewrite rel_eq /rel_def. iDestruct "Hrel" as (γ) "[HREL Hsaved]".
    iDestruct ( (reg_in C M) with "[$HREL $HM]") as %HMeq;eauto.
    rewrite /region_map_def HMeq big_sepM_insert; [|by rewrite lookup_delete_eq].
    iDestruct "Hpreds" as "[Hl' Hr]".
    iDestruct "Hl'" as (ρ Hl) "[Hstate Hresources]".
    iDestruct "Hresources" as (γ0 p0 φ0 Heq Hpers) "[#Hsaved0 Htoken]".
    iEval (rewrite /heap_key_resource Hι Hstatus) in "Htoken".
    iDestruct "Htoken" as "[%Hcontains _]".
    iDestruct (sts_full_state_std with "Hsts Hstate") as %Hρ.
    rewrite Hrev in Hρ. inversion Hρ as [Hρrev]. subst.
    iMod (sts_update_std _ _ _ _ Temporary with "Hsts Hstate") as "[Hsts Hstate]".
    assert (related_sts_pub_world W (<s[LHeap a ι := Temporary ]s> W)) as Hrelated.
    { apply related_sts_pub_revoked_temp; auto. }
    assert (LHeap a ι ∈ dom (std W)) as Hin by (rewrite elem_of_dom Hrev; eauto).
    iDestruct (region_map_monotone _ _ _ _ _ Hrelated eq_refl with "[Hr Hheapfrag]") as "Hr".
    { rewrite /std_update /= dom_insert_L. by apply heap_keys_known_insert. }
    { iFrame "%∗". }
    assert (is_Some (M !! LHeap a ι)) as [x Hsome].
    { apply elem_of_dom. rewrite -Hdom. done. }
    iDestruct (region_map_delete with "Hr") as "Hr".
    iDestruct (region_map_insert _ _ _ _ _ Temporary with "Hr") as "Hr";auto.
    iDestruct "Hr" as "[%Hknown' [Hheapfrag Hr]]".
    iDestruct (big_sepM_delete _ _ (LHeap a ι) _ Hsome with "[Hstate $Hr]") as "Hr".
    { iExists Temporary. iFrame. iSplitR;[iPureIntro;apply lookup_insert_eq|].
      iExists γ0,p0,φ0. iSplitR.
      { iPureIntro. rewrite HMeq lookup_insert_eq in Hsome. congruence. }
      iFrame "%#". by iApply heap_key_resource_quarantined.
    }
    iFrame "Hsts".
    iExists M.
    rewrite -HMeq.
    iFrame "∗%".
    iPureIntro.
    apply insert_id in Hsome; rewrite -Hsome.
    apply insert_id in Hl; rewrite -Hl.
    split.
    - repeat rewrite dom_insert_L;rewrite Hdom;set_solver.
    - repeat rewrite insert_insert_eq dom_insert_L;rewrite Hdomρ;set_solver.
  Qed.

  Lemma update_region_revoked_temp_pwl_updated E W C k p v φ `{∀ Wv, Persistent (φ Wv)}  :
    heap_key_live (heap_std W) k ->
    let W' := (<s[ k := Temporary ]s> W) in
    (std W) !! k = Some Revoked →
    isO p = false → isWL p = true →

    future_pub_mono C φ v -∗
    sts_full_world W C -∗
    region W C -∗
    k ↦ₖ v -∗
    φ (W',C, v) -∗
    rel C k p φ

    ={E}=∗

    region W' C
    ∗ sts_full_world W' C.
  Proof.
    intros Hlive.
    intro.
    iIntros (Hrev Hne Hpwl) "#HmonoV Hsts Hreg Hl #Hφ #Hrel".
    rewrite region_eq /region_def.
    iNamed "Hreg"; simplify_eq.
    iDestruct "Hmap" as "[%Hknown [Hheapfrag Hpreds]]".
    rewrite rel_eq /rel_def. iDestruct "Hrel" as (γ) "[HREL Hsaved]".
    iDestruct ( (reg_in C M) with "[$HREL $HM]") as %HMeq;eauto.
    rewrite /region_map_def HMeq big_sepM_insert; [|by rewrite lookup_delete_eq].
    iDestruct "Hpreds" as "[Hl' Hr]".
    iDestruct "Hl'" as (ρ Hl) "[Hstate Hresources]".
    iDestruct (sts_full_state_std with "Hsts Hstate") as %Hρ.
    rewrite Hrev in Hρ. inversion Hρ as [Hρrev]. subst.
    iMod (sts_update_std _ _ _ _ Temporary with "Hsts Hstate") as "[Hsts Hstate]".
    assert (related_sts_pub_world W (<s[k := Temporary ]s> W)) as Hrelated.
    { apply related_sts_pub_revoked_temp; auto. }
    assert (k ∈ dom (std W)) as Hin by (rewrite elem_of_dom Hrev; eauto).
    iDestruct (region_map_monotone _ _ _ _ _ Hrelated eq_refl with "[Hr Hheapfrag]") as "Hr".
    { rewrite /std_update /= dom_insert_L. by apply heap_keys_known_insert. }
    { iFrame "%∗". }
    assert (is_Some (M !! k)) as [x Hsome].
    { apply elem_of_dom. rewrite -Hdom. done. }
    iDestruct (region_map_delete with "Hr") as "Hr".
    iDestruct (region_map_insert _ _ _ _ _ Temporary with "Hr") as "Hr";auto.
    iDestruct "Hr" as "[%Hknown' [Hheapfrag Hr]]".
    iDestruct (big_sepM_delete _ _ k _ Hsome with "[Hl Hstate $Hr]") as "Hr".
    { iExists Temporary. iFrame. iSplitR;[iPureIntro;apply lookup_insert_eq|].
      iExists γ, p, φ. rewrite HMeq lookup_insert_eq in Hsome.
      inversion Hsome. iSplitR; first done. iFrame "%#".
      iApply heap_key_resource_live_intro; first exact Hlive.
      rewrite /region_std_interp Hpwl. iExists v. iFrame "%#∗".
    }
    subst W'.
    iFrame "Hsts".
    iExists M.
    rewrite -HMeq.
    iFrame "∗%".
    iPureIntro.
    apply insert_id in Hsome; rewrite -Hsome.
    apply insert_id in Hl; rewrite -Hl.
    split.
    - repeat rewrite dom_insert_L;rewrite Hdom;set_solver.
    - repeat rewrite insert_insert_eq dom_insert_L;rewrite Hdomρ;set_solver.
  Qed.

  Lemma update_region_revoked_temp_pwl E W C k p v φ `{∀ Wv, Persistent (φ Wv)}  :
    heap_key_live (heap_std W) k ->
    (std W) !! k = Some Revoked →
    isO p = false → isWL p = true →

    future_pub_mono C φ v -∗
    sts_full_world W C -∗
    region W C -∗
    k ↦ₖ v -∗
    φ (W,C,v) -∗
    rel C k p φ

    ={E}=∗

    region (<s[ k := Temporary ]s> W) C
    ∗ sts_full_world (<s[k := Temporary ]s>W) C.
  Proof.
    intros Hlive.
    iIntros (Hrev Hne Hpwl) "#HmonoV Hsts Hreg Hl #Hφ #Hrel".
    assert (related_sts_pub_world W (<s[k := Temporary ]s> W)) as Hrelated.
    { apply related_sts_pub_revoked_temp; auto. }
    iDestruct ("HmonoV" $! W ((<s[ k := Temporary ]s> W)) with "[] Hφ") as "Hφ'"; [done|].
    iApply (update_region_revoked_temp_pwl_updated with "HmonoV Hsts Hreg Hl Hφ' Hrel");auto.
  Qed.

  (* ---------------------------------------------------------------------------------------- *)
  (* ------------------- IF THΕ FULL STS IS REVOKED, WΕ CAN REVOKE REGION ------------------- *)
  (* ---------------------------------------------------------------------------------------- *)

  (* Note that Mρ by definition matches up with the full sts. Mρ starts out by being indirectly revoked *)
  Lemma monotone_revoke_region_def W C MC Mρ :
    ⌜dom (std W) = dom MC⌝
    -∗ sts_full_world (revoke W) C
    -∗ region_map_def W C MC Mρ
    -∗ sts_full_world (revoke W) C ∗ region_map_def (revoke W) C MC Mρ.
  Proof.
    iIntros (Hdom) "Hfull Hr".
    rewrite /revoke in Hdom |- *.
    destruct W as [ [Wstd_sta Wloc] W_heap ].
    iDestruct "Hr" as "[%Hknown [Hheapfrag Hr]]".
    iDestruct (big_sepM_exists with "Hr") as (m') "Hr".
    iDestruct (big_sepM2_sep with "Hr") as "[HMρ Hr]".
    iDestruct (big_sepM2_sep with "Hr") as "[Hstates Hr]".
    iAssert (∀ a ρ, ⌜m' !! a = Some ρ⌝ → ⌜ρ ≠ Temporary⌝)%I as %Hmonotemp.
    { iIntros (a ρ Hsome).
      iDestruct (big_sepM2_lookup_l _ _ _ a with "Hstates") as (γp) "[Hl Hstate]"; eauto.
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hρ.
      iPureIntro.
      eapply revoke_lookup_non_temp; eauto.
    }
    iFrame "Hfull".
    iSplit.
    { iPureIntro. eapply heap_keys_known_mono; [done| |exact Hknown].
      rewrite -revoke_dom_eq. set_solver. }
    iFrame "Hheapfrag". iApply big_sepM_exists. iExists m'.
    iApply big_sepM2_sep. iFrame.
    iDestruct (big_sepM2_sep with "[$Hstates $Hr]") as "Hr".
    iApply (big_sepM2_mono with "Hr").
    iIntros (a ρ γp Hm' HM) "/= [Hstate Ha]".
    specialize (Hmonotemp a ρ Hm').
    iDestruct "Ha" as (γpred p φ) "(%Hγp & %Hpers & #Hpred & Ha)".
    iFrame "Hstate". iExists γpred,p,φ. iFrame "%#".
    iApply (heap_key_resource_mono with "[] Ha"). iIntros "Ha".
    destruct ρ; cbn [region_std_interp]; first contradiction; last done.
    iDestruct "Ha" as (v Hne) "(Ha & #HmonoV & #Hφ)".
    iFrame "∗%#".
    iNext. iApply ("HmonoV" with "[] Hφ").
    iPureIntro. apply revoke_related_sts_priv_world.
  Qed.

  (* ---------------------------------------------------------------------------------------- *)
  (* ---------------- IF WΕ HAVE THE REGION, THEN WE CAN REVOKE THE FULL STS ---------------- *)
  (* ---------------------------------------------------------------------------------------- *)

  (* This matches the temprary resources in the map *)
  Definition temp_resources (W : WORLD) (C : CmptName) φ (a : LAddr) (p : Perm) : iProp Σ :=
    (∃ (v : LWord),
           ⌜isO p = false⌝
          ∗ a ↦ₖ v
          ∗ (if isWL p
             then future_pub_mono C φ v
             else (if isDL p then future_pub_mono C φ v else future_priv_mono C φ v))
          ∗ φ (W,C,v))%I.

  Definition close_addr_resources C W (a : LAddr) (is_later: bool) :=
    (∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝
                       ∗ (match heap_key_status (heap_std W) a with
                          | Some AllocObjectLive =>
                              if_later_P is_later (temp_resources W C φ a p)
                          | Some AllocObjectQuarantined => emp
                          | None => False
                          end)
                       ∗ rel C a p φ)%I.
  Definition close_list_resources C W (l : list LAddr) (is_later: bool) :=
   ([∗ list] a ∈ l, close_addr_resources C W a is_later)%I.

  (** [region_rel_get] for a key outside the open set. *)
  Lemma open_region_many_rel_get W C (s : list LAddr) (a : LAddr) :
    a ∉ s →
    std W !! a = Some Temporary →
    open_region_many W C s ∗ sts_full_world W C
    ==∗
    open_region_many W C s ∗ sts_full_world W C ∗
    ∃ p φ, ⌜∀ WCv, Persistent (φ WCv)⌝ ∗ rel C a p φ.
  Proof.
    iIntros (Hnin Hlookup) "[Hr Hsts]".
    rewrite open_region_many_eq /open_region_many_def.
    iNamed "Hr".
    iDestruct "Hmap" as "[%Hcovered [Hheap Hr]]".
    assert (is_Some (M !! a)) as [ [γ p] Hγp].
    { apply elem_of_dom. rewrite -Hdom elem_of_dom; eauto. }
    iMod (reg_get with "[$HM]") as "[HM Hrel]"; [eauto|].
    iDestruct (big_sepM_delete _ _ a with "Hr") as "[Hstate Hr]";
      [by rewrite lookup_delete_list_notin|].
    iDestruct "Hstate" as (ρ Ha) "[Hρ Hstate]".
    iDestruct "Hstate" as (γpred p' φ Heq Hpers) "(#Hsaved & Ha)".
    iDestruct (big_sepM_delete _ _ a with "[Hρ Ha $Hr]") as "Hr";
      [by rewrite lookup_delete_list_notin| |].
    { iExists ρ. iFrame "∗#%". }
    iModIntro. iSplitL "HM Hr Hheap".
    { iExists M, Mρ. iFrame "∗%". }
    iFrame "Hsts". iExists p, φ. iSplit; first done.
    rewrite rel_eq /rel_def. iExists γpred.
    simplify_eq. iFrame "Hsaved Hrel".
  Qed.

  (** Revoke the keys of [l] in a world open on [s], disjoint from [l],
      keeping the resources of the temporary keys [l']. *)
  Lemma monotone_revoke_list_sts_full_world_keep_open W C (l l' s : list LAddr) :
    ⊢ ⌜Forall (λ a, heap_key_live (heap_std W) a) l'⌝ → ⌜NoDup l'⌝ → ⌜NoDup l⌝ →
      ⌜l' ⊆+ l⌝ → ⌜l ## s⌝ →
    ([∗ list] a ∈ l', ⌜(std W) !! a = Some Temporary⌝)
    ∗ sts_full_world W C ∗ open_region_many W C s
    ==∗
    (sts_full_world (revoke_list l W) C
     ∗ open_region_many W C s
     ∗ close_list_resources C W l' true).
  Proof.
    rewrite /close_list_resources /close_addr_resources.
    iInduction (l) as [|x l] "IH" forall (l');
    iIntros (Hlive Hdup' Hdup Hsub Hdisj) "(#Hrel & Hfull & Hr)".
    - iFrame. apply submseteq_nil_r in Hsub as ->. repeat rewrite big_sepL_nil. done.
    - assert (x ∉ s ∧ l ## s) as [Hxs Hdisj'] by set_solver.
      destruct (decide (x ∈ l')) as [Hx_in|Hx_nin].
      + apply list_elem_of_split in Hx_in as [l1 [l2 Heq] ].
        rewrite Heq in Hsub.
        iRevert (Hsub Hdup Hdup' Hlive). rewrite Heq -Permutation_middle. iIntros (Hsub Hdup Hdup' Hlive).
        apply Forall_cons in Hlive as [Hlive_x Hlive_tail].
        apply NoDup_cons in Hdup as [Hnin Hdup].
        apply NoDup_cons in Hdup' as [Hnin' Hdup'].
        simpl. iDestruct "Hrel" as "[ Htemp Hrel]".
        iDestruct "Htemp" as %Htemp.
        iMod (open_region_many_rel_get with "[$Hfull $Hr]") as "(Hr & Hfull & #Hx)";
          [exact Hxs|apply Htemp|].
        iMod ("IH" with "[] [] [] [] [] [$Hrel $Hfull $Hr]") as "(Hfull & Hr & Hl)"; auto.
        { iPureIntro. apply submseteq_cons_l in Hsub as [k' [Hperm Hsub] ].
          apply Permutation.Permutation_cons_inv in Hperm. etrans;eauto. rewrite Hperm. done. }
        rewrite /revoke_list /= /=.
        rewrite Htemp.
        rewrite rel_eq /rel_def.
        rewrite open_region_many_eq /open_region_many_def.
        iNamed "Hr".
        iDestruct "Hmap" as "[%Hknown [Hheapfrag Hpreds]]".
        iDestruct "Hx" as (p' φ' Hpers) "Hx".
        iDestruct "Hx" as (γpred) "#(Hγpred & Hφ)".
        iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq; auto.
        assert (delete_list s M !! x = Some (γpred, p')) as HMx.
        { rewrite lookup_delete_list_notin // HMeq lookup_insert_eq //. }
        iDestruct (big_sepM_delete _ _ x with "Hpreds") as "[Ha Hpreds]"; first exact HMx.
        iDestruct "Ha" as (ρ Ha) "[Hstate Ha]".
        iDestruct (sts_full_state_std with "Hfull Hstate") as %Hlookup.
        simpl in Hlookup. rewrite revoke_list_not_elem_of_lookup in Hlookup; auto.
        rewrite Htemp in Hlookup. inversion Hlookup. subst ρ.
        iMod (sts_update_std _ _ _ _ (Revoked) with "Hfull Hstate") as "[Hfull Hstate]".
        iDestruct (region_map_delete with "[Hpreds Hheapfrag]") as "Hpreds".
        { iFrame "%∗". }
        iDestruct (region_map_insert _ _ _ _ _ Revoked with "Hpreds") as "Hpreds".
        iDestruct "Hpreds" as "[%Hknown' [Hheapfrag Hpreds]]".
        iDestruct (big_sepM_delete _ _ x (γpred, p') with "[$Hpreds Hstate]") as "Hpreds";
          first exact HMx.
        { iExists Revoked. iFrame "Hstate".
          iSplitR; [iPureIntro; apply lookup_insert_eq|].
          iExists γpred,p',φ'. iSplitR; first done. iFrame "%#".
          iApply heap_key_resource_live_intro; first exact Hlive_x. done. }
        iClear "IH". iFrame "∗ #".
        iModIntro. iSplitR "Ha".
        ++ iExists (<[x:=Revoked]> Mρ). rewrite delete_list_insert //. iFrame "∗%".
           iPureIntro. rewrite dom_insert_L.
           assert (x ∈ dom M) as Hin.
           { rewrite -Hdomρ. apply elem_of_dom. rewrite lookup_delete_list_notin // in Ha. eauto. }
           revert Hin Hdomρ. clear; intros Hin Hdomρ. rewrite Hdomρ. set_solver.
        ++ iSplitR;auto.
           iDestruct "Ha" as (γpred0 p0 φ0 Heq0 Hpers0) "(#Hsaved & Ha)".
           iDestruct (heap_key_resource_live_elim _ _ _ Hlive_x with "Ha") as "Ha".
           iDestruct "Ha" as (v Hne0) "(Hx & #HmonoV & #Hφ0)"; simplify_eq.
           rewrite /heap_key_live in Hlive_x. rewrite Hlive_x.
           iExists v; iFrame "%∗".
           destruct W as [ [ Wstd_sta Wloc] W_heap ].
           iDestruct (saved_pred_agree _ _ _ _ _ (Wstd_sta, Wloc, W_heap, C, v) with "Hφ Hsaved") as "#Hφeq". iFrame.
           iDestruct (internal_eq_iff with "Hφeq") as "Hφeq'".
           iSplitL "HmonoV";[|by iNext; iApply "Hφeq'"].
           all: destruct (isWL p0).
           +++ iApply future_pub_mono_eq_pred; auto.
           +++ destruct (isDL p0).
               ++++ iApply future_pub_mono_eq_pred; auto.
               ++++ iApply future_priv_mono_eq_pred; auto.
      + apply NoDup_cons in Hdup as [Hnin Hdup].
        apply submseteq_cons_r in Hsub as [Hsub | [l'' [Hcontr _] ] ].
        2: { exfalso. apply Hx_nin. rewrite Hcontr. apply list_elem_of_here. }
        iMod ("IH" with "[] [] [] [] [] [$Hrel $Hfull $Hr]") as "(Hfull & Hr & Hl)"; auto.
        rewrite open_region_many_eq /open_region_many_def.
        iNamed "Hr".
        iDestruct "Hmap" as "[%Hknown [Hheapfrag Hr]]".
        iClear "IH".
        rewrite /revoke_list /=. destruct W as [ [ [ Wstd_sta Wloc] Wseals] W_heap ].
        destruct (Wstd_sta !! x) as [ρx|] eqn:Hsome.
        2: { iFrame. iModIntro. rewrite Hsome. iFrame. iFrame. auto. }
        rewrite Hsome.
        destruct (decide (ρx = Temporary)) as [Hρx|Hρx].
        2: { destruct ρx; try contradiction; iFrame; iModIntro; iFrame; auto. }
        assert (is_Some (M !! x)) as [γp Hsomea].
        { apply elem_of_dom. rewrite -Hdom. rewrite elem_of_dom. eauto. }
        assert (delete_list s M !! x = Some γp) as HMx.
        { rewrite lookup_delete_list_notin //. }
        iDestruct (big_sepM_delete _ _ x with "Hr") as "[Hx Hr]"; first exact HMx.
        iDestruct "Hx" as (ρ Ha) "[Hstate Hρ]".
        iDestruct (sts_full_state_std with "Hfull Hstate") as %Hlookup.
        iMod (sts_update_std _ _ _ _ (Revoked) with "Hfull Hstate") as "[Hfull Hstate]".
        iDestruct (region_map_delete with "[Hr Hheapfrag]") as "Hpreds".
        { iFrame "%∗". }
        simplify_map_eq.
        simpl in *. rewrite revoke_list_not_elem_of_lookup in Hlookup;auto.
        rewrite Hlookup in Hsome. inversion Hsome. subst.
        iDestruct (region_map_insert _ _ _ _ _ Revoked with "Hpreds") as "Hpreds".
        iDestruct "Hpreds" as "[%Hknown' [Hheapfrag Hpreds]]".
        iDestruct (big_sepM_delete _ _ x with "[Hstate $Hpreds Hρ]") as "Hr"; first exact HMx.
        { iExists Revoked; iSplitR; first (by iPureIntro ; simplify_map_eq).
          iFrame.
          iDestruct "Hρ" as (γpred p φ Hγp Hpers) "[#Hsaved Haddr]".
          iExists γpred,p,φ. iFrame "%#".
          iApply (heap_key_resource_mono with "[] Haddr"). iIntros "_". done.
        }
        iModIntro. iFrame.
        iExists (<[x:=Revoked]> Mρ). rewrite delete_list_insert //. iFrame "∗%".
        iPureIntro. rewrite dom_insert_L.
        assert (x ∈ dom M) as Hin.
        { rewrite -Hdomρ. apply elem_of_dom. rewrite lookup_delete_list_notin // in Ha. eauto. }
        revert Hin Hdomρ. clear; intros Hin Hdom. rewrite Hdom. set_solver.
  Qed.

  Lemma monotone_revoke_list_sts_full_world_keep W C (l : list LAddr) (l' : list LAddr) :
    ⊢ ⌜Forall (λ a, heap_key_live (heap_std W) a) l'⌝ → ⌜NoDup l'⌝ → ⌜NoDup l⌝ → ⌜l' ⊆+ l⌝ →
    ([∗ list] a ∈ l', ⌜(std W) !! a = Some Temporary⌝)
    ∗ sts_full_world W C ∗ region W C
    ==∗
    (sts_full_world (revoke_list l W) C
     ∗ region W C
     ∗ close_list_resources C W l' true).
  Proof.
    iIntros (Hlive Hdup' Hdup Hsub) "(Hl & Hfull & Hr)".
    iMod (monotone_revoke_list_sts_full_world_keep_open _ _ _ _ []
            with "[] [] [] [] [] [$Hl $Hfull Hr]") as "(Hfull & Hr & Hl)"; auto.
    { iPureIntro. apply disjoint_nil_r. }
    { by iApply region_open_nil. }
    iModIntro. iFrame. by iApply region_open_nil.
  Qed.

  Lemma monotone_revoke_sts_full_world_keep W C (l : list LAddr)
     :
    Forall (λ a, heap_key_live (heap_std W) a) l ->
    ⌜NoDup l⌝ -∗
    ([∗ list] a ∈ l, ⌜(std W) !! a = Some Temporary⌝)
    ∗ sts_full_world W C ∗ region W C
    ==∗
    (sts_full_world (revoke W) C
     ∗ region W C
     ∗ close_list_resources C W l true).
  Proof.
    intros Hlive.
    iIntros (Hdup) "(Hl & Hfull & Hr)".
    rewrite revoke_list_dom.
    iAssert (⌜l ⊆+ (map_to_list (std W)).*1⌝)%I as %Hsub.
    { iClear "Hfull Hr". clear Hlive. iInduction l as [| x l] "IH".
      - iPureIntro. apply submseteq_nil_l.
      - iDestruct "Hl" as "[ Hin Hl]".
        iDestruct "Hin" as %Hin. apply NoDup_cons in Hdup as [Hnin Hdup].
        iDestruct ("IH" with "[] Hl") as %Hsub; auto.
        iPureIntro.
        assert (x ∈ (map_to_list (std W)).*1) as Helem.
        { apply map_to_list_fst. exists Temporary. by apply elem_of_map_to_list. }
        apply elem_of_Permutation in Helem as [l' Hl']. rewrite Hl'.
        apply submseteq_skip. revert Hsub. rewrite Hl'; intros Hsub.
        apply submseteq_cons_r in Hsub as [Hsub | [l'' [Heq _] ] ]; auto.
        assert (countable.encode x ∈ countable.encode <$> l) as Hcontr.
        { rewrite Heq. apply list_elem_of_here. }
        apply list_elem_of_fmap_1 in Hcontr as [y [Hxy Hy] ].
        apply encode_inj in Hxy. subst. contradiction.
    }
    iMod (monotone_revoke_list_sts_full_world_keep _ _ (map_to_list (std W)).*1 l
            with "[] [] [] [] [$Hl $Hfull $Hr]") as "(Hfull & Hr & Hi)"; auto.
    { iPureIntro. apply (NoDup_fst_map_to_list (M:=gmap LAddr) (A:=region_type)). }
    by iFrame.
  Qed.

  (* ---------------------------------------------------------------------------------------- *)
  (* ------------------------- REVOCATION OF A WORLD OPEN ON SOME KEYS ---------------------- *)
  (* ---------------------------------------------------------------------------------------- *)

  (** Revoking the keys outside [s], then sending the keys of [s] to
      Revoked, revokes the world when the keys of [s] are Temporary. *)
  Lemma revoke_list_std_update_keys_revoke W (s : list LAddr) :
    Forall (λ k, std W !! k = Some Temporary) s →
    std_update_keys (revoke_list (filter (λ a, a ∉ s) (map_to_list (std W)).*1) W) s Revoked
    = revoke W.
  Proof.
    intros Htemps.
    assert (∀ W', std_update_keys W' s Revoked
                  = (std (std_update_keys W' s Revoked), cus W', seal_std W', heap_std W'))
      as Hshape.
    { clear Htemps. intros W'. induction s as [|k s IH].
      - by destruct W' as [ [ [] ] ].
      - cbn [std_update_keys]. rewrite /std_update IH //. }
    rewrite Hshape /revoke /revoke_list /=.
    do 3 f_equal.
    apply (map_eq (M:=gmap LAddr)). intros i.
    destruct (decide (i ∈ s)) as [His|His].
    - rewrite std_update_keys_lookup_in //.
      rewrite /revoke_std_sta lookup_fmap.
      rewrite Forall_forall in Htemps. rewrite Htemps //.
    - rewrite std_update_keys_lookup_same //=.
      rewrite revoke_list_std_sta_spec /revoke_std_sta lookup_fmap.
      destruct (std W !! i) as [ρ|] eqn:Hi; last by rewrite /= Hi.
      rewrite Hi /=.
      destruct (in_dec LAddr_eq_dec i _) as [_|Hnin]; first by destruct ρ.
      exfalso. apply Hnin. apply list_elem_of_In, list_elem_of_filter. split; first done.
      apply map_to_list_fst. exists ρ. by apply elem_of_map_to_list.
  Qed.

  (** Update the state of every key of [s], whose fragments we own. *)
  Lemma sts_update_std_keys W C (s : list LAddr) (Φ : LAddr → iProp Σ) ρ ρ' :
    sts_full_world W C -∗
    ([∗ list] k ∈ s, Φ k ∗ sts_state_std C k ρ)
    ==∗
    sts_full_world (std_update_keys W s ρ') C ∗
    ([∗ list] k ∈ s, Φ k ∗ sts_state_std C k ρ') ∗
    ⌜Forall (λ k, std W !! k = Some ρ) s⌝.
  Proof.
    induction s as [|k s IH]; iIntros "Hfull Hs".
    - by iFrame.
    - iDestruct "Hs" as "[[HΦ Hst] Hs]".
      iDestruct (sts_full_state_std with "Hfull Hst") as %Hk.
      iMod (IH with "Hfull Hs") as "(Hfull & Hs & %Hs)".
      iMod (sts_update_std _ _ _ _ ρ' with "Hfull Hst") as "[Hfull Hst]".
      iModIntro. iFrame. iPureIntro. by apply Forall_cons.
  Qed.

  (** Put back an open key as a Revoked entry: a Revoked entry holds nothing. *)
  Lemma open_region_many_close_revoked W C (s : list LAddr) (k : LAddr) (p : Perm) φ
    `{Hpers : ∀ WCv, Persistent (φ WCv)} :
    heap_key_live (heap_std W) k →
    k ∉ s →
    open_region_many W C (k :: s) -∗
    sts_state_std C k Revoked -∗
    rel C k p φ -∗
    open_region_many W C s.
  Proof.
    iIntros (Hlive Hnin) "Hr Hst Hrel".
    rewrite open_region_many_eq /open_region_many_def rel_eq /rel_def.
    iNamed "Hr".
    iDestruct "Hrel" as (γpred) "#[HREL Hsaved]".
    iDestruct (reg_in C M with "[$HM $HREL]") as %HMeq.
    iDestruct "Hmap" as "[%Hknown [Hheap Hpreds]]".
    assert (k ∈ dom M) as Hk.
    { rewrite HMeq dom_insert_L. set_solver. }
    iExists M, (<[k:=Revoked]> Mρ). iFrame "HM".
    iSplit; first done.
    iSplit.
    { iPureIntro. rewrite dom_insert_L Hdomρ. set_solver. }
    rewrite /region_map_def. iSplit; first done. iFrame "Hheap".
    rewrite delete_list_insert //.
    iApply (big_sepM_delete _ _ k (γpred, p)).
    { rewrite lookup_delete_list_notin // HMeq lookup_insert_eq //. }
    iSplitL "Hst".
    { iExists Revoked. iSplit; first (iPureIntro; apply lookup_insert_eq).
      iFrame "Hst". iExists γpred, p, φ.
      iSplit; first done. iSplit; first done. iFrame "Hsaved".
      by iApply heap_key_resource_live_intro. }
    iApply (big_sepM_mono with "Hpreds").
    iIntros (k' γp Hk') "(%ρ & %Hρ & Hrest)".
    iExists ρ. iFrame "Hrest". iPureIntro. cbn [delete_list] in Hk', Hρ.
    apply lookup_delete_Some in Hk' as [Hne _].
    rewrite lookup_insert_ne //. rewrite lookup_delete_ne in Hρ; done.
  Qed.

  Lemma open_region_many_close_revoked_list W C (s : list LAddr) :
    Forall (λ k, heap_key_live (heap_std W) k) s →
    NoDup s →
    open_region_many W C s -∗
    ([∗ list] k ∈ s,
       (∃ p φ, ⌜∀ WCv, Persistent (φ WCv)⌝ ∗ rel C k p φ) ∗
       sts_state_std C k Revoked) -∗
    region W C.
  Proof.
    induction s as [|k s IH]; intros Hlive Hdup; iIntros "Hr Hs".
    - by iApply region_open_nil.
    - apply Forall_cons in Hlive as [Hlive_k Hlive].
      apply NoDup_cons in Hdup as [Hnin Hdup].
      iDestruct "Hs" as "[[(%p & %φ & %Hpers & Hrel) Hst] Hs]".
      iApply (IH with "[Hr Hst Hrel] Hs"); [done|done|].
      iApply (open_region_many_close_revoked with "Hr Hst Hrel"); done.
  Qed.

  (** Revoke a world open on [s], taking back the state fragments and the
      [rel]s of the open keys, which the opening returns. The resources of
      the temporary keys [l] are kept. *)
  Lemma monotone_revoke_keep_open W C (l s : list LAddr) :
    Forall (λ a, heap_key_live (heap_std W) a) (l ++ s) →
    NoDup (l ++ s) →
    ([∗ list] a ∈ l, ⌜std W !! a = Some Temporary⌝) ∗
    ([∗ list] k ∈ s, ∃ p φ, ⌜∀ WCv, Persistent (φ WCv)⌝ ∗
                            rel C k p φ ∗ sts_state_std C k Temporary) ∗
    sts_full_world W C ∗
    open_region_many W C s
    ==∗
    sts_full_world (revoke W) C ∗
    region (revoke W) C ∗
    close_list_resources C W l true ∗
    ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) (l ++ s)⌝.
  Proof.
    intros Hlive Hdup.
    iIntros "(Hl & Hs & Hfull & Hr)".
    apply Forall_app in Hlive as [Hlive_l Hlive_s].
    apply NoDup_app in Hdup as (Hdup_l & Hdisj & Hdup_s).
    iAssert (⌜Forall (λ a, std W !! a = Some Temporary) l⌝)%I as %Htemps_l.
    { iDestruct (big_sepL_forall with "Hl") as %Htemps.
      iPureIntro. apply Forall_lookup. done. }
    iAssert ([∗ list] k ∈ s,
               (∃ p φ, ⌜∀ WCv, Persistent (φ WCv)⌝ ∗ rel C k p φ) ∗
               sts_state_std C k Temporary)%I with "[Hs]" as "Hs".
    { iApply (big_sepL_mono with "Hs").
      iIntros (i k Hk) "(%p & %φ & %Hpers & Hrel & Hst)".
      iFrame "Hst". iExists p, φ. by iFrame "Hrel". }
    (* Revoke the keys outside [s], whose entries are in the open map *)
    set (L := filter (λ a, a ∉ s) (map_to_list (std W)).*1).
    iMod (monotone_revoke_list_sts_full_world_keep_open _ _ L l s
           with "[] [] [] [] [] [$Hl $Hfull $Hr]") as "(Hfull & Hr & Hl)".
    { done. }
    { done. }
    { iPureIntro. apply NoDup_filter, (NoDup_fst_map_to_list (M:=gmap LAddr)). }
    { iPureIntro. apply NoDup_submseteq; first done.
      intros a Ha. apply list_elem_of_filter. split; first by apply Hdisj.
      apply map_to_list_fst. exists Temporary. apply elem_of_map_to_list.
      rewrite Forall_forall in Htemps_l. by apply Htemps_l. }
    { iPureIntro. intros a Ha Has. apply list_elem_of_filter in Ha as [Ha _]. done. }
    (* Revoke the keys of [s] with their fragments *)
    iMod (sts_update_std_keys _ _ _ _ _ Revoked with "Hfull Hs") as "(Hfull & Hs & %Htemps_s)".
    assert (Forall (λ k, std W !! k = Some Temporary) s) as Htemps_s'.
    { apply Forall_forall. intros k Hk.
      rewrite Forall_forall in Htemps_s. specialize (Htemps_s k Hk). cbn in Htemps_s.
      rewrite revoke_list_not_elem_of_lookup in Htemps_s; first done.
      intros HkL. apply list_elem_of_filter in HkL as [HkL _]. done. }
    rewrite revoke_list_std_update_keys_revoke; last done.
    (* Put the keys of [s] back as Revoked entries, then revoke the map *)
    iDestruct (open_region_many_close_revoked_list with "Hr Hs") as "Hr"; [done|done|].
    rewrite region_eq /region_def.
    iNamed "Hr".
    iDestruct (monotone_revoke_region_def with "[] [$Hfull] [$Hmap]") as "[Hfull Hpreds]"; auto.
    iModIntro. iFrame. iSplitR.
    - iPureIntro.
      rewrite /revoke in Hdom |- *.
      repeat (split;auto).
      by rewrite -revoke_dom_eq.
    - iPureIntro. apply Forall_app. split.
      all: eapply Forall_impl; [done|]; cbn.
      all: intros a Ha; by apply revoke_lookup_Monotemp.
  Qed.

  (* revoke and keep temp resources in list l, with unknown p and φ *)
  Lemma monotone_revoke_keep W C l
     :
    Forall (λ a, heap_key_live (heap_std W) a) l ->
    NoDup l ->
    ([∗ list] a ∈ l, ⌜(std W) !! a = Some Temporary⌝)
    ∗ sts_full_world W C
    ∗ region W C
    ==∗
    sts_full_world (revoke W) C
    ∗ region (revoke W) C
    ∗ close_list_resources C W l true
    ∗ ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) l⌝.
  Proof.
    intros Hlive.
    iIntros (Hdup) "(Hl & HW & Hr)".
    iMod (monotone_revoke_keep_open _ _ l []
            ltac:(by rewrite app_nil_r) ltac:(by rewrite app_nil_r)
           with "[$Hl $HW Hr]") as "(HW & Hr & Hl & %Hrevoked)".
    { iSplitR; first done. by iApply region_open_nil. }
    iModIntro. iFrame. by rewrite app_nil_r in Hrevoked.
  Qed.



  (* ---------------------------------------------------------------------------------------- *)
  (* ----------------- REVOKING ALL TEMPORARY REGIONS, KNOWN AND UNKNOWN  ------------------- *)
  (* ---------------------------------------------------------------------------------------- *)

  (* The following helper lemmas are for revoking all temporary regions in the world *)

  (* However, we also want to be able to close regions that were valid in some world W, and which will be valid again
     in a public future world close l W' ! This is slightly more tricky: we must first update the region monotonically,
     after which it will be possible to consolidate the full_sts and region *)

  Lemma region_rel_dom W C a p φ :
    region W C -∗
    rel C a p φ -∗
    region W C ∗ ⌜a ∈ dom (std W)⌝.
  Proof.
    rewrite region_eq /region_def rel_eq /rel_def.
    iIntros "@ (%γ & #Hrel & _)".
    iDestruct (reg_in C M a γ p with "[$HM $Hrel]") as %HMeq.
    iSplitL; first by iExists M, Mρ; iFrame "%∗".
    iPureIntro. rewrite Hdom HMeq dom_insert_L. set_solver.
  Qed.

  Lemma close_list_consolidate_resources W C (l' l : list LAddr) :
    ⊢ ⌜l' ⊆+ l⌝ →
    (region (close_list l W) C
     ∗ sts_full_world W C
     ∗ close_list_resources C (close_list l W) l' false
       )
      ==∗
      (sts_full_world (close_list l' W) C
       ∗ region (close_list l W) C).
  Proof.
    rewrite /close_list_resources.
    iIntros (Hsub) "(Hr & Hsts & Htemps)".
    iInduction l' as [|x l'] "IH".
    - simpl. iFrame. done.
    - iDestruct "Htemps" as "[Hx Htemps]".
      assert (l' ⊆+ l) as Hsub'.
      { apply submseteq_cons_l in Hsub as [k [Hperm Hsub] ]. rewrite Hperm.
        apply submseteq_cons_r. left. auto. }
      iMod ("IH" $! Hsub' with "Hr Hsts Htemps") as "[Hsts Hr]".
      iClear "IH".
      rewrite /close_list /close_list /close_list_std_sta /=.
      iDestruct "Hx" as (p φ Hpers) "(Hres & #Hrel)".
      iAssert (∀ P : iProp Σ,
        heap_key_resource (heap_std (close_list l W)) x P -∗
        heap_key_resource (heap_std (close_list l W)) x
          (region_std_interp (close_list l W) C x p φ Temporary))%I
        with "[Hres]" as "Hrestore".
      { iIntros (P) "Haddr".
        destruct (heap_key_status (heap_std (close_list l W)) x) as [status|] eqn:Hstatus.
        - iEval (rewrite Hstatus) in "Hres".
          destruct status.
          + iClear "Haddr".
            iDestruct "Hres" as (v) "(%Hp & Ha & #Hmono & Hφ)".
            iApply heap_key_resource_live_intro; first exact Hstatus.
            cbn [region_std_interp]. iExists v.
            iFrame "Ha Hmono %". iNext. iExact "Hφ".
          + by iApply (heap_key_resource_quarantined_irrel with "Haddr").
        - iEval (rewrite Hstatus) in "Hres".
          iDestruct "Hres" as "[]". }
      destruct (std W !! x) eqn:Hsome;[|iFrame;done].
      destruct (decide (Revoked = r)).
      + subst.
        assert (x ∈ l) as Hinl.
        { apply elem_of_submseteq with (x:=x) in Hsub;[auto|apply elem_of_cons;by left]. }
        rewrite region_eq /region_def /region_map_def.
        iNamed "Hr".
        iDestruct "Hmap" as "[%Hknown [Hheapfrag Hr]]".
        rewrite rel_eq /rel_def.
        iDestruct "Hrel" as (γpred) "#[Hrel Hsaved]".
        iDestruct (reg_in C M x γpred p with "[$HM $Hrel]") as %HMeq. rewrite HMeq.
        iDestruct (big_sepM_delete _ _ x with "Hr") as "[Hx Hr]";[apply lookup_insert_eq|].
        rewrite delete_insert_id;[|apply lookup_delete_eq].
        iDestruct "Hx" as (ρ Hx) "[Hstate Hx]".
        iDestruct "Hx" as (γpred' p' φ' Heq Hpers') "(_ & Haddr)".
        iMod (sts_update_std _ _ _ _ Temporary with "Hsts Hstate") as "[Hsts Hstate]".
        rewrite HMeq.
        iDestruct (region_map_delete with "[Hr Hheapfrag]") as "Hr".
        { iFrame "%∗". }
        iDestruct (region_map_insert _ C _ _ x Temporary with "Hr") as "Hr"; auto.
        iDestruct "Hr" as "[%Hknown' [Hheapfrag Hr]]".
        iDestruct (big_sepM_delete _ _ x with "[ Haddr Hrestore Hstate $Hr]") as "Hr"
        ;[apply lookup_insert_eq|..].

        { iExists Temporary. iFrame. rewrite lookup_insert_eq. iSplit;auto. iExists γpred,p,φ. iSplitR; first done. iFrame "%#".
          iApply ("Hrestore" with "Haddr").
        }
        iFrame.
        rewrite -!HMeq /std_update /=.
        iFrame.
        iModIntro.
        repeat (iSplit; auto).
        iPureIntro. rewrite dom_insert_L. rewrite -Hdomρ.
        assert (x ∈ dom  Mρ);[apply elem_of_dom;eauto|]. set_solver.
      + iFrame; done.
  Qed.

  Lemma heap_key_live_back_quarantined h h' a :
    related_sts_heap_std h h' ->
    heap_key_status h a = Some AllocObjectQuarantined ->
    heap_key_live h' a ->
    False.
  Proof.
    intros Hrelated Hquarantined Hlive.
    destruct (heap_key_status_future _ _ _ _ Hrelated Hquarantined) as (s' & Hs' & Hq).
    rewrite /heap_key_live Hs' in Hlive. specialize (Hq eq_refl). congruence.
  Qed.

  Lemma close_list_resources_mono_pub_live W W' C l :
    related_sts_pub_world W W' ->
    Forall (λ a, heap_key_live (heap_std W') a) l ->
    close_list_resources C W l false -∗
    close_list_resources C W' l false.
  Proof.
    iIntros (Hrelated Hlive) "Hres".
    rewrite /close_list_resources.
    iApply (big_sepL_impl with "Hres").
    iIntros "!> %k %a %Ha (%p & %φ & %Hpers & Htemp & Hrel)".
    iExists p, φ. iFrame "Hrel". iSplit; first done.
    assert (heap_key_live (heap_std W') a) as Hlive_a.
    { rewrite Forall_lookup in Hlive. eauto. }
    unfold heap_key_live in Hlive_a. rewrite Hlive_a.
    destruct (heap_key_status (heap_std W) a) as [status|] eqn:Hstatus.
    - destruct status; last first.
      { exfalso. eapply heap_key_live_back_quarantined;
          [exact (proj2 (proj2 (proj2 Hrelated)))|exact Hstatus|exact Hlive_a]. }
      iDestruct "Htemp" as (v) "(%Hp & Ha & #Hmono & Hφ)".
      iExists v. iFrame "Ha Hmono %".
      destruct (isWL p); last destruct (isDL p);
      iApply ("Hmono" with "[] Hφ").
    all: try (iPureIntro; exact Hrelated).
    iPureIntro. by apply related_sts_pub_priv_world.
    - iDestruct "Htemp" as "[]".
  Qed.

  Lemma monotone_close_list_region_resources W W' C (l : list LAddr)
     :
    ⊢ sts_full_world W' C
     ∗ region W' C
     ∗ close_list_resources C (close_list l W') l false
     ==∗
     (sts_full_world (close_list l W') C
      ∗ region (close_list l W') C
     ).
  Proof.
    iIntros "(Hsts & Hr & Htemp)".
    assert (related_sts_pub_world W' (close_list l W')) as Hrelated'.
    { apply close_list_related_sts_pub; auto. }
    assert (dom (std W') = dom (std (close_list l W'))) as Heq.
    { rewrite /close_list.
      apply close_list_dom_eq. }
    iDestruct (region_monotone with "Hr") as "Hr";[apply Heq|apply Hrelated'|symmetry; apply close_list_heap| ].
    iMod (close_list_consolidate_resources _ _ l l with "[] [$Hr $Hsts Htemp]") as "[Hsts Hr]"
    ;[auto|eauto|iFrame;done].
  Qed.



  Lemma monotone_close_list_region W W' C (l : list LAddr)
     :
    Forall (λ a, heap_key_live (heap_std W') a) l ->
    ⊢ ⌜related_sts_pub_world W (close_list l W')⌝ -∗
     sts_full_world W' C
     ∗ region W' C
     ∗ (close_list_resources C W l false)
     ==∗
     (sts_full_world (close_list l W') C
      ∗ region (close_list l W') C
     ).
  Proof.
    intros Hlive.
    iIntros (Hrelated) "(Hsts & Hr & Htemp)".
    iApply (monotone_close_list_region_resources W W' C l); iFrame.
    iApply (close_list_resources_mono_pub_live W (close_list l W') C l
      with "Htemp").
    - exact Hrelated.
    - by rewrite close_list_heap.
  Qed.


  (* ---------------------------------------------------------------- *)
  (* ----------------- UPDATE OF A REVOKED WORLD  ------------------- *)
  (* ---------------------------------------------------------------- *)

  Lemma monotone_revoke_region_def_update_loc W W' C MC Mρ  :
    heap_std W = heap_std W' ->
    ⌜revoke_condition W⌝
    -∗ ⌜dom (std W) = dom MC⌝
    -∗ ⌜std W = std W'⌝
    -∗ ⌜related_sts_priv_world W W' ⌝
    -∗ sts_full_world W' C
    -∗ region_map_def W C MC Mρ
    -∗ sts_full_world W' C ∗ region_map_def W' C MC Mρ.
  Proof.
    intros Hheap.
    iIntros (Hrevoked Hdom Hstd Hrelated) "Hfull Hr".
    rewrite /revoke in Hdom |- *.
    destruct W as [ [ [Wstd_sta Wloc] Wseals] W_heap ].
    iDestruct "Hr" as "[%Hknown [Hheapfrag Hr]]".
    iDestruct (big_sepM_exists with "Hr") as (m') "Hr".
    iDestruct (big_sepM2_sep with "Hr") as "[HMρ Hr]".
    iDestruct (big_sepM2_sep with "Hr") as "[Hstates Hr]".
    iAssert (∀ a ρ, ⌜m' !! a = Some ρ⌝ → ⌜ρ ≠ Temporary⌝)%I as %Hmonotemp.
    { iIntros (a ρ Hsome).
      iDestruct (big_sepM2_lookup_l _ _ _ a with "Hstates") as (γp) "[Hl Hstate]"; eauto.
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hρ.
      iPureIntro.
      cbn in *; simplify_eq.
      rewrite /revoke_condition /= in Hrevoked.
      specialize (Hrevoked a); rewrite Hρ in Hrevoked.
      by intros ->.
    }
    iFrame "Hfull".
    iSplit.
    { iPureIntro. rewrite -Hheap -Hstd. exact Hknown. }
    iSplitL "Hheapfrag". { rewrite -Hheap. iFrame. }
    iApply big_sepM_exists. iExists m'.
    iApply big_sepM2_sep. iFrame.
    iDestruct (big_sepM2_sep with "[$Hstates $Hr]") as "Hr".
    iApply (big_sepM2_mono with "Hr").
    iIntros (a ρ γp Hm' HM) "/= [Hstate Ha]".
    specialize (Hmonotemp a ρ Hm').
    iDestruct "Ha" as (γpred p φ) "(%Hγp & %Hpers & #Hpred & Ha)".
    iFrame "Hstate". iExists γpred,p,φ. iFrame "%#".
    rewrite -Hheap.
    iApply (heap_key_resource_mono with "[] Ha"). iIntros "Ha".
    destruct ρ; cbn [region_std_interp]; first contradiction; last done.
    iDestruct "Ha" as (v Hne) "(Ha & #HmonoV & #Hφ)".
    iFrame "∗%#".
    iNext. iApply ("HmonoV" with "[] Hφ").
    iPureIntro. apply Hrelated.
  Qed.

  Lemma update_region_revoked_update_loc E W W' C  :
    heap_std W = heap_std W' ->
    revoke_condition W →
    std W = std W' →
    (related_sts_priv_world W W') →
    sts_full_world W' C -∗
    region W C

    ={E}=∗

    region W' C
    ∗ sts_full_world W' C.
  Proof.
    intros Hheap.
    intros Hrevoked Hstd Hrelated.
    iIntros "Hsts Hreg".
    rewrite region_eq /region_def.
    iNamed "Hreg"; simplify_eq.
    iDestruct (monotone_revoke_region_def_update_loc _ _ _ _ _ Hheap with "[] [] [] [] [$] [$]") as "[Hsts Hpreds]"; eauto.
    rewrite Hstd in Hdom.
    iFrame; eauto.
  Qed.






  (** Obtain that an address is Revoked if we own the points-to *)
   Lemma revoked_by_separation
     (W : WORLD) (C : CmptName)
     (a : LAddr) (w : LWord) :
     heap_key_live (heap_std W) a ->
     a ∈ dom (std W) →
     region W C
     ∗ sts_full_world W C
     ∗ laddr_addr a ↦ₐ w
     ==∗
     region W C
     ∗ sts_full_world W C
     ∗ laddr_addr a ↦ₐ w
     ∗ ⌜ std W !! a = Some Revoked ⌝
   .
   Proof.
     intros Hlive.
     iIntros (Hstd_a) "(Hregion & Hworld & Ha)".
     rewrite region_eq /region_def.
     iNamed "Hregion".
     rewrite /region_map_def.
     iDestruct "Hmap" as "[%Hknown [Hheapfrag Hr]]".
     assert (is_Some (M !! a)) as [ [γ p] Hγp].
     { apply elem_of_dom. rewrite -Hdom. auto. }
     iMod (reg_get with "[$HM]") as "[HM Hrel]";[eauto|].
     iDestruct (big_sepM_delete _ _ a with "Hr") as "[Hstate Hr]";[eauto|].
     iDestruct "Hstate" as (ρ Ha) "[Hρ Hstate]".
     iDestruct (sts_full_state_std with "Hworld Hρ") as %Hx''; simplify_eq.
     iDestruct "Hstate" as (γ' p' φ) "(% & % & Hφ & Hstate)"; simplify_eq.
     iFrame "Hworld".
     iAssert ( ⌜ ρ = Revoked ⌝ )%I as "%" ; last iFrame "%".
     {
       iDestruct (heap_key_resource_live_elim _ _ _ Hlive with "Hstate") as "Hstate".
       destruct ρ; last done; iExFalso.
       - iDestruct "Hstate" as (v) "(% & Ha' & _)"; simplify_eq.
         iDestruct (key_pointsto_eq with "Ha'") as "[Ha' _]".
         iApply (addr_dupl_false with "[$] [$]"); eauto.
       - iDestruct "Hstate" as (v) "(% & Ha' & _)"; simplify_eq.
         iDestruct (key_pointsto_eq with "Ha'") as "[Ha' _]".
         iApply (addr_dupl_false with "[$] [$]"); eauto.
     }
     iDestruct (big_sepM_delete _ _ a with "[Hρ Hφ Hstate $Hr]") as "Hr";[eauto| |].
     { iFrame "∗%"; done. }
     simplify_eq.
     by iFrame "%∗".
   Qed.

   Lemma revoked_by_separation_many
     (W : WORLD) (C : CmptName)
     (la : list LAddr) (lw : list LWord) :
     Forall (heap_key_live (heap_std W)) la ->
     Forall (λ a, a ∈ dom (std W)) la →
     region W C
     ∗ sts_full_world W C
     ∗ ([∗ list] a;w ∈ la;lw, laddr_addr a ↦ₐ w)
     ==∗
     region W C
     ∗ sts_full_world W C
     ∗ ([∗ list] a;w ∈ la;lw, laddr_addr a ↦ₐ w)
     ∗ ⌜ Forall (λ a, std W !! a = Some Revoked) la⌝
   .
   Proof.
     generalize dependent lw.
     induction la; iIntros (lw Hlive Hla) "(Hregion & Hworld & Hla)".
     - iFrame; done.
     - apply Forall_cons_1 in Hlive as [Hlive_a Hlive_tail].
       iDestruct (big_sepL2_length with "Hla") as "%Hlen_lw".
       destruct lw as [|w lw]; first (cbn in Hlen_lw ; congruence).
       rewrite big_sepL2_cons.
       iDestruct "Hla" as "[Ha Hla]".
       apply Forall_cons_iff in Hla.
       destruct Hla as [Ha Hla].
       iMod (IHla with "[$Hregion $Hworld $Hla]")
         as "(Hregion & Hworld & Hla & %Hforall_la)"; eauto.
       iMod (revoked_by_separation _ _ a with "[$Hregion $Hworld $Ha]")
         as "(Hregion & Hworld & Ha & %Hforall_a)"; eauto; simplify_eq.
       rewrite Forall_cons_iff.
       iFrame; done.
   Qed.

  Lemma revoked_by_separation_with_temp_resources W W' C a :
     heap_key_live (heap_std W) a ->
     heap_key_live (heap_std W') a ->
    a ∈ dom (std W') ->
    close_addr_resources C W a false
    ∗ sts_full_world W' C
    ∗ region W' C
    ==∗
    close_addr_resources C W a false
    ∗ sts_full_world W' C
    ∗ region W' C
    ∗ ⌜ std W' !! a = Some Revoked ⌝.
  Proof.
    intros Hlive_W Hlive.
    unfold heap_key_live in Hlive_W.
    rewrite /close_addr_resources Hlive_W.
    iIntros (Hin) "( (%&%&%& (%&%&Hv&Hmono&Hφ) &Hrel) & Hsts & Hr )".
    iDestruct (key_pointsto_eq with "Hv") as "[Hv Hshare]".
    rewrite elem_of_dom in Hin; destruct Hin as [? Hin].
    iMod (revoked_by_separation with "[$Hsts $Hr $Hv]") as "(Hsts & Hr & Hv & %H')"; eauto.
    { by rewrite elem_of_dom. }
    simplify_eq.
    iModIntro.
    iDestruct (key_pointsto_eq with "[$Hv $Hshare]") as "Hv".
    iFrame "∗%".
  Qed.

  Lemma revoked_by_separation_many_with_temp_resources W W' C la :
     Forall (λ a, heap_key_live (heap_std W) a) la ->
     Forall (λ a, heap_key_live (heap_std W') a) la ->
    Forall (λ a, a ∈ dom (std W')) la →
    close_list_resources C W la false
    ∗ sts_full_world W' C
    ∗ region W' C
    ==∗
    close_list_resources C W la false
    ∗ sts_full_world W' C
    ∗ region W' C
    ∗ ⌜ Forall (λ a, std W' !! a = Some Revoked) la⌝.
  Proof.
    induction la; iIntros (Hlive_W Hlive Hin) "(Hl & Hsts & Hr)"; cbn.
    - iModIntro; iFrame. by iPureIntro; apply Forall_nil.
    - apply Forall_cons_1 in Hlive_W as [Hlive_W_a Hlive_W_tail].
      apply Forall_cons_1 in Hlive as [Hlive_a Hlive_tail].
      iDestruct "Hl" as "[ Hl IHl]".
      apply Forall_cons in Hin as [Hin_a Hin].
      iMod (revoked_by_separation_with_temp_resources with "[$Hl $Hsts $Hr]")
        as "(Hl & Hsts & Hr & %)"; [exact Hlive_W_a|exact Hlive_a|done|].
      iMod (IHla with "[$IHl $Hsts $Hr]") as "(IHl & Hsts & Hr & %)";
        [exact Hlive_W_tail|exact Hlive_tail|done|].
      iModIntro.
      iFrame "∗%".
      by iPureIntro; apply Forall_cons.
  Qed.

End region_invariant_revocation.
