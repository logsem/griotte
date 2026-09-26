From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region proofmode.
From griotte Require Import region_invariants_revocation interp_weakening monotone.
From griotte Require Import world_ghost_theory world_std_revocation.
From griotte Require Import world_interp_stack.
From griotte Require Import allocator_resources heap_region.
From griotte Require Import wp_rules_interp.

Section VAE_Return_Repair.
  Context
    {Σ : gFunctors}
    {ceriseg : ceriseG Σ} {sealsg : sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ}
    {relg : relGS Σ} {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ}
    `{MP : MachineParameters}.
  Lemma vae_framed_resources_live
      (Worig Wcur : WORLD) (C : CmptName) (l : list Addr) :
    Forall (heap_cell_live (heap_std Worig)) l ->
    Forall (fun a => is_Some (heap_cell_status (heap_std Wcur) a)) l ->
    allocator_ctx ∗ world_interp Wcur C ∗ RevokedResources Worig C l
    ={⊤}=∗
      allocator_ctx ∗ world_interp Wcur C ∗ RevokedResources Worig C l ∗
      ⌜Forall (heap_cell_live (heap_std Wcur)) l⌝.
  Proof.
    induction l as [|a l IH]; intros Hlive Hsome;
      iIntros "(#Halloc & Hworld & Hl)".
    - iModIntro. iFrame "∗#". iPureIntro. constructor.
    - apply Forall_cons in Hlive as [Ha_live Hl_live].
      apply Forall_cons in Hsome as [Ha_some Hl_some].
      iDestruct "Hl" as "[Hitem Hl]".
      iDestruct "Hitem" as (p φ) "(%Hpers & Hrel & Hcell)".
      rewrite /heap_cell_live in Ha_live.
      iEval (rewrite Ha_live) in "Hcell".
      iDestruct "Hcell" as (v) "(%HpO & Ha & Hφ & Hmono)".
      iMod (framed_cell_live Wcur C a v Ha_some
        with "[$Halloc $Hworld $Ha]")
        as "(_ & Hworld & Ha & %Ha_cur)".
      iAssert (RevokedResources Worig C [a])%I
        with "[Hrel Ha Hφ Hmono]" as "Hitem".
      { rewrite /RevokedResources /= Ha_live.
        iSplitL "Hrel Ha Hφ Hmono"; last done.
        iExists p, φ. iFrame "Hrel". iSplit; first done.
        iExists v. rewrite /TmpRes. iFrame "Ha Hφ Hmono". done. }
      iMod (IH Hl_live Hl_some with "[$Halloc $Hworld $Hl]")
        as "(_ & Hworld & Hl & %Hl_cur)".
      iAssert (RevokedResources Worig C (a :: l))%I
        with "[Hitem Hl]" as "Hl".
      { replace (a :: l) with ([a] ++ l) by done.
        rewrite RevokedResources_app. iFrame. }
      iModIntro. iFrame "∗#". iPureIntro. constructor; assumption.
  Qed.

  Lemma vae_restore_quarantined
      (Wbase Wcur : WORLD) (C : CmptName) (l : list Addr) :
    heap_std Wbase = heap_std Wcur ->
    Forall
      (fun a => heap_cell_status (heap_std Wbase) a = Some AllocObjectQuarantined)
      l ->
    world_interp Wcur C ∗ RevokedResources Wbase C l
    ==∗
    world_interp (close_list l Wcur) C.
  Proof.
    intros Hheap Hq.
    assert (Forall
      (fun a => heap_cell_status (heap_std (close_list l Wcur)) a =
        Some AllocObjectQuarantined) l) as Hq_closed.
    { rewrite close_list_heap -Hheap. exact Hq. }
    rewrite (RevokedResources_quarantined Wbase C l Hq).
    rewrite -(RevokedResources_quarantined (close_list l Wcur) C l Hq_closed).
    iIntros "[Hworld Hres]".
    iApply (world_interp_restore_mixed with "[$Hworld $Hres]").
  Qed.

  Lemma vae_world_status_some
      (W : WORLD) (C : CmptName) (l : list Addr) :
    Forall (fun a => a ∈ dom (std W)) l ->
    world_interp W C -∗
    world_interp W C ∗
      ⌜Forall (fun a => is_Some (heap_cell_status (heap_std W) a)) l⌝.
  Proof.
    intros Hdom.
    rewrite world_interp_eq /world_interp_def.
    iIntros "(Hr & Hsts & Hseals)".
    iDestruct (region_cells_status_some W C l Hdom with "Hr")
      as "[Hr %Hstatuses]".
    iFrame. iPureIntro. exact Hstatuses.
  Qed.

  Lemma vae_quarantined_disjoint_stack
      (W : WORLD) (l : list Addr) (b e : Addr) :
    disjoint_from_heap b e ->
    Forall
      (fun a => heap_cell_status (heap_std W) a = Some AllocObjectQuarantined)
      l ->
    l ## finz.seq_between b e.
  Proof.
    intros Hstack Hq.
    rewrite elem_of_disjoint. intros a Ha Hstack_a.
    rewrite Forall_forall in Hq.
    specialize (Hq a Ha).
    unfold heap_cell_status in Hq.
    destruct (is_heap_address a) eqn:Hheap; last discriminate.
    rewrite /disjoint_from_heap elem_of_disjoint in Hstack.
    eapply (Hstack a); first exact Hstack_a.
    apply elem_of_finz_seq_between.
    apply withinBounds_true_iff. exact Hheap.
  Qed.

  Lemma vae_repair_public_world
      (Worig Wcur : WORLD) (closing : list Addr) :
    related_sts_priv_world Worig Wcur ->
    related_sts_pub (loc Worig) (loc Wcur)
      (wrel Worig) (wrel Wcur) ->
    (forall a, std Worig !! a = Some Temporary -> a ∈ closing) ->
    Forall (fun a => std (revoke Wcur) !! a = Some Revoked) closing ->
    related_sts_pub_world Worig (close_list closing (revoke Wcur)).
  Proof.
    intros Hpriv Hcus Hcover Hrevoked.
    pose proof Hpriv as Hpriv_full.
    destruct Hpriv as (Hstd & _ & Hseals & Hheap).
    split; cycle 1.
    { split; first exact Hcus.
      split; [exact Hseals|exact Hheap]. }
    cbn. split.
    - intros a Ha.
      rewrite -close_list_dom_eq -revoke_dom_eq.
      by apply Hstd.
    - intros a rho0 rho1 Ha0 Ha1.
      destruct rho0.
      + assert (a ∈ closing) as Hin by (apply Hcover; exact Ha0).
        rewrite Forall_forall in Hrevoked.
        pose proof (Hrevoked a Hin) as Hrev.
        eapply close_list_std_sta_revoked in Hrev; eauto.
        rewrite Ha1 in Hrev; simplify_eq.
        apply rtc_refl.
      + assert (std Wcur !! a = Some Permanent) as Hperm.
        { eapply region_state_priv_perm; eauto. }
        apply revoke_lookup_Perm in Hperm.
        rewrite -close_list_std_sta_same_alt in Ha1; [|congruence].
        rewrite Hperm in Ha1; simplify_eq.
        apply rtc_refl.
      + destruct rho1; try apply rtc_refl;
          apply rtc_once; constructor.
  Qed.

End VAE_Return_Repair.
