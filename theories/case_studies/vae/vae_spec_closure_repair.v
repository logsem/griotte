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
    {stsg : STSG LAddr region_type OType Word Σ}
    {relg : relGS Σ} {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ}
    `{MP : MachineParameters}.
  Lemma vae_framed_resources_live
      (Worig Wcur : WORLD) (C : CmptName) (l : list LAddr) :
    Forall (λ a, heap_key_live (heap_std Worig) a) l ->
    Forall (fun a => is_Some (heap_key_status (heap_std Wcur) a)) l ->
    allocator_ctx ∗ world_interp Wcur C ∗ RevokedResources Worig C l
    ={⊤}=∗
      allocator_ctx ∗ world_interp Wcur C ∗ RevokedResources Worig C l ∗
      ⌜Forall (λ a, heap_key_live (heap_std Wcur) a) l⌝.
  Proof.
    intros Hlive Hsome. iIntros "(#Halloc & Hworld & Hl)".
    iDestruct (counter_framed_resources_live Worig Wcur C l Hlive Hsome
      with "[$Hworld $Hl]") as "(Hworld & Hl & %Hcur)".
    by iFrame "∗#%".
  Qed.

  Lemma vae_restore_quarantined
      (Wbase Wcur : WORLD) (C : CmptName) (l : list LAddr) :
    heap_std Wbase = heap_std Wcur ->
    Forall
      (fun a => heap_key_status (heap_std Wbase) a = Some AllocObjectQuarantined)
      l ->
    world_interp Wcur C ∗ RevokedResources Wbase C l
    ==∗
    world_interp (close_list l Wcur) C.
  Proof.
    intros Hheap Hq.
    assert (Forall
      (fun a => heap_key_status (heap_std (close_list l Wcur)) a =
        Some AllocObjectQuarantined) l) as Hq_closed.
    { rewrite close_list_heap -Hheap. exact Hq. }
    rewrite (RevokedResources_quarantined Wbase C l Hq).
    rewrite -(RevokedResources_quarantined (close_list l Wcur) C l Hq_closed).
    iIntros "[Hworld Hres]".
    iApply (world_interp_restore with "[$Hworld $Hres]").
  Qed.

  Lemma vae_world_status_some
      (W : WORLD) (C : CmptName) (l : list LAddr) :
    Forall (fun a => a ∈ dom (std W)) l ->
    world_interp W C -∗
    world_interp W C ∗
      ⌜Forall (fun a => is_Some (heap_key_status (heap_std W) a)) l⌝.
  Proof.
    intros Hdom.
    rewrite world_interp_eq /world_interp_def.
    iIntros "(Hr & Hsts & Hseals)".
    iDestruct (region_addrs_status_some W C l Hdom with "Hr")
      as "[Hr %Hstatuses]".
    iFrame. iPureIntro. exact Hstatuses.
  Qed.

  Lemma vae_quarantined_disjoint_stack
      (W : WORLD) (l : list LAddr) (b e : Addr) :
    disjoint_from_heap b e ->
    Forall
      (fun a => heap_key_status (heap_std W) a = Some AllocObjectQuarantined)
      l ->
    l ## (LNonHeap <$> finz.seq_between b e).
  Proof.
    intros Hstack Hq.
    rewrite elem_of_disjoint. intros a Ha Hstack_a.
    apply list_elem_of_fmap in Hstack_a as [a' [-> Hstack_a] ].
    rewrite Forall_forall in Hq.
    specialize (Hq _ Ha). discriminate.
  Qed.

  Lemma vae_repair_public_world
      (Worig Wcur : WORLD) (closing : list LAddr) :
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

  (** Keep earlier live addresses first, adding only fresh addresses from
      each subsequent revocation list before the stack. *)
  Lemma vae_closing_lists (l0 l1 l2 stk : list LAddr) :
    let l1_unique := filter (fun a => a ∉ l0 ++ stk) l1 in
    let l2_unique := filter (fun a => a ∉ l0 ++ l1_unique ++ stk) l2 in
    let closing := (l0 ++ l1_unique ++ l2_unique) ++ stk in
    NoDup (l0 ++ stk) ->
    NoDup l1 ->
    NoDup l2 ->
    NoDup closing ∧ l1 ⊆ closing ∧ l2 ⊆ closing.
  Proof.
    intros l1_unique l2_unique closing Hnodup0 Hnodup1 Hnodup2.
    apply NoDup_app in Hnodup0 as (Hnodup0 & Hdisj0 & Hnodup_stack).
    split.
    - subst closing.
      apply NoDup_app. split.
      + apply NoDup_app. split; first exact Hnodup0.
        split.
        * intros a Ha0 Ha12.
          apply elem_of_app in Ha12 as [Ha1|Ha2].
          { subst l1_unique.
            apply list_elem_of_filter in Ha1 as [Hnot _].
            apply Hnot. apply elem_of_app; left; exact Ha0. }
          { subst l2_unique.
            apply list_elem_of_filter in Ha2 as [Hnot _].
            apply Hnot. apply elem_of_app; left; exact Ha0. }
        * apply NoDup_app. split.
          { subst l1_unique. apply NoDup_filter. exact Hnodup1. }
          split.
          { intros a Ha1 Ha2.
            subst l2_unique.
            apply list_elem_of_filter in Ha2 as [Hnot _].
            apply Hnot. apply elem_of_app; right.
            apply elem_of_app; left; exact Ha1. }
          { subst l2_unique. apply NoDup_filter. exact Hnodup2. }
      + split.
        * intros a Ha_rev Ha_stack.
          apply elem_of_app in Ha_rev as [Ha0|Ha12].
          { exact (Hdisj0 a Ha0 Ha_stack). }
          apply elem_of_app in Ha12 as [Ha1|Ha2].
          { subst l1_unique.
            apply list_elem_of_filter in Ha1 as [Hnot _].
            apply Hnot. apply elem_of_app; right; exact Ha_stack. }
          { subst l2_unique.
            apply list_elem_of_filter in Ha2 as [Hnot _].
            apply Hnot. apply elem_of_app; right.
            apply elem_of_app; right; exact Ha_stack. }
        * exact Hnodup_stack.
    - split; intros a Ha.
      + destruct (decide (a ∈ l0 ++ stk)) as [Hin|Hnot].
        * subst closing. set_solver.
        * assert (a ∈ l1_unique) as Hin.
          { subst l1_unique. apply list_elem_of_filter. auto. }
          subst closing. set_solver.
      + destruct (decide (a ∈ l0 ++ l1_unique ++ stk)) as [Hin|Hnot].
        * subst closing. set_solver.
        * assert (a ∈ l2_unique) as Hin.
          { subst l2_unique. apply list_elem_of_filter. auto. }
          subst closing. set_solver.
  Qed.

  (** Discard resources for addresses already covered by a framed list. *)
  Lemma vae_revoked_resources_filter (W : WORLD) (C : CmptName)
      (l excluded : list LAddr) :
    RevokedResources W C l -∗
    RevokedResources W C (filter (fun a => a ∉ excluded) l).
  Proof.
    induction l as [|a l IH]; simpl; first (iIntros "$").
    rewrite filter_cons. case_decide; simpl; iIntros "[Ha Hl]".
    - iFrame "Ha". by iApply IH.
    - by iApply IH.
  Qed.

  (** Framed live resources force their current world entries to be revoked. *)
  Lemma vae_framed_resources_revoked
      (Worig Wcur : WORLD) (C : CmptName) (l : list LAddr) :
    Forall (λ a, heap_key_live (heap_std Worig) a) l ->
    Forall (fun a => a ∈ dom (std Wcur)) l ->
    allocator_ctx ∗
    world_interp Wcur C ∗
    RevokedResources Worig C l
    ={⊤}=∗
    world_interp Wcur C ∗
    RevokedResources Worig C l ∗
    ⌜Forall (fun a => std Wcur !! a = Some Revoked) l⌝.
  Proof.
    intros Hlive Hdom.
    iIntros "(#Halloc & Hworld & Hl)".
    iDestruct (vae_world_status_some Wcur C l Hdom with "Hworld")
      as "[Hworld %Hstatuses]".
    iMod (vae_framed_resources_live Worig Wcur C l Hlive Hstatuses
      with "[$Halloc $Hworld $Hl]") as "(_ & Hworld & Hl & %Hlive_cur)".
    iMod (world_interp_revoked_by_separation_many_with_RevokedResources
      Worig Wcur C l Hlive Hlive_cur Hdom with "[$Hworld $Hl]")
      as "(Hworld & Hl & %Hrevoked)".
    iModIntro. iFrame. done.
  Qed.

End VAE_Return_Repair.
