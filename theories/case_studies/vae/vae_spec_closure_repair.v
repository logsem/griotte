From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region proofmode.
From griotte Require Import world_interp_revocation interp_weakening monotone.
From griotte Require Import world_ghost_theory world_std_revocation.
From griotte Require Import world_interp_stack.
From griotte Require Import allocator_resources heap_region.
From griotte Require Import wp_rules_interp case_study_spec_helpers.

Section VAE_Return_Repair.
  Context
    {Σ : gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg : sealStoreG Σ}
    {stsg : STSG Σ}
    {relg : relGS Σ} {cstackg : CSTACKG Σ}
    `{MP : MachineParameters}.

  (** Tombstoned keys are heap keys: they are disjoint from the stack. *)
  Lemma vae_quarantined_disjoint_stack (l : list LAddr) (b e : Addr) :
    disjoint_from_heap b e ->
    Forall (λ a, ∃ x ι, a = LHeap x ι) l ->
    l ## (LNonHeap <$> finz.seq_between b e).
  Proof.
    intros _ Hq.
    rewrite elem_of_disjoint. intros a Ha Hstack_a.
    apply list_elem_of_fmap in Hstack_a as [a' [-> _] ].
    rewrite Forall_forall in Hq.
    by destruct (Hq _ Ha) as (x & ι & ?).
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
    destruct Hpriv as (Hstd & _).
    split; cycle 1.
    { exact Hcus. }
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

  (** Discard cells for addresses already covered by a framed list. *)
  Lemma vae_revoked_cells_filter (W : WORLD) (C : CmptName)
      (l excluded : list LAddr) :
    RevokedCells W C l -∗
    RevokedCells W C (filter (fun a => a ∉ excluded) l).
  Proof.
    induction l as [|a l IH]; simpl; first (iIntros "$").
    rewrite filter_cons. case_decide; simpl; iIntros "[Ha Hl]".
    - iFrame "Ha". by iApply IH.
    - by iApply IH.
  Qed.

  (** Framed live resources force their current world entries to be revoked. *)
  Lemma vae_framed_resources_revoked
      (Worig Wcur : WORLD) (C : CmptName) (l : list LAddr) :
    Forall (fun a => a ∈ dom (std Wcur)) l ->
    world_interp Wcur C ∗
    RevokedCells Worig C l
    ={⊤}=∗
    world_interp Wcur C ∗
    RevokedCells Worig C l ∗
    ⌜Forall (fun a => std Wcur !! a = Some Revoked) l⌝.
  Proof.
    iIntros (Hdom) "[Hworld Hl]".
    iInduction l as [|k l] "IH"; first by iFrame.
    apply Forall_cons in Hdom as [Hk_dom Hdom].
    iDestruct "Hl" as "[(%pa & %Φa & %Hpers & #Hrel & %wa & HpO & Hk & HΦ & Hmono) Hl]".
    iMod ("IH" with "[//] Hworld Hl") as "(Hworld & Hl & %Hl_rev)".
    iAssert (∃ q, heap_key_live_share k q ∗ laddr_addr k ↦ₐ wa ∗
               (heap_key_live_share k q -∗ laddr_addr k ↦ₐ wa -∗ k ↦ₖ wa))%I
      with "[Hk]" as (q) "(Hshare & Hk & Hk_back)".
    { destruct k as [a|a ι]; cbn.
      - iExists 1%Qp. iFrame "Hk". by iIntros "_ $".
      - iDestruct "Hk" as "[Ha (%b & %e & %Hin & #Hobj & Hst)]".
        iExists _. iFrame "Hst Ha". iIntros "Hst Ha". iFrame "Ha".
        iExists b, e. by iFrame "Hobj Hst". }
    iMod (world_interp_revoked_by_separation with "[$Hshare $Hworld $Hk]")
      as "(Hshare & Hworld & Hk & %Hk_rev)"; first done.
    iDestruct ("Hk_back" with "Hshare Hk") as "Hk".
    iModIntro. iFrame "Hworld". iSplitL; [|iPureIntro; by constructor].
    iFrame "Hl". iExists pa, Φa. iFrame "Hrel". iSplit; first done.
    iExists wa. iFrame.
  Qed.

End VAE_Return_Repair.
