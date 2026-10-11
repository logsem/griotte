From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode.
From griotte Require Import region_invariants_revocation interp_weakening monotone.
From griotte Require Import world_interp_stack.
From griotte Require Import counter_spec_states.

(** * Preparation of the call to the switcher

    The lemmas of this file do not execute code. They are used before the
    call to [C_f] in the proof of [counter_spec]:
    - [counter_world_call]: revoke the world, to get the stack frame and
      the revoked temporary keys [l]. The keys of [l] are split into the
      live ones [l_live] and the quarantined ones [l_q].
    - [counter_world_quarantine]: close the quarantined keys [l_q]. The
      entry point of [C_f] is still safe in the resulting world. *)

Section Counter_World_Call.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Lemma counter_world_call W0 C (csp_b csp_e : Addr) :
    interp W0 C (WCap true RWL Local csp_b csp_e csp_b) -∗
    world_interp W0 C
    ={⊤}=∗
    ∃ (l l_live l_q : list LAddr) stk_mem,
      ⌜extract_temporaries_condition W0 (l ++ (LNonHeap <$> finz.seq_between csp_b csp_e))⌝ ∗
      ⌜l ≡ₚ l_live ++ l_q⌝ ∗
      ⌜Forall (λ a, heap_key_live (heap_std W0) a) l_live⌝ ∗
      ⌜Forall (λ a, heap_key_status (heap_std W0) a = Some AllocObjectQuarantined) l_q⌝ ∗
      ⌜revoked_keys (revoke W0) l⌝ ∗
      ⌜revoked_addresses (revoke W0) (finz.seq_between csp_b csp_e)⌝ ∗
      world_interp (revoke W0) C ∗
      ▷ StackRevokedResources W0 C (finz.seq_between csp_b csp_e) ∗
      ▷ RevokedResources W0 C l_live ∗
      ▷ RevokedResources W0 C l_q ∗
      [[csp_b, csp_e]] ↦ₐ [[stk_mem]].
  Proof.
    iIntros "#Hinterp_csp Hworld_interp_C".
    iMod (world_interp_revoke_stack with "[$Hinterp_csp $Hworld_interp_C]")
      as (l) "(%Hl_unk & Hworld_interp_C & Hstack_revoked & >%Hstack_revoked
               & >[%stk_mem Hstk] & [Hrevoked_l %Hrevoked_l])".
    assert (Forall (fun x : LAddr => x ∈ dom (std (revoke W0))) l) as Hdom_l.
    { apply Forall_forall. intros x Hx. rewrite -revoke_dom_eq.
      rewrite elem_of_dom. exists Temporary. destruct Hl_unk as [_ Htemp].
      apply Htemp. apply elem_of_app. by left. }
    iEval (rewrite world_interp_eq /world_interp_def) in "Hworld_interp_C".
    iDestruct "Hworld_interp_C" as "(Hr & Hsts & Hseals)".
    iDestruct (region_addrs_status_some (revoke W0) C l Hdom_l with "Hr") as "[Hr %Hstatuses_l]".
    rewrite revoke_heap in Hstatuses_l.
    destruct (heap_status_partition (heap_std W0) l Hstatuses_l)
      as (l_live & l_q & Hperm_l & Hlive_l & Hq_l).
    iEval (rewrite Hperm_l RevokedResources_app) in "Hrevoked_l".
    iDestruct "Hrevoked_l" as "[Hrevoked_live Hrevoked_q]".
    iModIntro.
    iExists l, l_live, l_q, stk_mem.
    iFrame "Hstk Hstack_revoked Hrevoked_live Hrevoked_q".
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    rewrite world_interp_eq /world_interp_def. iFrame.
  Qed.

  Lemma counter_world_quarantine W0 C (csp_b csp_e : Addr) (C_f : Sealable)
    (l l_live l_q : list LAddr) :
    extract_temporaries_condition W0 (l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) ->
    l ≡ₚ l_live ++ l_q ->
    Forall (λ a, heap_key_status (heap_std W0) a = Some AllocObjectQuarantined) l_q ->
    revoked_addresses (revoke W0) (finz.seq_between csp_b csp_e) ->
    interp W0 C (WSealed ot_switcher C_f) -∗
    world_interp (revoke W0) C -∗
    StackRevokedResources W0 C (finz.seq_between csp_b csp_e) -∗
    RevokedResources W0 C l_q
    ==∗
    ⌜revoked_addresses (close_list l_q (revoke W0)) (finz.seq_between csp_b csp_e)⌝ ∗
    world_interp (close_list l_q (revoke W0)) C ∗
    interp (close_list l_q (revoke W0)) C (WSealed ot_switcher C_f) ∗
    StackRevokedResources (close_list l_q (revoke W0)) C (finz.seq_between csp_b csp_e).
  Proof.
    iIntros (Hl_unk Hperm_l Hq_l Hrevoked_W0)
      "#Hinterp_C_f Hworld_interp_C Hstack_revoked Hrevoked_q".
    set (W1q := close_list l_q (revoke W0)).
    assert (Forall (fun a => heap_key_status (heap_std W1q) a = Some AllocObjectQuarantined) l_q)
      as Hq_W1q.
    { rewrite /W1q close_list_heap revoke_heap. exact Hq_l. }
    iAssert (RevokedResources W1q C l_q) with "[Hrevoked_q]" as "Hrevoked_q'".
    { rewrite (RevokedResources_quarantined W1q C l_q Hq_W1q)
        (RevokedResources_quarantined W0 C l_q Hq_l). iExact "Hrevoked_q". }
    iMod (world_interp_restore (revoke W0) C l_q with "[$Hworld_interp_C $Hrevoked_q']")
      as "Hworld_interp_C".
    assert (related_sts_priv_world W0 W1q) as Hpriv_W0_W1q.
    { eapply related_sts_priv_trans_world; [apply revoke_related_sts_priv_world |].
      apply related_sts_pub_priv_world, close_list_related_sts_pub. }
    assert (l_q ## (LNonHeap <$> finz.seq_between csp_b csp_e)) as Hq_stack.
    { destruct Hl_unk as [Hnd _]. apply NoDup_app in Hnd.
      destruct Hnd as (_ & Hdisj & _).
      intros x Hx Hxs. apply (Hdisj x);
        [rewrite Hperm_l; apply elem_of_app; right; exact Hx | exact Hxs]. }
    iModIntro.
    iFrame "Hworld_interp_C".
    iSplit.
    { iPureIntro. apply Forall_forall. intros x Hx.
      rewrite /W1q /close_list /= -close_list_std_sta_same;
        [|intros Hq; apply (Hq_stack (LNonHeap x) Hq); by apply elem_of_LNonHeap_fmap].
      rewrite /revoked_addresses Forall_forall in Hrevoked_W0.
      by apply Hrevoked_W0. }
    iSplit.
    { iApply (interp_monotone_sd_same_heap with "[] Hinterp_C_f"); last by iPureIntro.
      by rewrite /W1q close_list_heap revoke_heap. }
    iApply (StackRevokedResources_mono_priv with "Hstack_revoked"); eauto.
  Qed.

End Counter_World_Call.
