From iris.proofmode Require Import proofmode.
From griotte Require Import sts_multiple_updates.
From griotte Require Import logrel_binary interp_weakening_binary monotone_binary.
From griotte Require Import region_invariants_revocation_binary.
From griotte Require Import rules proofmode proofmode_binary.
From griotte Require Import world_ghost_theory_binary world_interp_stack_binary stack_world_resources_binary.
From griotte Require Import cmdc_spec_states_binary.

(** * Logical steps of the proof of [cmdc_spec]

    The lemmas of this file do not execute code. They are used between the
    block groups of [cmdc_spec_<segment>_blocks_<n>_binary] in the proof
    of [cmdc_spec]. *)

Section CMDC_World.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (** ** Sharing an address with a callee

      The world in which a call happens: the shared address [a] is added to
      the world as a permanent address. *)
  Definition cmdc_Wshare W (a : Addr) : WORLD :=
    <s[a := Permanent ]s> W.

  (** Relinquish [a], which holds [0] in both runs, into the world of the
      callee, so that the capability [(RW, Global, a, a_e, a)] is safe to
      share. The stack frame stays revoked. *)
  Lemma cmdc_world_share W C (a a_e csp_b csp_e : Addr) (target : Sealable)
    (stk_mem : list Word) :
    let W' := cmdc_Wshare W a in
    let stk := finz.seq_between csp_b csp_e in
    (a + 1)%a = Some a_e ->
    a ∉ dom (std W) ->
    revoked_addresses W stk ->
    world_interp W C -∗
    StackRevokedResources W C stk -∗
    interp W C (WSealed ot_switcher target, WSealed ot_switcher target) -∗
    a ↦ₐ WInt 0 -∗
    a ↣ₐ WInt 0 -∗
    [[ csp_b , csp_e ]] ↦ₐ [[ stk_mem ]]
    ={⊤}=∗
    world_interp W' C ∗
    rel C a RW interpC ∗
    interp W' C (WCap RW Global a a_e a, WCap RW Global a a_e a) ∗
    interp W' C (WSealed ot_switcher target, WSealed ot_switcher target) ∗
    StackRevokedResources W' C stk ∗
    ⌜ revoked_addresses W' stk ⌝ ∗
    ⌜ a ∉ stk ⌝ ∗
    [[ csp_b , csp_e ]] ↦ₐ [[ stk_mem ]].
  Proof.
    intros W' stk.
    iIntros (Ha_e Ha_fresh Hrevoked_stk)
      "Hworld #Hstack_revoked #Htarget Ha Hsa Hstk".
    iDestruct (big_sepL2_disjoint_pointsto with "[$Hstk $Ha]") as "%Ha_stk".

    (* Relinquish [a] into the world, as a permanent address *)
    iDestruct (init_PermRes W C a RW interpC (WInt 0, WInt 0) with "[] [$Ha] [$Hsa] []") as "Ha".
    { done. }
    { iApply future_priv_mono_interp_z. }
    { iApply interp_int. }
    iMod (world_interp_extend_perm with "Hworld Ha") as "(Hworld & #Hrel_a)"; auto.
    iModIntro.
    assert (related_sts_priv_world W W') as HW_priv_W'.
    { subst W'. by eapply related_sts_priv_world_fresh_Permanent. }
    iFrame "Hworld Hrel_a Hstk".

    (* The capability pointing to [a] is safe to share *)
    iSplit.
    { iEval (rewrite interp_diag_eq // /interp1_diag /=).
      rewrite (finz_seq_between_cons a); last solve_addr.
      rewrite (finz_seq_between_empty (a ^+ 1)%a); last solve_addr+Ha_e.
      iApply big_sepL_singleton.
      iExists RW, interp.
      iEval (cbn).
      iSplit; first done.
      iSplit; first (iPureIntro; by apply persistent_cond_interp).
      iSplit; first iFrame "Hrel_a".
      iSplit; first (iNext; by iApply zcond_interp).
      iSplit; first (iNext; by iApply rcond_interp).
      iSplit; first (iNext; by iApply wcond_interp).
      subst W'.
      iSplit.
      - iApply (monoReq_interp _ _ _ _ Permanent); last done.
        rewrite /cmdc_Wshare. by rewrite lookup_insert_eq.
      - iPureIntro. by rewrite lookup_insert_eq.
    }

    (* The entry point of the callee is still safe to share *)
    iSplit; first (iApply interp_monotone_sd; eauto).

    (* The stack is still revoked *)
    iSplit; first (iApply (StackRevokedResources_mono_priv with "Hstack_revoked"); auto).
    iPureIntro; split; last done.
    rewrite /revoked_addresses Forall_forall.
    rewrite /revoked_addresses Forall_forall in Hrevoked_stk.
    intros a' Ha'. subst W'; cbn.
    rewrite lookup_insert_ne; last (intros ->; set_solver+Ha_stk Ha').
    by apply Hrevoked_stk.
  Qed.

  (** ** Return from a call

      The callee returned a public future [Wret] of the world of the call.
      The shared address [a] is still permanent in the revoked world, which
      gives back the points-to of [a] in both runs. *)
  Lemma cmdc_world_return W Wret C (a csp_b csp_e : Addr) :
    let stk' := finz.seq_between (csp_b ^+ 4)%a csp_e in
    a ∉ finz.seq_between csp_b csp_e ->
    (csp_b <= csp_b ^+ 4)%a ->
    related_sts_pub_world (std_update_multiple (cmdc_Wshare W a) stk' Temporary) Wret ->
    world_interp (revoke Wret) C -∗
    rel C a RW interpC -∗
    ◇ ∃ v sv, a ↦ₐ v ∗ a ↣ₐ sv.
  Proof.
    intros stk'.
    iIntros (Ha_stk Hcsp_bounds Hrelated_pub) "Hworld #Hrel_a".
    assert (a ∉ stk') as Ha_stk'.
    { subst stk'.
      intro Ha_range. apply Ha_stk.
      rewrite !elem_of_finz_seq_between in Ha_range |- *.
      solve_addr+Hcsp_bounds Ha_range.
    }
    assert (std (revoke Wret) !! a = Some Permanent) as Ha_perm.
    { apply revoke_lookup_Perm.
      eapply region_state_pub_perm; first exact Hrelated_pub.
      rewrite /cmdc_Wshare std_update_multiple_insert_commute; last exact Ha_stk'.
      by rewrite lookup_insert_eq.
    }
    rewrite (open_world_interp_empty _ C).
    iDestruct (open_world_interp_permanent with "Hworld Hrel_a")
      as "(_ & _ & Ha)"; auto.
    { set_solver+. }
    iAssert (▷ ∃ v sv, a ↦ₐ v ∗ a ↣ₐ sv)%I with "[Ha]" as ">Ha".
    { iNext. iDestruct "Ha" as (v) "Ha".
      iDestruct (PermRes_acc with "Ha") as "[(Ha & Hsa & _) _]".
      by iExists v.1, v.2; iFrame. }
    by iModIntro.
  Qed.

End CMDC_World.
