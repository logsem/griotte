From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening proofmode.
From griotte Require Import sts_multiple_updates.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import dle_spec_states.

(** * Logical steps of the proof of [dle_spec]

    The lemmas of this file do not execute code. They are used between the
    block groups of [dle_spec_<segment>_blocks_<n>] in the proof of
    [dle_spec]. *)

Section DLE_World.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (** ** Sharing the data with the adversary

      The world in which the first call happens: [cgp_b] and [cgp_b + 1] are
      added to the revoked world as temporary addresses. *)
  Definition dle_Wshare W (cgp_b : Addr) : WORLD :=
    <s[(cgp_b ^+ 1)%a := Temporary ]s> (<s[cgp_b := Temporary ]s> (revoke W)).

  Lemma dle_world_share W0 C (cgp_b cgp_e csp_b csp_e : Addr) (C_f : Sealable) :
    let W3 := dle_Wshare W0 cgp_b in
    (cgp_b + length dle_main_data)%a = Some cgp_e ->
    cgp_b ∉ dom (std W0) ->
    (cgp_b ^+ 1)%a ∉ dom (std W0) ->
    revoked_addresses (revoke W0) (finz.seq_between csp_b csp_e) ->
    world_interp (revoke W0) C -∗
    StackRevokedResources W0 C (finz.seq_between csp_b csp_e) -∗
    interp W0 C (WSealed ot_switcher C_f) -∗
    cgp_b ↦ₐ WInt 0 -∗
    (cgp_b ^+ 1)%a ↦ₐ WCap RW Global cgp_b (cgp_b ^+ 1)%a cgp_b
    ={⊤}=∗
    world_interp W3 C ∗
    interp W3 C (WCap RW_DL Local (cgp_b ^+ 1)%a (cgp_b ^+ 2)%a (cgp_b ^+ 1)%a) ∗
    interp W3 C (WSealed ot_switcher C_f) ∗
    StackRevokedResources W3 C (finz.seq_between csp_b csp_e) ∗
    ⌜ revoked_addresses W3 (finz.seq_between csp_b csp_e) ⌝.
  Proof.
    intros W3.
    iIntros (Hcgp_contiguous Hcgp_b Hcgp_a Hstack_revoked)
      "Hworld_interp_C #Hstack_revoked_W0 #Hinterp_W0_C_f Hcgp_b Hcgp_a".
    set (W1 := revoke W0).

    (* First, extend the world such that [cgp_b] is valid with RW_DL access *)
    iDestruct (init_TmpRes W1 C cgp_b RW_DL interpC with "[] [$Hcgp_b] []")
      as "TmpRes_cgp_b"; auto.
    { iApply future_pub_mono_interp_z. }
    { iApply interp_int. }
    iMod (world_interp_extend_temp with "Hworld_interp_C TmpRes_cgp_b")
      as "(Hworld_interp_C & #Hrel_cgp_b)"; auto.
    { by rewrite -revoke_dom_eq. }
    set (W2 := <s[cgp_b:=Temporary]s> W1).

    (* And prove that the RW_DL capability pointing to it is safe *)
    iAssert (interp W2 C (WCap RW_DL Local cgp_b (cgp_b ^+ 1)%a cgp_b)) as "#Hinterp_cgp_b".
    { iEval (rewrite fixpoint_interp1_eq); iEval (cbn).
      rewrite (finz_seq_between_cons (cgp_b)%a); last solve_addr.
      rewrite (finz_seq_between_empty _ (cgp_b ^+ 1)%a); last solve_addr.
      iApply big_sepL_singleton.
      iExists RW_DL, interp.
      iEval (cbn).
      iSplit; first done.
      iSplit.
      { iPureIntro; intros WCv; tc_solve. }
      iSplit; first iFrame "Hrel_cgp_b".
      iSplit; first iApply zcond_interp.
      iSplit; first iApply rcond_interp.
      iSplit; first iApply wcond_interp.
      iSplit; first iApply monoReq_interp.
      + subst W2; cbn; by rewrite lookup_insert_eq.
      + by intro.
      + by iPureIntro; right; subst W2; cbn; rewrite lookup_insert_eq.
    }

    (* Second, extend the world such that [cgp_b+1] is valid with RW_DL access *)
    iDestruct (init_TmpRes W2 C (cgp_b ^+ 1)%a RW_DL (safeC interp_dl)
                with "[] [$Hcgp_a] []") as "TmpRes_cgp_a"; auto.
    { iApply future_pub_mono_interp_dl. }
    iMod (world_interp_extend_temp with "Hworld_interp_C TmpRes_cgp_a")
      as "(Hworld_interp_C & Hrel_cgp_a)"; auto.
    { subst W2.
      cbn; rewrite dom_insert_L not_elem_of_union; split.
      + rewrite not_elem_of_singleton; solve_addr+Hcgp_contiguous.
      + by rewrite -revoke_dom_eq.
    }
    iFrame "Hworld_interp_C".
    iModIntro.

    assert (related_sts_priv_world W0 W3) as Hrelated_priv_W0_W3.
    { eapply related_sts_priv_trans_world with (W' := W1) ; eauto
      ; first eapply revoke_related_sts_priv_world.
      eapply related_sts_pub_priv_trans_world with (W' := W2) ; eauto.
      { eapply related_sts_pub_world_revoked_temporary'.
        by rewrite -revoke_lookup_None -not_elem_of_dom.
      }
      apply related_sts_pub_priv_world.
      eapply related_sts_pub_world_revoked_temporary'.
      rewrite lookup_insert_ne; last solve_addr.
      by rewrite -revoke_lookup_None -not_elem_of_dom.
    }

    (* The RW_DL capability pointing to [cgp_b+1] is safe *)
    iSplit.
    { iEval (rewrite fixpoint_interp1_eq). iEval (cbn).
      rewrite (finz_seq_between_cons (cgp_b ^+ 1)%a); last solve_addr.
      rewrite (finz_seq_between_empty _ (cgp_b ^+ 2)%a); last solve_addr.
      iApply big_sepL_singleton.
      iExists RW_DL, interp_dl.
      iEval (cbn).
      iSplit; first done.
      iSplit; first (iPureIntro; apply persistent_cond_interp_dl).
      iSplit; first iFrame "Hrel_cgp_a".
      iSplit; first iApply zcond_interp_dl.
      iSplit; first (iApply rcond_interp_dl; auto).
      iSplit; first iApply wcond_interp_dl.
      iSplit; last (by iPureIntro; right; rewrite lookup_insert_eq).
      rewrite /monoReq; rewrite lookup_insert_eq; cbn.
      iApply mono_pub_interp_dl.
    }
    iSplit; first (iApply interp_monotone_sd; eauto).
    iSplit; first (iApply (StackRevokedResources_mono_priv with "Hstack_revoked_W0"); auto).

    (* The stack is still revoked *)
    iPureIntro.
    rewrite /revoked_addresses Forall_forall.
    intros x Hx.
    rewrite /revoked_addresses Forall_forall in Hstack_revoked.
    pose proof (Hstack_revoked x Hx) as Hx_revoked.
    assert (x ≠ cgp_b).
    { intros ->. apply Hcgp_b. rewrite revoke_dom_eq elem_of_dom; eauto. }
    assert (x ≠ (cgp_b ^+ 1)%a).
    { intros ->. apply Hcgp_a. rewrite revoke_dom_eq elem_of_dom; eauto. }
    rewrite /W3 /dle_Wshare /=.
    rewrite !lookup_insert_ne //.
  Qed.

  (** ** Return from the first call

      The adversary returned a public future [W4] of [W3]. Revoking [W4]
      gives back [cgp_b], and the stack and the entry point of the adversary
      are still valid in the revoked world. *)
  Lemma dle_world_return W0 W4 C (cgp_b cgp_e csp_b csp_e : Addr) (C_f : Sealable)
    (l : list Addr) :
    let W3 := dle_Wshare W0 cgp_b in
    let stk := finz.seq_between csp_b csp_e in
    let stk' := finz.seq_between (csp_b ^+ 4)%a csp_e in
    (cgp_b + length dle_main_data)%a = Some cgp_e ->
    (csp_b <= csp_b ^+ 4)%a ->
    revoked_addresses W3 stk ->
    extract_temporaries_condition W4 (l ++ stk') ->
    related_sts_pub_world (std_update_multiple W3 stk' Temporary) W4 ->
    RevokedResources W4 C l -∗
    interp W3 C (WSealed ot_switcher C_f) -∗
    StackRevokedResources W4 C stk -∗
    ◇ ( (∃ w, cgp_b ↦ₐ w) ∗
        interp (revoke W4) C (WSealed ot_switcher C_f) ∗
        StackRevokedResources (revoke W4) C stk ).
  Proof.
    intros W3 stk stk'.
    iIntros (Hcgp_contiguous Hcsp_bounds Hstack_revoked_W3 Hl_unk Hrelated_pub)
      "Hrevoked_l #Hinterp_W3_C_f #Hstack_revoked_W4".
    assert (std W3 !! cgp_b = Some Temporary) as HW3_cgp_b.
    { rewrite /W3 /dle_Wshare /=.
      rewrite lookup_insert_ne; last solve_addr.
      by rewrite lookup_insert_eq.
    }
    assert (Forall (λ a, std W3 !! a = Some Revoked) stk') as Hstack_revoked_W3'.
    { rewrite /revoked_addresses Forall_forall in Hstack_revoked_W3.
      apply Forall_forall; intros a Ha; apply Hstack_revoked_W3.
      rewrite !elem_of_finz_seq_between in Ha |- *; solve_addr+Ha Hcsp_bounds.
    }
    assert (related_sts_pub_world W3 W4) as Hrelated_pub_W3_W4.
    { eapply related_sts_pub_trans_world ; eauto.
      by apply related_sts_pub_update_multiple_temp.
    }

    (* Extract [cgp_b] out of the revoked addresses *)
    iDestruct (big_sepL_elem_of_extract _ (fun a => ▷ ∃ v, a ↦ₐ v)%I cgp_b
                with "[] [$Hrevoked_l]")
      as (l'') "(_ & _ & >[%wcgpb Hcgp_b])".
    { assert (W4.1 !! cgp_b = Some Temporary) as HW4.
      { eapply region_state_pub_temp; eauto. }
      destruct Hl_unk as [_ Hl_unk].
      apply Hl_unk in HW4.
      apply elem_of_app in HW4 as [?|Hstk]; first done.
      exfalso.
      rewrite Forall_forall in Hstack_revoked_W3'.
      apply Hstack_revoked_W3' in Hstk; congruence.
    }
    { by destruct Hl_unk as [Hl_unk _]; apply NoDup_app in Hl_unk as (? & _ & _). }
    { iIntros (a) "(%&%&%& _ & (%&_&$&?) )". }
    iModIntro.
    iSplitL "Hcgp_b"; first by iExists _.

    (* The entry point of the adversary and the stack are still valid *)
    assert (related_sts_priv_world W4 (revoke W4)) as Hrelated_priv_W4
        by apply revoke_related_sts_priv_world.
    iSplit.
    { iApply interp_monotone_sd; eauto.
      iApply interp_monotone_sd; eauto.
      iPureIntro; apply related_sts_pub_priv_world; auto.
    }
    iApply (StackRevokedResources_mono_priv with "Hstack_revoked_W4"); auto.
  Qed.

End DLE_World.
