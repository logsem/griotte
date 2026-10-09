From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode.
From griotte Require Import region_invariants_revocation interp_weakening monotone.
From griotte Require Import world_interp_stack.
From griotte Require Import counter_spec_states.

(** * Repair of the world before the return of [counter]

    The lemmas of this file do not execute code. They are used after the
    call to [C_f] in the proof of [counter_spec]:
    - [related_pub_W0_Wfixed]: the world obtained by closing the revoked
      addresses of the final world is a public future world of the
      initial world,
    - [counter_world_return]: the addresses [l] revoked before the call and
      the stack frame are still revoked after the call, and the world can be
      repaired for the return. *)

Section Counter_World_Return.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Lemma related_pub_W0_Wfixed (W0 W2 : WORLD) (csp_b csp_e : Addr ) (l : list Addr):
    let W1 := revoke W0 in
    let W3 := revoke W2 in
    (∀ a : finz MemNum, std W0 !! a = Some Temporary ↔ a ∈ l ++ finz.seq_between csp_b csp_e) ->
    Forall (λ a : finz MemNum, std W3 !! a = Some Revoked) (l++finz.seq_between csp_b csp_e) ->
    related_sts_pub_world W1 W2 ->
    related_sts_pub_world W0 (close_list (l ++ finz.seq_between csp_b csp_e) W3).
  Proof.
    intros * Htemporaries_W0 Hrevoked_W3 Hrelated_pub_W1_W2.

    destruct W0 as [W0_std W0_cus], W2 as [W2_std W2_cus]; cbn.
    destruct Hrelated_pub_W1_W2 as [HW1_W2_std HW1_W2_cus].
    split; cbn; cycle 1.
    { eapply related_sts_pub_trans; eauto; eapply related_sts_pub_refl. }
    destruct HW1_W2_std as [HW1_W2_std_dom HW1_W2_std_t].
    cbn in *.
    split.
    {
      intros a Ha.
      rewrite elem_of_dom -close_list_std_sta_is_Some -revoke_std_sta_lookup_Some -elem_of_dom.
      apply HW1_W2_std_dom.
      by rewrite elem_of_dom -revoke_std_sta_lookup_Some -elem_of_dom.
    }
    intros a ρ0 ρ2 Ha0 Ha2.
    destruct ρ0; cycle 1.
    - (* the initial a was in the Permanent state *)
      assert (a ∉ l ++ finz.seq_between csp_b csp_e) as Ha_notin.
      { destruct (Htemporaries_W0 a) as [_ ?].
        intro Hcontra; apply H in Hcontra. by rewrite Ha0 in Hcontra.
      }
      apply revoke_lookup_Perm in Ha0.
      assert (std (revoke ((W0_std, W0_cus))) !! a = Some Permanent) as Ha0' by done.
      rewrite -(std_sta_update_multiple_lookup_same_i _ (finz.seq_between (csp_b ^+ 4)%a csp_e) Temporary)
        in Ha0'.
      2: {
        intro Hcontra; apply Ha_notin.
        rewrite elem_of_app; right.
        rewrite !elem_of_finz_seq_between in Hcontra |- *.
        solve_addr.
      }
      rewrite -close_list_std_sta_same in Ha2; last done.
      destruct ρ2.
      + by apply revoke_std_sta_lookup_non_temp in Ha2.
      + done.
      + apply anti_revoke_lookup_Revoked in Ha2.
        destruct Ha2 as [Ha2|Ha2]; first eapply HW1_W2_std_t in Ha0; eauto.
        eapply HW1_W2_std_t in Ha0; last eauto.
        inversion Ha0 as [|??? Hcontra]; simplify_eq.
        inversion Hcontra.
    - (* the initial a was in the Revoked state *)
      destruct ρ2; last apply rtc_refl; apply rtc_once; constructor.
    - (* the initial a was in the Temporary state *)
      assert (a ∈ l ++ finz.seq_between csp_b csp_e) as Ha_in.
      { destruct (Htemporaries_W0 a) as [? _]; by apply Htemporaries_W0. }
      apply revoke_lookup_Monotemp in Ha0.
      assert (std (revoke ((W0_std, W0_cus))) !! a = Some Revoked) as Ha0' by done.
      assert (
          std ((std_update_multiple (revoke (W0_std, W0_cus)) (finz.seq_between (csp_b ^+ 4)%a csp_e)
                  Temporary)) !! a =
          Some (if (decide (a ∈ (finz.seq_between (csp_b ^+ 4)%a csp_e)))
                then Temporary
                else Revoked
        )).
      {
        destruct (decide (a ∈ (finz.seq_between (csp_b ^+ 4)%a csp_e))) as [Ha_in_stk | Ha_in_stk].
        + apply std_sta_update_multiple_lookup_in_i; eauto.
        + rewrite std_sta_update_multiple_lookup_same_i; eauto.
      }
      pose proof Ha_in as Ha_in'.
      rewrite Forall_forall in Hrevoked_W3.
      eapply Hrevoked_W3 in Ha_in;eauto.
      eapply close_list_std_sta_revoked in Ha_in; last apply Ha_in'.
      rewrite Ha_in in Ha2; simplify_eq.
      apply rtc_refl.
  Qed.

  (** After the call to [C_f], in the world [revoke W2]: the addresses [l]
      revoked before the call and the stack frame are still revoked, and
      closing them yields a public future world of the initial world
      [W0]. *)
  Lemma counter_world_return W0 W2 C (csp_b csp_e : Addr) (l : list Addr)
    (stk_mem : list Word) :
    extract_temporaries_condition W0 (l ++ finz.seq_between csp_b csp_e) ->
    revoked_addresses (revoke W0) l ->
    revoked_addresses (revoke W0) (finz.seq_between csp_b csp_e) ->
    related_sts_pub_world
      (std_update_multiple (revoke W0) (finz.seq_between (csp_b ^+ 4)%a csp_e) Temporary) W2 ->
    world_interp (revoke W2) C -∗
    RevokedResources W0 C l -∗
    [[csp_b, csp_e]] ↦ₐ [[stk_mem]]
    ==∗
    world_interp (revoke W2) C ∗
    RevokedResources W0 C l ∗
    [[csp_b, csp_e]] ↦ₐ [[stk_mem]] ∗
    ⌜related_sts_pub_world W0 (close_list (l ++ finz.seq_between csp_b csp_e) (revoke W2))⌝.
  Proof.
    iIntros (Hextract Hrevoked_l Hrevoked_stk Hpub_ext)
      "Hworld_interp_C Hrevoked_l Hstk".
    assert (related_sts_pub_world (revoke W0) W2) as Hpub_W1_W2.
    { eapply related_sts_pub_trans_world; last exact Hpub_ext.
      apply related_sts_pub_update_multiple_temp.
      apply Forall_forall; intros a Ha.
      rewrite /revoked_addresses Forall_forall in Hrevoked_stk.
      apply Hrevoked_stk.
      rewrite !elem_of_finz_seq_between in Ha |- *; solve_addr+Ha.
    }
    pose proof Hpub_W1_W2 as [ [Hdom _] _].
    iMod (world_interp_revoked_by_separation_many_with_RevokedResources
           with "[$Hworld_interp_C $Hrevoked_l]")
      as "(Hworld_interp_C & Hrevoked_l & %Hrevoked_l_W3)".
    { apply Forall_forall; intros a Ha.
      rewrite /revoked_addresses Forall_forall in Hrevoked_l.
      apply Hrevoked_l in Ha.
      rewrite -revoke_dom_eq.
      apply Hdom.
      rewrite elem_of_dom; eauto.
    }
    iMod (world_interp_revoked_by_separation_many with "[$Hworld_interp_C $Hstk]")
      as "(Hworld_interp_C & Hstk & %Hrevoked_stk_W3)".
    { apply Forall_forall; intros a Ha.
      rewrite /revoked_addresses Forall_forall in Hrevoked_stk.
      apply Hrevoked_stk in Ha.
      rewrite -revoke_dom_eq.
      apply Hdom.
      rewrite elem_of_dom; eauto.
    }
    iModIntro.
    iFrame.
    iPureIntro.
    destruct Hextract as [_ Htemps].
    eapply related_pub_W0_Wfixed; [exact Htemps | | exact Hpub_W1_W2].
    apply Forall_app; split; auto.
  Qed.

End Counter_World_Return.
