From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region proofmode register_tactics.
From griotte Require Import region_invariants_revocation region_invariants_allocation.
From griotte Require Import interp_weakening monotone.
From griotte Require Import world_ghost_theory world_interp_stack interp_switcher_call.
From griotte Require Import vae_spec_states.

(** * Preparation of the calls to the switcher

    The lemmas of this file do not execute code. They are used between the
    block groups and the calls to the switcher in the proofs of
    [vae_init_spec] and [vae_awkward_spec]:
    - [vae_world_flag_false] and [vae_world_flag_true]: the updates of the
      custom location [i] of the flag, before the first and the second
      call to [g],
    - [vae_world_stack]: the stack frame stays revoked in the world of the
      call,
    - [vae_world_callback]: the callback [g] stays safe in the world of
      the call, when it is a sealed entry point,
    - [vae_world_pub_call]: the world after a call is a public future
      world of the world of the call,
    - [vae_args_zero], [vae_rmap_zero] and [vae_call_args]: the argument
      registers of the calls to [g],
    - [vae_world_run_call]: revoke the world, before the call to [B.adv]. *)

Section VAE_World_Call.
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

  (** Before the first call to [g]: the flag is set to [false] in the
      revoked world [W1 = revoke W0]. *)
  Lemma vae_world_flag_false (W W0 : WORLD) (i : positive) :
    let W2 := <l[i:=false]l>(revoke W0) in
    related_sts_priv_world W W0 ->
    (∃ b : bool, loc W !! i = Some (encode b)) ->
    wrel W !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
    wrel W0 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
    (∃ b0 : bool, loc (revoke W0) !! i = Some (encode b0)) ∧
    revoke_condition (revoke W0) ∧
    related_sts_priv_world (revoke W0) W2 ∧
    related_sts_priv_world W0 W2 ∧
    loc W2 !! i = Some (encode false) ∧
    wrel W2 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv).
  Proof.
    intros W2 Hpriv [b Hloc] Hrel Hrel0.
    destruct (awk_loc_is_bool_mono_priv W W0 i b Hpriv Hloc Hrel) as [b0 Hloc0].
    assert (related_sts_priv_world (revoke W0) W2) as Hpriv12.
    { subst W2; eapply awk_loc_update_false_related_priv; eauto. }
    split; first by exists b0.
    split; first apply revoke_conditions_sat.
    split; first done.
    split.
    { eapply related_sts_priv_trans_world; last exact Hpriv12.
      apply revoke_related_sts_priv_world. }
    subst W2; split; [by simplify_map_eq | done].
  Qed.

  (** Before the second call to [g]: the flag is set to [true] in the
      revoked world [W4 = revoke W3], where [W3] is the world after the
      first call. *)
  Lemma vae_world_flag_true (W2 W3 : WORLD) (i : positive) (b : bool) :
    let W5 := <l[i:=true]l>(revoke W3) in
    loc W2 !! i = Some (encode b) ->
    wrel W2 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
    wrel W3 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
    related_sts_pub_world W2 W3 ->
    revoke_condition (revoke W3) ∧
    related_sts_priv_world (revoke W3) W5 ∧
    related_sts_priv_world W3 W5 ∧
    related_sts_priv_world W2 W5 ∧
    loc W5 !! i = Some (encode true).
  Proof.
    intros W5 Hloc Hrel Hrel3 Hpub.
    assert (related_sts_priv_world W2 (revoke W3)) as Hpriv24.
    { eapply related_sts_priv_trans_world.
      - by apply related_sts_pub_priv_world.
      - apply revoke_related_sts_priv_world. }
    destruct (awk_loc_is_bool_mono_priv _ _ i b Hpriv24 Hloc Hrel) as [b' Hloc'].
    assert (related_sts_pub_world (revoke W3) W5) as Hpub45.
    { subst W5; eapply awk_loc_update_true_related_pub; eauto. }
    assert (related_sts_priv_world W3 W5) as Hpriv35.
    { eapply (related_sts_priv_pub_trans_world W3 (revoke W3)); eauto.
      apply revoke_related_sts_priv_world. }
    split; first apply revoke_conditions_sat.
    split; first by apply related_sts_pub_priv_world.
    split; first done.
    split; first (eapply related_sts_pub_priv_trans_world; eauto).
    subst W5; by simplify_map_eq.
  Qed.

  (** The stack frame, revoked in [revoke Wm], stays revoked after an
      update of the custom location of the flag. *)
  Lemma vae_world_stack (Wm : WORLD) (C : CmptName) (i : positive) (x : bool)
    (la : list Addr) :
    let Wn := <l[i:=x]l>(revoke Wm) in
    related_sts_priv_world Wm Wn ->
    revoked_addresses (revoke Wm) la ->
    StackRevokedResources Wm C la -∗
    StackRevokedResources Wn C la ∗ ⌜revoked_addresses Wn la⌝.
  Proof.
    iIntros (Wn Hpriv Hrevoked) "Hstack".
    iSplit; last done.
    iApply (StackRevokedResources_mono_priv with "Hstack"); done.
  Qed.

  (** The callback [g] is safe in a private future world, when it is a
      sealed entry point. *)
  Lemma vae_world_callback (W W' : WORLD) (C : CmptName) (wg : Word) :
    related_sts_priv_world W W' ->
    (if is_sealed_with_o wg ot_switcher then interp W C wg else True) -∗
    (if is_sealed_with_o wg ot_switcher then interp W' C wg else True).
  Proof.
    iIntros (Hpriv) "Hg".
    destruct (is_sealed_with_o wg ot_switcher) eqn:Hsealed; last done.
    destruct wg as [| [|] | |]; try discriminate.
    iApply (interp_monotone_sd W W'); eauto.
  Qed.

  (** The world [W'] after a call is a public future world of the world [W]
      of the call, when the stack frame is revoked in [W]. *)
  Lemma vae_world_pub_call (W W' : WORLD) (b e : Addr) :
    revoked_addresses W (finz.seq_between b e) ->
    related_sts_pub_world
      (std_update_multiple W (finz.seq_between (b ^+ 4)%a e) Temporary) W' ->
    related_sts_pub_world W W'.
  Proof.
    intros Hrevoked Hpub.
    eapply related_sts_pub_trans_world; last exact Hpub.
    apply related_sts_pub_update_multiple_temp.
    apply Forall_forall; intros a Ha.
    rewrite /revoked_addresses Forall_forall in Hrevoked.
    apply Hrevoked.
    rewrite !elem_of_finz_seq_between in Ha |- *; solve_addr+Ha.
  Qed.

  (** The argument registers of [awkward] other than the callback [g] are
      cleared. *)
  Lemma vae_args_zero (rmap : Reg) :
    (∀ r, is_Some (rmap !! r)) ->
    (∀ (r : RegName) (v : Word),
        ⌜r ∉ ({[PC; cra; cgp; csp]} ∪ dom_arg_rmap 1 : gset RegName)⌝ →
        ⌜rmap !! r = Some v⌝ →
        ⌜v = WInt 0⌝ : iProp Σ) -∗
    ⌜∀ r, r ∈ ({[ ca1 ; ca2 ; ca3 ; ca4 ; ca5 ]} : gset RegName) → rmap !! r = Some (WInt 0)⌝.
  Proof.
    iIntros (Hfull) "#Hzero".
    iIntros (r Hr).
    destruct (Hfull r) as [v Hv].
    iDestruct ("Hzero" $! r v with "[%] [%]") as %->; [|done|done].
    rewrite /dom_arg_rmap.
    set_solver.
  Qed.

  (** The registers returned by a call to the switcher are cleared. *)
  Lemma vae_rmap_zero (rmap : Reg) :
    dom rmap = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ->
    map_Forall (λ _ w, w = WInt 0) rmap ->
    ∀ r, r ∈ ({[ ca2 ; ca3 ; ca4 ; ca5 ]} : gset RegName) →
         delete ct1 (delete ct0 rmap) !! r = Some (WInt 0).
  Proof.
    intros Hdom Hzero r Hr.
    rewrite !lookup_delete_ne; [|set_solver+Hr..].
    assert (is_Some (rmap !! r)) as [w Hw].
    { apply elem_of_dom; rewrite Hdom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver+Hr]. }
    rewrite Hw; f_equal.
    by eapply map_Forall_lookup_1 in Hw; last exact Hzero.
  Qed.

  (** The argument registers of the calls to [g]: all the argument
      registers are cleared, and [ct0] is the entry point of the
      switcher. *)
  Lemma vae_call_args W C (Nswitcher : namespace) (rmap : Reg) :
    dom rmap = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ca0 ; ca1 ; ct0 ]} ->
    (∀ r, r ∈ ({[ ca2 ; ca3 ; ca4 ; ca5 ]} : gset RegName) → rmap !! r = Some (WInt 0)) ->
    na_inv cerise_nais Nswitcher switcher_inv -∗
    ca0 ↦ᵣ WInt 0 -∗
    ca1 ↦ᵣ WInt 0 -∗
    ct0 ↦ᵣ vae_switcher_entry -∗
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) -∗
    ∃ rmap',
      ⌜ dom rmap' = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ⌝ ∗
      ([∗ map] rarg↦warg ∈ vae_call_adv_arg_rmap, rarg ↦ᵣ warg ∗ interp W C warg) ∗
      ([∗ map] r↦w ∈ rmap', r ↦ᵣ w).
  Proof.
    iIntros (Hrmap_dom Hzero) "#Hswitcher Hca0 Hca1 Hct0 Hrmap".
    iDestruct (big_sepM_delete _ _ ca2 with "Hrmap") as "[Hca2 Hrmap]".
    { apply Hzero; set_solver+. }
    iDestruct (big_sepM_delete _ _ ca3 with "Hrmap") as "[Hca3 Hrmap]".
    { rewrite lookup_delete_ne //; apply Hzero; set_solver+. }
    iDestruct (big_sepM_delete _ _ ca4 with "Hrmap") as "[Hca4 Hrmap]".
    { rewrite !lookup_delete_ne //; apply Hzero; set_solver+. }
    iDestruct (big_sepM_delete _ _ ca5 with "Hrmap") as "[Hca5 Hrmap]".
    { rewrite !lookup_delete_ne //; apply Hzero; set_solver+. }
    iExists _; iFrame "Hrmap".
    iSplit.
    { iPureIntro.
      rewrite !dom_delete_L Hrmap_dom /dom_arg_rmap.
      set_solver+. }
    iAssert (interp W C (WInt 0)) as "#Hint"; first iApply interp_int.
    iAssert (interp W C vae_switcher_entry) as "#Hentry".
    { iApply (interp_switcher_call with "Hswitcher"). }
    rewrite /vae_call_adv_arg_rmap.
    repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
    done.
  Qed.

  (** Before the call to [B.adv]: revoke the world [W0], to get the stack
      frame. The entry point of [B.adv] is still safe in the revoked
      world. *)
  Lemma vae_world_run_call W0 C (csp_b csp_e : Addr) (C_f : Sealable) :
    interp W0 C (WCap RWL Local csp_b csp_e csp_b) -∗
    interp W0 C (WSealed ot_switcher C_f) -∗
    world_interp W0 C
    ={⊤}=∗
    ∃ stk_mem,
      world_interp (revoke W0) C ∗
      interp (revoke W0) C (WSealed ot_switcher C_f) ∗
      ▷ StackRevokedResources (revoke W0) C (finz.seq_between csp_b csp_e) ∗
      ⌜revoked_addresses (revoke W0) (finz.seq_between csp_b csp_e)⌝ ∗
      [[csp_b, csp_e]] ↦ₐ [[stk_mem]].
  Proof.
    iIntros "#Hinterp_csp #Hinterp_C_f Hworld_interp_C".
    iMod (world_interp_revoke_stack with "[$Hinterp_csp $Hworld_interp_C]")
      as (l) "(_ & Hworld_interp_C & Hstack_revoked & >%Hstack_revoked
               & >[%stk_mem Hstk] & _ & _)".
    pose proof (revoke_related_sts_priv_world W0) as Hpriv_W0_W1.
    iModIntro.
    iExists stk_mem.
    iFrame "Hworld_interp_C Hstk".
    iSplit; first (iApply interp_monotone_sd; eauto).
    iSplit; last done.
    iNext.
    iApply (StackRevokedResources_mono_priv with "Hstack_revoked"); eauto.
  Qed.

End VAE_World_Call.
