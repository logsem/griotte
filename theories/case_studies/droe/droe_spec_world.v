From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening proofmode.
From griotte Require Import sts_multiple_updates.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import register_tactics.
From griotte Require Import droe_spec_states.

(** * Logical steps of the proof of [droe_spec]

    The lemmas of this file do not execute code. They are used between the
    block groups of [droe_spec_<segment>_blocks_<n>] in the proof of
    [droe_spec]. *)

Section DROE_World.
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

  (** ** Initial memory *)

  Lemma droe_data_split (cgp_b cgp_e : Addr) :
    (cgp_b + length droe_main_data)%a = Some cgp_e ->
    [[ cgp_b , cgp_e ]] ↦ₐ [[ droe_main_data ]] -∗
    cgp_b ↦ₐ WInt 0 ∗
    (cgp_b ^+ 1)%a ↦ₐ WInt 0.
  Proof.
    iIntros (Hcgp_contiguous) "Hcgp_main".
    iDestruct (region_pointsto_cons with "Hcgp_main") as "[$ Hcgp_main]".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Hcgp_main") as "[$ _]".
    { transitivity (Some (cgp_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }
  Qed.

  Lemma droe_imports_split (pc_b pc_a : Addr) (C_f : Sealable) :
    (pc_b + length (droe_main_imports C_f))%a = Some pc_a ->
    [[ pc_b , pc_a ]] ↦ₐ [[ droe_main_imports C_f ]] -∗
    droe_imports pc_b C_f.
  Proof.
    iIntros (Himports_contiguous) "Himports_main".
    iDestruct (region_pointsto_cons with "Himports_main") as "[$ Himports_main]".
    { transitivity (Some (pc_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[$ Himports_main]".
    { transitivity (Some (pc_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[$ _]".
    { transitivity (Some (pc_b ^+ 3)%a); auto; solve_addr. }
    { solve_addr. }
  Qed.

  (** ** Arguments of a call to the switcher

      The entry point of the adversary takes one argument, [ca0]. The other
      argument registers are passed unchanged. *)

  Lemma droe_switcher_call_args W C (rmap : Reg) (wca0 wca1 wct0 wct2 wct3 : Word) :
    dom rmap = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ; ct0 ; ct1 ; ct2 ; ct3 ; cs0 ; cs1 ]} ->
    ca0 ↦ᵣ wca0 -∗
    interp W C wca0 -∗
    ca1 ↦ᵣ wca1 -∗
    ct0 ↦ᵣ wct0 -∗
    ct2 ↦ᵣ wct2 -∗
    ct3 ↦ᵣ wct3 -∗
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) -∗
    ∃ arg_rmap rmap',
      ⌜ dom rmap' = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ⌝ ∗
      ⌜ is_arg_rmap arg_rmap 8 ⌝ ∗
      ([∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg ∗
                                     (if decide (rarg ∈ dom_arg_rmap 1)
                                      then interp W C warg
                                      else True)) ∗
      ([∗ map] r↦w ∈ rmap', r ↦ᵣ w).
  Proof.
    iIntros (Hrmap_dom) "Hca0 #Hinterp_ca0 Hca1 Hct0 Hct2 Hct3 Hrmap".
    iExtractList "Hrmap" [ca2;ca3;ca4;ca5] as ["Hca2"; "Hca3"; "Hca4"; "Hca5"].
    iInsertList "Hrmap" [ct2;ct3].
    iExists {[ ca0 := wca0; ca1 := wca1; ca2 := wca2; ca3 := wca3;
               ca4 := wca4; ca5 := wca5; ct0 := wct0 ]}, _.
    iFrame "Hrmap".
    iSplit.
    { iPureIntro.
      repeat (rewrite dom_insert_L); repeat (rewrite dom_delete_L).
      rewrite Hrmap_dom /dom_arg_rmap.
      set_solver+.
    }
    iSplit; first by rewrite /is_arg_rmap.
    repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
    done.
  Qed.

  (** ** Sharing the data with the adversary

      The world in which the call happens: [cgp_b] and [cgp_b + 1] are
      added to the revoked world as permanent addresses, with a read-only
      safety predicate that fixes their content. *)
  Definition droe_Wshare W (cgp_b : Addr) : WORLD :=
    <s[(cgp_b ^+ 1)%a := Permanent ]s> (<s[cgp_b := Permanent ]s> (revoke W)).

  (** The safety predicate of [cgp_b]: it always contains [42]. *)
  Definition droe_b_pred : WORLD * CmptName * Word → iProp Σ :=
    safeC (interp_dro_eq (WInt 42)).

  Lemma droe_world_share W0 C (cgp_b cgp_e csp_b csp_e : Addr) (C_f : Sealable) :
    let W3 := droe_Wshare W0 cgp_b in
    (cgp_b + length droe_main_data)%a = Some cgp_e ->
    cgp_b ∉ dom (std W0) ->
    (cgp_b ^+ 1)%a ∉ dom (std W0) ->
    revoked_addresses (revoke W0) (finz.seq_between csp_b csp_e) ->
    world_interp (revoke W0) C -∗
    StackRevokedResources W0 C (finz.seq_between csp_b csp_e) -∗
    interp W0 C (WSealed ot_switcher C_f) -∗
    cgp_b ↦ₐ WInt 42 -∗
    (cgp_b ^+ 1)%a ↦ₐ WCap RW Global cgp_b (cgp_b ^+ 1)%a cgp_b
    ={⊤}=∗
    world_interp W3 C ∗
    rel C cgp_b RO_DRO droe_b_pred ∗
    interp W3 C (WCap RO_DRO Global (cgp_b ^+ 1)%a (cgp_b ^+ 2)%a (cgp_b ^+ 1)%a) ∗
    interp W3 C (WSealed ot_switcher C_f) ∗
    StackRevokedResources W3 C (finz.seq_between csp_b csp_e) ∗
    ⌜ revoked_addresses W3 (finz.seq_between csp_b csp_e) ⌝.
  Proof.
    intros W3.
    iIntros (Hcgp_contiguous Hcgp_b Hcgp_a Hstack_revoked)
      "Hworld_interp_C #Hstack_revoked_W0 #Hinterp_W0_C_f Hcgp_b Hcgp_a".
    set (W1 := revoke W0).

    (* First, extend the world such that [cgp_b] is permanent, with value 42 *)
    iDestruct (init_PermRes W1 C cgp_b RO_DRO droe_b_pred
                with "[] [$Hcgp_b] []") as "PermRes_cgp_b"; auto.
    { rewrite /future_priv_mono.
      iIntros "!>" (W W' Hrelated) "H"; cbn.
      iSplitR; [done | by rewrite !fixpoint_interp1_eq].
    }
    { cbn.
      iSplitR; [done | by rewrite !fixpoint_interp1_eq].
    }
    iMod (world_interp_extend_perm with "Hworld_interp_C PermRes_cgp_b")
      as "(Hworld_interp_C & #Hrel_cgp_b)"; auto.
    { by rewrite -revoke_dom_eq. }
    set (W2 := <s[cgp_b:=Permanent]s> W1).

    (* And prove that the RO_DRO capability pointing to it is safe *)
    iAssert (interp W2 C (WCap RO_DRO Global cgp_b (cgp_b ^+ 1)%a cgp_b)) as "#Hinterp_cgp_b".
    { iEval (cbn). iEval (rewrite fixpoint_interp1_eq). iEval (cbn).
      rewrite (finz_seq_between_cons (cgp_b)%a); last solve_addr.
      rewrite (finz_seq_between_empty _ (cgp_b ^+ 1)%a); last solve_addr.
      iApply big_sepL_singleton.
      iExists RO_DRO, (interp_dro_eq _).
      iEval (cbn).
      iSplit; first done.
      iSplit.
      { iPureIntro; intros WCv; tc_solve. }
      iSplit; first iFrame "Hrel_cgp_b".
      iSplit.
      { iIntros "!>" (W1').
        iIntros "!>" (W1'' z) "[-> H]".
        rewrite /interp_dro_eq /=.
        iSplitR; [done | by rewrite !fixpoint_interp1_eq].
      }
      iSplit.
      { iIntros "!>" (W1').
        iIntros "!>" (w') "[-> H]".
        done.
      }
      iSplit; first done.
      iSplit.
      + rewrite /monoReq; subst W2 W1; cbn; rewrite lookup_insert_eq.
        iIntros (?) "%Hcontra"; rewrite /canStore in Hcontra.
        destruct (isLocalWord w); done.
      + iPureIntro.
        by rewrite lookup_insert_eq.
    }

    (* Second, extend the world such that [cgp_b+1] is permanent, with value
       the RW capability pointing to [cgp_b] *)
    iDestruct (init_PermRes W2 C (cgp_b ^+1)%a RO_DRO
                 (safeC (interp_dro_eq (WCap RW Global cgp_b (cgp_b ^+ 1)%a cgp_b)))
                with "[] [$Hcgp_a] []") as "PermRes_cgp_a"; auto.
    { rewrite /future_priv_mono.
      iIntros "!>" (W W' Hrelated) "[% H]"; cbn.
      iSplitR; [done |].
      iApply interp_monotone_nl; eauto.
    }
    { cbn; iSplit; done. }
    iMod (world_interp_extend_perm with "Hworld_interp_C PermRes_cgp_a")
      as "(Hworld_interp_C & #Hrel_cgp_a)"; auto.
    { subst W2 W1.
      cbn; rewrite dom_insert_L not_elem_of_union; split.
      + rewrite not_elem_of_singleton; solve_addr+Hcgp_contiguous.
      + by rewrite -revoke_dom_eq.
    }
    iFrame "Hworld_interp_C Hrel_cgp_b".
    iModIntro.

    assert (related_sts_priv_world W0 W3) as Hrelated_priv_W0_W3.
    { eapply related_sts_priv_trans_world with (W' := W1) ; eauto
      ; first eapply revoke_related_sts_priv_world.
      eapply related_sts_priv_trans_world with (W' := W2) ; eauto
      ; apply related_sts_priv_world_fresh_Permanent.
    }

    (* The RO_DRO capability pointing to [cgp_b+1] is safe *)
    iSplit.
    { iEval (cbn). iEval (rewrite fixpoint_interp1_eq). iEval (cbn).
      rewrite (finz_seq_between_cons (cgp_b ^+ 1)%a); last solve_addr.
      rewrite (finz_seq_between_empty _ (cgp_b ^+ 2)%a); last solve_addr.
      iApply big_sepL_singleton.
      iExists RO_DRO, (interp_dro_eq _).
      iEval (cbn).
      iSplit; first done.
      iSplit.
      { iPureIntro; intros WCv; tc_solve. }
      iSplit; first iFrame "Hrel_cgp_a".
      iSplit.
      { iIntros "!>" (W1').
        iIntros "!>" (W1'' z) "[% H]"; done.
      }
      iSplit.
      { iIntros "!>" (W1').
        iIntros "!>" (w') "[-> H]".
        done.
      }
      iSplit; first done.
      iSplit.
      + rewrite /monoReq /W3 /droe_Wshare; cbn; rewrite lookup_insert_eq.
        iIntros (?) "%Hcontra"; rewrite /canStore in Hcontra.
        destruct (isLocalWord w); done.
      + iPureIntro.
        by rewrite /W3 /droe_Wshare /= lookup_insert_eq.
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
    rewrite /W3 /droe_Wshare /=.
    rewrite !lookup_insert_ne //.
  Qed.

  (** ** Return from the call

      The adversary returned a public future [W4] of [W3]. Since [cgp_b] is
      permanent in [W3], it is still permanent in [revoke W4], and opening
      the world gives back [cgp_b], which still contains [42]. *)
  Lemma droe_world_return W0 W4 C (cgp_b cgp_e csp_b csp_e : Addr) :
    let W3 := droe_Wshare W0 cgp_b in
    let stk := finz.seq_between csp_b csp_e in
    let stk' := finz.seq_between (csp_b ^+ 4)%a csp_e in
    (cgp_b + length droe_main_data)%a = Some cgp_e ->
    (csp_b <= csp_b ^+ 4)%a ->
    revoked_addresses W3 stk ->
    related_sts_pub_world (std_update_multiple W3 stk' Temporary) W4 ->
    world_interp (revoke W4) C -∗
    rel C cgp_b RO_DRO droe_b_pred -∗
    ◇ cgp_b ↦ₐ WInt 42.
  Proof.
    intros W3 stk stk'.
    iIntros (Hcgp_contiguous Hcsp_bounds Hstack_revoked_W3 Hrelated_pub)
      "Hworld_interp #Hrel_cgp_b".
    assert (std W3 !! cgp_b = Some Permanent) as HW3_cgp_b.
    { rewrite /W3 /droe_Wshare /=.
      rewrite lookup_insert_ne; last solve_addr.
      by rewrite lookup_insert_eq.
    }
    assert (cgp_b ∉ stk') as Hcgp_b_stk'.
    { intros Hin.
      rewrite /revoked_addresses Forall_forall in Hstack_revoked_W3.
      assert (cgp_b ∈ stk) as Hin'.
      { rewrite /stk /stk' !elem_of_finz_seq_between in Hin |- *; solve_addr+Hin Hcsp_bounds. }
      apply Hstack_revoked_W3 in Hin'; congruence.
    }
    rewrite open_world_interp_empty.
    iDestruct (open_world_interp_permanent with "Hworld_interp Hrel_cgp_b")
      as "(_ & _ & [%w (_ & >Hcgp_b & Hw & _)])"; auto.
    { set_solver+. }
    { eapply (region_state_priv_perm W4); eauto.
      { eapply revoke_related_sts_priv_world. }
      eapply region_state_pub_perm; eauto.
      by rewrite std_sta_update_multiple_lookup_same_i.
    }
    rewrite /droe_b_pred /=.
    iDestruct "Hw" as "[>-> _]".
    by iModIntro.
  Qed.

End DROE_World.
