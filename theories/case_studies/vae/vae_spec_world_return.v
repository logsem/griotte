From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode.
From griotte Require Import region_invariants_revocation interp_weakening monotone.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import vae_spec_states.

(** * Repair of the world before the return of [awkward]

    The lemmas of this file do not execute code. They are used after the
    second call to [g] in the proof of [vae_awkward_spec]:
    - [related_pub_W0_Wfixed]: the world obtained by closing the revoked
      addresses of the final world is a public future world of the
      initial world,
    - [vae_world_return]: the flag is still [true] after the second call,
      and the world can be repaired for the return. *)

Section VAE_World_Return.
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

  Lemma related_pub_W0_Wfixed (W0 W3 W6 : WORLD) (l : list Addr) (csp_b csp_e : Addr)
    (b : bool) (i : positive) :
    let W1 := revoke W0 in
    let W2 := <l[i:=false]l>W1 in
    let W4 := revoke W3 in
    let W5 := <l[i:=true]l>W4 in
    let W7 := revoke W6 in
    (* initial revocation W0 *)
    (∀ a : finz MemNum, std W0 !! a = Some Temporary ↔ a ∈ l ++ finz.seq_between csp_b csp_e) ->
    (* final revocation W7 *)
    Forall (λ a : finz MemNum, std W7 !! a = Some Revoked) (l ++ finz.seq_between csp_b csp_e)->
    (* world transition of the first call *)
    related_sts_pub_world W2 W3 ->
    (* world transition of the second call *)
    related_sts_pub_world W5 W6 ->
    (* custom invariant `i` in initial world W0 *)
    loc W1 !! i = Some (encode b) ->
    wrel W0 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
    (* custom invariant `i` in final world W7 *)
    loc W7 !! i = Some (encode true) ->
    wrel W7 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
    (* public transition between initial and fixed *)
    related_sts_pub_world W0 (close_list (l ++ finz.seq_between csp_b csp_e) W7).
  Proof.
    eapply awk_two_call_world_repair
      with (closing := l ++ finz.seq_between csp_b csp_e); eauto.
  Qed.

  (** After the second call to [g], in the world [W6]: the flag is still
      [true], the addresses [l] revoked at the entry of [awkward] are still
      revoked, and closing them with the stack frame yields a public future
      world of the initial world [W0]. *)
  Lemma vae_world_return (W0 W3 W6 : WORLD) (C : CmptName) (i : positive) (b : bool)
    (l : list Addr) (csp_b csp_e : Addr) :
    let W2 := <l[i:=false]l>(revoke W0) in
    let W5 := <l[i:=true]l>(revoke W3) in
    extract_temporaries_condition W0 (l ++ finz.seq_between csp_b csp_e) ->
    Forall (λ a, std (revoke W0) !! a = Some Revoked) l ->
    revoked_addresses (revoke W6) (finz.seq_between csp_b csp_e) ->
    related_sts_pub_world W2 W3 ->
    related_sts_pub_world W5 W6 ->
    loc (revoke W0) !! i = Some (encode b) ->
    wrel W0 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
    wrel W3 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
    sts_rel_loc (A:=Addr) C i awk_rel_pub awk_rel_priv -∗
    world_interp (revoke W6) C -∗
    RevokedResources W0 C l
    ==∗
    world_interp (revoke W6) C ∗
    RevokedResources W0 C l ∗
    ⌜loc (revoke W6) !! i = Some (encode true)⌝ ∗
    ⌜related_sts_pub_world W0 (close_list (l ++ finz.seq_between csp_b csp_e) (revoke W6))⌝.
  Proof.
    iIntros (W2 W5 Hextract Hrevoked_l Hrevoked_stk Hpub23 Hpub56 Hloc0 Hrel0 Hrel3)
      "#Hsts_rel Hworld_interp_C Hrevoked_l".
    iMod (world_interp_revoked_by_separation_many_with_RevokedResources
           with "[$Hworld_interp_C $Hrevoked_l]")
      as "(Hworld_interp_C & Hrevoked_l & %Hrevoked_l_W7)".
    { apply Forall_forall; intros a Ha.
      rewrite Forall_forall in Hrevoked_l.
      apply Hrevoked_l in Ha.
      rewrite -revoke_dom_eq.
      destruct Hpub56 as [ [Hdom_5_6 _] _ ].
      apply Hdom_5_6.
      cbn.
      rewrite -revoke_dom_eq.
      destruct Hpub23 as [ [Hdom_2_3 _] _ ].
      apply Hdom_2_3.
      by rewrite elem_of_dom.
    }
    iDestruct (world_interp_rel_loc_valid with "Hworld_interp_C Hsts_rel")
      as %Hrel7.
    assert (loc W5 !! i = Some (encode true)) as Hloc5.
    { subst W5; by simplify_map_eq. }
    pose proof (awk_loc_true_mono_pub W5 W6 i Hpub56 Hloc5 Hrel3) as Hloc6.
    iModIntro.
    iFrame.
    iSplit; first done.
    iPureIntro.
    destruct Hextract as [_ Htemps].
    eapply (related_pub_W0_Wfixed W0 W3 W6 l); eauto.
    apply Forall_app; split; auto.
  Qed.

End VAE_World_Return.
