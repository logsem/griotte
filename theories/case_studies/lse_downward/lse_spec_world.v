From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode.
From griotte Require Import region_invariants_revocation interp_weakening monotone.
From griotte Require Import world_interp_stack.
From griotte Require Import lse_spec_states.

(** * Revocation of the world in [run] and [f]

    The lemmas of this file do not execute code:
    - [lse_world_call]: used before the call to [C_f] in the proof of
      [lse_run_spec]. Revoke the world, to get the stack frame and its
      revoked resources. The entry point of [C_f] is still safe in the
      revoked world.
    - [lse_world_f]: used at the entry point of [f] in the proof of
      [lse_f_spec]. Revoke the world, to get the stack frame and the
      revoked temporary addresses [l]. Closing them in the revoked world
      yields a public future world of the initial world, for the return of
      [f]. *)

Section LSE_World.
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

  Lemma lse_world_call W0 C (csp_b csp_e : Addr) (C_f : Sealable) :
    interp W0 C (WCap RWL Local csp_b csp_e csp_b) -∗
    interp W0 C (WSealed ot_switcher C_f) -∗
    world_interp W0 C
    ={⊤}=∗
    ∃ stk_mem,
      ⌜revoked_addresses (revoke W0) (finz.seq_between csp_b csp_e)⌝ ∗
      world_interp (revoke W0) C ∗
      interp (revoke W0) C (WSealed ot_switcher C_f) ∗
      ▷ StackRevokedResources (revoke W0) C (finz.seq_between csp_b csp_e) ∗
      [[csp_b, csp_e]] ↦ₐ [[stk_mem]].
  Proof.
    iIntros "#Hinterp_csp #Hinterp_C_f Hworld_interp_C".
    iMod (world_interp_revoke_stack with "[$Hinterp_csp $Hworld_interp_C]")
      as (l) "(_ & Hworld_interp_C & Hstack_revoked & >%Hstack_revoked
               & >[%stk_mem Hstk] & _)".
    pose proof (revoke_related_sts_priv_world W0) as Hpriv_W0_W1.
    iModIntro.
    iExists stk_mem.
    iFrame "Hworld_interp_C Hstk".
    iSplit; first done.
    iSplit; first (iApply interp_monotone_sd; eauto).
    iNext.
    iApply (StackRevokedResources_mono_priv with "Hstack_revoked"); eauto.
  Qed.

  Lemma lse_world_f W0 C (csp_b csp_e : Addr) :
    interp W0 C (WCap RWL Local csp_b csp_e csp_b) -∗
    world_interp W0 C
    ={⊤}=∗
    ∃ l stk_mem,
      ⌜extract_temporaries_condition W0 (l ++ finz.seq_between csp_b csp_e)⌝ ∗
      ⌜related_sts_pub_world W0
         (close_list (l ++ finz.seq_between csp_b csp_e) (revoke W0))⌝ ∗
      world_interp (revoke W0) C ∗
      ▷ RevokedResources W0 C l ∗
      [[csp_b, csp_e]] ↦ₐ [[stk_mem]].
  Proof.
    iIntros "#Hinterp_csp Hworld_interp_C".
    iMod (world_interp_revoke_stack with "[$Hinterp_csp $Hworld_interp_C]")
      as (l) "(%Hextract & Hworld_interp_C & _ & _ & >[%stk_mem Hstk] & Hrevoked_l & _)".
    iModIntro.
    iExists l, stk_mem.
    iFrame "Hworld_interp_C Hstk Hrevoked_l".
    iSplit; first done.
    iPureIntro.
    apply related_pub_revoke_close_list.
    by destruct Hextract.
  Qed.

End LSE_World.
