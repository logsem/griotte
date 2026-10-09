From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode.
From griotte Require Import region_invariants_revocation interp_weakening monotone.
From griotte Require Import world_interp_stack.
From griotte Require Import counter_spec_states.

(** * Preparation of the call to the switcher

    The lemma of this file does not execute code. It is used before the
    call to [C_f] in the proof of [counter_spec]:
    - [counter_world_call]: revoke the world, to get the stack frame and
      the revoked temporary addresses [l]. The entry point of [C_f] is
      still safe in the revoked world. *)

Section Counter_World_Call.
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

  Lemma counter_world_call W0 C (csp_b csp_e : Addr) (C_f : Sealable) :
    interp W0 C (WCap RWL Local csp_b csp_e csp_b) -∗
    interp W0 C (WSealed ot_switcher C_f) -∗
    world_interp W0 C
    ={⊤}=∗
    ∃ l stk_mem,
      ⌜extract_temporaries_condition W0 (l ++ finz.seq_between csp_b csp_e)⌝ ∗
      ⌜revoked_addresses (revoke W0) l⌝ ∗
      ⌜revoked_addresses (revoke W0) (finz.seq_between csp_b csp_e)⌝ ∗
      world_interp (revoke W0) C ∗
      interp (revoke W0) C (WSealed ot_switcher C_f) ∗
      ▷ StackRevokedResources (revoke W0) C (finz.seq_between csp_b csp_e) ∗
      ▷ RevokedResources W0 C l ∗
      [[csp_b, csp_e]] ↦ₐ [[stk_mem]].
  Proof.
    iIntros "#Hinterp_csp #Hinterp_C_f Hworld_interp_C".
    iMod (world_interp_revoke_stack with "[$Hinterp_csp $Hworld_interp_C]")
      as (l) "(%Hextract & Hworld_interp_C & Hstack_revoked & >%Hstack_revoked
               & >[%stk_mem Hstk] & Hrevoked_l & %Hrevoked_l)".
    pose proof (revoke_related_sts_priv_world W0) as Hpriv_W0_W1.
    iModIntro.
    iExists l, stk_mem.
    iFrame "Hworld_interp_C Hstk Hrevoked_l".
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    iSplit; first (iApply interp_monotone_sd; eauto).
    iNext.
    iApply (StackRevokedResources_mono_priv with "Hstack_revoked"); eauto.
  Qed.

End Counter_World_Call.
