From iris.proofmode Require Import proofmode.
From griotte Require Import sts_multiple_updates.
From griotte Require Import logrel_binary interp_weakening_binary monotone_binary.
From griotte Require Import region_invariants_revocation_binary.
From griotte Require Import rules proofmode proofmode_binary.
From griotte Require Import world_ghost_theory_binary world_interp_stack_binary stack_world_resources_binary.
From griotte Require Import write_only_secret_spec_states_binary.

(** * Logical steps of the proof of [write_only_secret_spec]

    The lemmas of this file do not execute code:
    - the safety predicate [write_only_pred] of the cell holding the
      secret, which is shared with [B] as a permanent region of the world
      of [B]: a pair of safe words, or any pair of integers. The two runs
      may store different integers in the cell. Since the capability given
      to [B] cannot read the cell, the region does not need to satisfy the
      read condition of the logical relation;
    - the sharing of the cell before the call to [B.f], used between the
      block groups of [write_only_secret_spec_<segment>_blocks_<n>_binary]
      in the proof of [write_only_secret_spec]. *)

(** ** Safety predicate of the shared cell *)
Section Write_only_pred.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
  .

  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO (Word * Word)) -n> iPropO Σ).

  (** Either a pair of safe words, or any pair of integers. *)
  Program Definition write_only_pred : V :=
    λne (W : WORLD) (C : leibnizO CmptName) (ww : leibnizO (Word * Word)),
      (interp W C ww ∨ ⌜∃ z1 z2 : Z, ww = (WInt z1, WInt z2)⌝)%I.
  Solve All Obligations with solve_proper.

  Lemma persistent_cond_write_only_pred : persistent_cond write_only_pred.
  Proof. intros WCv; apply _. Qed.

  Lemma zcond_write_only_pred C : ⊢ zcond write_only_pred C.
  Proof.
    iModIntro; iIntros (W1 W2 z1 z2) "_".
    iRight; iPureIntro; by exists z1, z2.
  Qed.

  Lemma wcond_write_only_pred C : ⊢ wcond write_only_pred C interp.
  Proof. iModIntro; iIntros (W w) "Hw"; by iLeft. Qed.

  Lemma future_priv_mono_write_only_pred_z C (z1 z2 : Z) :
    ⊢ future_priv_mono C (safeC write_only_pred) (WInt z1, WInt z2).
  Proof.
    iModIntro; iIntros (W W') "_ _".
    iRight; iPureIntro; by exists z1, z2.
  Qed.

  Lemma monoReq_write_only_pred W C a :
    std W !! a = Some Permanent →
    ⊢ monoReq W C a WO write_only_pred.
  Proof.
    intros Ha.
    rewrite /monoReq Ha.
    iIntros (w [Hw1 _] W1 W2 Hrelated) "!> [Hw | Hw]".
    - iLeft.
      iApply (interp_monotone_nl with "[//] [] Hw").
      iPureIntro.
      rewrite /canStore in Hw1.
      cbn; by destruct (isLocalWord w.1).
    - by iRight.
  Qed.

  (** The write-only capability to a permanent cell with predicate
      [write_only_pred] is safe to share. *)
  Lemma interp_write_only_cap W C (a a' : Addr) :
    (a + 1)%a = Some a' →
    std W !! a = Some Permanent →
    rel C a WO (safeC write_only_pred) -∗
    interp W C (WCap WO Global a a' a, WCap WO Global a a' a).
  Proof.
    iIntros (Ha' Hstd) "#Hrel".
    iEval (rewrite interp_diag_eq // /interp1_diag /=).
    rewrite (finz_seq_between_cons a); last solve_addr.
    rewrite (finz_seq_between_empty (a ^+ 1)%a); last solve_addr.
    iApply big_sepL_singleton.
    iExists WO, write_only_pred.
    iSplit; first done.
    iSplit; first (iPureIntro; apply persistent_cond_write_only_pred).
    iSplit; first iFrame "Hrel".
    iSplit; first (iNext; iApply zcond_write_only_pred).
    iSplit; first done.
    iSplit; first (iNext; iApply wcond_write_only_pred).
    iSplit; first (by iApply monoReq_write_only_pred).
    done.
  Qed.

End Write_only_pred.

Section Write_only_secret_World.
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

  (** ** Sharing the secret cell with a callee

      Relinquish the cell [a], which holds an integer in each run, into the
      world of the callee, as a permanent address with the predicate
      [write_only_pred], so that the capability [(WO, Global, a, a', a)] is
      safe to share. The stack frame stays revoked. *)
  Lemma write_only_secret_world_share W C (a a' csp_b csp_e : Addr) (target : Sealable)
    (stk_mem : list Word) (secret1 secret2 : Z) :
    let W' := <s[a := Permanent ]s> W in
    let stk := finz.seq_between csp_b csp_e in
    (a + 1)%a = Some a' ->
    a ∉ dom (std W) ->
    revoked_addresses W stk ->
    world_interp W C -∗
    StackRevokedResources W C stk -∗
    interp W C (WSealed ot_switcher target, WSealed ot_switcher target) -∗
    a ↦ₐ WInt secret1 -∗
    a ↣ₐ WInt secret2 -∗
    [[ csp_b , csp_e ]] ↦ₐ [[ stk_mem ]]
    ={⊤}=∗
    world_interp W' C ∗
    interp W' C (WCap WO Global a a' a, WCap WO Global a a' a) ∗
    interp W' C (WSealed ot_switcher target, WSealed ot_switcher target) ∗
    StackRevokedResources W' C stk ∗
    ⌜ revoked_addresses W' stk ⌝ ∗
    [[ csp_b , csp_e ]] ↦ₐ [[ stk_mem ]].
  Proof.
    intros W' stk.
    iIntros (Ha' Ha_fresh Hrevoked_stk)
      "Hworld #Hstack_revoked #Htarget Ha Hsa Hstk".
    iDestruct (big_sepL2_disjoint_pointsto with "[$Hstk $Ha]") as "%Ha_stk".

    (* Relinquish [a] into the world, as a permanent address whose two runs
       may hold different integers *)
    iDestruct (init_PermRes W C a WO (safeC write_only_pred) (WInt secret1, WInt secret2)
                with "[] [$Ha] [$Hsa] []") as "Ha".
    { done. }
    { iApply future_priv_mono_write_only_pred_z. }
    { iRight; iPureIntro; by eexists _, _. }
    iMod (world_interp_extend_perm with "Hworld Ha") as "(Hworld & #Hrel_a)"; auto.
    iModIntro.
    assert (related_sts_priv_world W W') as HW_priv_W'.
    { subst W'. by eapply related_sts_priv_world_fresh_Permanent. }
    iFrame "Hworld Hstk".

    (* The write-only capability to [a] is safe to share *)
    iSplit.
    { iApply (interp_write_only_cap with "Hrel_a"); first done.
      subst W'; by rewrite /= lookup_insert_eq. }

    (* The entry point of the callee is still safe to share *)
    iSplit; first (iApply interp_monotone_sd; eauto).

    (* The stack is still revoked *)
    iSplit; first (iApply (StackRevokedResources_mono_priv with "Hstack_revoked"); auto).
    iPureIntro.
    rewrite /revoked_addresses Forall_forall.
    rewrite /revoked_addresses Forall_forall in Hrevoked_stk.
    intros a'' Ha''. subst W'; cbn.
    rewrite lookup_insert_ne; last (intros ->; set_solver+Ha_stk Ha'').
    by apply Hrevoked_stk.
  Qed.

End Write_only_secret_World.
