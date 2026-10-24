From iris.proofmode Require Import proofmode.
From griotte Require Import logrel memory_region rules proofmode.
From griotte Require Import switcher_preamble.

(** * Sealing by the switcher's otype

    Monotonicity of [ot_switcher_prop] in the world, and its stability under
    [lborrow]. *)

Section Switcher_sealing.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Lemma mono_priv_ot_switcher (C : CmptName) (w : LWord) :
    ⊢ future_priv_mono C ot_switcher_propC w.
  Proof.
    iIntros (W W' Hrelated_W_W').
    iModIntro.
    iIntros "Hot_switcher".
    iEval (cbn) in "Hot_switcher".
    iEval (cbn).
    iNamed "Hot_switcher".
    iExists g_tbl, b_tbl, e_tbl, a_tbl, bpcc, epcc, bcgp, ecgp, nargs, minstk, off, posture,
      eh, ehs.
    iFrame "#%".
    iIntros "!>" (W'' Hrelated_W'_W'').
    iApply "Hentry_cont".
    iPureIntro.
    by eapply related_sts_priv_trans_world.
  Qed.


  Lemma ot_switcher_prop_borrow (W : WORLD) (C : CmptName) (w : LWord) :
    ot_switcher_prop W C w -∗ ot_switcher_prop W C (lborrow w).
  Proof.
    iIntros "Hot_switcher".
    iEval (cbn) in "Hot_switcher".
    iEval (cbn).
    iNamed "Hot_switcher". subst w.
    iFrame "#∗%".
    iExists Local; iPureIntro; done.
  Qed.

End Switcher_sealing.
