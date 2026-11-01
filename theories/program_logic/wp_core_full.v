From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre.
From griotte Require Import rules_base.

(** * The full-link adapter

    [wp_core_full] runs one instruction at the link of a routing law from a
    WP of the instruction at the core link. The core step sees neither the
    link nor the posture: the adapter takes [handover_res] out of the link
    or out of what the thread holds at the pre-step MIE, by the routing
    law, and rebuilds the link and what the thread holds at the post-step
    MIE. *)

(** For the destruction of an existential posture under a later. *)
#[export] Instance InterruptStatus_inhabited : Inhabited InterruptStatus :=
  populate InterruptDisabled.

Section wp_core_full.
  Context `{MP : MachineParameters} `{ceriseg : ceriseG Σ} {th : Thread} {CL : CritLink Σ th}
    {CR : CritRoute Σ th CL}.

  (** The adapter, in the shape of the world accessor of the step lemma:
      the core step receives the MIE fragment of the thread at [b] and
      gives back the fragment at the post-step MIE [b'], under a later; the
      thread gets back what it holds at [b']. *)
  Lemma wp_core_full E b (Ψ : InterruptStatus → griotte_lang.val → iProp Σ) :
    route_pre th b →
    held b -∗
    MIE ↦ₜ b -∗
    (MIE ↦ₜ b -∗
     @wp _ _ _ _ (@wp' _ _ _ (memG_irisG (CL := link_core))) NotStuck E (Instr Executable)
       (λ v, ▷ ∃ b', MIE ↦ₜ b' ∗ Ψ b' v)) -∗
    WP Instr Executable @ E {{ v, ▷ ∃ b', held b' ∗ MIE ↦ₜ b' ∗ Ψ b' v }}.
  Proof.
    iIntros (Hpre) "Hh Hm HK".
    iEval (rewrite wp_unfold /wp_pre /=).
    iIntros (σ ns κ κs nt) "[Hσ Hl]".
    iDestruct (SI_mie_st with "Hσ Hm") as %Hb.
    iMod (crit_route σ with "Hl [Hh]") as "[Hho Hrestore]"; [by rewrite Hb | by rewrite Hb |].
    iSpecialize ("HK" with "Hm").
    iEval (rewrite wp_unfold /wp_pre /=) in "HK".
    iMod ("HK" $! σ ns κ κs nt with "[$Hσ]") as "[%Hred HK]".
    iModIntro. iSplit; first done.
    iIntros (e2 σ2 efs Hstep) "Hlc".
    pose proof (base_reducible_prim_step _ _ _ _ _ _ (normal_always_base_reducible σ) Hstep)
      as Hbstep.
    destruct (prim_step_instr_val _ _ _ _ _ Hbstep) as [ [v Hv] ->].
    iMod ("HK" with "[//] Hlc") as "HK".
    iModIntro. iNext. iMod "HK". iModIntro. iMod "HK" as "([Hσ _] & Hwp & _)".
    destruct (griotte_lang.of_to_val _ _ Hv).
    iEval (rewrite !wp_unfold /wp_pre /= griotte_lang.to_of_val) in "Hwp".
    iEval (rewrite !wp_unfold /wp_pre /= griotte_lang.to_of_val).
    iMod "Hwp" as "Hpost".
    iDestruct "Hpost" as (b') "[>Hm HΨ]".
    iDestruct (SI_mie_st with "Hσ Hm") as %Hb'.
    destruct b'.
    - iMod ("Hrestore" with "Hσ [Hho]") as "(Hσ & Hl & _)"; first by rewrite Hb'.
      iModIntro. iFrame "Hσ Hl". iSplitL; last done.
      iModIntro. iNext. iExists InterruptEnabled. by iFrame.
    - iMod ("Hrestore" with "Hσ []") as "(Hσ & Hl & Hp)"; first by rewrite Hb'.
      rewrite Hb'. iModIntro. iFrame "Hσ Hl". iSplitL; last done.
      iModIntro. iNext. iExists InterruptDisabled. by iFrame.
  Qed.

  (** The same, with the critical-section token lent to the core step: the
      core step may open and close invariants of the pool [crit], and gives
      the token back with its value. *)
  Lemma wp_core_full_crit E b (Ψ : InterruptStatus → griotte_lang.val → iProp Σ) :
    route_pre th b →
    held b -∗
    MIE ↦ₜ b -∗
    (na_own crit ⊤ -∗
     MIE ↦ₜ b -∗
     @wp _ _ _ _ (@wp' _ _ _ (memG_irisG (CL := link_core))) NotStuck E (Instr Executable)
       (λ v, ▷ ∃ b', na_own crit ⊤ ∗ MIE ↦ₜ b' ∗ Ψ b' v)) -∗
    WP Instr Executable @ E {{ v, ▷ ∃ b', held b' ∗ MIE ↦ₜ b' ∗ Ψ b' v }}.
  Proof.
    iIntros (Hpre) "Hh Hm HK".
    iEval (rewrite wp_unfold /wp_pre /=).
    iIntros (σ ns κ κs nt) "[Hσ Hl]".
    iDestruct (SI_mie_st with "Hσ Hm") as %Hb.
    iMod (crit_route σ with "Hl [Hh]") as "[Hho Hrestore]"; [by rewrite Hb | by rewrite Hb |].
    iDestruct (handover_res_crit with "Hho") as "[Htok Hho]".
    iSpecialize ("HK" with "Htok Hm").
    iEval (rewrite wp_unfold /wp_pre /=) in "HK".
    iMod ("HK" $! σ ns κ κs nt with "[$Hσ]") as "[%Hred HK]".
    iModIntro. iSplit; first done.
    iIntros (e2 σ2 efs Hstep) "Hlc".
    pose proof (base_reducible_prim_step _ _ _ _ _ _ (normal_always_base_reducible σ) Hstep)
      as Hbstep.
    destruct (prim_step_instr_val _ _ _ _ _ Hbstep) as [ [v Hv] ->].
    iMod ("HK" with "[//] Hlc") as "HK".
    iModIntro. iNext. iMod "HK". iModIntro. iMod "HK" as "([Hσ _] & Hwp & _)".
    destruct (griotte_lang.of_to_val _ _ Hv).
    iEval (rewrite !wp_unfold /wp_pre /= griotte_lang.to_of_val) in "Hwp".
    iEval (rewrite !wp_unfold /wp_pre /= griotte_lang.to_of_val).
    iMod "Hwp" as "Hpost".
    iDestruct "Hpost" as (b') "(>Htok & >Hm & HΨ)".
    iSpecialize ("Hho" with "Htok").
    iDestruct (SI_mie_st with "Hσ Hm") as %Hb'.
    destruct b'.
    - iMod ("Hrestore" with "Hσ [Hho]") as "(Hσ & Hl & _)"; first by rewrite Hb'.
      iModIntro. iFrame "Hσ Hl". iSplitL; last done.
      iModIntro. iNext. iExists InterruptEnabled. by iFrame.
    - iMod ("Hrestore" with "Hσ []") as "(Hσ & Hl & Hp)"; first by rewrite Hb'.
      rewrite Hb'. iModIntro. iFrame "Hσ Hl". iSplitL; last done.
      iModIntro. iNext. iExists InterruptDisabled. by iFrame.
  Qed.
End wp_core_full.
