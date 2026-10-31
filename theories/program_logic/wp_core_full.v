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

Section instr_val.
  Context `{MP : MachineParameters}.

  (* TODO: move to opsem/griotte_opsem_prop.v *)
  (** An instruction never leaves the machine executable. *)
  Lemma exec_not_executable i p φ : (exec i p φ).1 ≠ Executable.
  Proof.
    rewrite /exec. destruct (exec_opt i p φ) as [c|] eqn:Hc; last done.
    assert (∀ φ' z c', advancePC φ' z = Some c' → c'.1 = NextI) as Hadv.
    { intros φ' z c' Hadv. rewrite /advancePC in Hadv. repeat case_match; by simplify_eq/=. }
    destruct i; cbn in Hc; try unfold nextPC, exec_jcond in Hc;
      repeat (simplify_option_eq || case_match); simplify_eq/=.
    all: try done.
    all: try (unfold nextPC in Hc); apply Hadv in Hc; by rewrite Hc.
  Qed.

  (* TODO: move to opsem/griotte_opsem_prop.v *)
  (** One step of an instruction reaches a value, without forks. *)
  Lemma prim_step_instr_val σ κ e2 σ2 efs :
    griotte_lang.prim_step (Instr Executable) σ κ e2 σ2 efs →
    is_Some (griotte_lang.to_val e2) ∧ efs = [].
  Proof.
    intros (_ & -> & c & -> & Hstep)%prim_step_exec_inv. split; last done.
    inversion Hstep as [| |φ p g b e a i c' wa _ _ _ _ Hexec]; subst; try done.
    pose proof (exec_not_executable i p σ) as Hne.
    destruct (exec i p σ).1; done.
  Qed.
End instr_val.

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
End wp_core_full.
