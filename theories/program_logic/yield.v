From iris.proofmode Require Import proofmode.
From griotte Require Import rules_Ecall wp_core_full.

(** * A verified yield

    [wp_yield] is the environment call of verified code at a user thread:
    the thread hands its turn over ([YieldV]) and, when the switcher
    resumes it, continues at the next instruction, at the posture it
    yielded at, with every resource it kept. *)

(* TODO: move to program_logic/rules/rules_Ecall.v *)
Section yield.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}
    {CL : ∀ t, CritLink Σ t} {CR : ∀ t, CritRoute Σ t (CL t)} {th : Thread}.

  Lemma wp_yield (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
      (w : LWord) (dq : dfrac) (b : InterruptStatus) :
    th ≠ CtxSwitch →
    decodeInstrW w.(lw) = Ecall →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a -∗
    pc_a ↦ₐ{dq} w -∗
    MIE ↦ₜ[th] b -∗
    held (th := th) (CL := CL th) (CR := CR th) b -∗
    ▷ (PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a' -∗
       pc_a ↦ₐ{dq} w -∗
       MIE ↦ₜ[th] b -∗
       held (th := th) (CL := CL th) (CR := CR th) b -∗
       safe[th]) -∗
    safe[th].
  Proof.
    iIntros (Hth Hi Hpc Ha') "HPC Hpc_a HMIE Hheld Hk".
    iApply (wp_bind (@fill (tlang_ectx _) [SeqCtx])).
    (* Ecall. *)
    iApply (wp_wand with "[HPC Hpc_a HMIE Hheld]").
    { iApply (wp_core_full_ho (ceriseg := ceriseG_of th) (th := th) (CL := CL th)
                (CR := CR th) ⊤ b
                (λ b' v, ⌜b' = InterruptDisabled⌝ ∗ ⌜v = YieldV⌝ ∗
                   PC ↦ₚ[th] lword_of_word mtcc_vec ∗ pc_a ↦ₐ{dq} w ∗
                   vol_lent (ceriseg := ceriseG_of th)
                     (lmepcc_of_pc (Cap pc_p pc_g pc_b pc_e pc_a))
                     (lword_of_word (WInt MCAUSE_ECALL_MACHINE)) MTVAL_NONE b ∗
                   na_own crit ⊤)%I
               with "Hheld HMIE").
      { by intros ?%Hth. }
      iIntros "Hho HMIE".
      iDestruct (handover_res_vol with "Hho") as "[Hcrit Hvol]".
      iApply (wp_ecall (th := th) with "[$HPC $Hpc_a $HMIE $Hvol]"); [done | done |].
      iIntros "!> (HPC & Hpc_a & HMIE & Hvol)".
      rewrite tval_sw_ecall_user //.
      iNext. iExists InterruptDisabled. by iFrame. }
    iIntros (v) "Hpost".
    iDestruct "Hpost" as (b') "(HMIE & Hpart & >-> & >-> & HPC & Hpc_a & Hvol & Hcrit)".
    iApply wp_pure_step_later; first done. iNext. iIntros "_".
    iApply wp_value. rewrite HO_yield. iSplit; first done.
    rewrite /yield_body. iExists b, (lmepcc_of_pc (Cap pc_p pc_g pc_b pc_e pc_a)).
    iSplitL "Hcrit Hvol Hpart".
    { rewrite posture_res_gen_unfold. iFrame "Hpart".
      iExists (lmepcc_of_pc (Cap pc_p pc_g pc_b pc_e pc_a)), _, MTVAL_NONE, b.
      rewrite handover_at_vol. by iFrame. }
    iFrame "HMIE HPC".
    (* The resumed thread continues after the [ecall]. *)
    iApply bi.later_intro. iIntros "HMIE HPC Hheld". rewrite safe_unfold.
    rewrite lmepcc_of_pc_correct //.
    assert (executeAllowed pc_p = true) as Hx by (by inversion Hpc).
    rewrite (yield_resume_pc_cap pc_p pc_g pc_b pc_e pc_a pc_a' Hx Ha').
    iApply ("Hk" with "HPC Hpc_a HMIE Hheld").
  Qed.
End yield.
