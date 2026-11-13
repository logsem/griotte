From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre.
From griotte Require Export logrel.
From griotte Require Import ftlr_base ftlr_contract interp_weakening traps.ecall.
Import CoreWPNotations.

(** * The environment call in the fundamental theorem

    The step lemma dispatches [Ecall] here, before the table of the other
    cases: the environment call consumes the lent volatile part, and its
    post-state keeps the values that the step pins in it. *)

(** The value of an environment call, by kind. *)
Lemma tval_sw_ecall_cases (th : Thread) (v : tval (kind_of th)) :
  v = tval_sw (kind_of th) Ecall NextIV →
  (th ≠ CtxSwitch ∧ v = YieldV) ∨ (th = CtxSwitch ∧ v = NextIV).
Proof.
  intros ->. destruct (decide (th = CtxSwitch)) as [Hth | Hth].
  - right. split; first done. by apply tval_sw_ecall_ctx.
  - left. split; first done. by apply tval_sw_ecall_user.
Qed.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {cthreads : CmptThreads} {CL : ∀ t, CritLink Σ t}
    `{MP: MachineParameters}
    {CR : ∀ t, CritRoute Σ t (CL t)}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  #[local] Notation V := (interpO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

  (** The case of the environment call: it consumes the lent volatile
      part and ends at InterruptDisabled, in the post-state
      [ftlr_ecall_post]. *)
  Lemma ecall_case (m : InterruptStatus) (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (ρ : region_part) (P : V) :
    ftlr_contract m W C regs p p' g b e a w Ecall ρ P.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hi.
    iIntros (mshwmb_v mshwm_v) "@".
    iDestruct (pc_open_acc_fetch with "WorldRes") as " [ (Ha & Hinterp) WorldRes ]".
    iApply (wp_ecall (th := th) with "[$HPC $Ha $Hmie $Hvol]"); [done | done |].
    iIntros "!> (HPC & Ha & Hmie & Hvol)".
    iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
    iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.
    rewrite /ftlr_contract_post.
    iNext. iExists W, InterruptDisabled. iFrame "Hworld_interp Hmie".
    iSplit; first (iPureIntro; apply related_sts_pub_refl_world).
    iSplit; first (iPureIntro; by intros).
    iSplit; first done.
    iLeft.
    iExists m, (Cap p g b e a), regs. iFrame "Hvol HPC Hmap Hreg".
    iSplit; first done. iSplit; first done. iSplit; first done. iSplit; first done.
    (* the environment call does not touch the high-water mark *)
    iSplitL "Hhwm"; first (iExists mshwm_v; iFrame "Hhwm"; by iPureIntro).
    rewrite lmepcc_of_pc_correct //.
    assert (is_Some (a + 1)%a) as [a' Ha'].
    { inversion HcorrectPC; solve_addr. }
    assert (executeAllowed p = true) as Hx by (by inversion HcorrectPC).
    rewrite (yield_resume_pc_cap p g b e a a' Hx Ha').
    iApply interp_expression_at. iApply "IH".
    by iApply (interp_next_PC with "Hinv_interp").
  Qed.

End fundamental.
