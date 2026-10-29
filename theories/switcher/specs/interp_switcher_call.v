From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Export logrel region_invariants bitblast.
From griotte Require Import fundamental switcher_preamble.
From griotte Require Export interp_switcher_call_gen.
From griotte Require Import switcher_exception.

(** * Validity of the switcher's call entry point

    [interp_expr_switcher_call_gen], instantiated with the trap safety of
    the switcher ([switcher_trap_safety_intro]). *)

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  #[local] Notation V := (interpO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

  Lemma interp_expr_switcher_call (W : WORLD) (C : CmptName) :
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static
    ⊢ interp_expr interp (interp_cont interp) W C (Cap XSRW_ Local b_switcher e_switcher a_switcher_call).
  Proof.
    iIntros "Hres".
    iApply interp_expr_switcher_call_gen.
    by iApply switcher_trap_safety_intro.
  Qed.

  Lemma interp_switcher_call (W : WORLD) (C : CmptName) :
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static
    ⊢ interp W C switcher_entry_call.
  Proof.
    iIntros "[#Hinv #Hstatic]".
    rewrite interp_unfold /=.
    iSplit; first (iPureIntro; exact switcher_not_heap_range).
    iIntros "!> %regs %W' % %".
    destruct g'; first done.
    iNext ; iApply (interp_expr_switcher_call with "[$Hinv $Hstatic]"); done.
  Qed.

End fundamental.
