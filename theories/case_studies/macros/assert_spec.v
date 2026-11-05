From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte Require Import fetch_spec.
From griotte Require Export assert.

(* Assert routine *)

(* Maintains a flag storing whether an assert has failed. *)

Section Assert_subroutine.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ}
      {MP: MachineParameters}
      {th : Thread} {CL : CritLink Σ th} {CR : CritRoute Σ th CL}
  .

  (* [assert_subroutine_instrs] asserts (ct0 == ct1) and jumps back to cra.
     It clobbers cra, ct0, ct1. It is followed in memory by:
    cap: (RW, flag, end, flag)
    flag: <0 or 1>
    end:
  *)

  (* The read-only part of the assert library: its code and the capability
     to the flag stored right after it. *)
  Definition assert_static (b_assert e_assert a_flag : Addr) : iProp Σ :=
    (⌜is_heap_address b_assert = false⌝ ∗ ∃ cap_addr,
       codefrag_pers b_assert assert_subroutine_instrs ∗
       ⌜(b_assert + length assert_subroutine_instrs)%a = Some cap_addr⌝ ∗
       ⌜(cap_addr + 1)%a = Some e_assert⌝ ∗
       ⌜is_Some (a_flag + 1)%a⌝ ∗
       cap_addr ↦ₐ□ Cap RW Global a_flag (a_flag ^+1) a_flag).

  #[global] Instance assert_static_persistent b_assert e_assert a_flag :
    Persistent (assert_static b_assert e_assert a_flag).
  Proof. apply _. Qed.

  Lemma assert_subroutine_success_spec
    (pc_g : Locality) (pc_b pc_e a_flag : Addr)
    ( n1 n2 flag : Z ) ( wret : Word) (b : InterruptStatus)
    (φ : tval (kind_of th) -> iProp Σ) :
    n1 = n2 →
    jalr_target_ok cnull cra wret = true →
    route_pre th (default b (jalr_target_mie wret)) →
    route_pre th b →
    (  assert_static pc_b pc_e a_flag
     ∗ PC ↦ₚ Cap RX pc_g pc_b pc_e pc_b
     ∗ cra ↦ᵣ wret
     ∗ ct0 ↦ᵣ WInt n1
     ∗ ct1 ↦ᵣ WInt n2
     ∗ MIE ↦ₜ b
     ∗ held b
     ∗ ▷ (PC ↦ₚ updatePcPerm wret
          ∗ cra ↦ᵣ wret
          ∗ ct0 ↦ᵣ WInt 0%Z
          ∗ ct1 ↦ᵣ WInt 0%Z
          ∗ MIE ↦ₜ default b (jalr_target_mie wret)
          ∗ held (default b (jalr_target_mie wret))
          -∗ WP Exec {{ φ }})
     ⊢ WP Exec {{ φ }})%I.
  Proof.
    iIntros (Heq Htgt Hroute' Hpre) "(#Hassert & HPC & Hrdst & Hct0 & Hct1 & Hmie & Hheld & Hφ)".
    iDestruct "Hassert" as "[%Hassert_not_heap Hassert]".
    iDestruct "Hassert" as (cap_addr) "(Hprog & %Hcap & %Hflag & %He & Hcap)".
    rewrite /assert_subroutine_instrs. codefrag_facts "Hprog".
    assert (SubBounds pc_b pc_e
              pc_b (pc_b ^+ length assert_subroutine_instrs))
      as HsubBounds by solve_addr.
    (* Sub ct0 ct0 ct1. *)
    iInstr "Hprog".
    rewrite (_: n1 - n2 = 0)%Z; last lia.
    (* Jne assert_fail ct0 0. *)
    iInstr "Hprog".
    (* Mov ct0 0. *)
    iInstr "Hprog".
    (* Mov ct1 0. *)
    iInstr "Hprog".
    (* Jalr cnull cra. *)
    iInstr "Hprog".
    1: { intros _. exact Hroute'. }
    iApply "Hφ". iFrame "∗".
  Qed.

End Assert_subroutine.

Section Assert.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ}
      {MP: MachineParameters}
      {th : Thread} {CL : CritLink Σ th} {CR : CritRoute Σ th CL}
  .

  Lemma assert_instrs_fetch (off : Z) (rdst rscratch : RegName) :
    assert_instrs off rdst rscratch =
      fetch_instrs off rdst ++
      encodeInstrsW [ Mov rscratch cra;
                      Jalr cra rdst;
                      Mov cra rscratch;
                      Mov rscratch 0;
                      Mov rdst 0 ].
  Proof. reflexivity. Qed.

  Lemma assert_success_spec
    (n off : Z) (rdst rscratch : RegName)
    (pc_g : Locality) (pc_p : Perm) (pc_b pc_e pc_a : Addr)
    (g_assert : Locality) (b_assert e_assert a_flag : Addr)
    (n1 n2 : Z) (wdst wcra wscratch : LWord) (dq : dfrac) (b : InterruptStatus)
    (φ : tval (kind_of th) -> iProp Σ) :

    let assert_macro := assert_instrs off rdst rscratch in
    let a_last := (pc_a ^+ length assert_macro) in
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a a_last →
    (pc_a + off)%a = Some (pc_b ^+ n) ->
    withinBounds pc_b pc_e (pc_b ^+ n) = true ->
    disjoint_from_shadow pc_b pc_e →
    rdst ≠ cnull →
    rscratch ≠ cnull →

    n1 = n2 →
    route_pre th b →
    (  assert_static b_assert e_assert a_flag
     ∗ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a
     ∗ rdst ↦ᵣ wdst
     ∗ rscratch ↦ᵣ wscratch
     ∗ cra ↦ᵣ wcra
     ∗ ct0 ↦ᵣ WInt n1
     ∗ ct1 ↦ᵣ WInt n2
     ∗ MIE ↦ₜ b
     ∗ held b
     ∗ codefrag_pers pc_a assert_macro
     ∗ (pc_b ^+ n) ↦ₐ{dq} (Sentry Inherit RX g_assert b_assert e_assert b_assert)
     ∗ ▷ (PC ↦ₚ Cap pc_p pc_g pc_b pc_e a_last
          ∗ rdst ↦ᵣ WInt 0
          ∗ rscratch ↦ᵣ WInt 0
          ∗ cra ↦ᵣ wcra
          ∗ ct0 ↦ᵣ WInt 0
          ∗ ct1 ↦ᵣ WInt 0
          ∗ MIE ↦ₜ b
          ∗ held b
          ∗ codefrag_pers pc_a assert_macro
          ∗ (pc_b ^+ n) ↦ₐ{dq} (Sentry Inherit RX g_assert b_assert e_assert b_assert)
          -∗ WP Exec {{ φ }})
     ⊢ WP Exec {{ φ }})%I.
  Proof.
    intros assert_macro a_last; subst assert_macro a_last.
    iIntros (Hpc_exec HsubBounds Hoff Hinbounds Hcode_shadow Hrdst_cnull Hrscratch_cnull Heq Hpre)
      "(#Hassert & HPC & Hrdst & Hrscratch & Hcra & Hct0 & Hct1 & Hmie & Hheld & #Hcode_main
        & Hpc_bn & Hφ)".
    iAssert (⌜is_heap_address b_assert = false⌝)%I as %Hassert_not_heap.
    { by iDestruct "Hassert" as "[$ _]". }
    codefrag_facts "Hcode_main".
    rewrite assert_instrs_fetch.
    focus_block_0 "Hcode_main" as "Hfetch" "Hcont"; iHide "Hcode_main" as hcode.
    iApply (fetch_spec n off rdst with "[-]"); last iFrame "∗ Hfetch"; eauto.
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hassert_not_heap /=.
      reflexivity. }
    iNext; iIntros "(HPC & Hrdst & _ & Hpc_bn)".
    unfocus_block "Hfetch" "Hcont" as "Hcode_main"; subst hcode.
    focus_block 1 "Hcode_main" as a_assert Ha_assert "Hcode" "Hcont"; iHide "Hcode_main" as hcode.
    iDestruct (regname_neq with "Hrdst Hcra") as %Hrdst_cra.
    (* Mov rscratch cra. *)
    iInstr "Hcode".
    (* Jalr cra rdst. *)
    iInstr "Hcode".
    iEval (cbn) in "HPC".
    (* The return target is the link sentry, executable as the PC is. *)
    iApply (assert_subroutine_success_spec with "[-]"); last iFrame "∗ Hassert"; try done.
    all: try (by destruct b).
    iNext; iIntros "(HPC & Hcra & Hct0 & Hct1 & Hmie & Hheld)".
    (* The return sentry restores the posture [b]. *)
    rewrite (_ : default (default b (sentry_kind_mie Inherit))
                   (jalr_target_mie (Sentry (ret_kind b) pc_p pc_g pc_b pc_e (a_assert ^+ 2)))
                 = b); last by destruct b.
    iEval (cbn) in "HPC".
    iGo "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
    replace (a_assert ^+ 5) with (pc_a ^+ length (assert_instrs off rdst rscratch))
      by (cbn; solve_addr).
    iApply "Hφ"; iFrame "∗ Hcode_main".
  Qed.

End Assert.

Section assert_thread_indep.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}.

  (** The assert library's static part is the same at any two threads. *)
  Lemma assert_static_thread_indep (t t' : Thread) (b_assert e_assert a_flag : Addr) :
    assert_static (ceriseg := ceriseG_of t) b_assert e_assert a_flag ⊣⊢
    assert_static (ceriseg := ceriseG_of t') b_assert e_assert a_flag.
  Proof.
    rewrite /assert_static.
    setoid_rewrite (codefrag_pers_thread_indep t t').
    setoid_rewrite (pointsto_pers_thread_indep t t').
    reflexivity.
  Qed.
End assert_thread_indep.
