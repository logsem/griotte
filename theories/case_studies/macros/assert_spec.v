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
  .

  (* Asserts (ct0 == ct1). Jumps back to cra.
     Clobbers cra, ct0, ct1.
   *)
  Definition assert_subroutine_instrs :=
    encodeInstrsW [
      Sub ct0 ct0 ct1;
      Jnz 4 ct0;
      (* success case *)
      Mov ct0 0;
      Mov ct1 0;
      Jalr cnull cra; (* return *)
      (* failure case *)
      Mov ct1 PC; (* pointer to cap: *)
      Lea ct1 7; (* pointer to cap: *)
      CLoad ct1 ct1 0;
      Store ct1 1 0;
      Mov ct0 0;
      Mov ct1 0;
      Jalr cnull cra (* return *)
    ].
  (* followed in memory by:
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
       cap_addr ↦ₐ□ WCap true RW Global a_flag (a_flag ^+1)%a a_flag).

  Global Instance assert_static_persistent b_assert e_assert a_flag :
    Persistent (assert_static b_assert e_assert a_flag).
  Proof. apply _. Qed.

  Lemma assert_subroutine_spec
    (pc_g : Locality) (pc_b pc_e a_flag : Addr)
    ( n1 n2 flag : Z ) ( wret : Word) ( wnull : LWord)
    (φ : language.val griotte_lang -> iProp Σ) :
    disjoint_from_shadow pc_b pc_e →
    is_shadow_address a_flag = false →
    is_heap_address a_flag = false →
    (  assert_static pc_b pc_e a_flag
     ∗ PC ↦ᵣ WCap true RX pc_g pc_b pc_e pc_b
     ∗ cra ↦ᵣ wret
     ∗ ct0 ↦ᵣ WInt n1
     ∗ ct1 ↦ᵣ WInt n2
     ∗ cnull ↦ᵣ wnull
     ∗ a_flag ↦ₐ WInt flag
     ∗ ▷ (PC ↦ᵣ updatePcPerm wret
          ∗ cra ↦ᵣ wret
          ∗ ct0 ↦ᵣ WInt 0
          ∗ ct1 ↦ᵣ WInt 0
          ∗ cnull ↦ᵣ WInt 0
          ∗ a_flag ↦ₐ WInt (if (n1 =? n2)%Z then flag else 1%Z)
          -∗ WP Seq (Instr Executable) {{ φ }})
     ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    iIntros (Hcode_shadow Hflag_not_shadow Hflag_not_heap)
      "(#Hassert & HPC & Hrdst & Hct0 & Hct1 & Hcnull & Hflag & Hφ)".
    iDestruct "Hassert" as "[%Hassert_not_heap Hassert]".
    iDestruct "Hassert" as (cap_addr) "(Hprog & %Hcap & %Hpc_e & %He_flag & Hcap)".
    destruct He_flag as [e_flag He_flag].
    rewrite /assert_subroutine_instrs.
    codefrag_facts "Hprog". rename H into HcontProg.
    assert (SubBounds pc_b pc_e
              pc_b (pc_b ^+ length assert_subroutine_instrs)%a)
      as HsubBounds by solve_addr.
    iInstr "Hprog".
    destruct (decide (n1 = n2)) as [Heq|Heq].
    { (* n1 = n2 *)
      subst n2. rewrite (_: n1 - n1 = 0)%Z; last lia.
      iGo "Hprog".
      iApply "Hφ". iFrame "∗". rewrite Z.eqb_refl //. }
    { (* n1 ≠ n2 *)
      iInstr "Hprog". { intros Hcontra; inversion Hcontra; lia. }
      iInstr "Hprog".
      iInstr "Hprog".
      rewrite (_: (pc_b ^+ 12)%a = cap_addr); [|solve_addr].
      assert (is_shadow_address cap_addr = false) as Hcap_not_shadow.
      { eapply disjoint_from_shadow_not_in; first exact Hcode_shadow.
        apply withinBounds_true_iff; solve_addr. }
      assert (is_heap_cap (WCap true RW Global a_flag (a_flag ^+ 1)%a a_flag) = false)
        as Hcap_not_heap.
      { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hflag_not_heap /=.
        reflexivity. }
      iInstr "Hprog"; first solve_addr.
      iInstr "Hprog"; first solve_addr.
      iGo "Hprog".
      iApply "Hφ". iFrame "∗". rewrite (_: (n1 =? n2)%Z = false) //.
      by apply Z.eqb_neq. }
  Qed.

  Lemma assert_subroutine_success_spec
    (pc_g : Locality) (pc_b pc_e a_flag : Addr)
    ( n1 n2 flag : Z ) ( wret : Word) ( wnull : LWord)
    (φ : language.val griotte_lang -> iProp Σ) :
    n1 = n2 →
    (  assert_static pc_b pc_e a_flag
     ∗ PC ↦ᵣ WCap true RX pc_g pc_b pc_e pc_b
     ∗ cra ↦ᵣ wret
     ∗ ct0 ↦ᵣ WInt n1
     ∗ ct1 ↦ᵣ WInt n2
     ∗ cnull ↦ᵣ wnull
     ∗ ▷ (PC ↦ᵣ updatePcPerm wret
          ∗ cra ↦ᵣ wret
          ∗ ct0 ↦ᵣ WInt 0%Z
          ∗ ct1 ↦ᵣ WInt 0%Z
          ∗ cnull ↦ᵣ WInt 0
          -∗ WP Seq (Instr Executable) {{ φ }})
     ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    iIntros (Heq) "(#Hassert & HPC & Hrdst & Hct0 & Hct1 & Hcnull & Hφ)".
    iDestruct "Hassert" as "[%Hassert_not_heap Hassert]".
    iDestruct "Hassert" as (cap_addr) "(Hprog & %Hcap & %Hflag & %He & Hcap)".
    rewrite /assert_subroutine_instrs. codefrag_facts "Hprog".
    assert (SubBounds pc_b pc_e
              pc_b (pc_b ^+ length assert_subroutine_instrs)%a)
      as HsubBounds by solve_addr.
    iInstr "Hprog".
    rewrite (_: n1 - n2 = 0)%Z; last lia.
    iGo "Hprog".
    iApply "Hφ". iFrame "∗".
  Qed.

End Assert_subroutine.

Section Assert.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ}
      {MP: MachineParameters}
  .

  Lemma assert_success_spec
    (n : Z) (rdst rscratch1 rscratch2 : RegName)
    (pc_g : Locality) (pc_p : Perm) (pc_b pc_e pc_a : Addr)
    (g_assert : Locality) (b_assert e_assert a_flag : Addr)
    (n1 n2 : Z) (wdst wcra w1 w2 wnull : LWord) (dq : dfrac)
    (φ : language.val griotte_lang -> iProp Σ) :

    let assert_macro := assert_instrs n rdst rscratch1 rscratch2 in
    let a_last := (pc_a ^+ length assert_macro)%a in
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a a_last →
    withinBounds pc_b pc_e (pc_b ^+ n)%a = true ->
    disjoint_from_shadow pc_b pc_e →

    n1 = n2 →
    (  assert_static b_assert e_assert a_flag
     ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
     ∗ rdst ↦ᵣ wdst
     ∗ rscratch1 ↦ᵣ w1
     ∗ rscratch2 ↦ᵣ w2
     ∗ cra ↦ᵣ wcra
     ∗ ct0 ↦ᵣ WInt n1
     ∗ ct1 ↦ᵣ WInt n2
     ∗ cnull ↦ᵣ wnull
     ∗ codefrag_pers pc_a assert_macro
     ∗ (pc_b ^+ n)%a ↦ₐ{dq} (WSentry true RX g_assert b_assert e_assert b_assert)
     ∗ ▷ (PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e a_last
          ∗ rdst ↦ᵣ WInt 0
          ∗ rscratch1 ↦ᵣ WInt 0
          ∗ rscratch2 ↦ᵣ WInt 0
          ∗ cra ↦ᵣ wcra
          ∗ ct0 ↦ᵣ WInt 0
          ∗ ct1 ↦ᵣ WInt 0
          ∗ cnull ↦ᵣ WInt 0
          ∗ codefrag_pers pc_a assert_macro
          ∗ (pc_b ^+ n)%a ↦ₐ{dq} (WSentry true RX g_assert b_assert e_assert b_assert)
          -∗ WP Seq (Instr Executable) {{ φ }})
     ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    intros assert_macro a_last; subst assert_macro a_last.
    iIntros (Hpc_exec HsubBounds Hinbounds Hcode_shadow Heq)
      "(#Hassert & HPC & Hrdst & Hrscratch1 & Hrscratch2 & Hcra & Hct0 & Hct1 & Hcnull & #Hcode_main & Hpc_bn & Hφ)".
    iAssert (⌜is_heap_address b_assert = false⌝)%I as %Hassert_not_heap.
    { by iDestruct "Hassert" as "[$ _]". }
    codefrag_facts "Hcode_main".
    rewrite /assert_instrs /assembled_assert.
    repeat (iEval (cbn [concat]) in "Hcode_main").
    repeat (iEval (cbn [fmap list_fmap]) in "Hcode_main").
    repeat (iEval (cbn [concat]) in "Hcode_main").
    focus_block_0 "Hcode_main" as "Hfetch" "Hcont"; iHide "Hcode_main" as hcode.
    iDestruct (regname_neq with "Hrscratch1 Hcnull") as "%".
    iDestruct (regname_neq with "Hrscratch2 Hcnull") as "%".
    iDestruct (regname_neq with "Hrdst Hcnull") as "%".
    iApply (fetch_spec n rdst rscratch1 rscratch2 with "[-]"); last iFrame "∗ Hfetch"; eauto.
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hassert_not_heap /=.
      reflexivity. }
    iNext; iIntros "(HPC & Hrdst & Hrscratch1 & Hrscratch2 & _ & Hpc_bn)".
    unfocus_block "Hfetch" "Hcont" as "Hcode_main"; subst hcode.
    focus_block 1 "Hcode_main" as a_assert Ha_assert "Hcode" "Hcont"; iHide "Hcode_main" as hcode.
    iGo "Hcode".
    iEval (cbn) in "HPC".
    iApply (assert_subroutine_success_spec with "[-]"); eauto; iFrame "∗ Hassert".
    iNext; iIntros "(HPC & Hcra & Hct0 & Hct1 & Hcnull)".
    iEval (cbn) in "HPC".
    iGo "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
    replace (a_assert ^+ 5)%a with (pc_a ^+ 14)%a by solve_addr.
    iApply "Hφ"; iFrame "∗ Hcode_main".
  Qed.

End Assert.
