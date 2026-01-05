From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel rules proofmode.
From cap_machine Require Import fetch_spec.
From cap_machine Require Export assert.

(* Assert routine *)

(* Maintains a flag storing whether an assert has failed. *)

Section Assert_subroutine.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ}
      {nainv: logrel_na_invs Σ}
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
      Load ct1 ct1;
      Store ct1 1;
      Mov ct0 0;
      Mov ct1 0;
      Jalr cnull cra (* return *)
    ].
  (* followed in memory by:
    cap: (RW, flag, end, flag)
    flag: <0 or 1>
    end:
  *)

  Definition assert_inv (b_assert e_assert a_flag : Addr) : iProp Σ :=
    (∃ cap_addr,
       codefrag b_assert assert_subroutine_instrs ∗
       ⌜(b_assert + length assert_subroutine_instrs)%a = Some cap_addr⌝ ∗
       ⌜(cap_addr + 1)%a = Some e_assert⌝ ∗
       ⌜is_Some (a_flag + 1)%a⌝ ∗
       cap_addr ↦ₐ WCap RW Global a_flag (a_flag ^+1)%a a_flag).

  Lemma assert_subroutine_spec
    (pc_g : Locality) (pc_b pc_e a_flag : Addr)
    ( n1 n2 flag : Z ) ( wret wnull : Word)
    (N : namespace) (E : coPset) (φ : language.val cap_lang -> iProp Σ) :
    ↑N ⊆ E →
    (  na_inv logrel_nais N (assert_inv pc_b pc_e a_flag)
     ∗ na_own logrel_nais E
     ∗ PC ↦ᵣ WCap RX pc_g pc_b pc_e pc_b
     ∗ cra ↦ᵣ wret
     ∗ ct0 ↦ᵣ WInt n1
     ∗ ct1 ↦ᵣ WInt n2
     ∗ cnull ↦ᵣ wnull
     ∗ a_flag ↦ₐ WInt flag
     ∗ ▷ (na_own logrel_nais E
          ∗ PC ↦ᵣ updatePcPerm wret
          ∗ cra ↦ᵣ wret
          ∗ ct0 ↦ᵣ WInt 0
          ∗ ct1 ↦ᵣ WInt 0
          ∗ cnull ↦ᵣ WInt 0
          ∗ a_flag ↦ₐ WInt (if (n1 =? n2)%Z then flag else 1%Z)
          -∗ WP Seq (Instr Executable) {{ φ }})
     ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    iIntros (HNE) "(#Hinv & Hna & HPC & Hrdst & Hct0 & Hct1 & Hcnull & Hflag & Hφ)".
    iMod (na_inv_acc with "Hinv Hna") as "(>Hassert & Hna & Hinv_close)"; auto.
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
      iMod ("Hinv_close" with "[Hprog Hcap $Hna]") as "Hna".
      { iExists _. iNext. iFrame. iPureIntro. repeat split; solve_addr. }
      iApply "Hφ". iFrame. rewrite Z.eqb_refl //. }
    { (* n1 ≠ n2 *)
      iInstr "Hprog". { assert (n1 - n2 ≠ 0)%Z by lia. congruence. }
      iInstr "Hprog".
      iInstr "Hprog".
      rewrite (_: (pc_b ^+ 12)%a = cap_addr); [|solve_addr].
      iInstr "Hprog"; first solve_addr.
      iInstr "Hprog"; first solve_addr.
      iGo "Hprog".
      iMod ("Hinv_close" with "[Hprog Hcap $Hna]") as "Hna".
      { iExists _. iNext. iFrame. iPureIntro. repeat split; solve_addr. }
      iApply "Hφ". iFrame. rewrite (_: (n1 =? n2)%Z = false) //.
      by apply Z.eqb_neq. }
  Qed.

  Lemma assert_subroutine_success_spec
    (pc_g : Locality) (pc_b pc_e a_flag : Addr)
    ( n1 n2 flag : Z ) ( wret wnull : Word)
    (N : namespace) (E : coPset) (φ : language.val cap_lang -> iProp Σ) :
    ↑N ⊆ E →
    n1 = n2 →
    (  na_inv logrel_nais N (assert_inv pc_b pc_e a_flag)
     ∗ na_own logrel_nais E
     ∗ PC ↦ᵣ WCap RX pc_g pc_b pc_e pc_b
     ∗ cra ↦ᵣ wret
     ∗ ct0 ↦ᵣ WInt n1
     ∗ ct1 ↦ᵣ WInt n2
     ∗ cnull ↦ᵣ wnull
     ∗ ▷ (na_own logrel_nais E
          ∗ PC ↦ᵣ updatePcPerm wret
          ∗ cra ↦ᵣ wret
          ∗ ct0 ↦ᵣ WInt 0%Z
          ∗ ct1 ↦ᵣ WInt 0%Z
          ∗ cnull ↦ᵣ WInt 0
          -∗ WP Seq (Instr Executable) {{ φ }})
     ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    iIntros (HNE Heq) "(#Hinv & Hna & HPC & Hrdst & Hct0 & Hct1 & Hcnull & Hφ)".
    iMod (na_inv_acc with "Hinv Hna") as "(>Hassert & Hna & Hinv_close)"; auto.
    iDestruct "Hassert" as (cap_addr) "(Hprog & %Hcap & %Hflag & %He & Hcap)".
    rewrite /assert_subroutine_instrs. codefrag_facts "Hprog".
    assert (SubBounds pc_b pc_e
              pc_b (pc_b ^+ length assert_subroutine_instrs)%a)
      as HsubBounds by solve_addr.
    iInstr "Hprog".
    rewrite (_: n1 - n2 = 0)%Z; last lia.
    iGo "Hprog".
    iMod ("Hinv_close" with "[Hprog Hcap $Hna]") as "Hna".
    { iExists _. iNext. iFrame. iPureIntro. repeat split; solve_addr. }
    iApply "Hφ". iFrame.
  Qed.

End Assert_subroutine.

Section Assert.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ}
      {nainv: logrel_na_invs Σ}
      {MP: MachineParameters}
  .

  Lemma assert_success_spec
    (n : Z) (rdst rscratch1 rscratch2 : RegName)
    (pc_g : Locality) (pc_p : Perm) (pc_b pc_e pc_a : Addr)
    (g_assert : Locality) (b_assert e_assert a_flag : Addr)
    (n1 n2 : Z) (wdst wcra w1 w2 wnull : Word)
    (N : namespace) (E : coPset) (φ : language.val cap_lang -> iProp Σ) :

    let assert_macro := assert_instrs n rdst rscratch1 rscratch2 in
    let a_last := (pc_a ^+ length assert_macro)%a in
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a a_last →
    withinBounds pc_b pc_e (pc_b ^+ n)%a = true ->

    ↑N ⊆ E →
    n1 = n2 →
    (  na_inv logrel_nais N (assert_inv b_assert e_assert a_flag)
     ∗ na_own logrel_nais E
     ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
     ∗ rdst ↦ᵣ wdst
     ∗ rscratch1 ↦ᵣ w1
     ∗ rscratch2 ↦ᵣ w2
     ∗ cra ↦ᵣ wcra
     ∗ ct0 ↦ᵣ WInt n1
     ∗ ct1 ↦ᵣ WInt n2
     ∗ cnull ↦ᵣ wnull
     ∗ codefrag pc_a assert_macro
     ∗ (pc_b ^+ n)%a ↦ₐ (WSentry RX g_assert b_assert e_assert b_assert)
     ∗ ▷ (na_own logrel_nais E
          ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e a_last
          ∗ rdst ↦ᵣ WInt 0
          ∗ rscratch1 ↦ᵣ WInt 0
          ∗ rscratch2 ↦ᵣ WInt 0
          ∗ cra ↦ᵣ wcra
          ∗ ct0 ↦ᵣ WInt 0
          ∗ ct1 ↦ᵣ WInt 0
          ∗ cnull ↦ᵣ WInt 0
          ∗ codefrag pc_a assert_macro
          ∗ (pc_b ^+ n)%a ↦ₐ (WSentry RX g_assert b_assert e_assert b_assert)
          -∗ WP Seq (Instr Executable) {{ φ }})
     ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    intros assert_macro a_last; subst assert_macro a_last.
    iIntros (Hpc_exec HsubBounds Hinbounds HNE Heq)
      "(#Hinv & Hna & HPC & Hrdst & Hrscratch1 & Hrscratch2 & Hcra & Hct0 & Hct1 & Hcnull & Hcode & Hpc_bn & Hφ)".
    codefrag_facts "Hcode".
    rewrite /assert_instrs /assembled_assert.
    repeat (iEval (cbn [concat]) in "Hcode").
    repeat (iEval (cbn [fmap list_fmap]) in "Hcode").
    focus_block_0 "Hcode" as "Hfetch" "Hcont".
    iDestruct (regname_neq with "Hrscratch1 Hcnull") as "%".
    iDestruct (regname_neq with "Hrscratch2 Hcnull") as "%".
    iDestruct (regname_neq with "Hrdst Hcnull") as "%".
    iApply (fetch_spec with "[-]"); last iFrame; eauto.
    iNext; iIntros "(HPC & Hrdst & Hrscratch1 & Hrscratch2 & Hfetch & Hpc_bn)".
    unfocus_block "Hfetch" "Hcont" as "Hcode".
    focus_block 1 "Hcode" as a_assert Ha_assert "Hassert" "Hcont".
    iGo "Hassert".
    rewrite load_word_sentry.
    iEval (cbn) in "HPC".
    iApply (assert_subroutine_success_spec with "[-]"); eauto; iFrame "#∗".
    iNext; iIntros "(Hna & HPC & Hcra & Hct0 & Hct1 & Hcnull )".
    iEval (cbn) in "HPC".
    iGo "Hassert".
    unfocus_block "Hassert" "Hcont" as "Hcode".
    replace (a_assert ^+ 5)%a with (pc_a ^+ 14)%a by solve_addr.
    iApply "Hφ"; iFrame.
  Qed.

End Assert.
