From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel rules proofmode.
From cap_machine Require Import fetch.

(* Assert routine *)

(* Maintains a flag storing whether an assert has failed. *)

Section Assert_subroutine.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ}
      {nainv: logrel_na_invs Σ}
      {MP: MachineParameters}
  .

  (* Asserts (rsrc1 == rsrc2).
     Jumps back to rret.
   *)
  Definition assert_subroutine_instrs (rret rsrc1 rsrc2 : RegName) :=
    encodeInstrsW [
      Sub rsrc1 rsrc1 rsrc2;
      Jnz 4 rsrc1;
      (* success case *)
      Mov rsrc1 0;
      Mov rsrc2 0;
      JmpCap rret; (* return *)
      (* failure case *)
      Mov rsrc2 PC; (* pointer to cap: *)
      Lea rsrc2 7; (* pointer to cap: *)
      Load rsrc2 rsrc2;
      Store rsrc2 1;
      Mov rsrc1 0;
      Mov rsrc2 0;
      JmpCap rret (* return *)
    ].
  (* followed in memory by:
    cap: (RW, flag, end, flag)
    flag: <0 or 1>
    end:
  *)

  Definition assert_inv (rret rsrc1 rsrc2 : RegName) (b_assert e_assert a_flag : Addr) : iProp Σ :=
    (∃ cap_addr,
       codefrag b_assert (assert_subroutine_instrs rret rsrc1 rsrc2) ∗
       ⌜(b_assert + length (assert_subroutine_instrs rret rsrc1 rsrc2))%a = Some cap_addr⌝ ∗
       ⌜(cap_addr + 1)%a = Some a_flag⌝ ∗
       ⌜(a_flag + 1)%a = Some e_assert⌝ ∗
       cap_addr ↦ₐ WCap RW Global a_flag e_assert a_flag).

  Lemma assert_subroutine_spec
    (rret rsrc1 rsrc2 : RegName)
    (pc_g : Locality) (pc_b pc_e a_flag : Addr)
    ( n1 n2 flag : Z ) ( wret : Word)
    (N : namespace) (E : coPset) (φ : language.val cap_lang -> iProp Σ) :
    ↑N ⊆ E →
    (  na_inv logrel_nais N (assert_inv rret rsrc1 rsrc2 pc_b pc_e a_flag)
     ∗ na_own logrel_nais E
     ∗ PC ↦ᵣ WCap RX pc_g pc_b pc_e pc_b
     ∗ rret ↦ᵣ wret
     ∗ rsrc1 ↦ᵣ WInt n1
     ∗ rsrc2 ↦ᵣ WInt n2
     ∗ a_flag ↦ₐ WInt flag
     ∗ ▷ (na_own logrel_nais E
          ∗ PC ↦ᵣ updatePcPerm wret
          ∗ rret ↦ᵣ wret
          ∗ rsrc1 ↦ᵣ WInt 0
          ∗ rsrc2 ↦ᵣ WInt 0
          ∗ a_flag ↦ₐ WInt (if (n1 =? n2)%Z then flag else 1%Z)
          -∗ WP Seq (Instr Executable) {{ φ }})
     ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    iIntros (HNE) "(#Hinv & Hna & HPC & Hrdst & Hrsrc1 & Hrsrc2 & Hflag & Hφ)".
    iMod (na_inv_acc with "Hinv Hna") as "(>Hassert & Hna & Hinv_close)"; auto.
    iDestruct "Hassert" as (cap_addr) "(Hprog & %Hcap & %Hflag & %He & Hcap)".
    rewrite /assert_subroutine_instrs.
    codefrag_facts "Hprog". rename H into HcontProg.
    assert (SubBounds pc_b pc_e
              pc_b (pc_b ^+ length (assert_subroutine_instrs rret rsrc1 rsrc2))%a)
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
    (rret rsrc1 rsrc2 : RegName)
    (pc_g : Locality) (pc_b pc_e a_flag : Addr)
    ( n1 n2 flag : Z ) ( wret : Word)
    (N : namespace) (E : coPset) (φ : language.val cap_lang -> iProp Σ) :
    ↑N ⊆ E →
    n1 = n2 →
    (  na_inv logrel_nais N (assert_inv rret rsrc1 rsrc2 pc_b pc_e a_flag)
     ∗ na_own logrel_nais E
     ∗ PC ↦ᵣ WCap RX pc_g pc_b pc_e pc_b
     ∗ rret ↦ᵣ wret
     ∗ rsrc1 ↦ᵣ WInt n1
     ∗ rsrc2 ↦ᵣ WInt n2
     ∗ ▷ (na_own logrel_nais E
          ∗ PC ↦ᵣ updatePcPerm wret
          ∗ rret ↦ᵣ wret
          ∗ rsrc1 ↦ᵣ WInt 0%Z
          ∗ rsrc2 ↦ᵣ WInt 0%Z
          -∗ WP Seq (Instr Executable) {{ φ }})
     ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    iIntros (HNE Heq) "(#Hinv & Hna & HPC & Hrdst & Hrsrc1 & Hrsrc2 & Hφ)".
    iMod (na_inv_acc with "Hinv Hna") as "(>Hassert & Hna & Hinv_close)"; auto.
    iDestruct "Hassert" as (cap_addr) "(Hprog & %Hcap & %Hflag & %He & Hcap)".
    rewrite /assert_subroutine_instrs. codefrag_facts "Hprog".
    assert (SubBounds pc_b pc_e
              pc_b (pc_b ^+ length (assert_subroutine_instrs rret rsrc1 rsrc2))%a)
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

  (* assert macros:
   - fetch the assert entry point an the n-th position in the import table
   - execute the assert subroutine

   - rret, rsrc1 and rsrc2 are all clobbered
   *)
  Definition assert_instrs (n : Z) (rdst rscratch1 rscratch2 rsrc1 rsrc2 : RegName) :=
    fetch_instrs n rdst rscratch1 rscratch2 ++
    encodeInstrsW [
      Jalr rscratch1 rdst;
      Mov rscratch1 0%Z;
      Mov rdst 0%Z
    ].

  Lemma updatePcPerm_seal_perm_sentry (p : Perm) (g : Locality) (b e a : Addr) :
    isSentry p = false ->
    updatePcPerm (WCap (seal_perm_sentry p) g b e a) = WCap p g b e a.
  Proof.
    intros Hsentry.
    destruct p; auto.
    by cbn in Hsentry.
  Qed.

  Lemma assert_success_spec
    (n : Z) (rdst rscratch1 rscratch2 rsrc1 rsrc2 : RegName)
    (pc_g : Locality) (pc_p : Perm) (pc_b pc_e pc_a : Addr)
    (g_assert : Locality) (b_assert e_assert a_flag : Addr)
    (n1 n2 flag : Z) (wdst w1 w2 : Word)
    (N : namespace) (E : coPset) (φ : language.val cap_lang -> iProp Σ) :

    let assert_macro := assert_instrs n rdst rscratch1 rscratch2 rsrc1 rsrc2 in
    let a_last := (pc_a ^+ length assert_macro)%a in
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a a_last →
    withinBounds pc_b pc_e (pc_b ^+ n)%a = true ->

    ↑N ⊆ E →
    n1 = n2 →
    (  na_inv logrel_nais N (assert_inv rscratch1 rsrc1 rsrc2 b_assert e_assert a_flag)
     ∗ na_own logrel_nais E
     ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
     ∗ rdst ↦ᵣ wdst
     ∗ rscratch1 ↦ᵣ w1
     ∗ rscratch2 ↦ᵣ w1
     ∗ rsrc1 ↦ᵣ WInt n1
     ∗ rsrc2 ↦ᵣ WInt n2
     ∗ codefrag pc_a assert_macro
     ∗ (pc_b ^+ n)%a ↦ₐ (WCap E_RX g_assert b_assert e_assert b_assert)
     ∗ ▷ (na_own logrel_nais E
          ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e a_last
          ∗ rdst ↦ᵣ WInt 0
          ∗ rscratch1 ↦ᵣ WInt 0
          ∗ rscratch2 ↦ᵣ WInt 0
          ∗ rsrc1 ↦ᵣ WInt 0
          ∗ rsrc2 ↦ᵣ WInt 0
          ∗ codefrag pc_a assert_macro
          -∗ WP Seq (Instr Executable) {{ φ }})
     ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    intros assert_macro a_last; subst assert_macro a_last.
    iIntros (Hpc_exec HsubBounds Hinbounds HNE Heq)
      "(#Hinv & Hna & HPC & Hrdst & Hrscratch1 & Hrscratch2 & Hrsrc1 & Hrsrc2 & Hcode & Hpc_bn & Hφ)".
    codefrag_facts "Hcode".
    rewrite /assert_instrs.
    focus_block_0 "Hcode" as "Hfetch" "Hcont".
    iApply (fetch_spec with "[-]"); eauto; iFrame.
    iNext; iIntros "(HPC & Hrdst & Hrscratch1 & Hrscratch2 & Hfetch & Hpc_bn)".
    unfocus_block "Hfetch" "Hcont" as "Hcode".
    focus_block 1 "Hcode" as a_assert Ha_assert "Hassert" "Hcont".
    iGo "Hassert".
    rewrite load_word_sentry.
    iEval (cbn) in "HPC".
    iApply (assert_subroutine_success_spec with "[-]"); eauto; iFrame "#∗".
    iNext; iIntros "(Hna & HPC & Hrscratch1 & Hrsrc1 & Hrsrc2)".
    rewrite updatePcPerm_seal_perm_sentry; last solve_pure.
    iGo "Hassert".
    unfocus_block "Hassert" "Hcont" as "Hcode".
    replace (a_assert ^+ 3)%a with (pc_a ^+ 12)%a by solve_addr.
    iApply "Hφ"; iFrame.
  Qed.

End Assert.
