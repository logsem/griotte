From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel region_invariants bitblast.
From cap_machine Require Import ftlr_base interp_weakening.
From cap_machine Require Import rules proofmode monotone.
From cap_machine.proofmode Require Import map_simpl register_tactics proofmode.

Section wp_interp.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {cstackg : CSTACKG Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Notation CSTK := (leibnizO cstack).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> (leibnizO Word) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation K := (WORLD -n> (leibnizO CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (V).

  Lemma wp_store_interp (E : coPset) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wsrc wdst : Word)
    :
    decodeInstrW wi = Store rdst (inr rsrc) →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

     {{{ interp W C wsrc
           ∗ interp W C wdst
           ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rdst ↦ᵣ wdst
           ∗ region W C
           ∗ sts_full_world W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          ( ∃ p g b e a,
           ⌜ wdst = WCap p g b e a ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rdst ↦ᵣ WCap p g b e a
           ∗ region W C
           ∗ sts_full_world W C
           ∗ ⌜ canStore p wsrc = true ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' φ)
      "(#Hinterp_src & #Hinterp_dst & HPC & Hi & Hsrc & Hdst & Hregion & Hworld)".
    iIntros "Hφ".

    destruct (is_cap wdst) eqn:Hcap;cycle 1.
    {
      iApply (wp_store_fail_reg_not_cap _ _ _ _ _ _ _ rdst rsrc with "[$]")
      ; try solve_pure.
      iIntros "!> _". iApply "Hφ"; by iLeft. }
    destruct wdst;try done. destruct sb; try done.

    destruct (decide (canStore p wsrc = true))%a as [Hstore_src|Hstore_src]; cycle 1.
    {
      iApply (wp_store_fail_reg_perm with "[HPC Hi Hdst Hsrc]")
      ; try iFrame
      ; try solve_pure.
      { by destruct ( canStore p wsrc ); auto. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }
    pose proof ( canStore_writeAllowed p wsrc Hstore_src ) as Hp_stk_wa.
    destruct (decide (b <= a))%a as [Hba|Hba]; cycle 1.
    {
      iApply (wp_store_fail_reg with "[HPC Hi Hdst Hsrc]")
      ; try iFrame
      ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }
    destruct (decide (a < e))%a as [Hae|Hae]; cycle 1.
    {
      iApply (wp_store_fail_reg with "[HPC Hi Hdst Hsrc]")
      ; try iFrame
      ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }

    iDestruct (writeAllowed_valid_cap with "Hinterp_dst") as "%Hdst_in_region"; auto.
    assert ( ∃ ρ, std W !! a = Some ρ ∧ ρ ≠ Revoked) as ( ρ & Hρ & Hρ_not_revoked).
    {
      rewrite Forall_lookup in Hdst_in_region.
      assert ( a ∈ finz.seq_between b e) as Ha.
      { apply elem_of_finz_seq_between; solve_addr. }
      rewrite elem_of_list_lookup in Ha.
      destruct Ha as [ka Hka].
      apply Hdst_in_region in Hka.
      done.
    }

    iDestruct (write_allowed_inv _ _ a with "Hinterp_dst") as (p' P Hflows Hpers) "(Hrel & Hzcond & Hwcond & Hrcond & Hmono)";[solve_addr|auto|..].

    iDestruct (region_open with "[$]") as (v) "(Hr & Hsts & Hstate & Ha & %Hno & _ & _)";[|done|].
    { destruct ρ;auto. done. }

    iApply (wp_store_success_reg _ _ _ _ _ _ _ _ rdst rsrc with "[$HPC Hi Hsrc Hdst Ha]")
    ; try iFrame
    ; try solve_pure.
    { rewrite /withinBounds; solve_addr. }
    iNext; iIntros "(HPC & Hi & Hsrc & Hdst & Ha)".

    iDestruct (region_close
                with "[$Hstate $Hr $Ha $Hrel]")
      as "Hregion".
    { rewrite /safeC. auto. }
    { destruct ρ; naive_solver. }
    { iFrame "%". rewrite /safeC /=.
      iDestruct ("Hwcond" with "Hinterp_src") as "HP".
      iFrame "HP".
      rewrite /monoReq Hρ.
      destruct ρ;[simpl..|exfalso;done].
      - destruct (isWL p');auto.
        destruct (isDL p'); first done.
       by (iSpecialize ("Hmono" with "[%]");[eapply canStore_flowsto;eauto|]).
      - by (iSpecialize ("Hmono" with "[%]");[eapply canStore_flowsto;eauto|]).
    }

    iApply "Hφ"; iRight; iFrame "∗%".
    iSplit; first done.
    iPureIntro; solve_addr.
  Qed.

  Lemma wp_store_interp_cap (E : coPset) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr)
    (wi wsrc : Word)
    :
    decodeInstrW wi = Store rdst (inr rsrc) →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

     {{{ interp W C wsrc
           ∗ interp W C (WCap p g b e a)
           ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rdst ↦ᵣ (WCap p g b e a)
           ∗ region W C
           ∗ sts_full_world W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          (⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rdst ↦ᵣ WCap p g b e a
           ∗ region W C
           ∗ sts_full_world W C
           ∗ ⌜ canStore p wsrc = true ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' φ)
      "(#Hinterp_src & #Hinterp_dst & HPC & Hi & Hsrc & Hdst & Hregion & Hworld)".
    iIntros "Hφ".
    iApply (wp_store_interp with "[-Hφ]");eauto;[iFrame "∗ #"|].
    iNext. iIntros (ret) "[? | (%&%&%&%&%&%&?&?&?&?&?&?&?&%&%)]"
    ; iApply "Hφ" ; auto.
    iRight. simplify_eq.  iFrame.
    auto.
  Qed.

  Lemma wp_store_interp_z (E : coPset) (W : WORLD) (C : CmptName) (rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wdst : Word) (z : Z)
    :
    decodeInstrW wi = Store rdst (inl z) →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

     {{{ interp W C wdst
           ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rdst ↦ᵣ wdst
           ∗ region W C
           ∗ sts_full_world W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          ( ∃ p g b e a,
           ⌜ wdst = WCap p g b e a ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rdst ↦ᵣ WCap p g b e a
           ∗ region W C
           ∗ sts_full_world W C
           ∗ ⌜ writeAllowed p ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' φ)
      "(#Hinterp_dst & HPC & Hi & Hdst & Hregion & Hworld)".
    iIntros "Hφ".

    destruct (is_cap wdst) eqn:Hcap;cycle 1.
    {
      iApply (wp_store_fail_z_not_cap with "[$]")
      ; try solve_pure; eauto.
      iIntros "!> _". iApply "Hφ"; by iLeft. }
    destruct wdst;try done. destruct sb; try done.

    destruct (decide (writeAllowed p = true))%a as [Hstore_src|Hstore_src]; cycle 1.
    {
      iApply (wp_store_fail_z_perm with "[HPC Hi Hdst]")
      ; try iFrame
      ; try solve_pure
      ; eauto.
      { by destruct ( writeAllowed p ); auto. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }
    destruct (decide (b <= a))%a as [Hba|Hba]; cycle 1.
    {
      iApply (wp_store_fail_z with "[HPC Hi Hdst]")
      ; try iFrame
      ; try solve_pure
      ; eauto.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }
    destruct (decide (a < e))%a as [Hae|Hae]; cycle 1.
    {
      iApply (wp_store_fail_z with "[HPC Hi Hdst]")
      ; try iFrame
      ; try solve_pure
      ; eauto.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }

    iDestruct (writeAllowed_valid_cap with "Hinterp_dst") as "%Hdst_in_region"; auto.
    assert ( ∃ ρ, std W !! a = Some ρ ∧ ρ ≠ Revoked) as ( ρ & Hρ & Hρ_not_revoked).
    {
      rewrite Forall_lookup in Hdst_in_region.
      assert ( a ∈ finz.seq_between b e) as Ha.
      { apply elem_of_finz_seq_between; solve_addr. }
      rewrite elem_of_list_lookup in Ha.
      destruct Ha as [ka Hka].
      apply Hdst_in_region in Hka.
      done.
    }

    iDestruct (write_allowed_inv _ _ a with "Hinterp_dst") as (p' P Hflows Hpers) "(Hrel & Hzcond & Hwcond & Hrcond & Hmono)";[solve_addr|auto|..].

    iDestruct (region_open with "[$]") as (v) "(Hr & Hsts & Hstate & Ha & %Hno & _ & _)";[|done|].
    { destruct ρ;auto. done. }

    iApply (wp_store_success_z _ _ _ _ _ _ _ _ rdst with "[$HPC Hi Hdst Ha]")
    ; try iFrame
    ; try solve_pure
    ; eauto.
    { rewrite /withinBounds; solve_addr. }
    iNext; iIntros "(HPC & Hi & Hdst & Ha)".

    iDestruct (region_close
                with "[$Hstate $Hr $Ha $Hrel]")
      as "Hregion".
    { rewrite /safeC. auto. }
    { destruct ρ; naive_solver. }
    { iFrame "%". rewrite /safeC /=.
      iSplitL;[|iApply "Hwcond";iClear "∗ #"; by rewrite !fixpoint_interp1_eq /=].
      rewrite /monoReq Hρ.
      destruct ρ;[simpl..|exfalso;done].
      - destruct (isWL p');auto.
        destruct (isDL p') ; first done.
        by (iSpecialize ("Hmono" $! (WInt z) with "[%]");[eapply canStore_flowsto;eauto|]).
      - by (iSpecialize ("Hmono" $! (WInt z) with "[%]");[eapply canStore_flowsto;eauto|]).
    }

    iApply "Hφ"; iRight; iFrame "∗%".
    iSplit; first done.
    iPureIntro; solve_addr.
  Qed.

  Lemma wp_store_interp_z_cap (E : coPset) (W : WORLD) (C : CmptName) (rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr)
    (wi : Word) (z : Z)
    :
    decodeInstrW wi = Store rdst (inl z) →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

     {{{  interp W C (WCap p g b e a)
           ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rdst ↦ᵣ (WCap p g b e a)
           ∗ region W C
           ∗ sts_full_world W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          (⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rdst ↦ᵣ WCap p g b e a
           ∗ region W C
           ∗ sts_full_world W C
           ∗ ⌜ writeAllowed p ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' φ)
      "(#Hinterp_dst & HPC & Hi & Hdst & Hregion & Hworld)".
    iIntros "Hφ".
    iApply (wp_store_interp_z with "[-Hφ]");eauto;[iFrame "∗ #"|].
    iNext. iIntros (ret) "[? | (%&%&%&%&%&%&?&?&?&?&?&?&?&%&%)]"
    ; iApply "Hφ" ; auto.
    iRight. simplify_eq.  iFrame.
    auto.
  Qed.

  Lemma wp_unseal_unknown E pc_p pc_g pc_b pc_e pc_a pc_a' wi r1 r2 wsealr wsealed  :
    decodeInstrW wi = UnSeal r2 r1 r2 →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

    {{{  PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
          ∗ pc_a ↦ₐ wi
          ∗ r1 ↦ᵣ wsealr
          ∗ r2 ↦ᵣ wsealed
    }}}
      Instr Executable @ E
      {{{ retv, RET retv;
          ⌜ retv = FailedV ⌝
          ∨ ∃ psr gsr bsr esr asr wsb,
              ⌜ retv = NextIV ⌝
              ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ wi
              ∗ r1 ↦ᵣ wsealr
              ∗ r2 ↦ᵣ WSealable wsb
              ∗ ⌜ wsealr = (WSealRange psr gsr bsr esr asr) ⌝ ∗ ⌜ permit_unseal psr = true ⌝
              ∗ ⌜ wsealed = WSealed asr wsb ⌝
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpc_a' ϕ) "(HPC & Hpc_a & Hr1 & Hr2) Hφ".

    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_UnSeal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | ]; iApply "Hφ"; [iRight | by iLeft].
    rewrite lookup_insert_ne // lookup_insert  in H2.
    rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert in H3.
    apply incrementPC_Some_inv in H6.
    destruct H6 as ( ppc & gpc & bpc & epc & apc & apc' & HPC & Hapc' & ->).
    rewrite lookup_insert_ne // lookup_insert in HPC.
    simplify_eq.
    iExists p, g, b, e, a, sb.
    rewrite (insert_commute _ _ PC) //.
    rewrite (insert_commute _ _ r1) //.
    rewrite !insert_insert.
    iDestruct (big_sepM_insert with "Hmap") as "[HPC Hmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_insert with "Hmap") as "[Hr1 Hmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_insert with "Hmap") as "[Hr2 Hmap]"; first by simplify_map_eq.
    iFrame; done.
  Qed.

  Lemma wp_unseal_unknown_sealed E pc_p pc_g pc_b pc_e pc_a pc_a' wi r1 r2 psr gsr bsr esr asr wsealed  :
    decodeInstrW wi = UnSeal r2 r1 r2 →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    permit_unseal psr = true ->
    (bsr <= asr < esr)%ot ->

    {{{  PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
          ∗ pc_a ↦ₐ wi
          ∗ r1 ↦ᵣ WSealRange psr gsr bsr esr asr
          ∗ r2 ↦ᵣ wsealed
    }}}
      Instr Executable @ E
      {{{ retv, RET retv;
          ⌜ retv = FailedV ⌝
          ∨ ∃ wsb,
              ⌜ retv = NextIV ⌝
              ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ wi
              ∗ r1 ↦ᵣ WSealRange psr gsr bsr esr asr
              ∗ r2 ↦ᵣ WSealable wsb
              ∗ ⌜ wsealed = WSealed asr wsb ⌝
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpc_a' Hpsr Hsr ϕ) "(HPC & Hpc_a & Hr1 & Hr2) Hφ".

    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_UnSeal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | ]; iApply "Hφ"; [iRight | by iLeft].
    rewrite lookup_insert_ne // lookup_insert  in H2.
    rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert in H3.
    apply incrementPC_Some_inv in H6.
    destruct H6 as ( ppc & gpc & bpc & epc & apc & apc' & HPC & Hapc' & ->).
    rewrite lookup_insert_ne // lookup_insert in HPC.
    simplify_eq.
    iExists sb.
    rewrite (insert_commute _ _ PC) //.
    rewrite (insert_commute _ _ r1) //.
    rewrite !insert_insert.
    iDestruct (big_sepM_insert with "Hmap") as "[HPC Hmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_insert with "Hmap") as "[Hr1 Hmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_insert with "Hmap") as "[Hr2 Hmap]"; first by simplify_map_eq.
    iFrame; done.
  Qed.

End wp_interp.
