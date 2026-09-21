From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Export logrel region_invariants.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Import rules proofmode monotone.
From griotte Require Import map_simpl register_tactics proofmode.

Section wp_interp.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> (leibnizO Word) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation K := (CSTK -n> list WORLD -n> leibnizO (list CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (V).

  Lemma wp_store_interp (E : coPset) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wsrc wdst : Word)
    :
    decodeInstrW wi = Store rdst (inr rsrc) 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

     {{{ interp W C wsrc
           ∗ interp W C wdst
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rdst ↦ᵣ wdst
           ∗ world_interp W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          ( ∃ p g b e a,
           ⌜ wdst = WCap true p g b e a ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rdst ↦ᵣ WCap true p g b e a
           ∗ world_interp W C
           ∗ ⌜ writeAllowed p = true ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ?? φ)
      "(#Hinterp_src & #Hinterp_dst & HPC & Hi & Hsrc & Hdst & Hworld_interp)".
    iIntros "Hφ".

    destruct (is_cap wdst) eqn:Hcap;cycle 1.
    {
      iApply (wp_store_fail_reg_not_cap _ _ _ _ _ _ _ rdst rsrc with "[$]")
      ; try solve_pure.
      iIntros "!> _". iApply "Hφ"; by iLeft. }
    destruct wdst; try done. destruct sb; try done.
    destruct tag; cycle 1.
    {
      iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap %Hdistinct]".
      try (destruct Hdistinct as (? & ? & ?)).
      iApply (wp_store_fail_tag _ _ _ _ _ _ _ _ _ _ (WCap false p g b e a)
                with "[$Hi $Hmap]"); eauto; try (by simplify_map_eq).
      iNext; iIntros "_". iApply "Hφ"; by iLeft.
    }

    destruct (decide (writeAllowed p = true))%a as [Hp_stk_wa|Hp_stk_wa]; cycle 1.
    {
      iApply (wp_store_fail_reg_perm with "[HPC Hi Hdst Hsrc]")
      ; try iFrame
      ; try solve_pure.
      { by destruct (writeAllowed p); auto. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }
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
      rewrite list_elem_of_lookup in Ha.
      destruct Ha as [ka Hka].
      apply Hdst_in_region in Hka.
      done.
    }

    iDestruct (write_allowed_inv _ _ a with "Hinterp_dst") as (p' P Hflows Hpers) "(Hrel & Hzcond & Hwcond & Hrcond & Hmono)";[solve_addr|auto|..].

    iDestruct (open_world_interp with "[$Hrel] [$Hworld_interp]")
      as "(Hworld_interp & Hstate & (%w & WorldRes) )"
    ; [|eauto|]; [ destruct ρ;auto;done|].
    iDestruct (WorldRes_acc_forall with "WorldRes") as " [ (>Ha & Hinterp & HmonoP) WorldRes ]".


    iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ a with "Hinterp_dst") as %Hnot_shadow.
    { eapply writeAllowed_nonO; eauto. }
    { apply withinBounds_true_iff; solve_addr. }
    iApply (wp_store_success_reg_store_word _ _ _ _ _ _ _ _ rdst rsrc with "[$HPC Hi Hsrc Hdst Ha]")
    ; try iFrame
    ; try solve_pure.
    { rewrite /withinBounds; solve_addr. }
    iNext; iIntros "(HPC & Hi & Hsrc & Hdst & Ha)".

    iAssert (P W C (store_word p wsrc)) as "Hinterp'".
    {
      iApply "Hwcond".
      rewrite /store_word.
      destruct (canStore p wsrc); first done.
      iApply interp_clear_tag.
    }
    iAssert (mono_invariant C p' (safeC P) (store_word p wsrc) ρ) as "Hmono'".
    {
      rewrite /monoReq Hρ mono_invariant_eq.
      destruct ρ;[simpl..|exfalso;done].
      - destruct (isWL p');auto.
        destruct (isDL p'); first done.
        by (iSpecialize ("Hmono" with "[%]");[eapply canStore_store_word_flowsto;eauto|]).
      - by (iSpecialize ("Hmono" with "[%]");[eapply canStore_store_word_flowsto;eauto|]).
    }

    iDestruct ("WorldRes" with "[$Ha $Hinterp' $Hmono']") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hrel WorldRes") as "Hworld_interp"; eauto.
    { destruct ρ;auto;contradiction. }

    iApply "Hφ"; iRight; iFrame "∗%".
    iSplit; first done.
    iPureIntro; solve_addr.
  Qed.

  Lemma wp_store_interp_cap (E : coPset) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr)
    (wi wsrc : Word)
    :
    decodeInstrW wi = Store rdst (inr rsrc) 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

     {{{ interp W C wsrc
           ∗ interp W C (WCap true p g b e a)
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rdst ↦ᵣ (WCap true p g b e a)
           ∗ world_interp W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          (⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rdst ↦ᵣ WCap true p g b e a
           ∗ world_interp W C
           ∗ ⌜ writeAllowed p = true ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ? ? φ)
      "(#Hinterp_src & #Hinterp_dst & HPC & Hi & Hsrc & Hdst & Hworld_interp)".
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
    decodeInstrW wi = Store rdst (inl z) 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rdst ≠ cnull ->

     {{{ interp W C wdst
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rdst ↦ᵣ wdst
           ∗ world_interp W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          ( ∃ p g b e a,
           ⌜ wdst = WCap true p g b e a ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rdst ↦ᵣ WCap true p g b e a
           ∗ world_interp W C
           ∗ ⌜ writeAllowed p ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ? φ)
      "(#Hinterp_dst & HPC & Hi & Hdst & Hworld_interp)".
    iIntros "Hφ".

    destruct (is_cap wdst) eqn:Hcap;cycle 1.
    {
      iApply (wp_store_fail_z_not_cap with "[$]")
      ; try solve_pure; eauto.
      iIntros "!> _". iApply "Hφ"; by iLeft. }
    destruct wdst; try done. destruct sb; try done.
    destruct tag; cycle 1.
    {
      iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %Hdistinct]".
      try (destruct Hdistinct as (? & ? & ?)).
      iApply (wp_store_fail_tag _ _ _ _ _ _ _ _ _ _ (WCap false p g b e a)
                with "[$Hi $Hmap]"); eauto; try (by simplify_map_eq).
      iNext; iIntros "_". iApply "Hφ"; by iLeft.
    }

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
      rewrite list_elem_of_lookup in Ha.
      destruct Ha as [ka Hka].
      apply Hdst_in_region in Hka.
      done.
    }

    iDestruct (write_allowed_inv _ _ a with "Hinterp_dst") as (p' P Hflows Hpers) "(Hrel & Hzcond & Hwcond & Hrcond & Hmono)";[solve_addr|auto|..].

    iDestruct (open_world_interp with "[$Hrel] [$Hworld_interp]")
      as "(Hworld_interp & Hstate & (%w & WorldRes) )"
    ; [|eauto|]; [ destruct ρ;auto;done|].
    iDestruct (WorldRes_acc_forall with "WorldRes") as " [ (>Ha & Hinterp & HmonoP) WorldRes ]".

    iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ a with "Hinterp_dst") as %Hnot_shadow.
    { eapply writeAllowed_nonO; eauto. }
    { apply withinBounds_true_iff; solve_addr. }
    iApply (wp_store_success_z _ _ _ _ _ _ _ _ rdst with "[$HPC Hi Hdst Ha]")
    ; try iFrame
    ; try solve_pure
    ; eauto.
    { rewrite /withinBounds; solve_addr. }
    iNext; iIntros "(HPC & Hi & Hdst & Ha)".

    iAssert (P W C (WInt z)) as "Hinterp'".
    { iApply "Hwcond"; iApply interp_int. }
    iAssert (mono_invariant C p' (safeC P) (WInt z) ρ) as "Hmono'".
    {
      rewrite /monoReq Hρ mono_invariant_eq.
      destruct ρ;[simpl..|exfalso;done].
      - destruct (isWL p');auto.
        destruct (isDL p'); first done.
        by (iSpecialize ("Hmono" $! (WInt z) with "[%]");[eapply canStore_flowsto;eauto|]).
      - by (iSpecialize ("Hmono" $! (WInt z) with "[%]");[eapply canStore_flowsto;eauto|]).
    }

    iDestruct ("WorldRes" with "[$Ha $Hinterp' $Hmono']") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hrel WorldRes") as "Hworld_interp"; eauto.
    { destruct ρ;auto;contradiction. }

    iApply "Hφ"; iRight; iFrame "∗%".
    iSplit; first done.
    iPureIntro; solve_addr.
  Qed.

  Lemma wp_store_interp_z_cap (E : coPset) (W : WORLD) (C : CmptName) (rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr)
    (wi : Word) (z : Z)
    :
    decodeInstrW wi = Store rdst (inl z) 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rdst ≠ cnull ->

     {{{  interp W C (WCap true p g b e a)
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rdst ↦ᵣ (WCap true p g b e a)
           ∗ world_interp W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          (⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rdst ↦ᵣ WCap true p g b e a
           ∗ world_interp W C
           ∗ ⌜ writeAllowed p ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ? φ)
      "(#Hinterp_dst & HPC & Hi & Hdst & Hworld_interp)".
    iIntros "Hφ".
    iApply (wp_store_interp_z with "[-Hφ]");eauto;[iFrame "∗ #"|].
    iNext. iIntros (ret) "[? | (%&%&%&%&%&%&?&?&?&?&?&?&%&%)]"
    ; iApply "Hφ" ; auto.
    iRight. simplify_eq.  iFrame.
    auto.
  Qed.

  Lemma wp_unseal_unknown E pc_p pc_g pc_b pc_e pc_a pc_a' wi r1 r2 wsealr wsealed  :
    decodeInstrW wi = UnSeal r2 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{  PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ pc_a ↦ₐ wi
          ∗ r1 ↦ᵣ wsealr
          ∗ r2 ↦ᵣ wsealed
    }}}
      Instr Executable @ E
      {{{ retv, RET retv;
          ⌜ retv = FailedV ⌝
          ∨ (∃ psr gsr bsr esr asr ot wsb,
              ⌜ retv = NextIV ⌝
              ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ wi
              ∗ r1 ↦ᵣ wsealr
              ∗ r2 ↦ᵣ WSealable (machine_word.unseal gsr wsb)
              ∗ ⌜ wsealr = (WSealRange true psr gsr bsr esr asr) ⌝ ∗ ⌜ permit_unseal psr = true ⌝
              ∗ ⌜ wsealed = WSealed ot wsb ⌝
              ∗ ⌜ get_tag_sealable wsb = true ⌝
              ∗ ⌜ withinBounds bsr esr ot = true ⌝ )
          ∨ ∃ tsr psr gsr bsr esr asr ot sb,
              ⌜ retv = NextIV ⌝
              ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ wi
              ∗ r1 ↦ᵣ wsealr
              ∗ r2 ↦ᵣ WSealable (clear_tag_sealable (machine_word.unseal gsr sb))
              ∗ ⌜ wsealr = WSealRange tsr psr gsr bsr esr asr ⌝
              ∗ ⌜ wsealed = WSealed ot sb ⌝
              ∗ ⌜ tsr && get_tag_sealable sb && permit_unseal psr &&
                    withinBounds bsr esr ot = false ⌝
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpc_a' ?? ϕ) "(HPC & Hpc_a & Hr1 & Hr2) Hφ".

    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_UnSeal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | ].
    { iApply "Hφ". iRight. iLeft.
      simplify_map_eq.
      match goal with
      | Hinc : incrementPC _ = Some _ |- _ =>
          apply incrementPC_Some_inv in Hinc;
          destruct Hinc as (tpc & ppc & gpc & bpc & epc & apc & apc' & HPC & Hapc' & ->)
      end.
      rewrite lookup_insert_ne // lookup_insert_eq in HPC.
      simplify_eq.
      iExists p, g, b, e, a, o, sb.
      rewrite (insert_insert_ne _ _ PC) //.
      rewrite (insert_insert_ne _ _ r1) //.
      rewrite !insert_insert_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[HPC Hmap]"; first by simplify_map_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[Hr1 Hmap]"; first by simplify_map_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[Hr2 Hmap]"; first by simplify_map_eq.
      iFrame; done.
    }
    { iApply "Hφ". iRight. iRight.
      simplify_map_eq.
      match goal with
      | Hinc : incrementPC _ = Some _ |- _ =>
          apply incrementPC_Some_inv in Hinc;
          destruct Hinc as (tpc & ppc & gpc & bpc & epc & apc & apc' & HPC & Hapc' & ->)
      end.
      rewrite lookup_insert_ne // lookup_insert_eq in HPC.
      simplify_eq.
      iExists t, p, g, b, e, a, a', sb.
      rewrite (insert_insert_ne _ _ PC) //.
      rewrite (insert_insert_ne _ _ r1) //.
      rewrite !insert_insert_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[HPC Hmap]"; first by simplify_map_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[Hr1 Hmap]"; first by simplify_map_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[Hr2 Hmap]"; first by simplify_map_eq.
      iFrame; done.
    }
    { iApply "Hφ". by iLeft. }
  Qed.

  Lemma wp_unseal_unknown' E pc_p pc_g pc_b pc_e pc_a pc_a' wi r1 r2 wsealr wsealed  :
    decodeInstrW wi = UnSeal r1 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{  PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ pc_a ↦ₐ wi
          ∗ r1 ↦ᵣ wsealr
          ∗ r2 ↦ᵣ wsealed
    }}}
      Instr Executable @ E
      {{{ retv, RET retv;
          ⌜ retv = FailedV ⌝
          ∨ (∃ psr gsr bsr esr asr ot wsb,
              ⌜ retv = NextIV ⌝
              ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ wi
              ∗ r1 ↦ᵣ WSealable (machine_word.unseal gsr wsb)
              ∗ r2 ↦ᵣ wsealed
              ∗ ⌜ wsealr = (WSealRange true psr gsr bsr esr asr) ⌝ ∗ ⌜ permit_unseal psr = true ⌝
              ∗ ⌜ wsealed = WSealed ot wsb ⌝
              ∗ ⌜ get_tag_sealable wsb = true ⌝
              ∗ ⌜ withinBounds bsr esr ot = true ⌝ )
          ∨ ∃ tsr psr gsr bsr esr asr ot sb,
              ⌜ retv = NextIV ⌝
              ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ wi
              ∗ r1 ↦ᵣ WSealable (clear_tag_sealable (machine_word.unseal gsr sb))
              ∗ r2 ↦ᵣ wsealed
              ∗ ⌜ wsealr = WSealRange tsr psr gsr bsr esr asr ⌝
              ∗ ⌜ wsealed = WSealed ot sb ⌝
              ∗ ⌜ tsr && get_tag_sealable sb && permit_unseal psr &&
                    withinBounds bsr esr ot = false ⌝
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpc_a' ?? ϕ) "(HPC & Hpc_a & Hr1 & Hr2) Hφ".

    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_UnSeal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | ].
    { iApply "Hφ". iRight. iLeft.
      simplify_map_eq.
      match goal with
      | Hinc : incrementPC _ = Some _ |- _ =>
          apply incrementPC_Some_inv in Hinc;
          destruct Hinc as (tpc & ppc & gpc & bpc & epc & apc & apc' & HPC & Hapc' & ->)
      end.
      rewrite lookup_insert_ne // lookup_insert_eq in HPC.
      simplify_eq.
      iExists p, g, b, e, a, o, sb.
      rewrite (insert_insert_ne _ _ PC) //.
      rewrite !insert_insert_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[HPC Hmap]"; first by simplify_map_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[Hr1 Hmap]"; first by simplify_map_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[Hr2 Hmap]"; first by simplify_map_eq.
      iFrame; done.
    }
    { iApply "Hφ". iRight. iRight.
      simplify_map_eq.
      match goal with
      | Hinc : incrementPC _ = Some _ |- _ =>
          apply incrementPC_Some_inv in Hinc;
          destruct Hinc as (tpc & ppc & gpc & bpc & epc & apc & apc' & HPC & Hapc' & ->)
      end.
      rewrite lookup_insert_ne // lookup_insert_eq in HPC.
      simplify_eq.
      iExists t, p, g, b, e, a, a', sb.
      rewrite (insert_insert_ne _ _ PC) //.
      rewrite !insert_insert_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[HPC Hmap]"; first by simplify_map_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[Hr1 Hmap]"; first by simplify_map_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[Hr2 Hmap]"; first by simplify_map_eq.
      iFrame; done.
    }
    { iApply "Hφ". by iLeft. }
  Qed.

  Lemma wp_unseal_unknown_sealed E pc_p pc_g pc_b pc_e pc_a pc_a' wi r1 r2 psr gsr bsr esr asr wsealed  :
    decodeInstrW wi = UnSeal r2 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    permit_unseal psr = true ->
    (bsr <= asr < esr)%ot ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{  PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ pc_a ↦ₐ wi
          ∗ r1 ↦ᵣ WSealRange true psr gsr bsr esr asr
          ∗ r2 ↦ᵣ wsealed
    }}}
      Instr Executable @ E
      {{{ retv, RET retv;
          ⌜ retv = FailedV ⌝
          ∨ (∃ ot wsb,
              ⌜ retv = NextIV ⌝
              ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ wi
              ∗ r1 ↦ᵣ WSealRange true psr gsr bsr esr asr
              ∗ r2 ↦ᵣ WSealable (machine_word.unseal gsr wsb)
              ∗ ⌜ wsealed = WSealed ot wsb ⌝
              ∗ ⌜ get_tag_sealable wsb = true ⌝
              ∗ ⌜ withinBounds bsr esr ot = true ⌝ )
          ∨ ∃ ot sb,
              ⌜ retv = NextIV ⌝
              ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ wi
              ∗ r1 ↦ᵣ WSealRange true psr gsr bsr esr asr
              ∗ r2 ↦ᵣ WSealable (clear_tag_sealable (machine_word.unseal gsr sb))
              ∗ ⌜ wsealed = WSealed ot sb ⌝
              ∗ ⌜ get_tag_sealable sb && withinBounds bsr esr ot = false ⌝
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpc_a' Hpsr Hsr ?? ϕ) "(HPC & Hpc_a & Hr1 & Hr2) Hφ".

    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_UnSeal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | ].
    { iApply "Hφ". iRight. iLeft.
      simplify_map_eq.
      match goal with
      | Hinc : incrementPC _ = Some _ |- _ =>
          apply incrementPC_Some_inv in Hinc;
          destruct Hinc as (tpc & ppc & gpc & bpc & epc & apc & apc' & HPC & Hapc' & ->)
      end.
      rewrite lookup_insert_ne // lookup_insert_eq in HPC.
      simplify_eq.
      iExists o, sb.
      rewrite (insert_insert_ne _ _ PC) //.
      rewrite (insert_insert_ne _ _ r1) //.
      rewrite !insert_insert_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[HPC Hmap]"; first by simplify_map_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[Hr1 Hmap]"; first by simplify_map_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[Hr2 Hmap]"; first by simplify_map_eq.
      iFrame; done.
    }
    { iApply "Hφ". iRight. iRight.
      simplify_map_eq.
      match goal with
      | Hinc : incrementPC _ = Some _ |- _ =>
          apply incrementPC_Some_inv in Hinc;
          destruct Hinc as (tpc & ppc & gpc & bpc & epc & apc & apc' & HPC & Hapc' & ->)
      end.
      rewrite lookup_insert_ne // lookup_insert_eq in HPC.
      simplify_eq.
      iExists a', sb.
      rewrite (insert_insert_ne _ _ PC) //.
      rewrite (insert_insert_ne _ _ r1) //.
      rewrite !insert_insert_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[HPC Hmap]"; first by simplify_map_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[Hr1 Hmap]"; first by simplify_map_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[Hr2 Hmap]"; first by simplify_map_eq.
      match goal with Hinvalid : _ && withinBounds _ _ _ = false |- _ =>
        rewrite Hpsr !andb_true_r /= in Hinvalid
      end.
      iFrame; done.
    }
    { iApply "Hφ". by iLeft. }
  Qed.

  Lemma wp_load_interp (E : coPset) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wsrc wdst : Word)
    :
    decodeInstrW wi = Load rdst rsrc 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

     {{{ interp W C wsrc
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rdst ↦ᵣ wdst
           ∗ world_interp W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          ( ∃ p g b e a wload,
           ⌜ wsrc = WCap true p g b e a ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ WCap true p g b e a
           ∗ rdst ↦ᵣ wload ∗ interp W C wload
           ∗ world_interp W C
           ∗ ⌜ readAllowed p = true ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ?? φ)
      "(#Hinterp_src & HPC & Hi & Hsrc & Hdst & Hworld_interp)".
    iIntros "Hφ".

    destruct (is_cap wsrc) eqn:Hcap;cycle 1.
    {
      iApply (wp_load_fail_not_cap with "[HPC Hi Hsrc Hdst]")
      ; try iFrame
      ; try solve_pure.
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }
    destruct wsrc;try done. destruct sb; try done.
    destruct tag; cycle 1.
    {
      iDestruct (map_of_regs_3 with "HPC Hdst Hsrc") as "[Hmap (%&%&%)]".
      iApply (wp_load_fail_tag _ _ _ _ _ _ _ _ _ _ (WCap false p g b e a)
                with "[$Hi $Hmap]"); eauto; try (by simplify_map_eq).
      iNext; iIntros "_". iApply "Hφ"; by iLeft.
    }

    destruct (decide (readAllowed p = true))%a as [Hra_src|Hra_src]; cycle 1.
    {
      iApply (wp_load_fail_not_ra with "[HPC Hi Hsrc Hdst]")
      ; try iFrame
      ; try solve_pure.
      { destruct p as [ [] ? ? ? ]; cbn in * ; done. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }
    destruct (decide (b <= a))%a as [Hba|Hba]; cycle 1.
    {
      iApply (wp_load_fail_not_withinbounds with "[HPC Hi Hsrc Hdst]")
      ; try iFrame
      ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }
    destruct (decide (a < e))%a as [Hae|Hae]; cycle 1.
    {
      iApply (wp_load_fail_not_withinbounds with "[HPC Hi Hsrc Hdst]")
      ; try iFrame
      ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }

    iDestruct (readAllowed_valid_cap with "Hinterp_src") as "%Hsrc_in_region"; auto.
    assert ( ∃ ρ, std W !! a = Some ρ ∧ ρ ≠ Revoked) as ( ρ & Hρ & Hρ_not_revoked).
    {
      rewrite Forall_lookup in Hsrc_in_region.
      assert ( a ∈ finz.seq_between b e) as Ha.
      { apply elem_of_finz_seq_between; solve_addr. }
      rewrite list_elem_of_lookup in Ha.
      destruct Ha as [ka Hka].
      apply Hsrc_in_region in Hka.
      done.
    }

    iDestruct (read_allowed_inv _ _ a with "Hinterp_src") as (p' P Hflows Hpers) "(Hrel & Hzcond & Hwcond & Hrcond & Hmono)";[solve_addr|auto|..].

    iDestruct (open_world_interp with "[$Hrel] [$Hworld_interp]")
      as "(Hworld_interp & Hstate & (%w & WorldRes) )"
    ; [|eauto|]; [ destruct ρ;auto;done|].
    iDestruct (WorldRes_acc with "WorldRes") as "[ (>Ha & Hinterp) WorldRes ]".

    iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ a with "Hinterp_src") as %Hnot_shadow.
    { eapply readAllowed_nonO; eauto. }
    { apply withinBounds_true_iff; solve_addr. }
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%Hpc_src & %Hpc_dst & %Hsrc_dst)]".
    iDestruct (memMap_resource_2ne_apply with "Hi Ha") as "[Hmem %Hpc_a]".
    iApply (wp_load E pc_p pc_g pc_b pc_e pc_a rdst rsrc wi with "[$Hmap $Hmem]")
      ; try done; try (by simplify_map_eq).
    { by rewrite !dom_insert; set_solver+. }
    { exists true, p, g, b, e, a. split.
      - unfold read_reg_inr. by simplify_map_eq.
      - case_decide; last done. exists w. by simplify_map_eq. }
    { intros p0 g0 b0 e0 a0 (Hsrc0 & _). simpl_map_regs by eauto. simplify_map_eq. done. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    destruct Hspec as [p0 g0 b0 e0 a0 loadv actualv Hallow Hlookup Hactual Hinc|].
    2: { iApply "Hφ". by iLeft. }
    destruct Hallow as (Hsrc0 & _). simpl_map_regs by eauto.
    rewrite lookup_insert_ne in Hsrc0; last congruence.
    rewrite lookup_insert decide_True in Hsrc0; last done.
    injection Hsrc0 as <- <- <- <- <-.
    rewrite lookup_insert_ne in Hlookup; last congruence.
    rewrite lookup_insert decide_True in Hlookup; last done.
    injection Hlookup as ->.
    unfold incrementPC, incrementPC_gen in Hinc. simplify_map_eq.
    rewrite (insert_insert_ne _ rdst PC) // insert_insert_eq.
    rewrite (insert_insert_ne _ rdst rsrc) // insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(HPC & Hsrc & Hdst)"; eauto.
    iDestruct (memMap_resource_2ne with "Hmem") as "[Hi Ha]"; auto.
    pose proof (Hpers (W, C, loadv)).
    iDestruct "Hinterp" as "#HφV /=".

    iDestruct ("WorldRes" with "[$Ha $HφV]") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hrel WorldRes") as "Hworld_interp"; eauto.
    { destruct ρ;auto;contradiction. }

    iApply "Hφ"; iRight; iFrame "∗%".
    iSplit; first done.
    iSplit; first done.
    iSplit; last solve_addr.
    destruct Hactual as [-> | ->]; last iApply interp_clear_tag.
    iDestruct ("Hwcond" with "HφV") as "H"; cbn.
    iApply interp_weakening_word_load; eauto.
  Qed.

  Lemma wp_load_interp_cap (E : coPset) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr)
    (wi wdst : Word)
    :
    decodeInstrW wi = Load rdst rsrc 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

     {{{ interp W C (WCap true p g b e a)
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ (WCap true p g b e a)
           ∗ rdst ↦ᵣ wdst
           ∗ world_interp W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          (∃ wload,
              ⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ (WCap true p g b e a)
           ∗ rdst ↦ᵣ wload ∗ interp W C wload
           ∗ world_interp W C
           ∗ ⌜ readAllowed p = true ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ?? φ)
      "(#Hinterp_src & HPC & Hi & Hsrc & Hdst & Hworld_interp)".
    iIntros "Hφ".
    iApply (wp_load_interp with "[-Hφ]");eauto;[iFrame "∗ #"|].
    iNext. iIntros (ret) "[? | (%&%&%&%&%&%&%&?&?&?&?&?&?&?&?&%&%)]"
    ; iApply "Hφ" ; auto.
    iRight. simplify_eq.  iFrame.
    auto.
  Qed.

  (* Accesses retain the original current address and report their checked effective address. *)

  Lemma wp_store_interp_imm (E : coPset) (imm : Z) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wsrc wdst : Word)
    :
    decodeInstrW wi = Store rdst (inr rsrc) imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

     {{{ interp W C wsrc
           ∗ interp W C wdst
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rdst ↦ᵣ wdst
           ∗ world_interp W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          ( ∃ p g b e a ea,
           ⌜ wdst = WCap true p g b e a ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rdst ↦ᵣ WCap true p g b e a
           ∗ world_interp W C
           ∗ ⌜ writeAllowed p = true ⌝
           ∗ ⌜(a + imm)%a = Some ea⌝
           ∗ ⌜(b <= ea < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ?? φ)
      "(#Hinterp_src & #Hinterp_dst & HPC & Hi & Hsrc & Hdst & Hworld_interp)".
    iIntros "Hφ".

    destruct (is_cap wdst) eqn:Hcap;cycle 1.
    {
      iApply (wp_store_fail_reg_not_cap_imm _ _ _ _ _ _ _ _ rdst rsrc with "[$]")
      ; try solve_pure; try done.
      iIntros "!> _". iApply "Hφ"; by iLeft. }
    destruct wdst; try done. destruct sb; try done.
    destruct tag; cycle 1.
    {
      iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap %Hdistinct]".
      try (destruct Hdistinct as (? & ? & ?)).
      iApply (wp_store_fail_tag_imm _ _ _ _ _ _ _ _ _ _ _ (WCap false p g b e a)
                with "[$Hi $Hmap]"); eauto; try (by simplify_map_eq); try (by rewrite lookup_reg_not_cnull //; simplify_map_eq).
      iNext; iIntros "_". iApply "Hφ"; by iLeft.
    }

    destruct (a + imm)%a as [ea|] eqn:Hea; cycle 1.
    {
      iApply (wp_store_fail_reg_overflow_imm E imm pc_p pc_g pc_b pc_e pc_a wi rdst rsrc p g b e a wsrc with "[$]"); try solve_pure; try done.
      iNext; iIntros "_". iApply "Hφ"; by iLeft.
    }

    destruct (decide (writeAllowed p = true))%a as [Hp_stk_wa|Hp_stk_wa]; cycle 1.
    {
      iApply (wp_store_fail_reg_perm_imm with "[HPC Hi Hdst Hsrc]")
      ; try iFrame
      ; try solve_pure; try done.
      { by destruct (writeAllowed p); auto. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }
    destruct (decide (b <= ea))%a as [Hba|Hba]; cycle 1.
    {
      iApply (wp_store_fail_reg_imm with "[HPC Hi Hdst Hsrc]")
      ; try iFrame
      ; try solve_pure; try done.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }
    destruct (decide (ea < e))%a as [Hae|Hae]; cycle 1.
    {
      iApply (wp_store_fail_reg_imm with "[HPC Hi Hdst Hsrc]")
      ; try iFrame
      ; try solve_pure; try done.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }

    iDestruct (writeAllowed_valid_cap with "Hinterp_dst") as "%Hdst_in_region"; auto.
    assert ( ∃ ρ, std W !! ea = Some ρ ∧ ρ ≠ Revoked) as ( ρ & Hρ & Hρ_not_revoked).
    {
      rewrite Forall_lookup in Hdst_in_region.
      assert ( ea ∈ finz.seq_between b e) as Ha.
      { apply elem_of_finz_seq_between; solve_addr. }
      rewrite list_elem_of_lookup in Ha.
      destruct Ha as [ka Hka].
      apply Hdst_in_region in Hka.
      done.
    }

    iDestruct (write_allowed_inv _ _ ea with "Hinterp_dst") as (p' P Hflows Hpers) "(Hrel & Hzcond & Hwcond & Hrcond & Hmono)";[solve_addr|auto|..].

    iDestruct (open_world_interp with "[$Hrel] [$Hworld_interp]")
      as "(Hworld_interp & Hstate & (%w & WorldRes) )"
    ; [|eauto|]; [ destruct ρ;auto;done|].
    iDestruct (WorldRes_acc_forall with "WorldRes") as " [ (>Ha & Hinterp & HmonoP) WorldRes ]".


    iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ ea with "Hinterp_dst") as %Hnot_shadow.
    { eapply writeAllowed_nonO; eauto. }
    { apply withinBounds_true_iff; solve_addr. }
    iApply (wp_store_success_reg_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_a' wi rdst rsrc w p g b e a ea imm wsrc with "[$HPC Hi Hsrc Hdst Ha]")
    ; try iFrame
    ; try solve_pure; try done.
    { rewrite /withinBounds; solve_addr. }
    iNext; iIntros "(HPC & Hi & Hsrc & Hdst & Ha)".

    iAssert (P W C (store_word p wsrc)) as "Hinterp'".
    {
      iApply "Hwcond".
      rewrite /store_word.
      destruct (canStore p wsrc); first done.
      iApply interp_clear_tag.
    }
    iAssert (mono_invariant C p' (safeC P) (store_word p wsrc) ρ) as "Hmono'".
    {
      rewrite /monoReq Hρ mono_invariant_eq.
      destruct ρ;[simpl..|exfalso;done].
      - destruct (isWL p');auto.
        destruct (isDL p'); first done.
        by (iSpecialize ("Hmono" with "[%]");[eapply canStore_store_word_flowsto;eauto|]).
      - by (iSpecialize ("Hmono" with "[%]");[eapply canStore_store_word_flowsto;eauto|]).
    }

    iDestruct ("WorldRes" with "[$Ha $Hinterp' $Hmono']") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hrel WorldRes") as "Hworld_interp"; eauto.
    { destruct ρ;auto;contradiction. }

    iApply "Hφ"; iRight. iExists p, g, b, e, a, ea. iFrame "∗%".
    iSplit; first done.
    iPureIntro; solve_addr.
  Qed.

  Lemma wp_store_interp_cap_imm (E : coPset) (imm : Z) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr)
    (wi wsrc : Word)
    :
    decodeInstrW wi = Store rdst (inr rsrc) imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

     {{{ interp W C wsrc
           ∗ interp W C (WCap true p g b e a)
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rdst ↦ᵣ (WCap true p g b e a)
           ∗ world_interp W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          (∃ ea, ⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rdst ↦ᵣ WCap true p g b e a
           ∗ world_interp W C
           ∗ ⌜ writeAllowed p = true ⌝
           ∗ ⌜(a + imm)%a = Some ea⌝
           ∗ ⌜(b <= ea < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ? ? φ)
      "(#Hinterp_src & #Hinterp_dst & HPC & Hi & Hsrc & Hdst & Hworld_interp)".
    iIntros "Hφ".
    iApply (wp_store_interp_imm with "[-Hφ]");eauto;[iFrame "∗ #"|].
    iNext. iIntros (ret) "Hpost". iApply "Hφ".
    iDestruct "Hpost" as "[Hfail | Hsuccess]"; first (iLeft; done).
    iDestruct "Hsuccess" as (p0 g0 b0 e0 a0 ea) "(%Heq & Hrest)".
    simplify_eq. iRight. iExists ea. iExact "Hrest".
  Qed.

  Lemma wp_store_interp_z_imm (E : coPset) (imm : Z) (W : WORLD) (C : CmptName) (rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wdst : Word) (z : Z)
    :
    decodeInstrW wi = Store rdst (inl z) imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rdst ≠ cnull ->

     {{{ interp W C wdst
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rdst ↦ᵣ wdst
           ∗ world_interp W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          ( ∃ p g b e a ea,
           ⌜ wdst = WCap true p g b e a ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rdst ↦ᵣ WCap true p g b e a
           ∗ world_interp W C
           ∗ ⌜ writeAllowed p ⌝
           ∗ ⌜(a + imm)%a = Some ea⌝
           ∗ ⌜(b <= ea < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ? φ)
      "(#Hinterp_dst & HPC & Hi & Hdst & Hworld_interp)".
    iIntros "Hφ".

    destruct (is_cap wdst) eqn:Hcap;cycle 1.
    {
      iApply (wp_store_fail_z_not_cap_imm with "[$]")
      ; try solve_pure; try done.
      iIntros "!> _". iApply "Hφ"; by iLeft. }
    destruct wdst; try done. destruct sb; try done.
    destruct tag; cycle 1.
    {
      iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %Hdistinct]".
      try (destruct Hdistinct as (? & ? & ?)).
      iApply (wp_store_fail_tag_imm _ _ _ _ _ _ _ _ _ _ _ (WCap false p g b e a)
                with "[$Hi $Hmap]"); eauto; try (by simplify_map_eq); try (by rewrite lookup_reg_not_cnull //; simplify_map_eq).
      iNext; iIntros "_". iApply "Hφ"; by iLeft.
    }

    destruct (a + imm)%a as [ea|] eqn:Hea; cycle 1.
    {
      iApply (wp_store_fail_z_overflow_imm E imm pc_p pc_g pc_b pc_e pc_a wi rdst p g b e a z with "[$]"); try solve_pure; try done.
      iNext; iIntros "_". iApply "Hφ"; by iLeft.
    }

    destruct (decide (writeAllowed p = true))%a as [Hstore_src|Hstore_src]; cycle 1.
    {
      iApply (wp_store_fail_z_perm_imm with "[HPC Hi Hdst]")
      ; try iFrame
      ; try solve_pure
      ; try done.
      { by destruct ( writeAllowed p ); auto. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }
    destruct (decide (b <= ea))%a as [Hba|Hba]; cycle 1.
    {
      iApply (wp_store_fail_z_imm with "[HPC Hi Hdst]")
      ; try iFrame
      ; try solve_pure
      ; try done.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }
    destruct (decide (ea < e))%a as [Hae|Hae]; cycle 1.
    {
      iApply (wp_store_fail_z_imm with "[HPC Hi Hdst]")
      ; try iFrame
      ; try solve_pure
      ; try done.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }

    iDestruct (writeAllowed_valid_cap with "Hinterp_dst") as "%Hdst_in_region"; auto.
    assert ( ∃ ρ, std W !! ea = Some ρ ∧ ρ ≠ Revoked) as ( ρ & Hρ & Hρ_not_revoked).
    {
      rewrite Forall_lookup in Hdst_in_region.
      assert ( ea ∈ finz.seq_between b e) as Ha.
      { apply elem_of_finz_seq_between; solve_addr. }
      rewrite list_elem_of_lookup in Ha.
      destruct Ha as [ka Hka].
      apply Hdst_in_region in Hka.
      done.
    }

    iDestruct (write_allowed_inv _ _ ea with "Hinterp_dst") as (p' P Hflows Hpers) "(Hrel & Hzcond & Hwcond & Hrcond & Hmono)";[solve_addr|auto|..].

    iDestruct (open_world_interp with "[$Hrel] [$Hworld_interp]")
      as "(Hworld_interp & Hstate & (%w & WorldRes) )"
    ; [|eauto|]; [ destruct ρ;auto;done|].
    iDestruct (WorldRes_acc_forall with "WorldRes") as " [ (>Ha & Hinterp & HmonoP) WorldRes ]".

    iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ ea with "Hinterp_dst") as %Hnot_shadow.
    { eapply writeAllowed_nonO; try done. }
    { apply withinBounds_true_iff; solve_addr. }
    iApply (wp_store_success_z_imm E pc_p pc_g pc_b pc_e pc_a pc_a' wi rdst z w p g b e a ea imm with "[$HPC Hi Hdst Ha]")
    ; try iFrame
    ; try solve_pure; try done.
    { rewrite /withinBounds; solve_addr. }
    iNext; iIntros "(HPC & Hi & Hdst & Ha)".

    iAssert (P W C (WInt z)) as "Hinterp'".
    { iApply "Hwcond"; iApply interp_untagged; done. }
    iAssert (mono_invariant C p' (safeC P) (WInt z) ρ) as "Hmono'".
    {
      rewrite /monoReq Hρ mono_invariant_eq.
      destruct ρ;[simpl..|exfalso;done].
      - destruct (isWL p');auto.
        destruct (isDL p'); first done.
        by (iSpecialize ("Hmono" $! (WInt z) with "[%]");[eapply canStore_flowsto;eauto|]).
      - by (iSpecialize ("Hmono" $! (WInt z) with "[%]");[eapply canStore_flowsto;eauto|]).
    }

    iDestruct ("WorldRes" with "[$Ha $Hinterp' $Hmono']") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hrel WorldRes") as "Hworld_interp"; try done.
    { destruct ρ;auto;contradiction. }

    iApply "Hφ"; iRight. iExists p, g, b, e, a, ea. iFrame "∗%".
    iSplit; first done.
    iPureIntro; solve_addr.
  Qed.

  Lemma wp_store_interp_z_cap_imm (E : coPset) (imm : Z) (W : WORLD) (C : CmptName) (rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr)
    (wi : Word) (z : Z)
    :
    decodeInstrW wi = Store rdst (inl z) imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rdst ≠ cnull ->

     {{{  interp W C (WCap true p g b e a)
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rdst ↦ᵣ (WCap true p g b e a)
           ∗ world_interp W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          (∃ ea, ⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rdst ↦ᵣ WCap true p g b e a
           ∗ world_interp W C
           ∗ ⌜ writeAllowed p ⌝
           ∗ ⌜(a + imm)%a = Some ea⌝
           ∗ ⌜(b <= ea < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ? φ)
      "(#Hinterp_dst & HPC & Hi & Hdst & Hworld_interp)".
    iIntros "Hφ".
    iApply (wp_store_interp_z_imm with "[-Hφ]");eauto;[iFrame "∗ #"|].
    iNext. iIntros (ret) "Hpost". iApply "Hφ".
    iDestruct "Hpost" as "[Hfail | Hsuccess]"; first (iLeft; done).
    iDestruct "Hsuccess" as (p0 g0 b0 e0 a0 ea) "(%Heq & Hrest)".
    simplify_eq. iRight. iExists ea. iExact "Hrest".
  Qed.

  Lemma wp_load_interp_imm (E : coPset) (imm : Z) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wsrc wdst : Word)
    :
    decodeInstrW wi = Load rdst rsrc imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

     {{{ interp W C wsrc
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rdst ↦ᵣ wdst
           ∗ world_interp W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          ( ∃ p g b e a ea wload,
           ⌜ wsrc = WCap true p g b e a ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ WCap true p g b e a
           ∗ rdst ↦ᵣ wload ∗ interp W C wload
           ∗ world_interp W C
           ∗ ⌜ readAllowed p = true ⌝
           ∗ ⌜(a + imm)%a = Some ea⌝
           ∗ ⌜(b <= ea < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ?? φ)
      "(#Hinterp_src & HPC & Hi & Hsrc & Hdst & Hworld_interp)".
    iIntros "Hφ".

    destruct (is_cap wsrc) eqn:Hcap;cycle 1.
    {
      iApply (wp_load_fail_not_cap_imm with "[HPC Hi Hsrc Hdst]")
      ; try iFrame
      ; try solve_pure; try done.
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }
    destruct wsrc;try done. destruct sb; try done.
    destruct tag; cycle 1.
    {
      iDestruct (map_of_regs_3 with "HPC Hdst Hsrc") as "[Hmap (%&%&%)]".
      iApply (wp_load_fail_tag_imm _ _ _ _ _ _ _ _ _ _ _ (WCap false p g b e a)
                with "[$Hi $Hmap]"); eauto; try (by simplify_map_eq); try (by rewrite lookup_reg_not_cnull //; simplify_map_eq).
      iNext; iIntros "_". iApply "Hφ"; by iLeft.
    }

    destruct (a + imm)%a as [ea|] eqn:Hea; cycle 1.
    {
      iDestruct (map_of_regs_3 with "HPC Hdst Hsrc") as "[Hmap (%&%&%)]".
      iApply (wp_load_fail_addr_imm with "[$Hi $Hmap]"); eauto; try (by simplify_map_eq); try (by rewrite lookup_reg_not_cnull //; simplify_map_eq).
      iNext; iIntros "_". iApply "Hφ"; by iLeft.
    }

    destruct (decide (readAllowed p = true))%a as [Hra_src|Hra_src]; cycle 1.
    {
      iApply (wp_load_fail_not_ra_imm with "[HPC Hi Hsrc Hdst]")
      ; try iFrame
      ; try solve_pure; try done.
      { destruct p as [ [] ? ? ? ]; cbn in * ; done. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }
    destruct (decide (b <= ea))%a as [Hba|Hba]; cycle 1.
    {
      iApply (wp_load_fail_not_withinbounds_imm with "[HPC Hi Hsrc Hdst]")
      ; try iFrame
      ; try solve_pure; try done.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }
    destruct (decide (ea < e))%a as [Hae|Hae]; cycle 1.
    {
      iApply (wp_load_fail_not_withinbounds_imm with "[HPC Hi Hsrc Hdst]")
      ; try iFrame
      ; try solve_pure; try done.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }

    iDestruct (readAllowed_valid_cap with "Hinterp_src") as "%Hsrc_in_region"; auto.
    assert ( ∃ ρ, std W !! ea = Some ρ ∧ ρ ≠ Revoked) as ( ρ & Hρ & Hρ_not_revoked).
    {
      rewrite Forall_lookup in Hsrc_in_region.
      assert ( ea ∈ finz.seq_between b e) as Ha.
      { apply elem_of_finz_seq_between; solve_addr. }
      rewrite list_elem_of_lookup in Ha.
      destruct Ha as [ka Hka].
      apply Hsrc_in_region in Hka.
      done.
    }

    iDestruct (read_allowed_inv _ _ ea with "Hinterp_src") as (p' P Hflows Hpers) "(Hrel & Hzcond & Hwcond & Hrcond & Hmono)";[solve_addr|auto|..].

    iDestruct (open_world_interp with "[$Hrel] [$Hworld_interp]")
      as "(Hworld_interp & Hstate & (%w & WorldRes) )"
    ; [|eauto|]; [ destruct ρ;auto;done|].
    iDestruct (WorldRes_acc with "WorldRes") as "[ (>Ha & Hinterp) WorldRes ]".

    iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ ea with "Hinterp_src") as %Hnot_shadow.
    { eapply readAllowed_nonO; eauto. }
    { apply withinBounds_true_iff; solve_addr. }
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%Hpc_src & %Hpc_dst & %Hsrc_dst)]".
    iDestruct (memMap_resource_2ne_apply with "Hi Ha") as "[Hmem %Hpc_a]".
    iApply (wp_load_memory_imm E pc_p pc_g pc_b pc_e pc_a rdst rsrc imm wi _ _ (DfracOwn 1) with "[$Hmap $Hmem]");
      try done; try (by simplify_map_eq).
    { by rewrite !dom_insert; set_solver+. }
    { exists true, p, g, b, e, a. split.
      - unfold read_reg_inr. by simplify_map_eq.
      - rewrite /reg_allows_load_imm Hea. case_decide; last done. exists w. by simplify_map_eq. }
    { intros p0 g0 b0 e0 a0 ea0 (Hsrc0 & Haddr & _).
      simpl_map_regs by eauto. simplify_map_eq. done. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    destruct Hspec as [p0 g0 b0 e0 a0 ea0 loadv actualv Hallow Hlookup Hactual Hinc|].
    2: { iApply "Hφ". by iLeft. }
    destruct Hallow as (Hsrc0 & Haddr & _). simpl_map_regs by eauto.
    rewrite lookup_insert_ne in Hsrc0; last congruence.
    rewrite lookup_insert decide_True in Hsrc0; last done.
    injection Hsrc0 as <- <- <- <- <-.
    rewrite Hea in Haddr. injection Haddr as <-.
    rewrite lookup_insert_ne in Hlookup; last congruence.
    rewrite lookup_insert decide_True in Hlookup; last done.
    injection Hlookup as ->.
    unfold incrementPC, incrementPC_gen in Hinc. simplify_map_eq.
    rewrite (insert_insert_ne _ rdst PC) // insert_insert_eq.
    rewrite (insert_insert_ne _ rdst rsrc) // insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(HPC & Hsrc & Hdst)"; eauto.
    iDestruct (memMap_resource_2ne with "Hmem") as "[Hi Ha]"; auto.
    pose proof (Hpers (W, C, loadv)).
    iDestruct "Hinterp" as "#HφV /=".
    iDestruct ("WorldRes" with "[$Ha $HφV]") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hrel WorldRes") as "Hworld_interp"; eauto.
    { destruct ρ;auto;contradiction. }
    iApply "Hφ"; iRight. iExists p, g, b, e, a, ea, actualv. iFrame "∗%".
    iSplit; first done.
    iSplit; first done.
    iSplit; last solve_addr.
    destruct Hactual as [-> | ->]; last iApply interp_clear_tag.
    iDestruct ("Hwcond" with "HφV") as "H"; cbn.
    iApply interp_weakening_word_load; eauto.

  Qed.

  Lemma wp_load_interp_cap_imm (E : coPset) (imm : Z) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr)
    (wi wdst : Word)
    :
    decodeInstrW wi = Load rdst rsrc imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

     {{{ interp W C (WCap true p g b e a)
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ (WCap true p g b e a)
           ∗ rdst ↦ᵣ wdst
           ∗ world_interp W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          (∃ ea wload,
              ⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ (WCap true p g b e a)
           ∗ rdst ↦ᵣ wload ∗ interp W C wload
           ∗ world_interp W C
           ∗ ⌜ readAllowed p = true ⌝
           ∗ ⌜(a + imm)%a = Some ea⌝
           ∗ ⌜(b <= ea < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ?? φ)
      "(#Hinterp_src & HPC & Hi & Hsrc & Hdst & Hworld_interp)".
    iIntros "Hφ".
    iApply (wp_load_interp_imm with "[-Hφ]");eauto;[iFrame "∗ #"|].
    iNext. iIntros (ret) "Hpost". iApply "Hφ".
    iDestruct "Hpost" as "[Hfail | Hsuccess]"; first (iLeft; done).
    iDestruct "Hsuccess" as (p0 g0 b0 e0 a0 ea wload) "(%Heq & Hrest)".
    simplify_eq. iRight. iExists ea, wload. iExact "Hrest".
  Qed.

End wp_interp.
