From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Export logrel_binary region_invariants_binary.
From griotte Require Import interp_weakening_binary.
From griotte Require Import rules rules_binary proofmode monotone_binary.
From griotte Require Import map_simpl register_tactics.

(** * Lockstep instruction rules with [interp]

    Each rule executes one instruction in the implementation run and the same
    instruction in the specification run, on related operands. When the
    implementation fails, the specification run is left untouched (the
    expression relation only observes halting of the implementation). When the
    implementation succeeds, the specification also succeeds, and the results
    are related. *)
Section wp_interp.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO (Word * Word)) -n> iPropO Σ).
  Implicit Types interp : (V).

  Lemma wp_store_interp (E : coPset) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wsrc wsrc' wdst wdst' : Word)
    :
    ↑specN ⊆ E →
    decodeInstrW wi = Store rdst (inr rsrc) →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

     {{{ spec_ctx
           ∗ ⤇ Seq (Instr Executable)
           ∗ interp W C (wsrc, wsrc')
           ∗ interp W C (wdst, wdst')
           ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
           ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ pc_a ↣ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rsrc ↣ᵣ wsrc'
           ∗ rdst ↦ᵣ wdst
           ∗ rdst ↣ᵣ wdst'
           ∗ world_interp W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          ( ∃ p g b e a,
           ⌜ wdst = WCap p g b e a ⌝
           ∗ ⌜ wdst' = WCap p g b e a ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ ⤇ Seq (Instr NextI)
           ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
           ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ pc_a ↣ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rsrc ↣ᵣ wsrc'
           ∗ rdst ↦ᵣ WCap p g b e a
           ∗ rdst ↣ᵣ WCap p g b e a
           ∗ world_interp W C
           ∗ ⌜ canStore p wsrc = true ⌝
           ∗ ⌜ canStore p wsrc' = true ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (HE Hdecode_wi Hcorrect_pc Hpca' ?? φ)
      "(#Hsctx & Hj & #Hinterp_src & #Hinterp_dst & HPC & HsPC & Hi & Hsi & Hsrc & Hssrc & Hdst & Hsdst
      & Hworld_interp)".
    iIntros "Hφ".
    iApply wp_fupd.

    destruct (is_cap wdst) eqn:Hcap;cycle 1.
    {
      iApply (wp_store_fail_reg_not_cap _ _ _ _ _ _ _ rdst rsrc with "[$]")
      ; try solve_pure.
      iIntros "!> _ !>". iApply "Hφ"; by iLeft. }
    destruct wdst;try done. destruct sb; try done.
    iDestruct (interp_eq_not_sealed with "Hinterp_dst") as %<-; first done.
    iDestruct (interp_canStore _ _ p with "Hinterp_src") as %Hcan_eq.

    destruct (decide (canStore p wsrc = true))%a as [Hstore_src|Hstore_src]; cycle 1.
    {
      iApply (wp_store_fail_reg_perm with "[HPC Hi Hdst Hsrc]")
      ; try iFrame
      ; try solve_pure.
      { by destruct ( canStore p wsrc ); auto. }
      iNext; iIntros "_ !>".
      iApply "Hφ"; by iLeft.
    }
    pose proof ( canStore_writeAllowed p wsrc Hstore_src ) as Hp_stk_wa.
    destruct (decide (b <= a))%a as [Hba|Hba]; cycle 1.
    {
      iApply (wp_store_fail_reg with "[HPC Hi Hdst Hsrc]")
      ; try iFrame
      ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "_ !>".
      iApply "Hφ"; by iLeft.
    }
    destruct (decide (a < e))%a as [Hae|Hae]; cycle 1.
    {
      iApply (wp_store_fail_reg with "[HPC Hi Hdst Hsrc]")
      ; try iFrame
      ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "_ !>".
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

    iDestruct (write_allowed_inv _ _ a with "Hinterp_dst")
      as (p' P Hflows Hpers) "(Hrel & Hzcond & Hwcond & Hrcond & Hmono)";[solve_addr|auto|..].

    iDestruct (open_world_interp with "[$Hrel] [$Hworld_interp]")
      as "(Hworld_interp & Hstate & (%w & WorldRes) )"
    ; [|eauto|]; [ destruct ρ;auto;done|].
    iDestruct (WorldRes_acc_forall with "WorldRes") as " [ (>Ha & >Hsa & Hinterp & HmonoP) WorldRes ]".

    iApply (wp_store_success_reg _ _ _ _ _ _ _ _ rdst rsrc with "[$HPC Hi Hsrc Hdst Ha]")
    ; try iFrame
    ; try solve_pure.
    { rewrite /withinBounds; solve_addr. }
    iNext; iIntros "(HPC & Hi & Hsrc & Hdst & Ha)".

    iMod (step_store_success_reg _ _ _ _ _ _ _ _ rdst rsrc
           with "[$Hsctx $Hj $HsPC $Hsi $Hssrc $Hsdst $Hsa]")
      as "(Hj & HsPC & Hsi & Hssrc & Hsdst & Hsa)"; eauto.
    { rewrite /withinBounds; solve_addr. }

    iAssert (P W C (wsrc, wsrc')) as "Hinterp'".
    {
      iDestruct ("Hwcond" with "Hinterp_src") as "HP".
      iFrame "HP".
    }
    iAssert (mono_invariant C p' (safeC P) (wsrc, wsrc') ρ) as "Hmono'".
    {
      rewrite /monoReq Hρ mono_invariant_eq.
      destruct ρ;[simpl..|exfalso;done].
      - destruct (isWL p');auto.
        destruct (isDL p'); first done.
        iSpecialize ("Hmono" $! (wsrc, wsrc') with "[%]"); last done.
        split; eapply canStore_flowsto; eauto; by rewrite -Hcan_eq.
      - iSpecialize ("Hmono" $! (wsrc, wsrc') with "[%]"); last done.
        split; eapply canStore_flowsto; eauto; by rewrite -Hcan_eq.
    }

    iDestruct ("WorldRes" $! (wsrc, wsrc') with "[$Ha $Hsa $Hinterp' $Hmono']") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hrel WorldRes") as "Hworld_interp"; eauto.
    { destruct ρ;auto;contradiction. }

    iModIntro.
    iApply "Hφ"; iRight; iFrame "∗%".
    repeat (iSplit; first done).
    iPureIntro; split; [by rewrite -Hcan_eq | solve_addr].
  Qed.

  Lemma wp_store_interp_cap (E : coPset) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr)
    (wi wsrc wsrc' : Word)
    :
    ↑specN ⊆ E →
    decodeInstrW wi = Store rdst (inr rsrc) →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

     {{{ spec_ctx
           ∗ ⤇ Seq (Instr Executable)
           ∗ interp W C (wsrc, wsrc')
           ∗ interp W C (WCap p g b e a, WCap p g b e a)
           ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
           ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ pc_a ↣ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rsrc ↣ᵣ wsrc'
           ∗ rdst ↦ᵣ (WCap p g b e a)
           ∗ rdst ↣ᵣ (WCap p g b e a)
           ∗ world_interp W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          (⌜ retv = NextIV ⌝
           ∗ ⤇ Seq (Instr NextI)
           ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
           ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ pc_a ↣ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rsrc ↣ᵣ wsrc'
           ∗ rdst ↦ᵣ WCap p g b e a
           ∗ rdst ↣ᵣ WCap p g b e a
           ∗ world_interp W C
           ∗ ⌜ canStore p wsrc = true ⌝
           ∗ ⌜ canStore p wsrc' = true ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (HE Hdecode_wi Hcorrect_pc Hpca' ? ? φ) "H Hφ".
    iApply (wp_store_interp with "H");eauto.
    iNext. iIntros (ret) "[? | (%&%&%&%&%&%&%&H)]"
    ; iApply "Hφ" ; auto.
    iRight. simplify_eq. iFrame.
  Qed.

  Lemma wp_store_interp_z (E : coPset) (W : WORLD) (C : CmptName) (rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wdst wdst' : Word) (z : Z)
    :
    ↑specN ⊆ E →
    decodeInstrW wi = Store rdst (inl z) →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rdst ≠ cnull ->

     {{{ spec_ctx
           ∗ ⤇ Seq (Instr Executable)
           ∗ interp W C (wdst, wdst')
           ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
           ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ pc_a ↣ₐ wi
           ∗ rdst ↦ᵣ wdst
           ∗ rdst ↣ᵣ wdst'
           ∗ world_interp W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          ( ∃ p g b e a,
           ⌜ wdst = WCap p g b e a ⌝
           ∗ ⌜ wdst' = WCap p g b e a ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ ⤇ Seq (Instr NextI)
           ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
           ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ pc_a ↣ₐ wi
           ∗ rdst ↦ᵣ WCap p g b e a
           ∗ rdst ↣ᵣ WCap p g b e a
           ∗ world_interp W C
           ∗ ⌜ writeAllowed p ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (HE Hdecode_wi Hcorrect_pc Hpca' ? φ)
      "(#Hsctx & Hj & #Hinterp_dst & HPC & HsPC & Hi & Hsi & Hdst & Hsdst & Hworld_interp)".
    iIntros "Hφ".
    iApply wp_fupd.

    destruct (is_cap wdst) eqn:Hcap;cycle 1.
    {
      iApply (wp_store_fail_z_not_cap with "[$]")
      ; try solve_pure; eauto.
      iIntros "!> _ !>". iApply "Hφ"; by iLeft. }
    destruct wdst;try done. destruct sb; try done.
    iDestruct (interp_eq_not_sealed with "Hinterp_dst") as %<-; first done.

    destruct (decide (writeAllowed p = true))%a as [Hstore_src|Hstore_src]; cycle 1.
    {
      iApply (wp_store_fail_z_perm with "[HPC Hi Hdst]")
      ; try iFrame
      ; try solve_pure
      ; eauto.
      { by destruct ( writeAllowed p ); auto. }
      iNext; iIntros "_ !>".
      iApply "Hφ"; by iLeft.
    }
    destruct (decide (b <= a))%a as [Hba|Hba]; cycle 1.
    {
      iApply (wp_store_fail_z with "[HPC Hi Hdst]")
      ; try iFrame
      ; try solve_pure
      ; eauto.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "_ !>".
      iApply "Hφ"; by iLeft.
    }
    destruct (decide (a < e))%a as [Hae|Hae]; cycle 1.
    {
      iApply (wp_store_fail_z with "[HPC Hi Hdst]")
      ; try iFrame
      ; try solve_pure
      ; eauto.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "_ !>".
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

    iDestruct (write_allowed_inv _ _ a with "Hinterp_dst")
      as (p' P Hflows Hpers) "(Hrel & Hzcond & Hwcond & Hrcond & Hmono)";[solve_addr|auto|..].

    iDestruct (open_world_interp with "[$Hrel] [$Hworld_interp]")
      as "(Hworld_interp & Hstate & (%w & WorldRes) )"
    ; [|eauto|]; [ destruct ρ;auto;done|].
    iDestruct (WorldRes_acc_forall with "WorldRes") as " [ (>Ha & >Hsa & Hinterp & HmonoP) WorldRes ]".

    iApply (wp_store_success_z _ _ _ _ _ _ _ _ rdst with "[$HPC Hi Hdst Ha]")
    ; try iFrame
    ; try solve_pure
    ; eauto.
    { rewrite /withinBounds; solve_addr. }
    iNext; iIntros "(HPC & Hi & Hdst & Ha)".

    iMod (step_store_success_z _ _ _ _ _ _ _ _ rdst
           with "[$Hsctx $Hj $HsPC $Hsi $Hsdst $Hsa]")
      as "(Hj & HsPC & Hsi & Hsdst & Hsa)"; eauto.
    { rewrite /withinBounds; solve_addr. }

    iAssert (P W C (WInt z, WInt z)) as "Hinterp'".
    { iApply "Hwcond"; iApply interp_int. }
    iAssert (mono_invariant C p' (safeC P) (WInt z, WInt z) ρ) as "Hmono'".
    {
      rewrite /monoReq Hρ mono_invariant_eq.
      destruct ρ;[simpl..|exfalso;done].
      - destruct (isWL p');auto.
        destruct (isDL p'); first done.
        iSpecialize ("Hmono" $! (WInt z, WInt z) with "[%]"); last done.
        split; eapply canStore_flowsto;eauto.
      - iSpecialize ("Hmono" $! (WInt z, WInt z) with "[%]"); last done.
        split; eapply canStore_flowsto;eauto.
    }

    iDestruct ("WorldRes" $! (WInt z, WInt z) with "[$Ha $Hsa $Hinterp' $Hmono']") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hrel WorldRes") as "Hworld_interp"; eauto.
    { destruct ρ;auto;contradiction. }

    iModIntro.
    iApply "Hφ"; iRight; iFrame "∗%".
    repeat (iSplit; first done).
    iPureIntro; solve_addr.
  Qed.

  Lemma wp_store_interp_z_cap (E : coPset) (W : WORLD) (C : CmptName) (rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr)
    (wi : Word) (z : Z)
    :
    ↑specN ⊆ E →
    decodeInstrW wi = Store rdst (inl z) →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rdst ≠ cnull ->

     {{{ spec_ctx
           ∗ ⤇ Seq (Instr Executable)
           ∗ interp W C (WCap p g b e a, WCap p g b e a)
           ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
           ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ pc_a ↣ₐ wi
           ∗ rdst ↦ᵣ (WCap p g b e a)
           ∗ rdst ↣ᵣ (WCap p g b e a)
           ∗ world_interp W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          (⌜ retv = NextIV ⌝
           ∗ ⤇ Seq (Instr NextI)
           ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
           ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ pc_a ↣ₐ wi
           ∗ rdst ↦ᵣ WCap p g b e a
           ∗ rdst ↣ᵣ WCap p g b e a
           ∗ world_interp W C
           ∗ ⌜ writeAllowed p ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (HE Hdecode_wi Hcorrect_pc Hpca' ? φ) "H Hφ".
    iApply (wp_store_interp_z with "H");eauto.
    iNext. iIntros (ret) "[? | (%&%&%&%&%&%&%&H)]"
    ; iApply "Hφ" ; auto.
    iRight. simplify_eq. iFrame.
  Qed.

  Lemma wp_unseal_unknown E W C pc_p pc_g pc_b pc_e pc_a pc_a' wi r1 r2 wsealr wsealed wsealed' :
    ↑specN ⊆ E →
    decodeInstrW wi = UnSeal r2 r1 r2 →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ spec_ctx
          ∗ ⤇ Seq (Instr Executable)
          ∗ interp W C (wsealed, wsealed')
          ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
          ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a
          ∗ pc_a ↦ₐ wi
          ∗ pc_a ↣ₐ wi
          ∗ r1 ↦ᵣ wsealr
          ∗ r1 ↣ᵣ wsealr
          ∗ r2 ↦ᵣ wsealed
          ∗ r2 ↣ᵣ wsealed'
    }}}
      Instr Executable @ E
      {{{ retv, RET retv;
          ⌜ retv = FailedV ⌝
          ∨ ∃ psr gsr bsr esr asr wsb wsb',
              ⌜ retv = NextIV ⌝
              ∗ ⤇ Seq (Instr NextI)
              ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
              ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ wi
              ∗ pc_a ↣ₐ wi
              ∗ r1 ↦ᵣ wsealr
              ∗ r1 ↣ᵣ wsealr
              ∗ r2 ↦ᵣ WSealable wsb
              ∗ r2 ↣ᵣ WSealable wsb'
              ∗ ⌜ wsealr = (WSealRange psr gsr bsr esr asr) ⌝ ∗ ⌜ permit_unseal psr = true ⌝
              ∗ ⌜ wsealed = WSealed asr wsb ⌝
              ∗ ⌜ wsealed' = WSealed asr wsb' ⌝
      }}}.
  Proof.
    iIntros (HE Hinstr Hvpc Hpc_a' ?? ϕ)
      "(#Hsctx & Hj & #Hinterp & HPC & HsPC & Hpc_a & Hspc_a & Hr1 & Hsr1 & Hr2 & Hsr2) Hφ".
    iApply wp_fupd.

    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_UnSeal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ psr gsr bsr esr asr sb Hr1 Hr2 Hpsr Hwb HincrPC | ]
    ; last (iModIntro; iApply "Hφ"; by iLeft).
    rewrite /lookup_reg in Hr1 Hr2.
    simplify_map_eq.
    apply incrementPC_Some_inv in HincrPC.
    destruct HincrPC as ( ppc & gpc & bpc & epc & apc & apc' & HPC & Hapc' & ->).
    rewrite lookup_insert_ne // lookup_insert_eq in HPC.
    simplify_eq.
    iDestruct (interp_eq_unless_sealed with "Hinterp")
      as "%Heq"; destruct Heq as [<- | (o & sb1 & sb' & Heq1 & ->)]
    ; simplify_eq.
    + iMod (step_unseal_r2 with "[$Hsctx $Hj $HsPC $Hspc_a $Hsr1 $Hsr2]")
        as "(Hj & HsPC & Hspc_a & Hsr1 & Hsr2)"; eauto.
      iModIntro; iApply "Hφ"; iRight.
      iExists psr, gsr, bsr, esr, asr, sb, sb.
      rewrite /insert_reg decide_False //.
      rewrite (insert_insert_ne _ _ PC) //.
      rewrite (insert_insert_ne _ _ r1) //.
      rewrite !insert_insert_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[HPC Hmap]"; first by simplify_map_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[Hr1 Hmap]"; first by simplify_map_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[Hr2 Hmap]"; first by simplify_map_eq.
      iFrame; done.
    + iMod (step_unseal_r2 with "[$Hsctx $Hj $HsPC $Hspc_a $Hsr1 $Hsr2]")
        as "(Hj & HsPC & Hspc_a & Hsr1 & Hsr2)"; eauto.
      iModIntro; iApply "Hφ"; iRight.
      iExists psr, gsr, bsr, esr, o, sb1, sb'.
      rewrite /insert_reg decide_False //.
      rewrite (insert_insert_ne _ _ PC) //.
      rewrite (insert_insert_ne _ _ r1) //.
      rewrite !insert_insert_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[HPC Hmap]"; first by simplify_map_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[Hr1 Hmap]"; first by simplify_map_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[Hr2 Hmap]"; first by simplify_map_eq.
      iFrame; done.
  Qed.

  Lemma wp_unseal_unknown_sealed E W C pc_p pc_g pc_b pc_e pc_a pc_a' wi r1 r2
    psr gsr bsr esr asr wsealed wsealed' :
    ↑specN ⊆ E →
    decodeInstrW wi = UnSeal r2 r1 r2 →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    permit_unseal psr = true ->
    (bsr <= asr < esr)%ot ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ spec_ctx
          ∗ ⤇ Seq (Instr Executable)
          ∗ interp W C (wsealed, wsealed')
          ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
          ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a
          ∗ pc_a ↦ₐ wi
          ∗ pc_a ↣ₐ wi
          ∗ r1 ↦ᵣ WSealRange psr gsr bsr esr asr
          ∗ r1 ↣ᵣ WSealRange psr gsr bsr esr asr
          ∗ r2 ↦ᵣ wsealed
          ∗ r2 ↣ᵣ wsealed'
    }}}
      Instr Executable @ E
      {{{ retv, RET retv;
          ⌜ retv = FailedV ⌝
          ∨ ∃ wsb wsb',
              ⌜ retv = NextIV ⌝
              ∗ ⤇ Seq (Instr NextI)
              ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
              ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ wi
              ∗ pc_a ↣ₐ wi
              ∗ r1 ↦ᵣ WSealRange psr gsr bsr esr asr
              ∗ r1 ↣ᵣ WSealRange psr gsr bsr esr asr
              ∗ r2 ↦ᵣ WSealable wsb
              ∗ r2 ↣ᵣ WSealable wsb'
              ∗ ⌜ wsealed = WSealed asr wsb ⌝
              ∗ ⌜ wsealed' = WSealed asr wsb' ⌝
      }}}.
  Proof.
    iIntros (HE Hinstr Hvpc Hpc_a' Hpsr Hsr ?? ϕ) "H Hφ".
    iApply (wp_unseal_unknown with "H"); eauto.
    iNext. iIntros (retv) "[%Hretv | (%&%&%&%&%&%&%&H)]"; iApply "Hφ".
    { iLeft; iPureIntro; exact Hretv. }
    iDestruct "H" as "(? & ? & ? & ? & ? & ? & ? & ? & ? & ? & %Heq & ? & ? & ?)".
    simplify_eq.
    iRight. iFrame.
  Qed.

  Lemma wp_load_interp (E : coPset) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wsrc wsrc' wdst wdst' : Word)
    :
    ↑specN ⊆ E →
    decodeInstrW wi = Load rdst rsrc →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

     {{{ spec_ctx
           ∗ ⤇ Seq (Instr Executable)
           ∗ interp W C (wsrc, wsrc')
           ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
           ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ pc_a ↣ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rsrc ↣ᵣ wsrc'
           ∗ rdst ↦ᵣ wdst
           ∗ rdst ↣ᵣ wdst'
           ∗ world_interp W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          ( ∃ p g b e a wload wload',
           ⌜ wsrc = WCap p g b e a ⌝
           ∗ ⌜ wsrc' = WCap p g b e a ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ ⤇ Seq (Instr NextI)
           ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
           ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ pc_a ↣ₐ wi
           ∗ rsrc ↦ᵣ WCap p g b e a
           ∗ rsrc ↣ᵣ WCap p g b e a
           ∗ rdst ↦ᵣ wload
           ∗ rdst ↣ᵣ wload'
           ∗ interp W C (wload, wload')
           ∗ world_interp W C
           ∗ ⌜ readAllowed p = true ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (HE Hdecode_wi Hcorrect_pc Hpca' ?? φ)
      "(#Hsctx & Hj & #Hinterp_src & HPC & HsPC & Hi & Hsi & Hsrc & Hssrc & Hdst & Hsdst & Hworld_interp)".
    iIntros "Hφ".
    iApply wp_fupd.

    destruct (is_cap wsrc) eqn:Hcap;cycle 1.
    {
      iApply (wp_load_fail_not_cap with "[HPC Hi Hsrc Hdst]")
      ; try iFrame
      ; try solve_pure.
      iNext; iIntros "_ !>".
      iApply "Hφ"; by iLeft.
    }
    destruct wsrc;try done. destruct sb; try done.
    iDestruct (interp_eq_not_sealed with "Hinterp_src") as %<-; first done.

    destruct (decide (readAllowed p = true))%a as [Hra_src|Hra_src]; cycle 1.
    {
      iApply (wp_load_fail_not_ra with "[HPC Hi Hsrc Hdst]")
      ; try iFrame
      ; try solve_pure.
      { destruct p as [ [] ? ? ? ]; cbn in * ; done. }
      iNext; iIntros "_ !>".
      iApply "Hφ"; by iLeft.
    }
    destruct (decide (b <= a))%a as [Hba|Hba]; cycle 1.
    {
      iApply (wp_load_fail_not_withinbounds with "[HPC Hi Hsrc Hdst]")
      ; try iFrame
      ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "_ !>".
      iApply "Hφ"; by iLeft.
    }
    destruct (decide (a < e))%a as [Hae|Hae]; cycle 1.
    {
      iApply (wp_load_fail_not_withinbounds with "[HPC Hi Hsrc Hdst]")
      ; try iFrame
      ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "_ !>".
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

    iDestruct (read_allowed_inv _ _ a with "Hinterp_src")
      as (p' P Hflows Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & Hmono)";[solve_addr|auto|..].

    iDestruct (open_world_interp with "[$Hrel] [$Hworld_interp]")
      as "(Hworld_interp & Hstate & (%w & WorldRes) )"
    ; [|eauto|]; [ destruct ρ;auto;done|].
    iDestruct (WorldRes_acc with "WorldRes") as "[ (>Ha & >Hsa & Hinterp) WorldRes ]".

    iApply (wp_load_success_alt _ rdst rsrc with "[$HPC Hi Hsrc Hdst Ha]")
    ; try iFrame
    ; try solve_pure.
    { split; auto. rewrite /withinBounds; solve_addr. }
    iNext; iIntros "(HPC & Hdst & Hi & Hsrc & Ha)".

    iMod (step_load_success_alt _ rdst rsrc
           with "[$Hsctx $Hj $HsPC $Hsi $Hsdst $Hssrc $Hsa]")
      as "(Hj & HsPC & Hsdst & Hsi & Hssrc & Hsa)"; eauto.
    { split; auto. rewrite /withinBounds; solve_addr. }

    pose proof (Hpers (W, C, w)).
    iDestruct "Hinterp" as "#HφV /=".

    iDestruct ("WorldRes" with "[$Ha $Hsa $HφV]") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hrel WorldRes") as "Hworld_interp"; eauto.
    { destruct ρ;auto;contradiction. }

    iModIntro.
    iApply "Hφ"; iRight; iFrame "∗%".
    iDestruct ("Hrcond" with "HφV") as "H"; cbn.
    iDestruct (interp_weakening_word_load _ _ p p' w with "H") as "$"; first done.
    iPureIntro; repeat split; auto; solve_addr.
  Qed.

  Lemma wp_load_interp_cap (E : coPset) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr)
    (wi wdst wdst' : Word)
    :
    ↑specN ⊆ E →
    decodeInstrW wi = Load rdst rsrc →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

     {{{ spec_ctx
           ∗ ⤇ Seq (Instr Executable)
           ∗ interp W C (WCap p g b e a, WCap p g b e a)
           ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
           ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ pc_a ↣ₐ wi
           ∗ rsrc ↦ᵣ (WCap p g b e a)
           ∗ rsrc ↣ᵣ (WCap p g b e a)
           ∗ rdst ↦ᵣ wdst
           ∗ rdst ↣ᵣ wdst'
           ∗ world_interp W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          (∃ wload wload',
              ⌜ retv = NextIV ⌝
           ∗ ⤇ Seq (Instr NextI)
           ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
           ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ pc_a ↣ₐ wi
           ∗ rsrc ↦ᵣ (WCap p g b e a)
           ∗ rsrc ↣ᵣ (WCap p g b e a)
           ∗ rdst ↦ᵣ wload
           ∗ rdst ↣ᵣ wload'
           ∗ interp W C (wload, wload')
           ∗ world_interp W C
           ∗ ⌜ readAllowed p = true ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (HE Hdecode_wi Hcorrect_pc Hpca' ?? φ) "H Hφ".
    iApply (wp_load_interp with "H");eauto.
    iNext. iIntros (ret) "[? | (%&%&%&%&%&%&%&%&%&H)]"
    ; iApply "Hφ" ; auto.
    iRight. simplify_eq. iFrame.
  Qed.

End wp_interp.
