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
    {stsg : STSG LAddr region_type OType Word Σ} {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ} {relg : relGS Σ}
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

  Local Hint Resolve addr_key_live : core.

  Lemma world_interp_heap_wf W C :
    world_interp W C -∗ ⌜heap_wf (heap_std W)⌝.
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros "(_ & Hsts & _)".
    iApply (sts_full_world_heap_wf with "Hsts").
  Qed.

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
    assert ( ∃ ρ, std W !! addr_key W a = Some ρ ∧ ρ ≠ Revoked) as ( ρ & Hρ & Hρ_not_revoked).
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

    iDestruct (world_interp_heap_wf with "Hworld_interp") as %Hheap_wf.
    iDestruct (interp_cap_addr_live W C p g b e a a with "Hinterp_dst") as %Hlive;
      [exact Hheap_wf|by eapply writeAllowed_nonO|apply withinBounds_true_iff; solve_addr|].
    iDestruct (open_world_interp W C (addr_key W a) p' (safeC P) ρ with "Hrel Hworld_interp")
      as "(Hworld_interp & Hstate & (%w & WorldRes))";
      [by apply addr_key_live|destruct ρ; auto; contradiction|exact Hρ|].
    iDestruct (WorldRes_acc_forall with "WorldRes") as " [ (>Ha & Hinterp & HmonoP) WorldRes ]".
    iDestruct (addr_key_pointsto with "Ha") as "[Ha Hshare]".


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

    iDestruct (addr_key_pointsto_join with "Ha Hshare") as "Ha".

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
    assert ( ∃ ρ, std W !! addr_key W a = Some ρ ∧ ρ ≠ Revoked) as ( ρ & Hρ & Hρ_not_revoked).
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

    iDestruct (world_interp_heap_wf with "Hworld_interp") as %Hheap_wf.
    iDestruct (interp_cap_addr_live W C p g b e a a with "Hinterp_dst") as %Hlive;
      [exact Hheap_wf|by eapply writeAllowed_nonO|apply withinBounds_true_iff; solve_addr|].
    iDestruct (open_world_interp W C (addr_key W a) p' (safeC P) ρ with "Hrel Hworld_interp")
      as "(Hworld_interp & Hstate & (%w & WorldRes))";
      [by apply addr_key_live|destruct ρ; auto; contradiction|exact Hρ|].
    iDestruct (WorldRes_acc_forall with "WorldRes") as " [ (>Ha & Hinterp & HmonoP) WorldRes ]".
    iDestruct (addr_key_pointsto with "Ha") as "[Ha Hshare]".

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

    iDestruct (addr_key_pointsto_join with "Ha Hshare") as "Ha".

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
    ↑Nallocator ⊆ E →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

     {{{ allocator_ctx ∗
           interp W C wsrc
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
    iIntros (Hdecode_wi HEalloc Hcorrect_pc Hpca' ?? φ)
      "(#Halloc & #Hinterp_src & HPC & Hi & Hsrc & Hdst & Hworld_interp)".
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
    assert ( ∃ ρ, std W !! addr_key W a = Some ρ ∧ ρ ≠ Revoked) as ( ρ & Hρ & Hρ_not_revoked).
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

    iDestruct (world_interp_heap_wf with "Hworld_interp") as %Hheap_wf.
    iDestruct (interp_cap_addr_live W C p g b e a a with "Hinterp_src") as %Hlive;
      [exact Hheap_wf|by eapply readAllowed_nonO|apply withinBounds_true_iff; solve_addr|].
    iDestruct (open_world_interp W C (addr_key W a) p' (safeC P) ρ with "Hrel Hworld_interp")
      as "(Hworld_interp & Hstate & (%w & WorldRes))";
      [by apply addr_key_live|destruct ρ; auto; contradiction|exact Hρ|].
    iDestruct (WorldRes_acc with "WorldRes") as "[ (>Ha & Hinterp) WorldRes ]".
    iDestruct (addr_key_pointsto with "Ha") as "[Ha Hshare]".

    iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ a with "Hinterp_src") as %Hnot_shadow.
    { eapply readAllowed_nonO; eauto. }
    { apply withinBounds_true_iff; solve_addr. }
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%Hpc_src & %Hpc_dst & %Hsrc_dst)]".
    iDestruct (memMap_resource_2ne_apply with "Hi Ha") as "[Hmem %Hpc_a]".
    iInv Nallocator as "> Halloc_body" "Halloc_close".
    iDestruct "Halloc_body" as (alloc_map R Halloc_dom Hcoh) "[Halloc_entries HR]".
    iEval (rewrite /allocator_entry big_sepM_sep) in "Halloc_entries".
    iDestruct "Halloc_entries" as "[Hshadow Halloc_states]".
    iAssert ([∗ map] k↦status ∈ shadow_status <$> alloc_map, k ↦ₛ status)%I
      with "[Hshadow]" as "Hshadow".
    { rewrite big_sepM_fmap. iExact "Hshadow". }
    (* Load rdst rsrc 0. *)
    iApply (wp_load_memory_shadow_imm (E ∖ ↑Nallocator)
      pc_p pc_g pc_b pc_e pc_a rdst rsrc 0 wi
      (<[pc_a:=wi]> (<[a:=w]> ∅))
      (<[PC:=WCap true pc_p pc_g pc_b pc_e pc_a]>
        (<[rsrc:=WCap true p g b e a]> (<[rdst:=wdst]> ∅)))
      (DfracOwn 1) (shadow_status <$> alloc_map) (DfracOwn 1)
      with "[Hmem Hshadow Hmap]"); eauto.
    { by simplify_map_eq. }
    { by rewrite !dom_insert; set_solver+. }
    { by rewrite lookup_insert_eq. }
    { exists true, p, g, b, e, a. split.
      - unfold read_reg_inr. by simplify_map_eq.
      - unfold reg_allows_load_imm. rewrite addr_add_0 /=.
        case_decide; last done. exists w. by simplify_map_eq. }
    { intros p0 g0 b0 e0 a0 ea0 (Hsrc0 & Haddr & _).
      simpl_map_regs by eauto. simplify_map_eq.
      rewrite addr_add_0 in Haddr. injection Haddr as <-. exact Hnot_shadow. }
    { iFrame "Hmem". iSplitL "Hshadow"; first (iNext; iExact "Hshadow").
      iNext. iExact "Hmap". }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hshadow & Hmap)".
    iAssert ([∗ map] k↦s ∈ alloc_map, allocator_entry k s)%I
      with "[Hshadow Halloc_states]" as "Halloc_entries".
    { rewrite /allocator_entry big_sepM_sep big_sepM_fmap. iFrame. }
    destruct retv; simpl in Hspec; [contradiction| |]; cycle 1.
    - destruct Hspec as
        (p0 & g0 & b0 & e0 & a0 & ea0 & loadv & actualv &
         Hallow & Hlookup & Hactual & Hobserved & Hinc).
      destruct Hallow as (Hsrc0 & Haddr & _). simpl_map_regs by eauto.
      rewrite lookup_insert_ne in Hsrc0; last congruence.
      rewrite lookup_insert decide_True in Hsrc0; last done.
      injection Hsrc0 as <- <- <- <- <-.
      rewrite addr_add_0 in Haddr. injection Haddr as <-.
      rewrite lookup_insert_ne in Hlookup; last congruence.
      rewrite lookup_insert decide_True in Hlookup; last done.
      injection Hlookup as ->.
      pose proof (Hpers (W, C, loadv)).
      iDestruct "Hinterp" as "#HφV /=".
      iDestruct ("Hwcond" with "HφV") as "#Hnormal_p'".
      iAssert (interp_in_mem p W C loadv)%I as "#Hnormal".
      { rewrite interp_in_mem_eq filter_heap_load_word.
        iApply (interp_weakening_word_load W C p p' (filter_heap W loadv));
          first exact Hflows.
        iEval (rewrite /interp_in_mem_pre filter_heap_load_word)
          in "Hnormal_p'".
        iExact "Hnormal_p'". }
      iDestruct (interp_in_mem_shadow_result W C (addr_key W a) p loadv actualv alloc_map R
        with "Hworld_interp HR Hnormal")
        as "(#Hload_interp & Hworld_interp & HR)";
        [exact Halloc_dom|exact Hcoh|exact Hobserved|].
      iMod ("Halloc_close" with "[Halloc_entries HR]") as "_".
      { iNext. iExists alloc_map, R. by iFrame "∗%". }
      iModIntro.
      unfold incrementPC, incrementPC_gen in Hinc. simplify_map_eq.
      rewrite (insert_insert_ne _ rdst PC) // insert_insert_eq.
      rewrite (insert_insert_ne _ rdst rsrc) // insert_insert_eq.
      iDestruct (regs_of_map_3 with "Hmap") as "(HPC & Hsrc & Hdst)"; eauto.
      iDestruct (memMap_resource_2ne with "Hmem") as "[Hi Ha]"; auto.
      iDestruct (addr_key_pointsto_join with "Ha Hshare") as "Ha".
      iDestruct ("WorldRes" with "[$Ha $HφV]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hrel WorldRes")
        as "Hworld_interp"; eauto.
      { destruct ρ; auto; contradiction. }
      iApply "Hφ"; iRight. iExists p, g, b, e, a, actualv. iFrame "∗%".
      iSplit; first done.
      iSplit; first done.
      iSplit; last solve_addr.
      iExact "Hload_interp".
    - iMod ("Halloc_close" with "[Halloc_entries HR]") as "_".
      { iNext. iExists alloc_map, R. by iFrame "∗%". }
      iModIntro. iApply "Hφ". by iLeft.
  Qed.

  Lemma wp_load_interp_cap (E : coPset) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr)
    (wi wdst : Word)
    :
    decodeInstrW wi = Load rdst rsrc 0 →
    ↑Nallocator ⊆ E →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

     {{{ allocator_ctx ∗
           interp W C (WCap true p g b e a)
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
    iIntros (Hdecode_wi HEalloc Hcorrect_pc Hpca' ?? φ)
      "(#Halloc & #Hinterp_src & HPC & Hi & Hsrc & Hdst & Hworld_interp)".
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
    assert ( ∃ ρ, std W !! addr_key W ea = Some ρ ∧ ρ ≠ Revoked) as ( ρ & Hρ & Hρ_not_revoked).
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

    iDestruct (world_interp_heap_wf with "Hworld_interp") as %Hheap_wf.
    iDestruct (interp_cap_addr_live W C p g b e a ea with "Hinterp_dst") as %Hlive;
      [exact Hheap_wf|by eapply writeAllowed_nonO|apply withinBounds_true_iff; solve_addr|].
    iDestruct (open_world_interp W C (addr_key W ea) p' (safeC P) ρ with "Hrel Hworld_interp")
      as "(Hworld_interp & Hstate & (%w & WorldRes))";
      [by apply addr_key_live|destruct ρ; auto; contradiction|exact Hρ|].
    iDestruct (WorldRes_acc_forall with "WorldRes") as " [ (>Ha & Hinterp & HmonoP) WorldRes ]".
    iDestruct (addr_key_pointsto with "Ha") as "[Ha Hshare]".


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

    iDestruct (addr_key_pointsto_join with "Ha Hshare") as "Ha".

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
    assert ( ∃ ρ, std W !! addr_key W ea = Some ρ ∧ ρ ≠ Revoked) as ( ρ & Hρ & Hρ_not_revoked).
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

    iDestruct (world_interp_heap_wf with "Hworld_interp") as %Hheap_wf.
    iDestruct (interp_cap_addr_live W C p g b e a ea with "Hinterp_dst") as %Hlive;
      [exact Hheap_wf|by eapply writeAllowed_nonO|apply withinBounds_true_iff; solve_addr|].
    iDestruct (open_world_interp W C (addr_key W ea) p' (safeC P) ρ with "Hrel Hworld_interp")
      as "(Hworld_interp & Hstate & (%w & WorldRes))";
      [by apply addr_key_live|destruct ρ; auto; contradiction|exact Hρ|].
    iDestruct (WorldRes_acc_forall with "WorldRes") as " [ (>Ha & Hinterp & HmonoP) WorldRes ]".
    iDestruct (addr_key_pointsto with "Ha") as "[Ha Hshare]".

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

    iDestruct (addr_key_pointsto_join with "Ha Hshare") as "Ha".

    iDestruct ("WorldRes" with "[$Ha $Hinterp' $Hmono']") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hrel WorldRes") as "Hworld_interp"; eauto.
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
    ↑Nallocator ⊆ E →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

     {{{ allocator_ctx ∗
           interp W C wsrc
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
    iIntros (Hdecode_wi HEalloc Hcorrect_pc Hpca' ?? φ)
      "(#Halloc & #Hinterp_src & HPC & Hi & Hsrc & Hdst & Hworld_interp)".
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
    assert ( ∃ ρ, std W !! addr_key W ea = Some ρ ∧ ρ ≠ Revoked) as ( ρ & Hρ & Hρ_not_revoked).
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

    iDestruct (world_interp_heap_wf with "Hworld_interp") as %Hheap_wf.
    iDestruct (interp_cap_addr_live W C p g b e a ea with "Hinterp_src") as %Hlive;
      [exact Hheap_wf|by eapply readAllowed_nonO|apply withinBounds_true_iff; solve_addr|].
    iDestruct (open_world_interp W C (addr_key W ea) p' (safeC P) ρ with "Hrel Hworld_interp")
      as "(Hworld_interp & Hstate & (%w & WorldRes))";
      [by apply addr_key_live|destruct ρ; auto; contradiction|exact Hρ|].
    iDestruct (WorldRes_acc with "WorldRes") as "[ (>Ha & Hinterp) WorldRes ]".
    iDestruct (addr_key_pointsto with "Ha") as "[Ha Hshare]".

    iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ ea with "Hinterp_src") as %Hnot_shadow.
    { eapply readAllowed_nonO; eauto. }
    { apply withinBounds_true_iff; solve_addr. }
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%Hpc_src & %Hpc_dst & %Hsrc_dst)]".
    iDestruct (memMap_resource_2ne_apply with "Hi Ha") as "[Hmem %Hpc_a]".
    iInv Nallocator as "> Halloc_body" "Halloc_close".
    iDestruct "Halloc_body" as (alloc_map R Halloc_dom Hcoh) "[Halloc_entries HR]".
    iEval (rewrite /allocator_entry big_sepM_sep) in "Halloc_entries".
    iDestruct "Halloc_entries" as "[Hshadow Halloc_states]".
    iAssert ([∗ map] k↦status ∈ shadow_status <$> alloc_map, k ↦ₛ status)%I
      with "[Hshadow]" as "Hshadow".
    { rewrite big_sepM_fmap. iExact "Hshadow". }
    (* Load rdst rsrc imm. *)
    iApply (wp_load_memory_shadow_imm (E ∖ ↑Nallocator)
      pc_p pc_g pc_b pc_e pc_a rdst rsrc imm wi
      (<[pc_a:=wi]> (<[ea:=w]> ∅))
      (<[PC:=WCap true pc_p pc_g pc_b pc_e pc_a]>
        (<[rsrc:=WCap true p g b e a]> (<[rdst:=wdst]> ∅)))
      (DfracOwn 1) (shadow_status <$> alloc_map) (DfracOwn 1)
      with "[Hmem Hshadow Hmap]"); eauto.
    { by simplify_map_eq. }
    { by rewrite !dom_insert; set_solver+. }
    { by rewrite lookup_insert_eq. }
    { exists true, p, g, b, e, a. split.
      - unfold read_reg_inr. by simplify_map_eq.
      - rewrite /reg_allows_load_imm Hea.
        case_decide; last done. exists w. by simplify_map_eq. }
    { intros p0 g0 b0 e0 a0 ea0 (Hsrc0 & Haddr & _).
      simpl_map_regs by eauto. simplify_map_eq. exact Hnot_shadow. }
    { iFrame "Hmem". iSplitL "Hshadow"; first (iNext; iExact "Hshadow").
      iNext. iExact "Hmap". }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hshadow & Hmap)".
    iAssert ([∗ map] k↦s ∈ alloc_map, allocator_entry k s)%I
      with "[Hshadow Halloc_states]" as "Halloc_entries".
    { rewrite /allocator_entry big_sepM_sep big_sepM_fmap. iFrame. }
    destruct retv; simpl in Hspec; [contradiction| |]; cycle 1.
    - destruct Hspec as
        (p0 & g0 & b0 & e0 & a0 & ea0 & loadv & actualv &
         Hallow & Hlookup & Hactual & Hobserved & Hinc).
      destruct Hallow as (Hsrc0 & Haddr & _). simpl_map_regs by eauto.
      rewrite lookup_insert_ne in Hsrc0; last congruence.
      rewrite lookup_insert decide_True in Hsrc0; last done.
      injection Hsrc0 as <- <- <- <- <-.
      rewrite Hea in Haddr. injection Haddr as <-.
      rewrite lookup_insert_ne in Hlookup; last congruence.
      rewrite lookup_insert decide_True in Hlookup; last done.
      injection Hlookup as ->.
      pose proof (Hpers (W, C, loadv)).
      iDestruct "Hinterp" as "#HφV /=".
      iDestruct ("Hwcond" with "HφV") as "#Hnormal_p'".
      iAssert (interp_in_mem p W C loadv)%I as "#Hnormal".
      { rewrite interp_in_mem_eq filter_heap_load_word.
        iApply (interp_weakening_word_load W C p p' (filter_heap W loadv));
          first exact Hflows.
        iEval (rewrite /interp_in_mem_pre filter_heap_load_word)
          in "Hnormal_p'".
        iExact "Hnormal_p'". }
      iDestruct (interp_in_mem_shadow_result W C (addr_key W ea) p loadv actualv alloc_map R
        with "Hworld_interp HR Hnormal")
        as "(#Hload_interp & Hworld_interp & HR)";
        [exact Halloc_dom|exact Hcoh|exact Hobserved|].
      iMod ("Halloc_close" with "[Halloc_entries HR]") as "_".
      { iNext. iExists alloc_map, R. by iFrame "∗%". }
      iModIntro.
      unfold incrementPC, incrementPC_gen in Hinc. simplify_map_eq.
      rewrite (insert_insert_ne _ rdst PC) // insert_insert_eq.
      rewrite (insert_insert_ne _ rdst rsrc) // insert_insert_eq.
      iDestruct (regs_of_map_3 with "Hmap") as "(HPC & Hsrc & Hdst)"; eauto.
      iDestruct (memMap_resource_2ne with "Hmem") as "[Hi Ha]"; auto.
      iDestruct (addr_key_pointsto_join with "Ha Hshare") as "Ha".
      iDestruct ("WorldRes" with "[$Ha $HφV]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hrel WorldRes")
        as "Hworld_interp"; eauto.
      { destruct ρ; auto; contradiction. }
      iApply "Hφ"; iRight. iExists p, g, b, e, a, ea, actualv. iFrame "∗%".
      iSplit; first done.
      iSplit; first done.
      iSplit; last solve_addr.
      iExact "Hload_interp".
    - iMod ("Halloc_close" with "[Halloc_entries HR]") as "_".
      { iNext. iExists alloc_map, R. by iFrame "∗%". }
      iModIntro. iApply "Hφ". by iLeft.

  Qed.

  Lemma wp_load_interp_cap_imm (E : coPset) (imm : Z) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr)
    (wi wdst : Word)
    :
    decodeInstrW wi = Load rdst rsrc imm →
    ↑Nallocator ⊆ E →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

     {{{ allocator_ctx ∗
           interp W C (WCap true p g b e a)
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
    iIntros (Hdecode_wi HEalloc Hcorrect_pc Hpca' ?? φ)
      "(#Halloc & #Hinterp_src & HPC & Hi & Hsrc & Hdst & Hworld_interp)".
    iIntros "Hφ".
    iApply (wp_load_interp_imm with "[-Hφ]");eauto;[iFrame "∗ #"|].
    iNext. iIntros (ret) "Hpost". iApply "Hφ".
    iDestruct "Hpost" as "[Hfail | Hsuccess]"; first (iLeft; done).
    iDestruct "Hsuccess" as (p0 g0 b0 e0 a0 ea wload) "(%Heq & Hrest)".
    simplify_eq. iRight. iExists ea, wload. iExact "Hrest".
  Qed.

  (** World Quarantined ⇒ shadow Quarantined, from [reg_auth] agreement and
      the one-way coherence clause of the allocator invariant. *)
  Lemma shadow_read_retained W C raw actual alloc_map R :
    dom alloc_map = heap_addresses →
    allocator_registry_coherent R alloc_map →
    load_memory_shadow_observation (shadow_status <$> alloc_map) RW raw actual →
    region W C -∗
    reg_auth R -∗
    ⌜filter_heap W actual = actual⌝ ∗
    region W C ∗
    reg_auth R.
  Proof.
    iIntros (Hdom Hcoh Hobs) "Hregion HR".
    iDestruct (region_heap_provenance with "Hregion") as "[Hregion #Hprov]".
    destruct (heap_cap_base raw) as [base|] eqn:Hbase; cycle 1.
    { rewrite /load_memory_shadow_observation Hbase in Hobs. subst actual.
      assert (heap_authority_base raw = None) as Hauth.
      { destruct (heap_authority_base raw) as [base'|] eqn:Hauth; last done.
        apply heap_authority_base_heap_cap_base in Hauth.
        rewrite Hbase in Hauth. discriminate. }
      iFrame. iPureIntro. by apply filter_heap_nonheap. }
    assert (is_heap_address base = true) as Hheap.
    { unfold heap_cap_base in Hbase.
      destruct (memory_cap_base raw) as [b|] eqn:Hmemory; last discriminate.
      destruct (is_heap_address b) eqn:Hheap; last discriminate.
      by simplify_eq. }
    assert (is_Some (alloc_map !! base)) as [s Hlookup].
    { apply elem_of_dom. rewrite Hdom elem_of_heap_addresses. exact Hheap. }
    rewrite /load_memory_shadow_observation Hbase in Hobs.
    specialize (Hobs (shadow_status s)).
    assert ((shadow_status <$> alloc_map) !! base = Some (shadow_status s))
      as Hshadow_lookup by (rewrite lookup_fmap Hlookup; reflexivity).
    specialize (Hobs Hshadow_lookup).
    destruct s; last first.
    { simpl in Hobs. subst actual.
      iFrame. iPureIntro. apply filter_heap_untagged, get_tag_clear_tag. }
    all: simpl in Hobs; subst actual.
    all: destruct (heap_authority_base raw) as [b|] eqn:Hauth; last first.
    all: try (iFrame; iPureIntro; by apply filter_heap_nonheap).
    all: pose proof (heap_authority_base_heap_cap_base raw b Hauth) as Hcap.
    all: rewrite Hbase in Hcap; inversion Hcap; subst b.
    all: destruct (heap_lookup_addr (heap_std W) base) as [bo|] eqn:Hheaplookup;
      last (iFrame; iPureIntro; by rewrite /filter_heap Hauth Hheaplookup).
    all: destruct bo as [ι obj]; destruct (alloc_object_status obj) eqn:Hstatus.
    all: try (iFrame; iPureIntro; by rewrite /filter_heap Hauth Hheaplookup /= Hstatus).
    all: apply heap_lookup_addr_sound in Hheaplookup as [Hι Hcontains].
    all: iDestruct (heap_provenance_quarantined with "Hprov") as "#Hq"; [done|done|].
    all: iDestruct (heap_provenance_alloc_obj with "Hprov") as "#Hobj"; first done.
    all: iDestruct (allocator_registry_quarantined with "HR Hq Hobj") as %Hq;
      [done|exact Hcontains|].
    all: congruence.
  Qed.

  Lemma load_read_retained_imm W C
    pc_b pc_e pc_a p e a raw w0 (imm : Z) :
    disjoint_from_shadow p e ->
    is_heap_cap raw = true ->
    (p + imm)%a = Some a ->
    withinBounds p e a = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ 1)%a ->
    (allocator_ctx ∗
     PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a ∗
     cgp ↦ᵣ WCap true RW Global p e p ∗ ca0 ↦ᵣ w0 ∗
     a ↦ₐ raw ∗ codefrag pc_a [encodeInstrW (Load ca0 cgp imm)] ∗
     region W C ∗
     ▷ (∀ actual,
       ⌜load_heap_in_world W raw actual⌝ -∗
       PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ 1)%a ∗
       cgp ↦ᵣ WCap true RW Global p e p ∗ ca0 ↦ᵣ actual ∗
       a ↦ₐ raw ∗ codefrag pc_a [encodeInstrW (Load ca0 cgp imm)] ∗
       region W C -∗
       WP Seq (Instr Executable)
         {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
     ⊢ WP Seq (Instr Executable)
         {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    iIntros (Hshadow Hheap_raw Hea Hbounds Hsub)
      "(#Halloc & HPC & Hcgp & Hca0 & Ha & Hcode & Hregion & Hpost)".
    codefrag_facts "Hcode". clear H0.
    (* Load ca0 cgp imm. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iDestruct (map_of_regs_3 with "HPC Hcgp Hca0")
      as "[Hmap (%Hpc_cgp & %Hpc_ca0 & %Hcgp_ca0)]".
    iDestruct (memMap_resource_2ne_apply with "Hi Ha")
      as "[Hmem %Hpc_a]".
    iInv Nallocator as ">Halloc_body" "Halloc_close".
    iDestruct "Halloc_body" as (alloc_map R Halloc_dom Hcoh) "[Halloc_entries HR]".
    iEval (rewrite /allocator_entry big_sepM_sep) in "Halloc_entries".
    iDestruct "Halloc_entries" as "[Hshadow Halloc_states]".
    iAssert ([∗ map] k↦status ∈ shadow_status <$> alloc_map,
      k ↦ₛ status)%I with "[Hshadow]" as "Hshadow".
    { rewrite big_sepM_fmap. iExact "Hshadow". }
    iApply (wp_load_memory_shadow_imm (⊤ ∖ ↑Nallocator)
      RX Global pc_b pc_e pc_a ca0 cgp imm
      (encodeInstrW (Load ca0 cgp imm))
      (<[pc_a:=encodeInstrW (Load ca0 cgp imm)]> (<[a:=raw]> ∅))
      (<[PC:=WCap true RX Global pc_b pc_e pc_a]>
        (<[cgp:=WCap true RW Global p e p]> (<[ca0:=w0]> ∅)))
      (DfracOwn 1) (shadow_status <$> alloc_map) (DfracOwn 1)
      with "[Hmem Hshadow Hmap]").
    { rewrite decode_encode_instrW_inv. reflexivity. }
    { solve_pure. }
    { by simplify_map_eq. }
    { by rewrite !dom_insert; set_solver+. }
    { by simplify_map_eq. }
    { exists true, RW, Global, p, e, p. split.
      - unfold read_reg_inr. by simplify_map_eq.
      - rewrite /reg_allows_load_imm Hea.
        case_decide; last done. exists raw. by simplify_map_eq. }
    { intros p0 g0 b0 e0 a0 ea0 (Hsrc0 & Haddr & _).
      simpl_map_regs by eauto. simplify_map_eq.
      eapply disjoint_from_shadow_not_in;
        [exact Hshadow|exact Hbounds]. }
    { iFrame "Hmem". iSplitL "Hshadow"; first (iNext; iExact "Hshadow").
      iNext. iExact "Hmap". }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hshadow & Hmap)".
    iAssert ([∗ map] k↦s ∈ alloc_map, allocator_entry k s)%I
      with "[Hshadow Halloc_states]" as "Halloc_entries".
    { rewrite /allocator_entry big_sepM_sep big_sepM_fmap. iFrame. }
    destruct retv; simpl in Hspec; [contradiction| |]; cycle 1.
    - destruct Hspec as
        (p0 & g0 & b0 & e0 & a0 & ea0 & loadv & actual &
         Hallow & Hlookup & Hactual & Hobserved & Hinc).
      destruct Hallow as (Hsrc0 & Haddr & _).
      simpl_map_regs by eauto.
      rewrite lookup_insert_ne in Hsrc0; last congruence.
      rewrite lookup_insert in Hsrc0. cbn in Hsrc0.
      injection Hsrc0 as <- <- <- <- <-.
      cbn in Haddr.
      rewrite Hea in Haddr. injection Haddr as <-.
      rewrite lookup_insert_ne in Hlookup; last congruence.
      rewrite lookup_insert in Hlookup.
      destruct (decide (a = a)) as [Heq|Hneq] in Hlookup;
        last (exfalso; apply Hneq; reflexivity).
      injection Hlookup as <-.
      change (load_memory_shadow_observation
        (shadow_status <$> alloc_map) RW raw actual) in Hobserved.
      change (actual = raw ∨ actual = clear_tag raw) in Hactual.
      iDestruct (shadow_read_retained W C raw actual alloc_map R
        with "Hregion HR")
        as "(%Hfilter & Hregion & HR)";
        [exact Halloc_dom|exact Hcoh|exact Hobserved|].
      iMod ("Halloc_close" with "[Halloc_entries HR]") as "_".
      { iNext. iExists alloc_map, R. by iFrame "∗%". }
      iModIntro.
      unfold incrementPC, incrementPC_gen in Hinc. simplify_map_eq.
      assert ((pc_a + 1)%a = Some (pc_a ^+ 1)%a) as Hpc by solve_addr.
      rewrite Hpc in Hinc. simplify_eq.
      iEval (rewrite (insert_insert_ne _ ca0 PC) //) in "Hmap".
      iEval (rewrite insert_insert_eq) in "Hmap".
      iEval (rewrite (insert_insert_ne _ cgp ca0) //) in "Hmap".
      iEval (rewrite insert_insert_eq) in "Hmap".
      iDestruct (regs_of_map_3 with "Hmap") as "(HPC & Hca0 & Hcgp)"; eauto.
      iDestruct (memMap_resource_2ne with "Hmem") as "[Hi Ha]"; auto.
      wp_pure.
      iSpecialize ("Hcode" with "Hi").
      iApply ("Hpost" $! actual with "[]"); last iFrame.
      iPureIntro. split; last exact Hfilter.
      destruct Hactual as [Hsame|Hclear].
      + subst actual. left. reflexivity.
      + subst actual. right. split; [exact Hheap_raw|reflexivity].
    - iMod ("Halloc_close" with "[Halloc_entries HR]") as "_".
      { iNext. iExists alloc_map, R. by iFrame "∗%". }
      iModIntro. wp_pure. wp_end. by iIntros (?).
  Qed.

  Lemma load_read_retained E W C
    pc_p pc_g pc_b pc_e pc_a pc_a' dst src wi wd b e a raw :
    ↑Nallocator ⊆ E →
    is_shadow_address a = false →
    decodeInstrW wi = Load dst src 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull → src ≠ cnull →
    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ wd ∗ src ↦ᵣ WCap true RW Global b e a ∗ a ↦ₐ raw ∗
        region W C ∗ allocator_ctx }}}
      Instr Executable @ E
    {{{ actual, RET NextIV;
        ⌜load_heap raw actual ∧ filter_heap W actual = actual⌝ ∗
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ actual ∗ src ↦ᵣ WCap true RW Global b e a ∗
        a ↦ₐ raw ∗ region W C }}}.
  Proof.
    iIntros (HE Hshadow Hinstr Hvpc Hbounds Hpc Hdst Hsrc Φ)
      "(HPC & Hi & Hdst & Hsrc & Ha & Hregion & #Halloc) HΦ".
    destruct (heap_cap_base raw) as [base|] eqn:Hbase.
    - iInv Nallocator as ">Halloc_body" "Halloc_close".
      iDestruct "Halloc_body" as (alloc_map R Halloc_dom Hcoh) "[Halloc_entries HR]".
      assert (is_Some (alloc_map !! base)) as [status Hlookup].
      { apply elem_of_dom. rewrite Halloc_dom elem_of_heap_addresses.
        unfold heap_cap_base in Hbase.
        destruct (memory_cap_base raw) as [base'|] eqn:Hmemory; last discriminate.
        destruct (is_heap_address base') eqn:Hheap; inversion Hbase; subst; done. }
      iDestruct (big_sepM_delete with "Halloc_entries") as "[Hentry Halloc_entries]";
        first exact Hlookup.
      iDestruct "Hentry" as "[Hstatus Hstatus_res]".
      destruct (shadow_status status) eqn:Hstatus_eq.
      + iApply (wp_load_success_heap_word with
          "[$HPC $Hi $Hdst $Hsrc $Ha $Hstatus]"); eauto.
        iNext. iIntros "(HPC & Hdst & Hi & Hsrc & Ha & Hstatus)".
        iAssert ([∗ map] x↦s ∈ alloc_map, allocator_entry x s)%I
          with "[Hstatus Hstatus_res Halloc_entries]" as "Halloc_entries".
        { iApply big_sepM_delete; first exact Hlookup.
          iFrame. rewrite /allocator_entry Hstatus_eq. iFrame. }
        iDestruct (shadow_read_retained W C raw raw alloc_map R
          with "Hregion HR")
          as "(%Hretained & Hregion & HR)";
          [exact Halloc_dom|exact Hcoh| |].
        { unfold load_memory_shadow_observation. rewrite Hbase.
          intros observed Hobserved. rewrite lookup_fmap Hlookup in Hobserved.
          inversion Hobserved; subst. by rewrite Hstatus_eq. }
        iMod ("Halloc_close" with "[Halloc_entries HR]") as "_".
        { iNext. iExists alloc_map, R. by iFrame "∗%". }
        iModIntro. iApply "HΦ". iFrame.
        iPureIntro. split; first by left. exact Hretained.
      + iApply (wp_load_success_heap_word_revoked with
          "[$HPC $Hi $Hdst $Hsrc $Ha $Hstatus]"); eauto.
        iNext. iIntros "(HPC & Hdst & Hi & Hsrc & Ha & Hstatus)".
        iAssert ([∗ map] x↦s ∈ alloc_map, allocator_entry x s)%I
          with "[Hstatus Hstatus_res Halloc_entries]" as "Halloc_entries".
        { iApply big_sepM_delete; first exact Hlookup.
          iFrame. rewrite /allocator_entry Hstatus_eq. iFrame. }
        iDestruct (shadow_read_retained W C raw
          (clear_tag raw) alloc_map R with "Hregion HR")
          as "(%Hretained & Hregion & HR)";
          [exact Halloc_dom|exact Hcoh| |].
        { unfold load_memory_shadow_observation. rewrite Hbase.
          intros observed Hobserved. rewrite lookup_fmap Hlookup in Hobserved.
          inversion Hobserved; subst. by rewrite Hstatus_eq. }
        iMod ("Halloc_close" with "[Halloc_entries HR]") as "_".
        { iNext. iExists alloc_map, R. by iFrame "∗%". }
        iModIntro. iApply "HΦ". iFrame.
        iPureIntro. split; last exact Hretained.
        right. split; last done. unfold is_heap_cap. by rewrite Hbase.
    - iApply (wp_load_success_notinstr with "[$HPC $Hi $Hdst $Hsrc $Ha]"); eauto.
      { unfold is_heap_cap. by rewrite Hbase. }
      iNext. iIntros "(HPC & Hdst & Hi & Hsrc & Ha)".
      iApply "HΦ". iFrame.
      iPureIntro. split; first by left.
      assert (heap_authority_base raw = None) as Hauth.
      { destruct (heap_authority_base raw) as [base'|] eqn:Hauth; last done.
        apply heap_authority_base_heap_cap_base in Hauth.
        rewrite Hbase in Hauth. discriminate. }
      by apply filter_heap_nonheap.
  Qed.

End wp_interp.
