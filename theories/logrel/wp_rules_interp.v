From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Export logrel region_invariants.
From griotte Require Import world_ghost_theory.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Import rules proofmode monotone.
From griotte Require Import map_simpl register_tactics proofmode.

Section wp_interp.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> (leibnizO LWord) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).
  Notation K := (CSTK -n> list WORLD -n> leibnizO (list CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LReg) -n> iPropO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

  Lemma lload_word_RW v : lload_word RW v = v.
  Proof. by destruct v as [ [] ?]. Qed.

  (** Accesses retain the original current address and report their checked
      effective address. *)

  Lemma wp_store_interp_imm {dq : dfrac} (E : coPset) (imm : Z) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wsrc wdst : LWord)
    :
    decodeInstrW wi.(lw) = Store rdst (inr rsrc) imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

     {{{ interp W C wsrc
           ∗ interp W C wdst
           ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rsrc ↦ᵣ[th] wsrc
           ∗ rdst ↦ᵣ[th] wdst
           ∗ world_interp W C
     }}}
       Instr Executable @[th] E
       {{{ retv, RET retv;
           ( ⌜ retv = FaultedV ⌝ ∗
             PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a ∗
             pc_a ↦ₐ{dq} wi ∗
             rsrc ↦ᵣ[th] wsrc ∗
             rdst ↦ᵣ[th] wdst ∗
             world_interp W C ) ∨
          ( ∃ p g b e a π ea,
           ⌜ wdst = WCap true p g b e a @@? π ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rsrc ↦ᵣ[th] wsrc
           ∗ rdst ↦ᵣ[th] WCap true p g b e a @@? π
           ∗ world_interp W C
           ∗ ⌜ writeAllowed p = true ⌝
           ∗ ⌜(a + imm)%a = Some ea⌝
           ∗ ⌜(b <= ea < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' Hsrc_null Hdst_null φ)
      "(#Hinterp_src & #Hinterp_dst & HPC & Hi & Hsrc & Hdst & Hworld_interp)".
    iIntros "Hφ".
    destruct wdst as [wdst π].
    destruct (is_cap wdst) eqn:Hcap;cycle 1.
    {
      iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %Hne]".
      iApply (wp_store_fail_not_cap_imm _ _ _ _ _ _ _ _ _ _ _ _ (wdst @@? π) with "[$HPC $Hi $Hmap]"); eauto.
      { rewrite llookup_reg_not_cnull //. by simplify_map_eq. }
      iNext; iIntros "(HPC & Hi & Hmap)".
      iDestruct (regs_of_map_2 with "Hmap") as "[Hsrc Hdst]"; first done.
      iApply "Hφ". iLeft. by iFrame. }
    destruct wdst as [|[tag p g b e a|] | |]; try done.
    destruct tag; cycle 1.
    {
      iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %Hne]".
      iApply (wp_store_fail_tag_imm _ _ _ _ _ _ _ _ _ _ _ _ (WCap false p g b e a @@? π) with "[$HPC $Hi $Hmap]"); eauto.
      { rewrite llookup_reg_not_cnull //. by simplify_map_eq. }
      iNext; iIntros "(HPC & Hi & Hmap)".
      iDestruct (regs_of_map_2 with "Hmap") as "[Hsrc Hdst]"; first done.
      iApply "Hφ". iLeft. by iFrame.
    }

    destruct (a + imm)%a as [ea|] eqn:Hea; cycle 1.
    {
      iApply (wp_store_fail_reg_overflow_imm with "[$HPC $Hi $Hsrc $Hdst]"); eauto.
      iNext; iIntros "(HPC & Hi & Hsrc & Hdst)".
      iApply "Hφ". iLeft. by iFrame.
    }

    destruct (decide (writeAllowed p = true))%a as [Hp_stk_wa|Hp_stk_wa]; cycle 1.
    {
      iApply (wp_store_fail_reg_perm_imm with "[$HPC $Hi $Hsrc $Hdst]"); eauto.
      { by destruct (writeAllowed p); auto. }
      iNext; iIntros "(HPC & Hi & Hsrc & Hdst)".
      iApply "Hφ". iLeft. by iFrame.
    }
    destruct (decide (b <= ea < e))%a as [Hbounds|Hbounds]; cycle 1.
    {
      iApply (wp_store_fail_reg_imm with "[$HPC $Hi $Hsrc $Hdst]"); eauto.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "(HPC & Hi & Hsrc & Hdst)".
      iApply "Hφ". iLeft. by iFrame.
    }
    assert (withinBounds b e ea = true) as Hwb by (apply withinBounds_true_iff; solve_addr).

    iDestruct (write_allowed_inv _ _ ea with "Hinterp_dst")
      as (p' P Hflows Hpers) "(Hrel & Hzcond & Hwcond & Hrcond & Hmono)";[solve_addr|auto|..].
    iDestruct (writeAllowed_valid_cap_implies_at _ _ _ _ _ _ _ ea with "Hinterp_dst")
      as %(ρ & Hρ & Hρ_not_revoked); [done|done|].
    iDestruct (interp_cap_addr_live _ _ _ _ _ _ _ ea with "Hinterp_dst") as %Hlive;
      [by eapply writeAllowed_nonO|done|].
    iDestruct (open_world_interp W C (addr_key π ea) p' (safeC P) ρ with "Hrel Hworld_interp")
      as "(Hworld_interp & Hstate & (%w & WorldRes))";
      [exact Hlive|destruct ρ; auto; contradiction|exact Hρ|].
    iDestruct (WorldRes_acc_forall with "WorldRes") as " [ (>Ha & Hinterp & HmonoP) WorldRes ]".
    iDestruct (addr_key_pointsto with "Ha") as "[Ha Hshare]".

    iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ ea with "Hinterp_dst") as %Hnot_shadow;
      [by eapply writeAllowed_nonO|done|].
    iDestruct (key_share_deref with "Hshare") as (dw Hdw) "[Hdw Hshare]".
    iEval (rewrite deref_witness_res_deref_res -Hdw) in "Hdw".
    iApply (wp_store_success_reg_store_word_imm with "[$HPC $Hi $Hsrc $Hdst $Ha $Hdw]"); eauto.
    iNext; iIntros "(HPC & Hi & Hsrc & Hdst & Ha & Hdw)".
    iEval (rewrite Hdw -deref_witness_res_deref_res) in "Hdw".
    iDestruct ("Hshare" with "Hdw") as "Hshare".

    iAssert (P W C (lstore_word p wsrc)) as "Hinterp'".
    { iApply "Hwcond". by iApply interp_lstore_word. }
    iAssert (mono_invariant C p' (safeC P) (lstore_word p wsrc) ρ) as "Hmono'".
    {
      rewrite /monoReq Hρ mono_invariant_eq.
      destruct ρ;[simpl..|exfalso;done].
      - destruct (isWL p');auto.
        destruct (isDL p'); first done.
        iApply "Hmono". iPureIntro.
          rewrite lw_lstore_word. by eapply canStore_store_word_flowsto.
      - iApply "Hmono". iPureIntro.
          rewrite lw_lstore_word. by eapply canStore_store_word_flowsto.
    }

    iDestruct (addr_key_pointsto_join with "Ha Hshare") as "Ha".

    iDestruct ("WorldRes" with "[$Ha $Hinterp' $Hmono']") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hrel WorldRes") as "Hworld_interp"; eauto.
    { destruct ρ;auto;contradiction. }

    iApply "Hφ"; iRight. iExists p, g, b, e, a, π, ea. iFrame "∗%".
    iPureIntro. split; first done. solve_addr.
  Qed.

  Lemma wp_store_interp {dq : dfrac} (E : coPset) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wsrc wdst : LWord)
    :
    decodeInstrW wi.(lw) = Store rdst (inr rsrc) 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

     {{{ interp W C wsrc
           ∗ interp W C wdst
           ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rsrc ↦ᵣ[th] wsrc
           ∗ rdst ↦ᵣ[th] wdst
           ∗ world_interp W C
     }}}
       Instr Executable @[th] E
       {{{ retv, RET retv;
           ( ⌜ retv = FaultedV ⌝ ∗
             PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a ∗
             pc_a ↦ₐ{dq} wi ∗
             rsrc ↦ᵣ[th] wsrc ∗
             rdst ↦ᵣ[th] wdst ∗
             world_interp W C ) ∨
          ( ∃ p g b e a π,
           ⌜ wdst = WCap true p g b e a @@? π ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rsrc ↦ᵣ[th] wsrc
           ∗ rdst ↦ᵣ[th] WCap true p g b e a @@? π
           ∗ world_interp W C
           ∗ ⌜ writeAllowed p = true ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ?? φ) "Hpre Hφ".
    iApply (wp_store_interp_imm with "Hpre"); eauto.
    iNext. iIntros (ret) "[Hfail | Hsucc]"; iApply "Hφ"; first (iLeft; iExact "Hfail").
    iRight.
    iDestruct "Hsucc" as (p g b e a π ea) "(? & ? & ? & ? & ? & ? & ? & ? & %Hea & %Hb)".
    rewrite addr_add_0 in Hea. injection Hea as <-.
    iExists p, g, b, e, a, π. by iFrame.
  Qed.

  Lemma wp_store_interp_cap_imm {dq : dfrac} (E : coPset) (imm : Z) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId)
    (wi wsrc : LWord)
    :
    decodeInstrW wi.(lw) = Store rdst (inr rsrc) imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

     {{{ interp W C wsrc
           ∗ interp W C (WCap true p g b e a @@? π)
           ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rsrc ↦ᵣ[th] wsrc
           ∗ rdst ↦ᵣ[th] (WCap true p g b e a @@? π)
           ∗ world_interp W C
     }}}
       Instr Executable @[th] E
       {{{ retv, RET retv;
           ( ⌜ retv = FaultedV ⌝ ∗
             PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a ∗
             pc_a ↦ₐ{dq} wi ∗
             rsrc ↦ᵣ[th] wsrc ∗
             rdst ↦ᵣ[th] WCap true p g b e a @@? π ∗
             world_interp W C ) ∨
          (∃ ea, ⌜ retv = NextIV ⌝
           ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rsrc ↦ᵣ[th] wsrc
           ∗ rdst ↦ᵣ[th] WCap true p g b e a @@? π
           ∗ world_interp W C
           ∗ ⌜ writeAllowed p = true ⌝
           ∗ ⌜(a + imm)%a = Some ea⌝
           ∗ ⌜(b <= ea < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ? ? φ) "Hpre Hφ".
    iApply (wp_store_interp_imm with "Hpre");eauto.
    iNext. iIntros (ret) "Hpost". iApply "Hφ".
    iDestruct "Hpost" as "[Hfail | Hsuccess]"; first (iLeft; iExact "Hfail").
    iDestruct "Hsuccess" as (p0 g0 b0 e0 a0 π0 ea) "(%Heq & Hrest)".
    simplify_eq. iRight. iExists ea. iExact "Hrest".
  Qed.

  Lemma wp_store_interp_cap {dq : dfrac} (E : coPset) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId)
    (wi wsrc : LWord)
    :
    decodeInstrW wi.(lw) = Store rdst (inr rsrc) 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

     {{{ interp W C wsrc
           ∗ interp W C (WCap true p g b e a @@? π)
           ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rsrc ↦ᵣ[th] wsrc
           ∗ rdst ↦ᵣ[th] (WCap true p g b e a @@? π)
           ∗ world_interp W C
     }}}
       Instr Executable @[th] E
       {{{ retv, RET retv;
           ( ⌜ retv = FaultedV ⌝ ∗
             PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a ∗
             pc_a ↦ₐ{dq} wi ∗
             rsrc ↦ᵣ[th] wsrc ∗
             rdst ↦ᵣ[th] WCap true p g b e a @@? π ∗
             world_interp W C ) ∨
          (⌜ retv = NextIV ⌝
           ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rsrc ↦ᵣ[th] wsrc
           ∗ rdst ↦ᵣ[th] WCap true p g b e a @@? π
           ∗ world_interp W C
           ∗ ⌜ writeAllowed p = true ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ? ? φ) "Hpre Hφ".
    iApply (wp_store_interp_cap_imm with "Hpre");eauto.
    iNext. iIntros (ret) "[Hfail | Hsucc]"; iApply "Hφ"; first (iLeft; iExact "Hfail").
    iRight.
    iDestruct "Hsucc" as (ea) "(? & ? & ? & ? & ? & ? & ? & %Hea & %Hb)".
    rewrite addr_add_0 in Hea. injection Hea as <-. by iFrame.
  Qed.

  Lemma wp_store_interp_z_imm {dq : dfrac} (E : coPset) (imm : Z) (W : WORLD) (C : CmptName) (rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wdst : LWord) (z : Z)
    :
    decodeInstrW wi.(lw) = Store rdst (inl z) imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rdst ≠ cnull ->

     {{{ interp W C wdst
           ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rdst ↦ᵣ[th] wdst
           ∗ world_interp W C
     }}}
       Instr Executable @[th] E
       {{{ retv, RET retv;
           ( ⌜ retv = FaultedV ⌝ ∗
             PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a ∗
             pc_a ↦ₐ{dq} wi ∗
             rdst ↦ᵣ[th] wdst ∗
             world_interp W C ) ∨
          ( ∃ p g b e a π ea,
           ⌜ wdst = WCap true p g b e a @@? π ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rdst ↦ᵣ[th] WCap true p g b e a @@? π
           ∗ world_interp W C
           ∗ ⌜ writeAllowed p ⌝
           ∗ ⌜(a + imm)%a = Some ea⌝
           ∗ ⌜(b <= ea < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' Hdst_null φ)
      "(#Hinterp_dst & HPC & Hi & Hdst & Hworld_interp)".
    iIntros "Hφ".
    destruct wdst as [wdst π].
    destruct (is_cap wdst) eqn:Hcap;cycle 1.
    {
      iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
      iApply (wp_store_fail_not_cap_imm _ _ _ _ _ _ _ _ _ _ _ _ (wdst @@? π) with "[$HPC $Hi $Hmap]"); eauto.
      { rewrite llookup_reg_not_cnull //. by simplify_map_eq. }
      iNext; iIntros "(HPC & Hi & Hmap)".
      iDestruct (regs_of_map_1 with "Hmap") as "Hdst".
      iApply "Hφ". iLeft. by iFrame. }
    destruct wdst as [|[tag p g b e a|] | |]; try done.
    destruct tag; cycle 1.
    {
      iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
      iApply (wp_store_fail_tag_imm _ _ _ _ _ _ _ _ _ _ _ _ (WCap false p g b e a @@? π) with "[$HPC $Hi $Hmap]"); eauto.
      { rewrite llookup_reg_not_cnull //. by simplify_map_eq. }
      iNext; iIntros "(HPC & Hi & Hmap)".
      iDestruct (regs_of_map_1 with "Hmap") as "Hdst".
      iApply "Hφ". iLeft. by iFrame.
    }

    destruct (a + imm)%a as [ea|] eqn:Hea; cycle 1.
    {
      iApply (wp_store_fail_z_overflow_imm with "[$HPC $Hi $Hdst]"); eauto.
      iNext; iIntros "(HPC & Hi & Hdst)".
      iApply "Hφ". iLeft. by iFrame.
    }

    destruct (decide (writeAllowed p = true))%a as [Hstore_src|Hstore_src]; cycle 1.
    {
      iApply (wp_store_fail_z_perm_imm with "[$HPC $Hi $Hdst]"); eauto.
      { by destruct ( writeAllowed p ); auto. }
      iNext; iIntros "(HPC & Hi & Hdst)".
      iApply "Hφ". iLeft. by iFrame.
    }
    destruct (decide (b <= ea < e))%a as [Hbounds|Hbounds]; cycle 1.
    {
      iApply (wp_store_fail_z_imm with "[$HPC $Hi $Hdst]"); eauto.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "(HPC & Hi & Hdst)".
      iApply "Hφ". iLeft. by iFrame.
    }
    assert (withinBounds b e ea = true) as Hwb by (apply withinBounds_true_iff; solve_addr).

    iDestruct (write_allowed_inv _ _ ea with "Hinterp_dst")
      as (p' P Hflows Hpers) "(Hrel & Hzcond & Hwcond & Hrcond & Hmono)";[solve_addr|auto|..].
    iDestruct (writeAllowed_valid_cap_implies_at _ _ _ _ _ _ _ ea with "Hinterp_dst")
      as %(ρ & Hρ & Hρ_not_revoked); [done|done|].
    iDestruct (interp_cap_addr_live _ _ _ _ _ _ _ ea with "Hinterp_dst") as %Hlive;
      [by eapply writeAllowed_nonO|done|].
    iDestruct (open_world_interp W C (addr_key π ea) p' (safeC P) ρ with "Hrel Hworld_interp")
      as "(Hworld_interp & Hstate & (%w & WorldRes))";
      [exact Hlive|destruct ρ; auto; contradiction|exact Hρ|].
    iDestruct (WorldRes_acc_forall with "WorldRes") as " [ (>Ha & Hinterp & HmonoP) WorldRes ]".
    iDestruct (addr_key_pointsto with "Ha") as "[Ha Hshare]".

    iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ ea with "Hinterp_dst") as %Hnot_shadow;
      [by eapply writeAllowed_nonO|done|].
    iDestruct (key_share_deref with "Hshare") as (dw Hdw) "[Hdw Hshare]".
    iEval (rewrite deref_witness_res_deref_res -Hdw) in "Hdw".
    iApply (wp_store_success_z_imm with "[$HPC $Hi $Hdst $Ha $Hdw]"); eauto.
    iNext; iIntros "(HPC & Hi & Hdst & Ha & Hdw)".
    iEval (rewrite Hdw -deref_witness_res_deref_res) in "Hdw".
    iDestruct ("Hshare" with "Hdw") as "Hshare".

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

    iApply "Hφ"; iRight. iExists p, g, b, e, a, π, ea. iFrame "∗%".
    iPureIntro. split; first done. solve_addr.
  Qed.

  Lemma wp_store_interp_z {dq : dfrac} (E : coPset) (W : WORLD) (C : CmptName) (rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wdst : LWord) (z : Z)
    :
    decodeInstrW wi.(lw) = Store rdst (inl z) 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rdst ≠ cnull ->

     {{{ interp W C wdst
           ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rdst ↦ᵣ[th] wdst
           ∗ world_interp W C
     }}}
       Instr Executable @[th] E
       {{{ retv, RET retv;
           ( ⌜ retv = FaultedV ⌝ ∗
             PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a ∗
             pc_a ↦ₐ{dq} wi ∗
             rdst ↦ᵣ[th] wdst ∗
             world_interp W C ) ∨
          ( ∃ p g b e a π,
           ⌜ wdst = WCap true p g b e a @@? π ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rdst ↦ᵣ[th] WCap true p g b e a @@? π
           ∗ world_interp W C
           ∗ ⌜ writeAllowed p ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ? φ) "Hpre Hφ".
    iApply (wp_store_interp_z_imm with "Hpre"); eauto.
    iNext. iIntros (ret) "[Hfail | Hsucc]"; iApply "Hφ"; first (iLeft; iExact "Hfail").
    iRight.
    iDestruct "Hsucc" as (p g b e a π ea) "(? & ? & ? & ? & ? & ? & ? & %Hea & %Hb)".
    rewrite addr_add_0 in Hea. injection Hea as <-.
    iExists p, g, b, e, a, π. by iFrame.
  Qed.

  Lemma wp_store_interp_z_cap_imm {dq : dfrac} (E : coPset) (imm : Z) (W : WORLD) (C : CmptName) (rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId)
    (wi : LWord) (z : Z)
    :
    decodeInstrW wi.(lw) = Store rdst (inl z) imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rdst ≠ cnull ->

     {{{  interp W C (WCap true p g b e a @@? π)
           ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rdst ↦ᵣ[th] (WCap true p g b e a @@? π)
           ∗ world_interp W C
     }}}
       Instr Executable @[th] E
       {{{ retv, RET retv;
           ( ⌜ retv = FaultedV ⌝ ∗
             PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a ∗
             pc_a ↦ₐ{dq} wi ∗
             rdst ↦ᵣ[th] WCap true p g b e a @@? π ∗
             world_interp W C ) ∨
          (∃ ea, ⌜ retv = NextIV ⌝
           ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rdst ↦ᵣ[th] WCap true p g b e a @@? π
           ∗ world_interp W C
           ∗ ⌜ writeAllowed p ⌝
           ∗ ⌜(a + imm)%a = Some ea⌝
           ∗ ⌜(b <= ea < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ? φ) "Hpre Hφ".
    iApply (wp_store_interp_z_imm with "Hpre");eauto.
    iNext. iIntros (ret) "Hpost". iApply "Hφ".
    iDestruct "Hpost" as "[Hfail | Hsuccess]"; first (iLeft; iExact "Hfail").
    iDestruct "Hsuccess" as (p0 g0 b0 e0 a0 π0 ea) "(%Heq & Hrest)".
    simplify_eq. iRight. iExists ea. iExact "Hrest".
  Qed.

  Lemma wp_store_interp_z_cap {dq : dfrac} (E : coPset) (W : WORLD) (C : CmptName) (rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId)
    (wi : LWord) (z : Z)
    :
    decodeInstrW wi.(lw) = Store rdst (inl z) 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rdst ≠ cnull ->

     {{{  interp W C (WCap true p g b e a @@? π)
           ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rdst ↦ᵣ[th] (WCap true p g b e a @@? π)
           ∗ world_interp W C
     }}}
       Instr Executable @[th] E
       {{{ retv, RET retv;
           ( ⌜ retv = FaultedV ⌝ ∗
             PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a ∗
             pc_a ↦ₐ{dq} wi ∗
             rdst ↦ᵣ[th] WCap true p g b e a @@? π ∗
             world_interp W C ) ∨
          (⌜ retv = NextIV ⌝
           ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rdst ↦ᵣ[th] WCap true p g b e a @@? π
           ∗ world_interp W C
           ∗ ⌜ writeAllowed p ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ? φ) "Hpre Hφ".
    iApply (wp_store_interp_z_cap_imm with "Hpre");eauto.
    iNext. iIntros (ret) "[Hfail | Hsucc]"; iApply "Hφ"; first (iLeft; iExact "Hfail").
    iRight.
    iDestruct "Hsucc" as (ea) "(? & ? & ? & ? & ? & ? & %Hea & %Hb)".
    rewrite addr_add_0 in Hea. injection Hea as <-. by iFrame.
  Qed.

  (** The stores of words [ws], safe in the world, through a safe
      capability with write permission, from its cursor: each store below
      the end opens the cell in the world and closes it with the stored
      word. The world is the destination at every step. *)
  Lemma world_interp_cells_store_acc (W : WORLD) (C : CmptName)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId) (ws : list LWord) :
    writeAllowed p = true →
    (b <= a)%a →
    interp W C (WCap true p g b e a @@? π) -∗
    ([∗ list] v ∈ ws, interp W C v) -∗
    cells_store_acc (λ _, world_interp W C) p e a π ws.
  Proof.
    iIntros (Hwa Hb) "#Hinterp_dst #Hws".
    iIntros "!>" (i Hi Hie) "Hworld_interp".
    set (ea := (a ^+ i)%a).
    assert (b <= ea < e)%a as Hbounds by (subst ea; solve_addr).
    assert (withinBounds b e ea = true) as Hwb by (apply withinBounds_true_iff; solve_addr).
    iDestruct (write_allowed_inv _ _ ea with "Hinterp_dst")
      as (p' P Hflows Hpers) "(Hrel & _ & Hwcond & _ & Hmono)"; [solve_addr | by rewrite Hwa |].
    iDestruct (writeAllowed_valid_cap_implies_at _ _ _ _ _ _ _ ea with "Hinterp_dst")
      as %(ρ & Hρ & Hρ_not_revoked); [done | done |].
    iDestruct (interp_cap_addr_live _ _ _ _ _ _ _ ea with "Hinterp_dst") as %Hlive;
      [by eapply writeAllowed_nonO | done |].
    iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ ea with "Hinterp_dst") as %Hnot_shadow;
      [by eapply writeAllowed_nonO | done |].
    iDestruct (open_world_interp W C (addr_key π ea) p' (safeC P) ρ with "Hrel Hworld_interp")
      as "(Hworld_interp & Hstate & (%v & WorldRes))";
      [exact Hlive | destruct ρ; auto; contradiction | exact Hρ |].
    iDestruct (WorldRes_acc_forall with "WorldRes") as "[ (>Ha & _ & _) WorldRes]".
    iDestruct (addr_key_pointsto with "Ha") as "[Ha Hshare]".
    iDestruct (key_share_deref with "Hshare") as (dw Hdw) "[Hdw Hshare]".
    iEval (rewrite deref_witness_res_deref_res -Hdw) in "Hdw".
    iModIntro. iExists v, (deref_share dw). iFrame "Ha Hdw". iSplit; first done.
    iIntros "!> Ha Hdw".
    iEval (rewrite Hdw -deref_witness_res_deref_res) in "Hdw".
    iDestruct ("Hshare" with "Hdw") as "Hshare".
    set (v' := lstore_word p (ws !!! i)).
    iAssert (P W C v') as "Hinterp'".
    { iApply "Hwcond". iApply interp_lstore_word.
      destruct (lookup_lt_is_Some_2 ws i) as [wi Hwi]; first lia.
      rewrite (list_lookup_total_correct _ _ _ Hwi).
      by iApply (big_sepL_lookup with "Hws"). }
    iAssert (mono_invariant C p' (safeC P) v' ρ) as "Hmono'".
    { rewrite /monoReq Hρ mono_invariant_eq.
      destruct ρ; [| | exfalso; done]; simpl.
      - destruct (isWL p'); auto.
        destruct (isDL p'); first done.
        iApply "Hmono". iPureIntro.
        rewrite lw_lstore_word. by eapply canStore_store_word_flowsto.
      - iApply "Hmono". iPureIntro.
        rewrite lw_lstore_word. by eapply canStore_store_word_flowsto. }
    iDestruct (addr_key_pointsto_join with "Ha Hshare") as "Ha".
    iDestruct ("WorldRes" with "[$Ha $Hinterp' $Hmono']") as "WorldRes".
    iModIntro.
    iApply (close_world_interp with "Hworld_interp Hstate Hrel WorldRes");
      first done; destruct ρ; auto; contradiction.
  Qed.

  (** The loads of [n] cells, safe in the world, through a safe capability
      with read permission, from its cursor: each load below the end opens
      the cell in the world, with the status witness of the world's heap
      provenance, and closes it as is. The loaded words are safe. *)
  Lemma world_interp_cells_load_acc (W : WORLD) (C : CmptName)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId) (n : nat) :
    readAllowed p = true →
    (b <= a)%a →
    interp W C (WCap true p g b e a @@? π) -∗
    cells_load_acc (λ _ ls, world_interp W C ∗ [∗ list] v ∈ ls, interp W C v)%I p e a π n.
  Proof.
    iIntros (Hra Hb) "#Hinterp_src".
    iIntros "!>" (i ls Hi Hie) "[Hworld_interp #Hls]".
    set (ea := (a ^+ i)%a).
    assert (b <= ea < e)%a as Hbounds by (subst ea; solve_addr).
    assert (withinBounds b e ea = true) as Hwb by (apply withinBounds_true_iff; solve_addr).
    iDestruct (read_allowed_inv _ _ ea with "Hinterp_src")
      as (p' P Hflows Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & Hmono)"; [solve_addr | auto |].
    iDestruct (readAllowed_valid_cap_implies _ _ _ _ _ _ _ ea with "Hinterp_src")
      as %(ρ & Hρ & Hρ_not_revoked); [done | done |].
    iDestruct (interp_cap_addr_live _ _ _ _ _ _ _ ea with "Hinterp_src") as %Hlive;
      [by eapply readAllowed_nonO | done |].
    iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ ea with "Hinterp_src") as %Hnot_shadow;
      [by eapply readAllowed_nonO | done |].
    iDestruct (open_world_interp W C (addr_key π ea) p' (safeC P) ρ with "Hrel Hworld_interp")
      as "(Hworld_interp & Hstate & (%v & WorldRes))";
      [exact Hlive | destruct ρ; auto; contradiction | exact Hρ |].
    iDestruct (WorldRes_acc with "WorldRes") as "[ (>Ha & Hinterp) WorldRes]".
    iDestruct (addr_key_pointsto with "Ha") as "[Ha Hshare]".
    iDestruct (world_interp_open_heap_provenance with "Hworld_interp")
      as "[Hworld_interp #Hprov]".
    iDestruct (heap_provenance_load_witness W v with "Hprov") as "Hwit".
    iDestruct (key_share_deref with "Hshare") as (dw Hdw) "[Hdw Hshare]".
    iModIntro. iExists v, (DfracOwn 1), (load_witness_of W v), dw.
    iFrame "Ha Hwit Hdw". iSplit; first done. iSplit; first done.
    iIntros "!>" (v' Hpost) "Ha _ Hdw".
    iDestruct ("Hshare" with "Hdw") as "Hshare".
    pose proof (Hpers (W, C, v)).
    iDestruct "Hinterp" as "#HφV /=".
    iDestruct ("Hrcond" with "HφV") as "#Hnormal_p'".
    iAssert (interp_in_mem p W C v)%I as "#Hnormal".
    { iEval (rewrite /interp_in_mem /= /interp_in_mem_pre filter_heap_load_word).
      iApply (interp_weakening_word_load W C p p' (filter_heap W v)); first exact Hflows.
      iEval (rewrite /interp_in_mem_pre filter_heap_load_word) in "Hnormal_p'".
      iExact "Hnormal_p'". }
    iDestruct (interp_in_mem_load_post with "Hnormal") as "#Hv'"; first exact Hpost.
    iDestruct (addr_key_pointsto_join with "Ha Hshare") as "Ha".
    iDestruct ("WorldRes" with "[$Ha $HφV]") as "WorldRes".
    iModIntro. iSplitL.
    - iApply (close_world_interp with "Hworld_interp Hstate Hrel WorldRes");
        first done; destruct ρ; auto; contradiction.
    - rewrite big_sepL_app /=. iFrame "Hls Hv'".
  Qed.

  Lemma wp_unseal_unknown {dq : dfrac} E pc_p pc_g pc_b pc_e pc_a pc_a' wi r1 r2 wsealr wsealed  :
    decodeInstrW wi.(lw) = UnSeal r2 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{  PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ pc_a ↦ₐ{dq} wi
          ∗ r1 ↦ᵣ[th] wsealr
          ∗ r2 ↦ᵣ[th] wsealed
    }}}
      Instr Executable @[th] E
      {{{ retv, RET retv;
          (⌜ retv = NextIV ⌝
              ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ{dq} wi
              ∗ r1 ↦ᵣ[th] wsealr
              ∗ r2 ↦ᵣ[th] lclear_tag wsealed
              ∗ ⌜ is_sealr wsealr.(lw) && is_sealed wsealed.(lw) = false ⌝)
          ∨ (∃ psr gsr bsr esr asr πsr ot wsb π,
              ⌜ retv = NextIV ⌝
              ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ{dq} wi
              ∗ r1 ↦ᵣ[th] wsealr
              ∗ r2 ↦ᵣ[th] WSealable (unseal_sb gsr wsb) @@? π
              ∗ ⌜ wsealr = WSealRange true psr gsr bsr esr asr @@? πsr ⌝
              ∗ ⌜ permit_unseal psr = true ⌝
              ∗ ⌜ wsealed = WSealed ot wsb @@? π ⌝
              ∗ ⌜ get_tag_sealable wsb = true ⌝
              ∗ ⌜ withinBounds bsr esr ot = true ⌝ )
          ∨ ∃ tsr psr gsr bsr esr asr πsr ot sb π,
              ⌜ retv = NextIV ⌝
              ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ{dq} wi
              ∗ r1 ↦ᵣ[th] wsealr
              ∗ r2 ↦ᵣ[th] WSealable (clear_tag_sealable (unseal_sb gsr sb)) @@? π
              ∗ ⌜ wsealr = WSealRange tsr psr gsr bsr esr asr @@? πsr ⌝
              ∗ ⌜ wsealed = WSealed ot sb @@? π ⌝
              ∗ ⌜ tsr && get_tag_sealable sb && permit_unseal psr &&
                    withinBounds bsr esr ot = false ⌝
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpc_a' Hr1_null Hr2_null ϕ) "(HPC & Hpc_a & Hr1 & Hr2) Hφ".

    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %]".
    iApply (wp_UnSeal with "[$HPC $Hmap $Hpc_a]"); eauto.
    { by unfold regs_of, operands_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hpc_a & Hmap)".

    destruct Hspec as [p g b e a πs o sb π Hsr Hsd Htag Hperm Hwb Hinc ->
                      |t p g b e a πs o sb π Hsr Hsd Hinvalid Hinc ->
                      | w1 w2 Hw1 Hw2 Hk Hinc -> | Hfail].
    { iApply "Hφ". iRight. iLeft.
      rewrite !llookup_reg_not_cnull // in Hsr Hsd. simplify_map_eq.
      iExists p, g, b, e, a, πs, o, sb, π.
      rewrite (insert_insert_ne _ _ r1) //.
      rewrite !insert_insert_eq.
      iRegsMap "Hmap".
      iFrame; done.
    }
    { iApply "Hφ". iRight. iRight.
      rewrite !llookup_reg_not_cnull // in Hsr Hsd. simplify_map_eq.
      iExists t, p, g, b, e, a, πs, o, sb, π.
      rewrite (insert_insert_ne _ _ r1) //.
      rewrite !insert_insert_eq.
      iRegsMap "Hmap".
      iFrame; done.
    }
    { iApply "Hφ". iLeft.
      rewrite !llookup_reg_not_cnull // in Hw1 Hw2. simplify_map_eq.
      rewrite (insert_insert_ne _ _ r1) //.
      rewrite !insert_insert_eq.
      iRegsMap "Hmap".
      iFrame; done.
    }
    { exfalso. destruct Hfail; try incrementPC_inv; simplify_map_eq; congruence. }
  Qed.

  Lemma wp_unseal_unknown' {dq : dfrac} E pc_p pc_g pc_b pc_e pc_a pc_a' wi r1 r2 wsealr wsealed  :
    decodeInstrW wi.(lw) = UnSeal r1 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{  PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ pc_a ↦ₐ{dq} wi
          ∗ r1 ↦ᵣ[th] wsealr
          ∗ r2 ↦ᵣ[th] wsealed
    }}}
      Instr Executable @[th] E
      {{{ retv, RET retv;
          (⌜ retv = NextIV ⌝
              ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ{dq} wi
              ∗ r1 ↦ᵣ[th] lclear_tag wsealed
              ∗ r2 ↦ᵣ[th] wsealed
              ∗ ⌜ is_sealr wsealr.(lw) && is_sealed wsealed.(lw) = false ⌝)
          ∨ (∃ psr gsr bsr esr asr πsr ot wsb π,
              ⌜ retv = NextIV ⌝
              ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ{dq} wi
              ∗ r1 ↦ᵣ[th] WSealable (unseal_sb gsr wsb) @@? π
              ∗ r2 ↦ᵣ[th] wsealed
              ∗ ⌜ wsealr = WSealRange true psr gsr bsr esr asr @@? πsr ⌝
              ∗ ⌜ permit_unseal psr = true ⌝
              ∗ ⌜ wsealed = WSealed ot wsb @@? π ⌝
              ∗ ⌜ get_tag_sealable wsb = true ⌝
              ∗ ⌜ withinBounds bsr esr ot = true ⌝ )
          ∨ ∃ tsr psr gsr bsr esr asr πsr ot sb π,
              ⌜ retv = NextIV ⌝
              ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ{dq} wi
              ∗ r1 ↦ᵣ[th] WSealable (clear_tag_sealable (unseal_sb gsr sb)) @@? π
              ∗ r2 ↦ᵣ[th] wsealed
              ∗ ⌜ wsealr = WSealRange tsr psr gsr bsr esr asr @@? πsr ⌝
              ∗ ⌜ wsealed = WSealed ot sb @@? π ⌝
              ∗ ⌜ tsr && get_tag_sealable sb && permit_unseal psr &&
                    withinBounds bsr esr ot = false ⌝
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpc_a' Hr1_null Hr2_null ϕ) "(HPC & Hpc_a & Hr1 & Hr2) Hφ".

    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %]".
    iApply (wp_UnSeal with "[$HPC $Hmap $Hpc_a]"); eauto.
    { by unfold regs_of, operands_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hpc_a & Hmap)".

    destruct Hspec as [p g b e a πs o sb π Hsr Hsd Htag Hperm Hwb Hinc ->
                      |t p g b e a πs o sb π Hsr Hsd Hinvalid Hinc ->
                      | w1 w2 Hw1 Hw2 Hk Hinc -> | Hfail].
    { iApply "Hφ". iRight. iLeft.
      rewrite !llookup_reg_not_cnull // in Hsr Hsd. simplify_map_eq.
      iExists p, g, b, e, a, πs, o, sb, π.
      rewrite !insert_insert_eq.
      iRegsMap "Hmap".
      iFrame; done.
    }
    { iApply "Hφ". iRight. iRight.
      rewrite !llookup_reg_not_cnull // in Hsr Hsd. simplify_map_eq.
      iExists t, p, g, b, e, a, πs, o, sb, π.
      rewrite !insert_insert_eq.
      iRegsMap "Hmap".
      iFrame; done.
    }
    { iApply "Hφ". iLeft.
      rewrite !llookup_reg_not_cnull // in Hw1 Hw2. simplify_map_eq.
      rewrite !insert_insert_eq.
      iRegsMap "Hmap".
      iFrame; done.
    }
    { exfalso. destruct Hfail; try incrementPC_inv; simplify_map_eq; congruence. }
  Qed.

  Lemma wp_unseal_unknown_sealed {dq : dfrac} E pc_p pc_g pc_b pc_e pc_a pc_a' wi r1 r2 psr gsr bsr esr asr wsealed  :
    decodeInstrW wi.(lw) = UnSeal r2 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    permit_unseal psr = true ->
    (bsr <= asr < esr)%ot ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{  PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ pc_a ↦ₐ{dq} wi
          ∗ r1 ↦ᵣ[th] WSealRange true psr gsr bsr esr asr
          ∗ r2 ↦ᵣ[th] wsealed
    }}}
      Instr Executable @[th] E
      {{{ retv, RET retv;
          (⌜ retv = NextIV ⌝
              ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ{dq} wi
              ∗ r1 ↦ᵣ[th] WSealRange true psr gsr bsr esr asr
              ∗ r2 ↦ᵣ[th] lclear_tag wsealed
              ∗ ⌜ is_sealed wsealed.(lw) = false ⌝)
          ∨ (∃ ot wsb π,
              ⌜ retv = NextIV ⌝
              ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ{dq} wi
              ∗ r1 ↦ᵣ[th] WSealRange true psr gsr bsr esr asr
              ∗ r2 ↦ᵣ[th] WSealable (unseal_sb gsr wsb) @@? π
              ∗ ⌜ wsealed = WSealed ot wsb @@? π ⌝
              ∗ ⌜ get_tag_sealable wsb = true ⌝
              ∗ ⌜ withinBounds bsr esr ot = true ⌝ )
          ∨ ∃ ot sb π,
              ⌜ retv = NextIV ⌝
              ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ{dq} wi
              ∗ r1 ↦ᵣ[th] WSealRange true psr gsr bsr esr asr
              ∗ r2 ↦ᵣ[th] WSealable (clear_tag_sealable (unseal_sb gsr sb)) @@? π
              ∗ ⌜ wsealed = WSealed ot sb @@? π ⌝
              ∗ ⌜ get_tag_sealable sb && withinBounds bsr esr ot = false ⌝
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpc_a' Hpsr Hsr Hr1_null Hr2_null ϕ) "(HPC & Hpc_a & Hr1 & Hr2) Hφ".

    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %]".
    iApply (wp_UnSeal with "[$HPC $Hmap $Hpc_a]"); eauto.
    { by unfold regs_of, operands_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hpc_a & Hmap)".

    destruct Hspec as [p g b e a πs o sb π Hsr' Hsd Htag Hperm Hwb Hinc ->
                      |t p g b e a πs o sb π Hsr' Hsd Hinvalid Hinc ->
                      | w1 w2 Hw1 Hw2 Hk Hinc -> | Hfail].
    { iApply "Hφ". iRight. iLeft.
      rewrite !llookup_reg_not_cnull // in Hsr' Hsd. simplify_map_eq.
      iExists o, sb, π.
      rewrite (insert_insert_ne _ _ r1) //.
      rewrite !insert_insert_eq.
      iRegsMap "Hmap".
      iFrame; done.
    }
    { iApply "Hφ". iRight. iRight.
      rewrite !llookup_reg_not_cnull // in Hsr' Hsd. simplify_map_eq.
      iExists o, sb, π.
      rewrite (insert_insert_ne _ _ r1) //.
      rewrite !insert_insert_eq.
      iRegsMap "Hmap".
      match goal with Hinvalid : _ && withinBounds _ _ _ = false |- _ =>
        rewrite Hpsr !andb_true_r /= in Hinvalid
      end.
      iFrame; done.
    }
    { iApply "Hφ". iLeft.
      rewrite !llookup_reg_not_cnull // in Hw1 Hw2. simplify_map_eq.
      rewrite (insert_insert_ne _ _ r1) //.
      rewrite !insert_insert_eq.
      iRegsMap "Hmap".
      iFrame; done.
    }
    { exfalso. destruct Hfail; try incrementPC_inv; simplify_map_eq; congruence. }
  Qed.

  (** A load through a valid capability: the world supplies the quarantine
      witness of the loaded word, which makes the loaded word valid. *)
  Lemma wp_load_interp_imm (E : coPset) (imm : Z) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wsrc wdst : LWord)
    :
    decodeInstrW wi.(lw) = CLoad rdst rsrc imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

     {{{ interp W C wsrc
           ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ[th] wsrc
           ∗ rdst ↦ᵣ[th] wdst
           ∗ world_interp W C
     }}}
       Instr Executable @[th] E
       {{{ retv, RET retv;
           ( ⌜ retv = FaultedV ⌝ ∗
             PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a ∗
             pc_a ↦ₐ wi ∗
             rsrc ↦ᵣ[th] wsrc ∗
             rdst ↦ᵣ[th] wdst ∗
             world_interp W C ) ∨
          ( ∃ p g b e a π ea wload,
           ⌜ wsrc = WCap true p g b e a @@? π ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ[th] WCap true p g b e a @@? π
           ∗ rdst ↦ᵣ[th] wload ∗ interp W C wload
           ∗ world_interp W C
           ∗ ⌜ readAllowed p = true ⌝
           ∗ ⌜(a + imm)%a = Some ea⌝
           ∗ ⌜(b <= ea < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' Hsrc_null Hdst_null φ)
      "(#Hinterp_src & HPC & Hi & Hsrc & Hdst & Hworld_interp)".
    iIntros "Hφ".
    destruct wsrc as [wsrc π].
    destruct (is_cap wsrc) eqn:Hcap;cycle 1.
    {
      iApply (wp_load_fail_not_cap_imm _ rdst rsrc with "[$HPC $Hi $Hdst $Hsrc]"); eauto.
      iNext; iIntros "(HPC & Hi & Hdst & Hsrc)".
      iApply "Hφ". iLeft. by iFrame.
    }
    destruct wsrc as [|[tag p g b e a|] | |]; try done.
    destruct tag; cycle 1.
    {
      iDestruct (map_of_regs_2 with "Hdst Hsrc") as "[Hmap %Hne]".
      iApply (wp_load_fail_tag_imm _ _ _ _ _ _ _ _ _ _ _ _ (WCap false p g b e a @@? π) with "[$HPC $Hi $Hmap]"); eauto.
      { rewrite llookup_reg_not_cnull //. by simplify_map_eq. }
      iNext; iIntros "(HPC & Hi & Hmap)".
      iDestruct (regs_of_map_2 with "Hmap") as "[Hdst Hsrc]"; first done.
      iApply "Hφ". iLeft. by iFrame.
    }

    destruct (a + imm)%a as [ea|] eqn:Hea; cycle 1.
    {
      iDestruct (map_of_regs_2 with "Hdst Hsrc") as "[Hmap %Hne]".
      iApply (wp_load_fail_addr_imm _ _ _ _ _ _ _ _ _ _ _ _ (WCap true p g b e a @@? π) with "[$HPC $Hi $Hmap]"); eauto.
      { rewrite llookup_reg_not_cnull //. by simplify_map_eq. }
      iNext; iIntros "(HPC & Hi & Hmap)".
      iDestruct (regs_of_map_2 with "Hmap") as "[Hdst Hsrc]"; first done.
      iApply "Hφ". iLeft. by iFrame.
    }

    destruct (decide (readAllowed p = true))%a as [Hra_src|Hra_src]; cycle 1.
    {
      iApply (wp_load_fail_not_ra_imm _ rdst rsrc with "[$HPC $Hi $Hdst $Hsrc]"); eauto.
      { destruct p as [ [] ? ? ? ]; cbn in * ; done. }
      iNext; iIntros "(HPC & Hi & Hdst & Hsrc)".
      iApply "Hφ". iLeft. by iFrame.
    }
    destruct (decide (b <= ea < e))%a as [Hbounds|Hbounds]; cycle 1.
    {
      iApply (wp_load_fail_not_withinbounds_imm _ rdst rsrc with "[$HPC $Hi $Hdst $Hsrc]"); eauto.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "(HPC & Hi & Hdst & Hsrc)".
      iApply "Hφ". iLeft. by iFrame.
    }
    assert (withinBounds b e ea = true) as Hwb by (apply withinBounds_true_iff; solve_addr).

    iDestruct (read_allowed_inv _ _ ea with "Hinterp_src")
      as (p' P Hflows Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & Hmono)";[solve_addr|auto|..].
    iDestruct (readAllowed_valid_cap_implies _ _ _ _ _ _ _ ea with "Hinterp_src")
      as %(ρ & Hρ & Hρ_not_revoked); [done|done|].
    iDestruct (interp_cap_addr_live _ _ _ _ _ _ _ ea with "Hinterp_src") as %Hlive;
      [by eapply readAllowed_nonO|done|].
    iDestruct (open_world_interp W C (addr_key π ea) p' (safeC P) ρ with "Hrel Hworld_interp")
      as "(Hworld_interp & Hstate & (%w & WorldRes))";
      [exact Hlive|destruct ρ; auto; contradiction|exact Hρ|].
    iDestruct (WorldRes_acc with "WorldRes") as "[ (>Ha & Hinterp) WorldRes ]".
    iDestruct (addr_key_pointsto with "Ha") as "[Ha Hshare]".

    iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ ea with "Hinterp_src") as %Hnot_shadow;
      [by eapply readAllowed_nonO|done|].
    (* The world's heap provenance supplies the status witness. *)
    iDestruct (world_interp_open_heap_provenance with "Hworld_interp") as "[Hworld_interp #Hprov]".
    iDestruct (heap_provenance_load_witness W w with "Hprov") as "Hwit".
    iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %Hsrc_dst]".
    iDestruct (memMap_resource_2ne_apply with "Hi Ha") as "[Hmem %Hpc_a]".
    (* CLoad rdst rsrc imm. *)
    iDestruct (key_share_deref with "Hshare") as (dw Hdw) "[Hdw Hshare]".
    iApply (wp_load_witness_imm with "[$HPC $Hmem $Hwit $Hdw $Hmap]"); eauto.
    { by rewrite !dom_insert; set_solver+. }
    { by rewrite lookup_insert_eq. }
    { intros p0 g0 b0 e0 ea0 Hallow.
      destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)].
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0').
      rewrite lookup_insert_eq in Hsrc0'. injection Hsrc0' as <- <- <- <- <- <-.
      rewrite Hea in Haddr. injection Haddr as <-.
      rewrite Hnot_shadow.
      destruct (is_revoker_address ea); first done.
      eexists. by simplify_map_eq. }
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hmem & _ & Hdw & Hmap)".
    iDestruct ("Hshare" with "Hdw") as "Hshare".
    destruct Hspec as [p0 g0 b0 e0 ea0 loadv loadv' Hallow Hsh Hl Hpost Hinc ->
                      |p0 g0 b0 e0 ea0 heap_a revoked Hallow Hsh
                      |p0 g0 b0 e0 ea0 Hallow Hrev Hl
                      |Hfail -> ->].
    2,3: exfalso;
      destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)];
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0');
      rewrite lookup_insert_eq in Hsrc0'; injection Hsrc0' as <- <- <- <- <- <-;
      rewrite Hea in Haddr; injection Haddr as <-;
      simplify_map_eq; congruence.
    2: { iDestruct (regs_of_map_2 with "Hmap") as "(Hsrc & Hdst)"; first done.
         iDestruct (memMap_resource_2ne with "Hmem") as "[Hi Ha]"; auto.
         iDestruct (addr_key_pointsto_join with "Ha Hshare") as "Ha".
         iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
         iDestruct (close_world_interp with "Hworld_interp Hstate Hrel WorldRes")
           as "Hworld_interp"; eauto.
         { destruct ρ; auto; contradiction. }
         iApply "Hφ". iLeft. by iFrame. }
    destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)].
    destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0').
    rewrite lookup_insert_eq in Hsrc0'. injection Hsrc0' as <- <- <- <- <- <-.
      rewrite Hea in Haddr. injection Haddr as <-.
    rewrite lookup_insert_ne // lookup_insert_eq in Hl. injection Hl as <-.
    pose proof (Hpers (W, C, w)).
    iDestruct "Hinterp" as "#HφV /=".
    iDestruct ("Hrcond" with "HφV") as "#Hnormal_p'".
    iAssert (interp_in_mem p W C w)%I as "#Hnormal".
    { iEval (rewrite /interp_in_mem /= /interp_in_mem_pre filter_heap_load_word).
      iApply (interp_weakening_word_load W C p p' (filter_heap W w)); first exact Hflows.
      iEval (rewrite /interp_in_mem_pre filter_heap_load_word) in "Hnormal_p'".
      iExact "Hnormal_p'". }
    iDestruct (interp_in_mem_load_post with "Hnormal") as "#Hload_interp"; first exact Hpost.
    rewrite linsert_reg_not_cnull //.
    apply incrementPC_Some_inv in Hinc
      as (tpc & ppc & gpc & bpc & epc & apc & apc'' & πpc & HPC & Hapc & ->).
    injection HPC as <- <- <- <- <- <- <-.
    rewrite Hpca' in Hapc. injection Hapc as <-.
    rewrite (insert_insert_ne _ rdst rsrc) // insert_insert_eq.
    iDestruct (regs_of_map_2 with "Hmap") as "(Hsrc & Hdst)"; eauto.
    iDestruct (memMap_resource_2ne with "Hmem") as "[Hi Ha]"; auto.
    iDestruct (addr_key_pointsto_join with "Ha Hshare") as "Ha".
    iDestruct ("WorldRes" with "[$Ha $HφV]") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hrel WorldRes")
      as "Hworld_interp"; eauto.
    { destruct ρ; auto; contradiction. }
    iApply "Hφ"; iRight. iExists p, g, b, e, a, π, ea, loadv'. iFrame "∗#%".
    iPureIntro. split; first done. solve_addr.
  Qed.

  Lemma wp_load_interp (E : coPset) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wsrc wdst : LWord)
    :
    decodeInstrW wi.(lw) = CLoad rdst rsrc 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

     {{{ interp W C wsrc
           ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ[th] wsrc
           ∗ rdst ↦ᵣ[th] wdst
           ∗ world_interp W C
     }}}
       Instr Executable @[th] E
       {{{ retv, RET retv;
           ( ⌜ retv = FaultedV ⌝ ∗
             PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a ∗
             pc_a ↦ₐ wi ∗
             rsrc ↦ᵣ[th] wsrc ∗
             rdst ↦ᵣ[th] wdst ∗
             world_interp W C ) ∨
          ( ∃ p g b e a π wload,
           ⌜ wsrc = WCap true p g b e a @@? π ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ[th] WCap true p g b e a @@? π
           ∗ rdst ↦ᵣ[th] wload ∗ interp W C wload
           ∗ world_interp W C
           ∗ ⌜ readAllowed p = true ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ?? φ) "Hpre Hφ".
    iApply (wp_load_interp_imm with "Hpre"); eauto.
    iNext. iIntros (ret) "[Hfail | Hsucc]"; iApply "Hφ"; first (iLeft; iExact "Hfail").
    iRight.
    iDestruct "Hsucc" as (p g b e a π ea wload)
      "(? & ? & ? & ? & ? & ? & ? & ? & ? & %Hea & %Hb)".
    rewrite addr_add_0 in Hea. injection Hea as <-.
    iExists p, g, b, e, a, π, wload. by iFrame.
  Qed.

  (** The fault cases of [wp_load_interp_same]: the opsem gives the load as
      a fault, and the registers and the memory are unchanged. *)
  #[local] Ltac load_same_fault :=
    iApply (wp_instr_faulted_1 with "[$HPC $Hsrc $Hi]"); [done | done | | ];
    [ intros ? ? ? ? s1 Hrr; rewrite /exec /= /lookup_reg Hrr /= decide_False //;
      destruct s1; cbn; try done
    | iIntros "!> (HPC & Hsrc & Hi)"; iApply "Hφ"; iLeft; by iFrame ].

  (** The key that a load through [w] reads, when it reads, is not in [s]. *)
  Definition load_key_closed (w : LWord) (s : list LAddr) : Prop :=
    ∀ p g b e a, w.(lw) = WCap true p g b e a → withinBounds b e a = true →
      addr_key w.(lprov) a ∉ s.

  (** [wp_load_interp_same] over a world open on [s], when the loaded key
      is not in [s]. *)
  Lemma wp_load_interp_same_open (E : coPset) (W : WORLD) (C : CmptName) (s : list LAddr)
    (r : RegName) (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wsrc : LWord) (dq : dfrac) :
    decodeInstrW wi.(lw) = CLoad r r 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r ≠ cnull →
    load_key_closed wsrc s →
    {{{ interp W C wsrc ∗
        PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a ∗
        pc_a ↦ₐ{dq} wi ∗
        r ↦ᵣ[th] wsrc ∗
        world_interp_open W C s }}}
      Instr Executable @[th] E
    {{{ retv, RET retv;
        ( ⌜retv = FaultedV⌝ ∗
          PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a ∗
          pc_a ↦ₐ{dq} wi ∗
          r ↦ᵣ[th] wsrc ∗
          world_interp_open W C s ) ∨
        ( ∃ wload,
          ⌜retv = NextIV⌝ ∗
          PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a' ∗
          pc_a ↦ₐ{dq} wi ∗
          r ↦ᵣ[th] wload ∗ interp W C wload ∗
          world_interp_open W C s ) }}}.
  Proof.
    iIntros (Hdecode Hcorrect_pc Hpca' Hr Hclosed φ)
      "(#Hinterp_src & HPC & Hi & Hsrc & Hworld_interp) Hφ".
    destruct wsrc as [wsrc π].
    (* The load faults unless [wsrc] is a tagged capability that allows it *)
    destruct wsrc as [z | [ [] p g b e a | ] | | ];
      try (load_same_fault; fail).
    destruct (readAllowed p) eqn:Hra;
      last (load_same_fault; by rewrite addr_add_0 /= Hra).
    destruct (withinBounds b e a) eqn:Hwb;
      last (load_same_fault; by rewrite addr_add_0 /= Hwb andb_false_r).
    apply withinBounds_true_iff in Hwb as Hbounds.
    pose proof (Hclosed p g b e a eq_refl Hwb) as Hnin_s. cbn in Hnin_s.
    (* Open the region of [a], as [wp_load_interp_imm] *)
    iDestruct (read_allowed_inv _ _ a with "Hinterp_src")
      as (p' P Hflows Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & Hmono)"; [solve_addr | auto |..].
    iDestruct (readAllowed_valid_cap_implies _ _ _ _ _ _ _ a with "Hinterp_src")
      as %(ρ & Hρ & Hρ_not_revoked); [done | done |].
    iDestruct (interp_cap_addr_live _ _ _ _ _ _ _ a with "Hinterp_src") as %Hlive;
      [by eapply readAllowed_nonO | done |].
    iDestruct (open_world_interp_next W C s (addr_key π a) p' (safeC P) ρ
                with "Hrel Hworld_interp")
      as "(Hworld_interp & Hstate & (%w & WorldRes))";
      [exact Hlive | exact Hnin_s | destruct ρ; auto; contradiction | exact Hρ |].
    iDestruct (WorldRes_acc with "WorldRes") as "[ (>Ha & Hinterp) WorldRes ]".
    iDestruct (addr_key_pointsto with "Ha") as "[Ha Hshare]".
    iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ a with "Hinterp_src") as %Hnot_shadow;
      [by eapply readAllowed_nonO | done |].
    iDestruct (world_interp_open_heap_provenance with "Hworld_interp") as "[Hworld_interp #Hprov]".
    iDestruct (heap_provenance_load_witness W w with "Hprov") as "Hwit".
    iDestruct (map_of_regs_1 with "Hsrc") as "Hmap".
    iDestruct (memMap_resource_2ne_apply_dq with "Hi Ha") as "[Hmem %Hpc_a]".
    iDestruct (key_share_deref with "Hshare") as (dw Hdw) "[Hdw Hshare]".
    iAssert (▷ ([∗ map] k↦revoked ∈ (∅ : ShadowTbl), k ↦ₛ{DfracDiscarded} revoked))%I
      as "Hshadow".
    { by rewrite big_sepM_empty. }
    iApply (wp_load_general_shadow_imm E pc_p pc_g pc_b pc_e pc_a None r r 0 wi
      (<[pc_a:=wi]> (<[a:=w]> ∅)) _ _ ∅ DfracDiscarded _ dw
      with "[$HPC $Hmem $Hshadow $Hmap $Hwit $Hdw]").
    { exact Hdecode. }
    { exact Hcorrect_pc. }
    { by rewrite !dom_insert; set_solver+. }
    { by simplify_map_eq. }
    { intros p0 g0 b0 e0 ea0 Hallow.
      destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)].
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0').
      rewrite lookup_insert_eq in Hsrc0'. injection Hsrc0' as <- <- <- <- <- <-.
      rewrite addr_add_0 in Haddr. injection Haddr as <-.
      rewrite Hnot_shadow.
      case_match; first done.
      eexists. by simplify_map_eq. }
    { by rewrite !dom_insert_L. }
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hmem & _ & _ & Hdw & Hmap)".
    iDestruct ("Hshare" with "Hdw") as "Hshare".
    destruct Hspec as [p0 g0 b0 e0 ea0 loadv loadv' Hallow Hsh Hl Hpost Hinc ->
                      |p0 g0 b0 e0 ea0 heap_a revoked Hallow Hsh
                      |p0 g0 b0 e0 ea0 Hallow Hrev Hl
                      |Hfail -> ->].
    2,3: exfalso;
      destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)];
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0');
      rewrite lookup_insert_eq in Hsrc0'; injection Hsrc0' as <- <- <- <- <- <-;
      rewrite addr_add_0 in Haddr; injection Haddr as <-;
      simplify_map_eq; congruence.
    2: { iDestruct (regs_of_map_1 with "Hmap") as "Hsrc".
         iDestruct (memMap_resource_2ne_dq with "Hmem") as "[Hi Ha]"; auto.
         iDestruct (addr_key_pointsto_join with "Ha Hshare") as "Ha".
         iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
         iDestruct (close_world_interp_next with "Hworld_interp Hstate Hrel WorldRes")
           as "Hworld_interp"; eauto.
         { destruct ρ; auto; contradiction. }
         iApply "Hφ". iLeft. by iFrame. }
    destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)].
    destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0').
    rewrite lookup_insert_eq in Hsrc0'. injection Hsrc0' as <- <- <- <- <- <-.
    rewrite addr_add_0 in Haddr. injection Haddr as <-.
    rewrite lookup_insert_ne // lookup_insert_eq in Hl. injection Hl as <-.
    pose proof (Hpers (W, C, w)) as Hpers_w.
    iDestruct "Hinterp" as "#HφV /=".
    iDestruct ("Hrcond" with "HφV") as "#Hnormal_p'".
    iAssert (interp_in_mem p W C w)%I as "#Hnormal".
    { iEval (rewrite /interp_in_mem /= /interp_in_mem_pre filter_heap_load_word).
      iApply (interp_weakening_word_load W C p p' (filter_heap W w)); first exact Hflows.
      iEval (rewrite /interp_in_mem_pre filter_heap_load_word) in "Hnormal_p'".
      iExact "Hnormal_p'". }
    iDestruct (interp_in_mem_load_post with "Hnormal") as "#Hload_interp"; first exact Hpost.
    rewrite linsert_reg_not_cnull //.
    apply incrementPC_Some_inv in Hinc
      as (tpc & ppc & gpc & bpc & epc & apc & apc'' & πpc & HPC & Hapc & ->).
    injection HPC as <- <- <- <- <- <- <-.
    rewrite Hpca' in Hapc. injection Hapc as <-.
    rewrite insert_insert_eq.
    iDestruct (regs_of_map_1 with "Hmap") as "Hsrc".
    iDestruct (memMap_resource_2ne_dq with "Hmem") as "[Hi Ha]"; auto.
    iDestruct (addr_key_pointsto_join with "Ha Hshare") as "Ha".
    iDestruct ("WorldRes" with "[$Ha $HφV]") as "WorldRes".
    iDestruct (close_world_interp_next with "Hworld_interp Hstate Hrel WorldRes")
      as "Hworld_interp"; eauto.
    { destruct ρ; auto; contradiction. }
    iApply "Hφ"; iRight. iExists loadv'. iFrame "∗#%". done.
  Qed.

  (** A load through a safe word into the register that holds it: it
      faults, or it loads a safe word ([wp_load_interp] for one register,
      with any fraction of the instruction). *)
  Lemma wp_load_interp_same (E : coPset) (W : WORLD) (C : CmptName) (r : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wsrc : LWord) (dq : dfrac) :
    decodeInstrW wi.(lw) = CLoad r r 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r ≠ cnull →
    {{{ interp W C wsrc ∗
        PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a ∗
        pc_a ↦ₐ{dq} wi ∗
        r ↦ᵣ[th] wsrc ∗
        world_interp W C }}}
      Instr Executable @[th] E
    {{{ retv, RET retv;
        ( ⌜retv = FaultedV⌝ ∗
          PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a ∗
          pc_a ↦ₐ{dq} wi ∗
          r ↦ᵣ[th] wsrc ∗
          world_interp W C ) ∨
        ( ∃ wload,
          ⌜retv = NextIV⌝ ∗
          PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a' ∗
          pc_a ↦ₐ{dq} wi ∗
          r ↦ᵣ[th] wload ∗ interp W C wload ∗
          world_interp W C ) }}}.
  Proof.
    iIntros (Hdecode Hcorrect_pc Hpca' Hr φ)
      "(#Hinterp_src & HPC & Hi & Hsrc & Hworld_interp) Hφ".
    iApply (wp_load_interp_same_open _ _ _ []
             with "[$HPC $Hi $Hsrc $Hinterp_src Hworld_interp]"); try done.
    { intros ? ? ? ? ? _ _. apply not_elem_of_nil. }
    { by iApply open_world_interp_empty. }
    iNext.
    iIntros (retv) "[(Heq & HPC & Hi & Hsrc & Hworld_interp)
                   | (%wload & Heq & HPC & Hi & Hsrc & Hload & Hworld_interp)]";
      iApply "Hφ"; [iLeft | iRight]; iFrame; by iApply open_world_interp_empty.
  Qed.

  Lemma wp_load_interp_cap_imm (E : coPset) (imm : Z) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId)
    (wi wdst : LWord)
    :
    decodeInstrW wi.(lw) = CLoad rdst rsrc imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

     {{{ interp W C (WCap true p g b e a @@? π)
           ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ[th] (WCap true p g b e a @@? π)
           ∗ rdst ↦ᵣ[th] wdst
           ∗ world_interp W C
     }}}
       Instr Executable @[th] E
       {{{ retv, RET retv;
           ( ⌜ retv = FaultedV ⌝ ∗
             PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a ∗
             pc_a ↦ₐ wi ∗
             rsrc ↦ᵣ[th] WCap true p g b e a @@? π ∗
             rdst ↦ᵣ[th] wdst ∗
             world_interp W C ) ∨
          (∃ ea wload,
              ⌜ retv = NextIV ⌝
           ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ[th] (WCap true p g b e a @@? π)
           ∗ rdst ↦ᵣ[th] wload ∗ interp W C wload
           ∗ world_interp W C
           ∗ ⌜ readAllowed p = true ⌝
           ∗ ⌜(a + imm)%a = Some ea⌝
           ∗ ⌜(b <= ea < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ?? φ) "Hpre Hφ".
    iApply (wp_load_interp_imm with "Hpre");eauto.
    iNext. iIntros (ret) "Hpost". iApply "Hφ".
    iDestruct "Hpost" as "[Hfail | Hsuccess]"; first (iLeft; iExact "Hfail").
    iDestruct "Hsuccess" as (p0 g0 b0 e0 a0 π0 ea wload) "(%Heq & Hrest)".
    simplify_eq. iRight. iExists ea, wload. iExact "Hrest".
  Qed.

  Lemma wp_load_interp_cap (E : coPset) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId)
    (wi wdst : LWord)
    :
    decodeInstrW wi.(lw) = CLoad rdst rsrc 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

     {{{ interp W C (WCap true p g b e a @@? π)
           ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ[th] (WCap true p g b e a @@? π)
           ∗ rdst ↦ᵣ[th] wdst
           ∗ world_interp W C
     }}}
       Instr Executable @[th] E
       {{{ retv, RET retv;
           ( ⌜ retv = FaultedV ⌝ ∗
             PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a ∗
             pc_a ↦ₐ wi ∗
             rsrc ↦ᵣ[th] WCap true p g b e a @@? π ∗
             rdst ↦ᵣ[th] wdst ∗
             world_interp W C ) ∨
          (∃ wload,
              ⌜ retv = NextIV ⌝
           ∗ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ[th] (WCap true p g b e a @@? π)
           ∗ rdst ↦ᵣ[th] wload ∗ interp W C wload
           ∗ world_interp W C
           ∗ ⌜ readAllowed p = true ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ?? φ) "Hpre Hφ".
    iApply (wp_load_interp_cap_imm with "Hpre");eauto.
    iNext. iIntros (ret) "[Hfail | Hsucc]"; iApply "Hφ"; first (iLeft; iExact "Hfail").
    iRight.
    iDestruct "Hsucc" as (ea wload) "(? & ? & ? & ? & ? & ? & ? & ? & %Hea & %Hb)".
    rewrite addr_add_0 in Hea. injection Hea as <-.
    iExists wload. by iFrame.
  Qed.

  (** A load through the world's witness keeps the world's view of the loaded
      word: a quarantined identifier's capability is loaded untagged. *)
  Lemma shadow_read_retained W p raw actual :
    load_post (load_witness_of W raw) p raw actual →
    filter_heap W actual = actual.
  Proof.
    intros Hpost.
    destruct (load_post_world W p raw actual Hpost) as [-> | [-> Hkeep] ]; last done.
    apply filter_heap_untagged. rewrite lw_lclear_tag. apply get_tag_clear_tag.
  Qed.

  Lemma load_read_retained {dq : dfrac} E W C
    pc_p pc_g pc_b pc_e pc_a pc_a' dst src (wi wd : LWord) b e a (raw : LWord) :
    is_shadow_address a = false →
    decodeInstrW wi.(lw) = CLoad dst src 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull → src ≠ cnull →
    {{{ PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ[th] wd ∗ src ↦ᵣ[th] WCap true RW Global b e a ∗ a ↦ₐ raw ∗
        region W C }}}
      Instr Executable @[th] E
    {{{ actual, RET NextIV;
        ⌜load_heap raw actual ∧ filter_heap W actual = actual⌝ ∗
        PC ↦ₚ[th] WCap true pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ[th] actual ∗ src ↦ᵣ[th] WCap true RW Global b e a ∗
        a ↦ₐ raw ∗ region W C }}}.
  Proof.
    iIntros (Hshadow Hinstr Hvpc Hbounds Hpc Hdst Hsrc Φ)
      "(HPC & Hi & Hdst & Hsrc & Ha & Hregion) HΦ".
    iDestruct (region_heap_provenance with "Hregion") as "[Hregion #Hprov]".
    iDestruct (heap_provenance_load_witness W raw with "Hprov") as "Hwit".
    iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %Hsrc_dst]".
    iDestruct (memMap_resource_2ne_apply_dq with "Hi Ha") as "[Hmem %Hpc_a]".
    iAssert (▷ ([∗ map] k↦revoked ∈ (∅ : ShadowTbl), k ↦ₛ{DfracDiscarded} revoked))%I
      as "Hshadow".
    { by rewrite big_sepM_empty. }
    iApply (wp_load_general_shadow_imm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DerefNoId
              with "[$HPC $Hmem $Hshadow $Hwit $Hmap //]"); eauto.
    { by rewrite !dom_insert; set_solver+. }
    { by simplify_map_eq. }
    { intros p0 g0 b0 e0 ea0 Hallow.
      destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)].
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0').
      rewrite lookup_insert_eq in Hsrc0'. injection Hsrc0' as <- <- <- <- <- <-.
      rewrite addr_add_0 in Haddr. injection Haddr as <-.
      rewrite Hshadow.
      destruct (is_revoker_address a); first done.
      eexists. by simplify_map_eq. }
    { by rewrite !dom_insert_L. }
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hmem & _ & _ & _ & Hmap)".
    destruct Hspec as [p0 g0 b0 e0 ea0 loadv loadv' Hallow Hsh Hl Hpost Hinc ->
                      |p0 g0 b0 e0 ea0 heap_a revoked Hallow Hsh
                      |p0 g0 b0 e0 ea0 Hallow Hrev Hl
                      |Hfail].
    2,3: exfalso;
      destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)];
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0');
      rewrite lookup_insert_eq in Hsrc0'; injection Hsrc0' as <- <- <- <- <- <-;
      rewrite addr_add_0 in Haddr; injection Haddr as <-;
      simplify_map_eq; congruence.
    2: { exfalso. eapply (load_failure_spec_impossible _ _ _ _ _ _ _ RW Global b e a a);
         eauto; try by simplify_map_eq.
         all: try by rewrite addr_add_0.
         all: try (by intros ? Hv; rewrite llookup_reg_not_cnull // in Hv; simplify_map_eq).
         all: rewrite llookup_reg_not_cnull //; by simplify_map_eq. }
    destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)].
    destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0').
    rewrite lookup_insert_eq in Hsrc0'. injection Hsrc0' as <- <- <- <- <- <-.
    rewrite addr_add_0 in Haddr. injection Haddr as <-.
    rewrite lookup_insert_ne // lookup_insert_eq in Hl. injection Hl as <-.
    pose proof (load_post_world_load_heap_in_world W RW raw loadv' Hpost) as Hloaded.
    rewrite lload_word_RW in Hloaded.
    rewrite linsert_reg_not_cnull //.
    apply incrementPC_Some_inv in Hinc
      as (tpc & ppc & gpc & bpc & epc & apc & apc'' & πpc & HPC & Hapc & ->).
    injection HPC as <- <- <- <- <- <- <-.
    rewrite Hpc in Hapc. injection Hapc as <-.
    rewrite (insert_insert_ne _ dst src) // insert_insert_eq.
    iDestruct (regs_of_map_2 with "Hmap") as "(Hsrc & Hdst)"; eauto.
    iDestruct (memMap_resource_2ne_dq with "Hmem") as "[Hi Ha]"; first done.
    iApply "HΦ". by iFrame.
  Qed.

End wp_interp.
