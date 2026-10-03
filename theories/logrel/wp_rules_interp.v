From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Export logrel region_invariants.
From griotte Require Import world_ghost_theory.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Import rules proofmode monotone.
From griotte Require Import map_simpl register_tactics proofmode.

(* TEMPORARY MCP workaround: the 5th constructor of [instr]. *)
Definition cload : RegName → RegName → Z → instr :=
  ltac:(intros d s i; constructor 5; [exact d | exact s | exact i]).

Section wp_interp.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
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

  (* TODO: move to program_logic/rules/rules_Load.v *)
  (** The general load rule with a status witness, over owned memory. *)
  Lemma wp_load_witness_imm Ep pc_p pc_g pc_b pc_e pc_a pc_π r1 r2 (imm : Z) w
      (mem : LMem) (regs : LReg) wit :
    decodeInstrW w.(lw) = cload r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs_of (cload r1 r2 imm) ⊆ dom regs →
    mem !! pc_a = Some w →
    allow_load_mem_or_shadow_offset r2 imm regs mem ∅ →
    {{{ (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
        load_witness_res wit ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ Load_spec regs r1 r2 imm regs' mem ∅ wit retv⌝ ∗
        ([∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
        load_witness_res wit ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaLoad φ) "(Hmem & Hwit & Hreg) Hφ".
    iDestruct (mem_remove_dq with "Hmem") as "Hmem".
    iAssert (▷ ([∗ map] k↦revoked ∈ (∅ : ShadowTbl), k ↦ₛ{DfracDiscarded} revoked))%I
      as "Hshadow".
    { by rewrite big_sepM_empty. }
    iApply (wp_load_general_shadow_imm with "[$Hmem $Hshadow $Hwit $Hreg]"); eauto.
    { rewrite create_gmap_default_dom list_to_set_elements_L. auto. }
    iNext. iIntros (? ?) "(?&Hmem&_&Hwit&?)". iApply "Hφ". iFrame.
    iDestruct (mem_remove_dq with "Hmem") as "Hmem". iFrame.
  Qed.

  (* TODO: move to program_logic/rules/rules_Store.v *)
  (** A store through a word that is not a capability fails, whatever its
      identifier. *)
  Lemma wp_store_fail_not_cap_imm Ep (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_π
      w dst (src : Z + RegName) regs wa :
    decodeInstrW w.(lw) = Store dst src imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs !!ₗ dst = Some wa →
    is_cap wa.(lw) = false →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ RET FailedV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Hdst Hcap φ) "(>Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "Hpc_a Hmap"); eauto.
    iNext. iIntros (r sr m st lreg lmem Rg Cg c σ' Her Hregs Hregs' Hpc_a' Hstep)
      "Hr Hsr Hm Hst HR HC Hpc_a Hmap".
    assert (lookup_reg dst r = Some wa.(lw)) as Hdst'.
    { eapply lookup_reg_weaken; last exact Hregs'. by rewrite lookup_reg_erase Hdst. }
    rewrite Hinstr /exec /= Hdst' /= in Hstep.
    assert (c = Failed ∧ σ' = (r, sr, m, st)) as [-> ->].
    { destruct wa as [ [| [|] | |] ?]; cbn in Hcap; try discriminate.
      all: cbn in Hstep; destruct (word_of_argument _ src); cbn in Hstep; by simplify_eq. }
    iApply (instr_close_fail with "Hr Hsr Hm Hst HR HC Hmap"); first done.
    iIntros "Hmap". iApply "Hφ". iFrame.
  Qed.

  (* TODO: move to logrel/logrel.v *)
  Lemma interp_lstore_word W C p v :
    interp W C v -∗ interp W C (lstore_word p v).
  Proof.
    iIntros "#Hv".
    destruct (canStore p v.(lw)) eqn:Hcs.
    - by rewrite lstore_word_canStore.
    - assert (lstore_word p v = lclear_tag v) as ->.
      { by rewrite /lstore_word /lclear_tag /lift_word /store_word Hcs. }
      iApply interp_clear_tag.
  Qed.

  Lemma lload_word_RW v : lload_word RW v = v.
  Proof. by destruct v as [ [] ?]. Qed.

  (** Accesses retain the original current address and report their checked
      effective address. *)

  Lemma wp_store_interp_imm (E : coPset) (imm : Z) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
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
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rdst ↦ᵣ wdst
           ∗ world_interp W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          ( ∃ p g b e a π ea,
           ⌜ wdst = WCap true p g b e a @@? π ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rdst ↦ᵣ WCap true p g b e a @@? π
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
      iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
      iApply (wp_store_fail_not_cap_imm _ _ _ _ _ _ _ _ _ _ _ _ (wdst @@? π) with "[$Hi $Hmap]"); eauto.
      { by simplify_map_eq. }
      { rewrite llookup_reg_not_cnull //. by simplify_map_eq. }
      iNext; iIntros "_". iApply "Hφ"; by iLeft. }
    destruct wdst as [|[tag p g b e a|] | |]; try done.
    destruct tag; cycle 1.
    {
      iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
      iApply (wp_store_fail_tag_imm _ _ _ _ _ _ _ _ _ _ _ _ (WCap false p g b e a @@? π) with "[$Hi $Hmap]"); eauto.
      { by simplify_map_eq. }
      { rewrite llookup_reg_not_cnull //. by simplify_map_eq. }
      iNext; iIntros "_". iApply "Hφ"; by iLeft.
    }

    destruct (a + imm)%a as [ea|] eqn:Hea; cycle 1.
    {
      iApply (wp_store_fail_reg_overflow_imm with "[$HPC $Hi $Hsrc $Hdst]"); eauto.
      iNext; iIntros "_". iApply "Hφ"; by iLeft.
    }

    destruct (decide (writeAllowed p = true))%a as [Hp_stk_wa|Hp_stk_wa]; cycle 1.
    {
      iApply (wp_store_fail_reg_perm_imm with "[$HPC $Hi $Hsrc $Hdst]"); eauto.
      { by destruct (writeAllowed p); auto. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }
    destruct (decide (b <= ea < e))%a as [Hbounds|Hbounds]; cycle 1.
    {
      iApply (wp_store_fail_reg_imm with "[$HPC $Hi $Hsrc $Hdst]"); eauto.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
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
    iApply (wp_store_success_reg_store_word_imm with "[$HPC $Hi $Hsrc $Hdst $Ha]"); eauto.
    iNext; iIntros "(HPC & Hi & Hsrc & Hdst & Ha)".

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

  Lemma wp_store_interp (E : coPset) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
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
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rdst ↦ᵣ wdst
           ∗ world_interp W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          ( ∃ p g b e a π,
           ⌜ wdst = WCap true p g b e a @@? π ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rdst ↦ᵣ WCap true p g b e a @@? π
           ∗ world_interp W C
           ∗ ⌜ writeAllowed p = true ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ?? φ) "Hpre Hφ".
    iApply (wp_store_interp_imm with "Hpre"); eauto.
    iNext. iIntros (ret) "[Hfail | Hsucc]"; iApply "Hφ"; first by iLeft.
    iRight.
    iDestruct "Hsucc" as (p g b e a π ea) "(? & ? & ? & ? & ? & ? & ? & ? & %Hea & %Hb)".
    rewrite addr_add_0 in Hea. injection Hea as <-.
    iExists p, g, b, e, a, π. by iFrame.
  Qed.

  Lemma wp_store_interp_cap_imm (E : coPset) (imm : Z) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
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
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rdst ↦ᵣ (WCap true p g b e a @@? π)
           ∗ world_interp W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          (∃ ea, ⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rdst ↦ᵣ WCap true p g b e a @@? π
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
    iDestruct "Hpost" as "[Hfail | Hsuccess]"; first (iLeft; done).
    iDestruct "Hsuccess" as (p0 g0 b0 e0 a0 π0 ea) "(%Heq & Hrest)".
    simplify_eq. iRight. iExists ea. iExact "Hrest".
  Qed.

  Lemma wp_store_interp_cap (E : coPset) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
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
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rdst ↦ᵣ (WCap true p g b e a @@? π)
           ∗ world_interp W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          (⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rdst ↦ᵣ WCap true p g b e a @@? π
           ∗ world_interp W C
           ∗ ⌜ writeAllowed p = true ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ? ? φ) "Hpre Hφ".
    iApply (wp_store_interp_cap_imm with "Hpre");eauto.
    iNext. iIntros (ret) "[Hfail | Hsucc]"; iApply "Hφ"; first by iLeft.
    iRight.
    iDestruct "Hsucc" as (ea) "(? & ? & ? & ? & ? & ? & ? & %Hea & %Hb)".
    rewrite addr_add_0 in Hea. injection Hea as <-. by iFrame.
  Qed.

  Lemma wp_store_interp_z_imm (E : coPset) (imm : Z) (W : WORLD) (C : CmptName) (rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wdst : LWord) (z : Z)
    :
    decodeInstrW wi.(lw) = Store rdst (inl z) imm →
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
          ( ∃ p g b e a π ea,
           ⌜ wdst = WCap true p g b e a @@? π ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rdst ↦ᵣ WCap true p g b e a @@? π
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
      iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
      iApply (wp_store_fail_not_cap_imm _ _ _ _ _ _ _ _ _ _ _ _ (wdst @@? π) with "[$Hi $Hmap]"); eauto.
      { by simplify_map_eq. }
      { rewrite llookup_reg_not_cnull //. by simplify_map_eq. }
      iNext; iIntros "_". iApply "Hφ"; by iLeft. }
    destruct wdst as [|[tag p g b e a|] | |]; try done.
    destruct tag; cycle 1.
    {
      iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
      iApply (wp_store_fail_tag_imm _ _ _ _ _ _ _ _ _ _ _ _ (WCap false p g b e a @@? π) with "[$Hi $Hmap]"); eauto.
      { by simplify_map_eq. }
      { rewrite llookup_reg_not_cnull //. by simplify_map_eq. }
      iNext; iIntros "_". iApply "Hφ"; by iLeft.
    }

    destruct (a + imm)%a as [ea|] eqn:Hea; cycle 1.
    {
      iApply (wp_store_fail_z_overflow_imm with "[$HPC $Hi $Hdst]"); eauto.
      iNext; iIntros "_". iApply "Hφ"; by iLeft.
    }

    destruct (decide (writeAllowed p = true))%a as [Hstore_src|Hstore_src]; cycle 1.
    {
      iApply (wp_store_fail_z_perm_imm with "[$HPC $Hi $Hdst]"); eauto.
      { by destruct ( writeAllowed p ); auto. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }
    destruct (decide (b <= ea < e))%a as [Hbounds|Hbounds]; cycle 1.
    {
      iApply (wp_store_fail_z_imm with "[$HPC $Hi $Hdst]"); eauto.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
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
    iApply (wp_store_success_z_imm with "[$HPC $Hi $Hdst $Ha]"); eauto.
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

    iApply "Hφ"; iRight. iExists p, g, b, e, a, π, ea. iFrame "∗%".
    iPureIntro. split; first done. solve_addr.
  Qed.

  Lemma wp_store_interp_z (E : coPset) (W : WORLD) (C : CmptName) (rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wdst : LWord) (z : Z)
    :
    decodeInstrW wi.(lw) = Store rdst (inl z) 0 →
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
          ( ∃ p g b e a π,
           ⌜ wdst = WCap true p g b e a @@? π ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rdst ↦ᵣ WCap true p g b e a @@? π
           ∗ world_interp W C
           ∗ ⌜ writeAllowed p ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ? φ) "Hpre Hφ".
    iApply (wp_store_interp_z_imm with "Hpre"); eauto.
    iNext. iIntros (ret) "[Hfail | Hsucc]"; iApply "Hφ"; first by iLeft.
    iRight.
    iDestruct "Hsucc" as (p g b e a π ea) "(? & ? & ? & ? & ? & ? & ? & %Hea & %Hb)".
    rewrite addr_add_0 in Hea. injection Hea as <-.
    iExists p, g, b, e, a, π. by iFrame.
  Qed.

  Lemma wp_store_interp_z_cap_imm (E : coPset) (imm : Z) (W : WORLD) (C : CmptName) (rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId)
    (wi : LWord) (z : Z)
    :
    decodeInstrW wi.(lw) = Store rdst (inl z) imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rdst ≠ cnull ->

     {{{  interp W C (WCap true p g b e a @@? π)
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rdst ↦ᵣ (WCap true p g b e a @@? π)
           ∗ world_interp W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          (∃ ea, ⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rdst ↦ᵣ WCap true p g b e a @@? π
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
    iDestruct "Hpost" as "[Hfail | Hsuccess]"; first (iLeft; done).
    iDestruct "Hsuccess" as (p0 g0 b0 e0 a0 π0 ea) "(%Heq & Hrest)".
    simplify_eq. iRight. iExists ea. iExact "Hrest".
  Qed.

  Lemma wp_store_interp_z_cap (E : coPset) (W : WORLD) (C : CmptName) (rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId)
    (wi : LWord) (z : Z)
    :
    decodeInstrW wi.(lw) = Store rdst (inl z) 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rdst ≠ cnull ->

     {{{  interp W C (WCap true p g b e a @@? π)
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rdst ↦ᵣ (WCap true p g b e a @@? π)
           ∗ world_interp W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          (⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rdst ↦ᵣ WCap true p g b e a @@? π
           ∗ world_interp W C
           ∗ ⌜ writeAllowed p ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ? φ) "Hpre Hφ".
    iApply (wp_store_interp_z_cap_imm with "Hpre");eauto.
    iNext. iIntros (ret) "[Hfail | Hsucc]"; iApply "Hφ"; first by iLeft.
    iRight.
    iDestruct "Hsucc" as (ea) "(? & ? & ? & ? & ? & ? & %Hea & %Hb)".
    rewrite addr_add_0 in Hea. injection Hea as <-. by iFrame.
  Qed.

  Lemma wp_unseal_unknown E pc_p pc_g pc_b pc_e pc_a pc_a' wi r1 r2 wsealr wsealed  :
    decodeInstrW wi.(lw) = UnSeal r2 r1 r2 →
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
          ∨ (∃ psr gsr bsr esr asr πsr ot wsb π,
              ⌜ retv = NextIV ⌝
              ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ wi
              ∗ r1 ↦ᵣ wsealr
              ∗ r2 ↦ᵣ WSealable (machine_word.unseal gsr wsb) @@? π
              ∗ ⌜ wsealr = WSealRange true psr gsr bsr esr asr @@? πsr ⌝
              ∗ ⌜ permit_unseal psr = true ⌝
              ∗ ⌜ wsealed = WSealed ot wsb @@? π ⌝
              ∗ ⌜ get_tag_sealable wsb = true ⌝
              ∗ ⌜ withinBounds bsr esr ot = true ⌝ )
          ∨ ∃ tsr psr gsr bsr esr asr πsr ot sb π,
              ⌜ retv = NextIV ⌝
              ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ wi
              ∗ r1 ↦ᵣ wsealr
              ∗ r2 ↦ᵣ WSealable (clear_tag_sealable (machine_word.unseal gsr sb)) @@? π
              ∗ ⌜ wsealr = WSealRange tsr psr gsr bsr esr asr @@? πsr ⌝
              ∗ ⌜ wsealed = WSealed ot sb @@? π ⌝
              ∗ ⌜ tsr && get_tag_sealable sb && permit_unseal psr &&
                    withinBounds bsr esr ot = false ⌝
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpc_a' Hr1_null Hr2_null ϕ) "(HPC & Hpc_a & Hr1 & Hr2) Hφ".

    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_UnSeal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [p g b e a πs o sb π Hsr Hsd Htag Hperm Hwb Hinc
                      |t p g b e a πs o sb π Hsr Hsd Hinvalid Hinc|].
    { iApply "Hφ". iRight. iLeft.
      rewrite !llookup_reg_not_cnull // in Hsr Hsd. simplify_map_eq.
      rewrite /linsert_reg in Hinc; try rewrite decide_False // in Hinc.
      apply incrementPC_Some_inv in Hinc
        as (tpc & ppc & gpc & bpc & epc & apc & apc' & πpc & HPC & Hapc' & ->).
      rewrite lookup_insert_ne // lookup_insert_eq in HPC.
      simplify_eq.
      iExists p, g, b, e, a, πs, o, sb, π.
      rewrite (insert_insert_ne _ _ PC) //.
      rewrite (insert_insert_ne _ _ r1) //.
      rewrite !insert_insert_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[HPC Hmap]"; first by simplify_map_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[Hr1 Hmap]"; first by simplify_map_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[Hr2 Hmap]"; first by simplify_map_eq.
      iFrame; done.
    }
    { iApply "Hφ". iRight. iRight.
      rewrite !llookup_reg_not_cnull // in Hsr Hsd. simplify_map_eq.
      rewrite /linsert_reg in Hinc; try rewrite decide_False // in Hinc.
      apply incrementPC_Some_inv in Hinc
        as (tpc & ppc & gpc & bpc & epc & apc & apc' & πpc & HPC & Hapc' & ->).
      rewrite lookup_insert_ne // lookup_insert_eq in HPC.
      simplify_eq.
      iExists t, p, g, b, e, a, πs, o, sb, π.
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
    decodeInstrW wi.(lw) = UnSeal r1 r1 r2 →
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
          ∨ (∃ psr gsr bsr esr asr πsr ot wsb π,
              ⌜ retv = NextIV ⌝
              ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ wi
              ∗ r1 ↦ᵣ WSealable (machine_word.unseal gsr wsb) @@? π
              ∗ r2 ↦ᵣ wsealed
              ∗ ⌜ wsealr = WSealRange true psr gsr bsr esr asr @@? πsr ⌝
              ∗ ⌜ permit_unseal psr = true ⌝
              ∗ ⌜ wsealed = WSealed ot wsb @@? π ⌝
              ∗ ⌜ get_tag_sealable wsb = true ⌝
              ∗ ⌜ withinBounds bsr esr ot = true ⌝ )
          ∨ ∃ tsr psr gsr bsr esr asr πsr ot sb π,
              ⌜ retv = NextIV ⌝
              ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ wi
              ∗ r1 ↦ᵣ WSealable (clear_tag_sealable (machine_word.unseal gsr sb)) @@? π
              ∗ r2 ↦ᵣ wsealed
              ∗ ⌜ wsealr = WSealRange tsr psr gsr bsr esr asr @@? πsr ⌝
              ∗ ⌜ wsealed = WSealed ot sb @@? π ⌝
              ∗ ⌜ tsr && get_tag_sealable sb && permit_unseal psr &&
                    withinBounds bsr esr ot = false ⌝
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpc_a' Hr1_null Hr2_null ϕ) "(HPC & Hpc_a & Hr1 & Hr2) Hφ".

    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_UnSeal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [p g b e a πs o sb π Hsr Hsd Htag Hperm Hwb Hinc
                      |t p g b e a πs o sb π Hsr Hsd Hinvalid Hinc|].
    { iApply "Hφ". iRight. iLeft.
      rewrite !llookup_reg_not_cnull // in Hsr Hsd. simplify_map_eq.
      rewrite /linsert_reg in Hinc; try rewrite decide_False // in Hinc.
      apply incrementPC_Some_inv in Hinc
        as (tpc & ppc & gpc & bpc & epc & apc & apc' & πpc & HPC & Hapc' & ->).
      rewrite lookup_insert_ne // lookup_insert_eq in HPC.
      simplify_eq.
      iExists p, g, b, e, a, πs, o, sb, π.
      rewrite (insert_insert_ne _ _ PC) //.
      rewrite !insert_insert_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[HPC Hmap]"; first by simplify_map_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[Hr1 Hmap]"; first by simplify_map_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[Hr2 Hmap]"; first by simplify_map_eq.
      iFrame; done.
    }
    { iApply "Hφ". iRight. iRight.
      rewrite !llookup_reg_not_cnull // in Hsr Hsd. simplify_map_eq.
      rewrite /linsert_reg in Hinc; try rewrite decide_False // in Hinc.
      apply incrementPC_Some_inv in Hinc
        as (tpc & ppc & gpc & bpc & epc & apc & apc' & πpc & HPC & Hapc' & ->).
      rewrite lookup_insert_ne // lookup_insert_eq in HPC.
      simplify_eq.
      iExists t, p, g, b, e, a, πs, o, sb, π.
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
    decodeInstrW wi.(lw) = UnSeal r2 r1 r2 →
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
          ∨ (∃ ot wsb π,
              ⌜ retv = NextIV ⌝
              ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ wi
              ∗ r1 ↦ᵣ WSealRange true psr gsr bsr esr asr
              ∗ r2 ↦ᵣ WSealable (machine_word.unseal gsr wsb) @@? π
              ∗ ⌜ wsealed = WSealed ot wsb @@? π ⌝
              ∗ ⌜ get_tag_sealable wsb = true ⌝
              ∗ ⌜ withinBounds bsr esr ot = true ⌝ )
          ∨ ∃ ot sb π,
              ⌜ retv = NextIV ⌝
              ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ wi
              ∗ r1 ↦ᵣ WSealRange true psr gsr bsr esr asr
              ∗ r2 ↦ᵣ WSealable (clear_tag_sealable (machine_word.unseal gsr sb)) @@? π
              ∗ ⌜ wsealed = WSealed ot sb @@? π ⌝
              ∗ ⌜ get_tag_sealable sb && withinBounds bsr esr ot = false ⌝
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpc_a' Hpsr Hsr Hr1_null Hr2_null ϕ) "(HPC & Hpc_a & Hr1 & Hr2) Hφ".

    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_UnSeal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [p g b e a πs o sb π Hsr' Hsd Htag Hperm Hwb Hinc
                      |t p g b e a πs o sb π Hsr' Hsd Hinvalid Hinc|].
    { iApply "Hφ". iRight. iLeft.
      rewrite !llookup_reg_not_cnull // in Hsr' Hsd. simplify_map_eq.
      rewrite /linsert_reg in Hinc; try rewrite decide_False // in Hinc.
      apply incrementPC_Some_inv in Hinc
        as (tpc & ppc & gpc & bpc & epc & apc & apc' & πpc & HPC & Hapc' & ->).
      rewrite lookup_insert_ne // lookup_insert_eq in HPC.
      simplify_eq.
      iExists o, sb, π.
      rewrite (insert_insert_ne _ _ PC) //.
      rewrite (insert_insert_ne _ _ r1) //.
      rewrite !insert_insert_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[HPC Hmap]"; first by simplify_map_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[Hr1 Hmap]"; first by simplify_map_eq.
      iDestruct (big_sepM_insert with "Hmap") as "[Hr2 Hmap]"; first by simplify_map_eq.
      iFrame; done.
    }
    { iApply "Hφ". iRight. iRight.
      rewrite !llookup_reg_not_cnull // in Hsr' Hsd. simplify_map_eq.
      rewrite /linsert_reg in Hinc; try rewrite decide_False // in Hinc.
      apply incrementPC_Some_inv in Hinc
        as (tpc & ppc & gpc & bpc & epc & apc & apc' & πpc & HPC & Hapc' & ->).
      rewrite lookup_insert_ne // lookup_insert_eq in HPC.
      simplify_eq.
      iExists o, sb, π.
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

  (** A load through a valid capability: the world supplies the quarantine
      witness of the loaded word, which makes the loaded word valid (§4.5). *)
  Lemma wp_load_interp_imm (E : coPset) (imm : Z) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wsrc wdst : LWord)
    :
    decodeInstrW wi.(lw) = cload rdst rsrc imm →
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
          ( ∃ p g b e a π ea wload,
           ⌜ wsrc = WCap true p g b e a @@? π ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ WCap true p g b e a @@? π
           ∗ rdst ↦ᵣ wload ∗ interp W C wload
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
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }
    destruct wsrc as [|[tag p g b e a|] | |]; try done.
    destruct tag; cycle 1.
    {
      iDestruct (map_of_regs_3 with "HPC Hdst Hsrc") as "[Hmap (%&%&%)]".
      iApply (wp_load_fail_tag_imm _ _ _ _ _ _ _ _ _ _ _ _ (WCap false p g b e a @@? π) with "[$Hi $Hmap]"); eauto.
      { by simplify_map_eq. }
      { rewrite llookup_reg_not_cnull //. by simplify_map_eq. }
      iNext; iIntros "_". iApply "Hφ"; by iLeft.
    }

    destruct (a + imm)%a as [ea|] eqn:Hea; cycle 1.
    {
      iDestruct (map_of_regs_3 with "HPC Hdst Hsrc") as "[Hmap (%&%&%)]".
      iApply (wp_load_fail_addr_imm _ _ _ _ _ _ _ _ _ _ _ _ (WCap true p g b e a @@? π) with "[$Hi $Hmap]"); eauto.
      { by simplify_map_eq. }
      { rewrite llookup_reg_not_cnull //. by simplify_map_eq. }
      iNext; iIntros "_". iApply "Hφ"; by iLeft.
    }

    destruct (decide (readAllowed p = true))%a as [Hra_src|Hra_src]; cycle 1.
    {
      iApply (wp_load_fail_not_ra_imm _ rdst rsrc with "[$HPC $Hi $Hdst $Hsrc]"); eauto.
      { destruct p as [ [] ? ? ? ]; cbn in * ; done. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }
    destruct (decide (b <= ea < e))%a as [Hbounds|Hbounds]; cycle 1.
    {
      iApply (wp_load_fail_not_withinbounds_imm _ rdst rsrc with "[$HPC $Hi $Hdst $Hsrc]"); eauto.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
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
    (* The world's heap provenance supplies the status witness (§4.5). *)
    iDestruct (world_interp_open_heap_provenance with "Hworld_interp") as "[Hworld_interp #Hprov]".
    iDestruct (heap_provenance_load_witness W w with "Hprov") as "Hwit".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%Hpc_src & %Hpc_dst & %Hsrc_dst)]".
    iDestruct (memMap_resource_2ne_apply with "Hi Ha") as "[Hmem %Hpc_a]".
    (* Load rdst rsrc imm. *)
    iApply (wp_load_witness_imm with "[$Hmem $Hwit $Hmap]"); eauto.
    { by simplify_map_eq. }
    { by rewrite !dom_insert; set_solver+. }
    { by rewrite lookup_insert_eq. }
    { intros p0 g0 b0 e0 ea0 Hallow.
      destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)].
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0').
      rewrite lookup_insert_ne // lookup_insert_eq in Hsrc0'. injection Hsrc0' as <- <- <- <- <- <-.
      rewrite Hea in Haddr. injection Haddr as <-.
      rewrite Hnot_shadow.
      destruct (is_revoker_address ea); first done.
      eexists. by simplify_map_eq. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & _ & Hmap)".
    destruct Hspec as [p0 g0 b0 e0 ea0 loadv loadv' Hallow Hsh Hl Hpost Hinc
                      |p0 g0 b0 e0 ea0 heap_a revoked Hallow Hsh
                      |p0 g0 b0 e0 ea0 Hallow Hrev Hl
                      |Hfail].
    2,3: exfalso;
      destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)];
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0');
      rewrite lookup_insert_ne // lookup_insert_eq in Hsrc0'; injection Hsrc0' as <- <- <- <- <- <-;
      rewrite Hea in Haddr; injection Haddr as <-;
      simplify_map_eq; congruence.
    2: { iApply "Hφ". by iLeft. }
    destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)].
    destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0').
    rewrite lookup_insert_ne // lookup_insert_eq in Hsrc0'. injection Hsrc0' as <- <- <- <- <- <-.
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
    rewrite /linsert_reg in Hinc; try rewrite decide_False // in Hinc.
    apply incrementPC_Some_inv in Hinc
      as (tpc & ppc & gpc & bpc & epc & apc & apc'' & πpc & HPC & Hapc & ->).
    rewrite lookup_insert_ne // lookup_insert_eq in HPC.
    injection HPC as <- <- <- <- <- <- <-.
    rewrite Hpca' in Hapc. injection Hapc as <-.
    rewrite (insert_insert_ne _ rdst PC) // insert_insert_eq.
    rewrite (insert_insert_ne _ rdst rsrc) // insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(HPC & Hsrc & Hdst)"; eauto.
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
    decodeInstrW wi.(lw) = cload rdst rsrc 0 →
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
          ( ∃ p g b e a π wload,
           ⌜ wsrc = WCap true p g b e a @@? π ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ WCap true p g b e a @@? π
           ∗ rdst ↦ᵣ wload ∗ interp W C wload
           ∗ world_interp W C
           ∗ ⌜ readAllowed p = true ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ?? φ) "Hpre Hφ".
    iApply (wp_load_interp_imm with "Hpre"); eauto.
    iNext. iIntros (ret) "[Hfail | Hsucc]"; iApply "Hφ"; first by iLeft.
    iRight.
    iDestruct "Hsucc" as (p g b e a π ea wload)
      "(? & ? & ? & ? & ? & ? & ? & ? & ? & %Hea & %Hb)".
    rewrite addr_add_0 in Hea. injection Hea as <-.
    iExists p, g, b, e, a, π, wload. by iFrame.
  Qed.

  Lemma wp_load_interp_cap_imm (E : coPset) (imm : Z) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId)
    (wi wdst : LWord)
    :
    decodeInstrW wi.(lw) = cload rdst rsrc imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

     {{{ interp W C (WCap true p g b e a @@? π)
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ (WCap true p g b e a @@? π)
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
           ∗ rsrc ↦ᵣ (WCap true p g b e a @@? π)
           ∗ rdst ↦ᵣ wload ∗ interp W C wload
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
    iDestruct "Hpost" as "[Hfail | Hsuccess]"; first (iLeft; done).
    iDestruct "Hsuccess" as (p0 g0 b0 e0 a0 π0 ea wload) "(%Heq & Hrest)".
    simplify_eq. iRight. iExists ea, wload. iExact "Hrest".
  Qed.

  Lemma wp_load_interp_cap (E : coPset) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId)
    (wi wdst : LWord)
    :
    decodeInstrW wi.(lw) = cload rdst rsrc 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

     {{{ interp W C (WCap true p g b e a @@? π)
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ (WCap true p g b e a @@? π)
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
           ∗ rsrc ↦ᵣ (WCap true p g b e a @@? π)
           ∗ rdst ↦ᵣ wload ∗ interp W C wload
           ∗ world_interp W C
           ∗ ⌜ readAllowed p = true ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ?? φ) "Hpre Hφ".
    iApply (wp_load_interp_cap_imm with "Hpre");eauto.
    iNext. iIntros (ret) "[Hfail | Hsucc]"; iApply "Hφ"; first by iLeft.
    iRight.
    iDestruct "Hsucc" as (ea wload) "(? & ? & ? & ? & ? & ? & ? & ? & %Hea & %Hb)".
    rewrite addr_add_0 in Hea. injection Hea as <-.
    iExists wload. by iFrame.
  Qed.

  (** A load through the world's witness keeps the world's view of the loaded
      word: a quarantined identifier's capability is loaded untagged (§4.8). *)
  Lemma shadow_read_retained W p raw actual :
    load_post (load_witness_of W raw) p raw actual →
    filter_heap W actual = actual.
  Proof.
    intros Hpost.
    destruct (load_post_world W p raw actual Hpost) as [-> | [-> Hkeep] ]; last done.
    apply filter_heap_untagged. rewrite lw_lclear_tag. apply get_tag_clear_tag.
  Qed.

  (** A load from a register file whose source is a valid, in-bounds
      read capability and whose PC can be incremented does not fail. *)
  Lemma load_failure_spec_impossible (regs : LReg) r1 r2 imm mem wit p g b e a ea pc_p pc_g
      pc_b pc_e pc_a pc_a' pc_π :
    lw <$> regs !!ₗ r2 = Some (WCap true p g b e a) →
    (a + imm)%a = Some ea →
    readAllowed p = true → withinBounds b e ea = true →
    is_shadow_address ea = false →
    is_Some (mem !! ea) →
    r1 ≠ PC →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    (pc_a + 1)%a = Some pc_a' →
    Load_failure_spec regs r1 r2 imm mem ∅ wit → False.
  Proof.
    intros Hr2 Hea Hra Hwb Hsh [v Hv] Hr1 HPC Hpca' Hfail.
    destruct Hfail as [w0 Hw0 Hcap|? ? ? ? ? H|? ? ? ? ? H H0|? ? ? ? ? ? H H0 H1
                      |? ? ? ? ? ? ? ? H H0 H1 H2 H3 Hinc|? ? ? ? ? ? ? ? H H0 H1|? ? ? ? ? ? H H0 H1 H2 Hinc].
    all: try (rewrite Hr2 in H; simplify_eq).
    - rewrite Hw0 /= in Hr2. injection Hr2 as Hw. rewrite Hw in Hcap. discriminate.
    - destruct H1; congruence.
    - rewrite /incrementPC /incrementPC_gen /linsert_reg in Hinc.
      destruct (decide (r1 = cnull)); rewrite lookup_insert_ne // HPC /= Hpca' in Hinc; discriminate.
  Qed.

  Lemma load_read_retained_imm W C
    pc_b pc_e pc_a p e a (raw w0 : LWord) (imm : Z) :
    disjoint_from_shadow p e ->
    is_heap_cap raw.(lw) = true ->
    (p + imm)%a = Some a ->
    withinBounds p e a = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ 1)%a ->
    (PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a ∗
     cgp ↦ᵣ WCap true RW Global p e p ∗ ca0 ↦ᵣ w0 ∗
     a ↦ₐ raw ∗ codefrag pc_a [encodeInstrW (cload ca0 cgp imm)] ∗
     region W C ∗
     ▷ (∀ actual,
       ⌜load_heap_in_world W raw actual⌝ -∗
       PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ 1)%a ∗
       cgp ↦ᵣ WCap true RW Global p e p ∗ ca0 ↦ᵣ actual ∗
       a ↦ₐ raw ∗ codefrag pc_a [encodeInstrW (cload ca0 cgp imm)] ∗
       region W C -∗
       WP Seq (Instr Executable)
         {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
     ⊢ WP Seq (Instr Executable)
         {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    iIntros (Hshadow Hheap_raw Hea Hbounds Hsub)
      "(HPC & Hcgp & Hca0 & Ha & Hcode & Hregion & Hpost)".
    codefrag_facts "Hcode". clear H0.
    iEval (rewrite /lword_of_word) in "HPC".
    (* Load ca0 cgp imm. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iDestruct (region_heap_provenance with "Hregion") as "[Hregion #Hprov]".
    iDestruct (heap_provenance_load_witness W raw with "Hprov") as "Hwit".
    iDestruct (map_of_regs_3 with "HPC Hcgp Hca0")
      as "[Hmap (%Hpc_cgp & %Hpc_ca0 & %Hcgp_ca0)]".
    iDestruct (memMap_resource_2ne_apply with "Hi Ha")
      as "[Hmem %Hpc_a]".
    assert (is_shadow_address a = false) as Hnot_shadow
      by (eapply disjoint_from_shadow_not_in; [exact Hshadow|exact Hbounds]).
    iApply (wp_load_witness_imm _ RX Global pc_b pc_e pc_a None ca0 cgp imm
              (encodeInstrW (cload ca0 cgp imm) @@? None) with "[$Hmem $Hwit $Hmap]").
    { apply decode_encode_instrW_inv. }
    { solve_pure. }
    { by simplify_map_eq. }
    { by rewrite !dom_insert; set_solver+. }
    { by simplify_map_eq. }
    { intros p0 g0 b0 e0 ea0 Hallow.
      destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)].
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0').
      rewrite lookup_insert_ne // lookup_insert_eq in Hsrc0'. injection Hsrc0' as <- <- <- <- <- <-.
      rewrite Hea in Haddr. injection Haddr as <-.
      rewrite Hnot_shadow.
      destruct (is_revoker_address a); first done.
      eexists. by simplify_map_eq. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & _ & Hmap)".
    destruct Hspec as [p0 g0 b0 e0 ea0 loadv loadv' Hallow Hsh Hl Hpost Hinc
                      |p0 g0 b0 e0 ea0 heap_a revoked Hallow Hsh
                      |p0 g0 b0 e0 ea0 Hallow Hrev Hl
                      |Hfail].
    2,3: exfalso;
      destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)];
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0');
      rewrite lookup_insert_ne // lookup_insert_eq in Hsrc0'; injection Hsrc0' as <- <- <- <- <- <-;
      rewrite Hea in Haddr; injection Haddr as <-;
      simplify_map_eq; congruence.
    2: { wp_pure. wp_end. by iIntros (?). }
    destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)].
    destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0').
    rewrite lookup_insert_ne // lookup_insert_eq in Hsrc0'. injection Hsrc0' as <- <- <- <- <- <-.
      rewrite Hea in Haddr. injection Haddr as <-.
    rewrite lookup_insert_ne // lookup_insert_eq in Hl. injection Hl as <-.
    pose proof (load_post_world_load_heap_in_world W RW raw loadv' Hpost) as Hloaded.
    rewrite lload_word_RW in Hloaded.
    rewrite /linsert_reg in Hinc; try rewrite decide_False // in Hinc.
    apply incrementPC_Some_inv in Hinc
      as (tpc & ppc & gpc & bpc & epc & apc & apc'' & πpc & HPC & Hapc & ->).
    rewrite lookup_insert_ne // lookup_insert_eq in HPC.
    injection HPC as <- <- <- <- <- <- <-.
    assert ((pc_a + 1)%a = Some (pc_a ^+ 1)%a) as Hpc by solve_addr.
    rewrite Hpc in Hapc. injection Hapc as <-.
    rewrite (insert_insert_ne _ ca0 PC) // insert_insert_eq.
    rewrite (insert_insert_ne _ ca0 cgp) // insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(HPC & Hcgp & Hca0)"; eauto.
    iDestruct (memMap_resource_2ne with "Hmem") as "[Hi Ha]"; auto.
    wp_pure.
    iSpecialize ("Hcode" with "Hi").
    iApply ("Hpost" $! loadv' with "[//]"). iFrame.
  Qed.

  Lemma load_read_retained E W C
    pc_p pc_g pc_b pc_e pc_a pc_a' dst src (wi wd : LWord) b e a (raw : LWord) :
    is_shadow_address a = false →
    decodeInstrW wi.(lw) = cload dst src 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull → src ≠ cnull →
    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ wd ∗ src ↦ᵣ WCap true RW Global b e a ∗ a ↦ₐ raw ∗
        region W C }}}
      Instr Executable @ E
    {{{ actual, RET NextIV;
        ⌜load_heap raw actual ∧ filter_heap W actual = actual⌝ ∗
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ actual ∗ src ↦ᵣ WCap true RW Global b e a ∗
        a ↦ₐ raw ∗ region W C }}}.
  Proof.
    iIntros (Hshadow Hinstr Hvpc Hbounds Hpc Hdst Hsrc Φ)
      "(HPC & Hi & Hdst & Hsrc & Ha & Hregion) HΦ".
    iDestruct (region_heap_provenance with "Hregion") as "[Hregion #Hprov]".
    iDestruct (heap_provenance_load_witness W raw with "Hprov") as "Hwit".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%Hpc_src & %Hpc_dst & %Hsrc_dst)]".
    iDestruct (memMap_resource_2ne_apply with "Hi Ha") as "[Hmem %Hpc_a]".
    iApply (wp_load_witness_imm with "[$Hmem $Hwit $Hmap]"); eauto.
    { by simplify_map_eq. }
    { by rewrite !dom_insert; set_solver+. }
    { by simplify_map_eq. }
    { intros p0 g0 b0 e0 ea0 Hallow.
      destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)].
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0').
      rewrite lookup_insert_ne // lookup_insert_eq in Hsrc0'. injection Hsrc0' as <- <- <- <- <- <-.
      rewrite addr_add_0 in Haddr. injection Haddr as <-.
      rewrite Hshadow.
      destruct (is_revoker_address a); first done.
      eexists. by simplify_map_eq. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & _ & Hmap)".
    destruct Hspec as [p0 g0 b0 e0 ea0 loadv loadv' Hallow Hsh Hl Hpost Hinc
                      |p0 g0 b0 e0 ea0 heap_a revoked Hallow Hsh
                      |p0 g0 b0 e0 ea0 Hallow Hrev Hl
                      |Hfail].
    2,3: exfalso;
      destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)];
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0');
      rewrite lookup_insert_ne // lookup_insert_eq in Hsrc0'; injection Hsrc0' as <- <- <- <- <- <-;
      rewrite addr_add_0 in Haddr; injection Haddr as <-;
      simplify_map_eq; congruence.
    2: { exfalso. eapply (load_failure_spec_impossible _ _ _ _ _ _ RW Global b e a a);
         eauto; try by simplify_map_eq.
         all: try by rewrite addr_add_0.
         all: rewrite llookup_reg_not_cnull //; by simplify_map_eq. }
    destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)].
    destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0').
    rewrite lookup_insert_ne // lookup_insert_eq in Hsrc0'. injection Hsrc0' as <- <- <- <- <- <-.
      rewrite addr_add_0 in Haddr. injection Haddr as <-.
    rewrite lookup_insert_ne // lookup_insert_eq in Hl. injection Hl as <-.
    pose proof (load_post_world_load_heap_in_world W RW raw loadv' Hpost) as Hloaded.
    rewrite lload_word_RW in Hloaded.
    rewrite /linsert_reg in Hinc; try rewrite decide_False // in Hinc.
    apply incrementPC_Some_inv in Hinc
      as (tpc & ppc & gpc & bpc & epc & apc & apc'' & πpc & HPC & Hapc & ->).
    rewrite lookup_insert_ne // lookup_insert_eq in HPC.
    injection HPC as <- <- <- <- <- <- <-.
    rewrite Hpc in Hapc. injection Hapc as <-.
    rewrite (insert_insert_ne _ dst PC) // insert_insert_eq.
    rewrite (insert_insert_ne _ dst src) // insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(HPC & Hsrc & Hdst)"; eauto.
    iDestruct (memMap_resource_2ne with "Hmem") as "[Hi Ha]"; auto.
    iApply "HΦ". by iFrame.
  Qed.

End wp_interp.
