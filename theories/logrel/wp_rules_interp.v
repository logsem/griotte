From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Export logrel world_interp_cells.
From griotte Require Import world_ghost_theory.
From griotte Require Import region_open interp_weakening.
From griotte Require Import rules shapes.regs shapes.memory_access ghost.deref_quar proofmode monotone.
From griotte Require Import map_simpl register_tactics proofmode.

Section wp_interp.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    {cthreads : CmptThreads}
    {CL : ∀ t, CritLink Σ t}
    `{MP: MachineParameters}
    {CR : ∀ t, CritRoute Σ t (CL t)}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> (leibnizO LWord) -n> iPropO Σ).
  #[local] Notation V := (interpO Σ).
  #[local] Notation K := (contO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

  Lemma wp_store_interp_imm {dq : dfrac} (E : coPset) (imm : Z) (W : WORLD) (C : CmptName) (mshwmb_v mshwm_v : Z) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wsrc wdst : LWord)
    :
    decodeInstrW wi.(lw) = Store rdst (inr rsrc) imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

     {{{ interp W C wsrc
           ∗ interp W C wdst
           ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rsrc ↦ᵣ[th] wsrc
           ∗ rdst ↦ᵣ[th] wdst
           ∗ world_interp W C
           ∗ hwm_res_ftlr mshwmb_v mshwm_v
     }}}
       Instr Executable @[th] E
       {{{ retv, RET retv;
           ( ⌜ retv = FaultedV ⌝ ∗
             PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a ∗
             pc_a ↦ₐ{dq} wi ∗
             rsrc ↦ᵣ[th] wsrc ∗
             (rdst ↦ᵣ[th] wdst ∨ rdst ↦ᵣ[th] lclear_tag wdst) ∗
             world_interp W C ∗
             (∃ mshwm_v', hwm_res_ftlr mshwmb_v mshwm_v' ∗ ⌜(mshwm_v' <= mshwm_v)%Z⌝) ) ∨
          ( ∃ p g b e a π ea,
           ⌜ wdst = Cap p g b e a @@? π ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rsrc ↦ᵣ[th] wsrc
           ∗ rdst ↦ᵣ[th] Cap p g b e a @@? π
           ∗ world_interp W C
           ∗ (∃ mshwm_v', hwm_res_ftlr mshwmb_v mshwm_v' ∗ ⌜(mshwm_v' <= mshwm_v)%Z⌝)
           ∗ ⌜ writeAllowed p = true ⌝
           ∗ ⌜(a + imm)%a = Some ea⌝
           ∗ ⌜ea ∈ₐ [b, e) ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' Hsrc_null Hdst_null φ)
      "(#Hinterp_src & #Hinterp_dst & HPC & Hi & Hsrc & Hdst & Hworld_interp & Hhwm)".
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
      iApply (wp_store_fail_tag_imm _ _ _ _ _ _ _ _ _ _ _ _ (Cap⁻ p g b e a @@? π) with "[$HPC $Hi $Hmap]"); eauto.
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
    iDestruct (interp_cap_mem_or_exposed_mmio _ _ _ _ _ _ _ ea with "Hinterp_dst")
      as %[ [Hmmio Hnexp] | (Hexp & -> & _ & _)]; [by eapply writeAllowed_nonO|done| |].
    2: { (* An exposed device: the store succeeds on [mtimecmp] and changes no
            resource, or faults. *)
         (* A device store skips [hwm_store]: [Hhwm] is returned as is. *)
         rewrite /is_exposed_mmio_address in Hexp.
         iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %Hne]".
         iApply (wp_store_timedev (th := th) (CL := CL th) (pc_π := None) (W := emp%I) with "[$HPC $Hi $Hmap]");
           [exact Hdecode_wi | exact Hcorrect_pc
           | split_and!; [by rewrite llookup_reg_not_cnull // lookup_insert_ne // lookup_insert_eq
                         | exact Hea | exact Hp_stk_wa | exact Hwb]
           | intros v Hv; apply live_witness_no_id; by simplify_map_eq
           | exact Hexp | exact Hpca' |].
         iIntros "!>" (retv) "(Hout & Hi & Hmap & _)".
         iDestruct (regs_of_map_2 with "Hmap") as "[Hsrc Hdst]"; first done.
         iDestruct "Hout" as "[ [-> HPC] | [-> HPC] ]".
         - iApply "Hφ". iLeft. by iFrame.
         - iApply "Hφ"; iRight. iExists p, g, b, e, a, None, ea. iFrame "∗%".
           iPureIntro. split_and!; try done; try lia; solve_addr. }

    iDestruct (write_allowed_inv _ _ ea with "Hinterp_dst")
      as (p' P Hflows Hpers) "(#Hrel & Hzcond & #Hwcond & Hrcond)";[solve_addr|done|auto|..].
    iDestruct (open_world_interp_cases W C π ea p' P p g with "Hrel Hworld_interp")
      as "[(%ρ & %Hρwl & #Hpart & Hworld_interp & (%w & WorldRes)) | (%ι & -> & #Hq & Hworld_interp)]";
      [done|..].
    2: { (* A tombstone: the store faults on the tag. *)
         iDestruct (interp_cap_has_authority with "Hinterp_dst") as %Hauth;
           [by eapply writeAllowed_nonO|exact Hwb|].
         iApply (wp_store_quar_imm with "[$HPC $Hi $Hdst $Hq]"); [eauto|eauto|exact Hauth|done|].
         iNext. iIntros "(HPC & Hi & Hdst)".
         iApply "Hφ". iLeft. by iFrame. }
    iDestruct (pc_open_acc_forall with "Hpart WorldRes") as " [ (>Ha & Hinterp) WorldRes ]".

    iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ ea with "Hinterp_dst") as %Hnot_shadow;
      [by eapply writeAllowed_nonO|done|].
    iAssert (▷ pc_content ρ W C P (lstore_word p wsrc))%I as "Hinterp'".
    { iNext. by iApply (pc_content_wcond with "Hwcond Hinterp_src"). }
    iDestruct (region_cell_cases with "Ha") as "[Ha | (%zc & [-> [-> ->] ] & Hcell)]".
    - (* The region holds the points-to *)
      iDestruct (addr_key_pointsto with "Ha") as "[Ha Hshare]".
      iDestruct (key_share_deref with "Hshare") as (dw Hdw) "[Hdw Hshare]".
      iEval (rewrite deref_witness_res_deref_res -Hdw) in "Hdw".
      iApply (wp_store_success_reg_store_word_imm with "[$HPC $Hi $Hsrc $Hdst $Ha $Hdw]"); eauto.
      iNext; iIntros "(HPC & Hi & Hsrc & Hdst & Ha & Hdw)".
      iEval (rewrite Hdw -deref_witness_res_deref_res) in "Hdw".
      iDestruct ("Hshare" with "Hdw") as "Hshare".
      iDestruct (addr_key_pointsto_join with "Ha Hshare") as "Ha".
      iDestruct ("WorldRes" with "[Ha $Hinterp']") as "WorldRes";
        first by iApply region_cell_pointsto.
      iDestruct (pc_close with "Hworld_interp Hpart WorldRes") as "Hworld_interp"; first done.
      iApply "Hφ"; iRight. iExists p, g, b, e, a, π, ea. iFrame "∗%".
      iPureIntro. split_and!; try done; try lia; solve_addr.
    - (* The region holds a zone cell: the zone store *)
      iDestruct "Hhwm" as "([Hb Hh] & %Hord)".
      iAssert (deref_res None 1%Qp)%I as "Hdw"; first by rewrite /deref_res.
      iApply (wp_store_zone_reg_imm with "[$HPC $Hi $Hsrc $Hdst $Hcell $Hb $Hh $Hdw]"); eauto.
      iNext; iIntros "(HPC & Hi & Hsrc & Hdst & Ha & Hb & Hh & _)".
      iDestruct ("WorldRes" with "[Ha $Hinterp']") as "WorldRes";
        first by iApply region_cell_nonheap.
      iDestruct (pc_close with "Hworld_interp Hpart WorldRes") as "Hworld_interp"; first done.
      iDestruct (hwm_res_at_after with "[//] Hb Hh") as "Hhwm".
      iApply "Hφ"; iRight. iExists p, g, b, e, a, None, ea. iFrame "∗%".
      iPureIntro. split_and!; try done; try lia; solve_addr.
  Qed.

  Lemma wp_store_interp_cap_imm {dq : dfrac} (E : coPset) (imm : Z) (W : WORLD) (C : CmptName) (mshwmb_v mshwm_v : Z) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId)
    (wi wsrc : LWord)
    :
    decodeInstrW wi.(lw) = Store rdst (inr rsrc) imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

     {{{ interp W C wsrc
           ∗ interp W C (Cap p g b e a @@? π)
           ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rsrc ↦ᵣ[th] wsrc
           ∗ rdst ↦ᵣ[th] (Cap p g b e a @@? π)
           ∗ world_interp W C
           ∗ hwm_res_ftlr mshwmb_v mshwm_v
     }}}
       Instr Executable @[th] E
       {{{ retv, RET retv;
           ( ⌜ retv = FaultedV ⌝ ∗
             PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a ∗
             pc_a ↦ₐ{dq} wi ∗
             rsrc ↦ᵣ[th] wsrc ∗
             (rdst ↦ᵣ[th] Cap p g b e a @@? π ∨ rdst ↦ᵣ[th] lclear_tag (Cap p g b e a @@? π)) ∗
             world_interp W C ∗
             (∃ mshwm_v', hwm_res_ftlr mshwmb_v mshwm_v' ∗ ⌜(mshwm_v' <= mshwm_v)%Z⌝) ) ∨
          (∃ ea, ⌜ retv = NextIV ⌝
           ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rsrc ↦ᵣ[th] wsrc
           ∗ rdst ↦ᵣ[th] Cap p g b e a @@? π
           ∗ world_interp W C
           ∗ (∃ mshwm_v', hwm_res_ftlr mshwmb_v mshwm_v' ∗ ⌜(mshwm_v' <= mshwm_v)%Z⌝)
           ∗ ⌜ writeAllowed p = true ⌝
           ∗ ⌜(a + imm)%a = Some ea⌝
           ∗ ⌜ea ∈ₐ [b, e) ⌝
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

  Lemma wp_store_interp_z_imm {dq : dfrac} (E : coPset) (imm : Z) (W : WORLD) (C : CmptName) (mshwmb_v mshwm_v : Z) (rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wdst : LWord) (z : Z)
    :
    decodeInstrW wi.(lw) = Store rdst (inl z) imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rdst ≠ cnull ->

     {{{ interp W C wdst
           ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rdst ↦ᵣ[th] wdst
           ∗ world_interp W C
           ∗ hwm_res_ftlr mshwmb_v mshwm_v
     }}}
       Instr Executable @[th] E
       {{{ retv, RET retv;
           ( ⌜ retv = FaultedV ⌝ ∗
             PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a ∗
             pc_a ↦ₐ{dq} wi ∗
             (rdst ↦ᵣ[th] wdst ∨ rdst ↦ᵣ[th] lclear_tag wdst) ∗
             world_interp W C ∗
             (∃ mshwm_v', hwm_res_ftlr mshwmb_v mshwm_v' ∗ ⌜(mshwm_v' <= mshwm_v)%Z⌝) ) ∨
          ( ∃ p g b e a π ea,
           ⌜ wdst = Cap p g b e a @@? π ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rdst ↦ᵣ[th] Cap p g b e a @@? π
           ∗ world_interp W C
           ∗ (∃ mshwm_v', hwm_res_ftlr mshwmb_v mshwm_v' ∗ ⌜(mshwm_v' <= mshwm_v)%Z⌝)
           ∗ ⌜ writeAllowed p ⌝
           ∗ ⌜(a + imm)%a = Some ea⌝
           ∗ ⌜ea ∈ₐ [b, e) ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' Hdst_null φ)
      "(#Hinterp_dst & HPC & Hi & Hdst & Hworld_interp & Hhwm)".
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
      iApply (wp_store_fail_tag_imm _ _ _ _ _ _ _ _ _ _ _ _ (Cap⁻ p g b e a @@? π) with "[$HPC $Hi $Hmap]"); eauto.
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
    iDestruct (interp_cap_mem_or_exposed_mmio _ _ _ _ _ _ _ ea with "Hinterp_dst")
      as %[ [Hmmio Hnexp] | (Hexp & -> & _ & _)]; [by eapply writeAllowed_nonO|done| |].
    2: { (* An exposed device: the store succeeds on [mtimecmp] and changes no
            resource, or faults. *)
         (* A device store skips [hwm_store]: [Hhwm] is returned as is. *)
         rewrite /is_exposed_mmio_address in Hexp.
         iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
         iApply (wp_store_timedev (th := th) (CL := CL th) (pc_π := None) (W := emp%I) with "[$HPC $Hi $Hmap]");
           [exact Hdecode_wi | exact Hcorrect_pc
           | split_and!; [by rewrite llookup_reg_not_cnull // lookup_singleton_eq
                         | exact Hea | exact Hstore_src | exact Hwb]
           | intros v Hv; apply live_witness_no_id; by simplify_map_eq
           | exact Hexp | exact Hpca' |].
         iIntros "!>" (retv) "(Hout & Hi & Hmap & _)".
         iDestruct (regs_of_map_1 with "Hmap") as "Hdst".
         iDestruct "Hout" as "[ [-> HPC] | [-> HPC] ]".
         - iApply "Hφ". iLeft. by iFrame.
         - iApply "Hφ"; iRight. iExists p, g, b, e, a, None, ea. iFrame "∗%".
           iPureIntro. split_and!; try done; try lia; solve_addr. }

    iDestruct (write_allowed_inv _ _ ea with "Hinterp_dst")
      as (p' P Hflows Hpers) "(#Hrel & Hzcond & #Hwcond & Hrcond)";[solve_addr|done|auto|..].
    iDestruct (open_world_interp_cases W C π ea p' P p g with "Hrel Hworld_interp")
      as "[(%ρ & %Hρwl & #Hpart & Hworld_interp & (%w & WorldRes)) | (%ι & -> & #Hq & Hworld_interp)]";
      [done|..].
    2: { (* A tombstone: the store faults on the tag. *)
         iDestruct (interp_cap_has_authority with "Hinterp_dst") as %Hauth;
           [by eapply writeAllowed_nonO|exact Hwb|].
         iApply (wp_store_quar_imm with "[$HPC $Hi $Hdst $Hq]"); [eauto|eauto|exact Hauth|done|].
         iNext. iIntros "(HPC & Hi & Hdst)".
         iApply "Hφ". iLeft. by iFrame. }
    iDestruct (pc_open_acc_forall with "Hpart WorldRes") as " [ (>Ha & Hinterp) WorldRes ]".

    iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ ea with "Hinterp_dst") as %Hnot_shadow;
      [by eapply writeAllowed_nonO|done|].
    iAssert (▷ pc_content ρ W C P (WInt z))%I as "Hinterp'".
    { iNext. by iApply pc_content_wcond_z. }
    iDestruct (region_cell_cases with "Ha") as "[Ha | (%zc & [-> [-> ->] ] & Hcell)]".
    - (* The region holds the points-to *)
      iDestruct (addr_key_pointsto with "Ha") as "[Ha Hshare]".
      iDestruct (key_share_deref with "Hshare") as (dw Hdw) "[Hdw Hshare]".
      iEval (rewrite deref_witness_res_deref_res -Hdw) in "Hdw".
      iApply (wp_store_success_z_imm with "[$HPC $Hi $Hdst $Ha $Hdw]"); eauto.
      iNext; iIntros "(HPC & Hi & Hdst & Ha & Hdw)".
      iEval (rewrite Hdw -deref_witness_res_deref_res) in "Hdw".
      iDestruct ("Hshare" with "Hdw") as "Hshare".
      iDestruct (addr_key_pointsto_join with "Ha Hshare") as "Ha".
      iDestruct ("WorldRes" with "[Ha $Hinterp']") as "WorldRes";
        first by iApply region_cell_pointsto.
      iDestruct (pc_close with "Hworld_interp Hpart WorldRes") as "Hworld_interp"; first done.
      iApply "Hφ"; iRight. iExists p, g, b, e, a, π, ea. iFrame "∗%".
      iPureIntro. split_and!; try done; try lia; solve_addr.
    - (* The region holds a zone cell: the zone store *)
      iDestruct "Hhwm" as "([Hb Hh] & %Hord)".
      iAssert (deref_res None 1%Qp)%I as "Hdw"; first by rewrite /deref_res.
      iApply (wp_store_zone_z_imm with "[$HPC $Hi $Hdst $Hcell $Hb $Hh $Hdw]"); eauto.
      iNext; iIntros "(HPC & Hi & Hdst & Ha & Hb & Hh & _)".
      iDestruct ("WorldRes" with "[Ha $Hinterp']") as "WorldRes";
        first by iApply region_cell_nonheap.
      iDestruct (pc_close with "Hworld_interp Hpart WorldRes") as "Hworld_interp"; first done.
      iDestruct (hwm_res_at_after with "[//] Hb Hh") as "Hhwm".
      iApply "Hφ"; iRight. iExists p, g, b, e, a, None, ea. iFrame "∗%".
      iPureIntro. split_and!; try done; try lia; solve_addr.
  Qed.

  Lemma wp_store_interp_z_cap_imm {dq : dfrac} (E : coPset) (imm : Z) (W : WORLD) (C : CmptName) (mshwmb_v mshwm_v : Z) (rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId)
    (wi : LWord) (z : Z)
    :
    decodeInstrW wi.(lw) = Store rdst (inl z) imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rdst ≠ cnull ->

     {{{  interp W C (Cap p g b e a @@? π)
           ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rdst ↦ᵣ[th] (Cap p g b e a @@? π)
           ∗ world_interp W C
           ∗ hwm_res_ftlr mshwmb_v mshwm_v
     }}}
       Instr Executable @[th] E
       {{{ retv, RET retv;
           ( ⌜ retv = FaultedV ⌝ ∗
             PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a ∗
             pc_a ↦ₐ{dq} wi ∗
             (rdst ↦ᵣ[th] Cap p g b e a @@? π ∨ rdst ↦ᵣ[th] lclear_tag (Cap p g b e a @@? π)) ∗
             world_interp W C ∗
             (∃ mshwm_v', hwm_res_ftlr mshwmb_v mshwm_v' ∗ ⌜(mshwm_v' <= mshwm_v)%Z⌝) ) ∨
          (∃ ea, ⌜ retv = NextIV ⌝
           ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rdst ↦ᵣ[th] Cap p g b e a @@? π
           ∗ world_interp W C
           ∗ (∃ mshwm_v', hwm_res_ftlr mshwmb_v mshwm_v' ∗ ⌜(mshwm_v' <= mshwm_v)%Z⌝)
           ∗ ⌜ writeAllowed p ⌝
           ∗ ⌜(a + imm)%a = Some ea⌝
           ∗ ⌜ea ∈ₐ [b, e) ⌝
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

  Lemma wp_unseal_unknown' {dq : dfrac} E pc_p pc_g pc_b pc_e pc_a pc_a' wi r1 r2 wsealr wsealed  :
    decodeInstrW wi.(lw) = UnSeal r1 r1 r2 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{  PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a
          ∗ pc_a ↦ₐ{dq} wi
          ∗ r1 ↦ᵣ[th] wsealr
          ∗ r2 ↦ᵣ[th] wsealed
    }}}
      Instr Executable @[th] E
      {{{ retv, RET retv;
          (⌜ retv = NextIV ⌝
              ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ{dq} wi
              ∗ r1 ↦ᵣ[th] lclear_tag wsealed
              ∗ r2 ↦ᵣ[th] wsealed
              ∗ ⌜ is_sealr wsealr.(lw) && is_sealed wsealed.(lw) = false ⌝)
          ∨ (∃ psr gsr bsr esr asr πsr ot wsb π,
              ⌜ retv = NextIV ⌝
              ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ{dq} wi
              ∗ r1 ↦ᵣ[th] WSealable (unseal_sb gsr wsb) @@? π
              ∗ r2 ↦ᵣ[th] wsealed
              ∗ ⌜ wsealr = SealRange psr gsr bsr esr asr @@? πsr ⌝
              ∗ ⌜ permit_unseal psr = true ⌝
              ∗ ⌜ wsealed = WSealed ot wsb @@? π ⌝
              ∗ ⌜ get_tag_sealable wsb = true ⌝
              ∗ ⌜ withinBounds bsr esr ot = true ⌝ )
          ∨ ∃ tsr psr gsr bsr esr asr πsr ot sb π,
              ⌜ retv = NextIV ⌝
              ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a'
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
    iApply (wp_regs_next_2 _ _ _ _ _ _ _ _ _ _ _ r1 wsealr r2 wsealed (unseal_word wsealr wsealed)
              with "[$HPC $Hpc_a $Hr1 $Hr2]");
      [exact Hinstr | rewrite /regs_instr_ok; split; [by apply sw_of_none | solve_writes_mshwmb] | exact Hvpc | exact Hpc_a'
      | exact Hr1_null | |].
    { intros Hne. apply unseal_next_ok; rewrite llookup_reg_not_cnull //; by simplify_map_eq. }
    iIntros "!> (HPC & Hpc_a & Hr1 & Hr2)". iApply "Hφ".
    destruct (is_sealr wsealr.(lw) && is_sealed wsealed.(lw)) eqn:Hkind.
    2: { iLeft. rewrite unseal_word_not_sealed //. iFrame; done. }
    destruct wsealr as [ [| [|tsr psr gsr bsr esr asr] | | ] πsr]; cbn in Hkind; try discriminate.
    destruct wsealed as [ [| | | ot sb] π]; cbn in Hkind; try discriminate.
    rewrite /unseal_word /=.
    destruct (tsr && get_tag_sealable sb && permit_unseal psr && withinBounds bsr esr ot) eqn:Hvalid.
    - iRight; iLeft.
      apply andb_prop in Hvalid as [ [ [-> Htag]%andb_prop Hperm]%andb_prop Hwb].
      rewrite and_tag_sealable_true.
      iExists psr, gsr, bsr, esr, asr, πsr, ot, sb, π. iFrame; done.
    - iRight; iRight. rewrite and_tag_sealable_false.
      iExists tsr, psr, gsr, bsr, esr, asr, πsr, ot, sb, π. iFrame; done.
  Qed.

  Lemma wp_unseal_unknown_sealed {dq : dfrac} E pc_p pc_g pc_b pc_e pc_a pc_a' wi r1 r2 psr gsr bsr esr asr wsealed  :
    decodeInstrW wi.(lw) = UnSeal r2 r1 r2 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    permit_unseal psr = true ->
    (bsr <= asr < esr)%ot ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{  PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a
          ∗ pc_a ↦ₐ{dq} wi
          ∗ r1 ↦ᵣ[th] SealRange psr gsr bsr esr asr
          ∗ r2 ↦ᵣ[th] wsealed
    }}}
      Instr Executable @[th] E
      {{{ retv, RET retv;
          (⌜ retv = NextIV ⌝
              ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ{dq} wi
              ∗ r1 ↦ᵣ[th] SealRange psr gsr bsr esr asr
              ∗ r2 ↦ᵣ[th] lclear_tag wsealed
              ∗ ⌜ is_sealed wsealed.(lw) = false ⌝)
          ∨ (∃ ot wsb π,
              ⌜ retv = NextIV ⌝
              ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ{dq} wi
              ∗ r1 ↦ᵣ[th] SealRange psr gsr bsr esr asr
              ∗ r2 ↦ᵣ[th] WSealable (unseal_sb gsr wsb) @@? π
              ∗ ⌜ wsealed = WSealed ot wsb @@? π ⌝
              ∗ ⌜ get_tag_sealable wsb = true ⌝
              ∗ ⌜ withinBounds bsr esr ot = true ⌝ )
          ∨ ∃ ot sb π,
              ⌜ retv = NextIV ⌝
              ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ{dq} wi
              ∗ r1 ↦ᵣ[th] SealRange psr gsr bsr esr asr
              ∗ r2 ↦ᵣ[th] WSealable (clear_tag_sealable (unseal_sb gsr sb)) @@? π
              ∗ ⌜ wsealed = WSealed ot sb @@? π ⌝
              ∗ ⌜ get_tag_sealable sb && withinBounds bsr esr ot = false ⌝
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpc_a' Hpsr Hsr Hr1_null Hr2_null ϕ) "(HPC & Hpc_a & Hr1 & Hr2) Hφ".
    iApply (wp_regs_next_2 _ _ _ _ _ _ _ _ _ _ _ r2 wsealed r1 (SealRange psr gsr bsr esr asr)
              (unseal_word (SealRange psr gsr bsr esr asr) wsealed)
              with "[$HPC $Hpc_a $Hr2 $Hr1]");
      [exact Hinstr | rewrite /regs_instr_ok; split; [by apply sw_of_none | solve_writes_mshwmb] | exact Hvpc | exact Hpc_a'
      | exact Hr2_null | |].
    { intros Hne. apply unseal_next_ok; rewrite llookup_reg_not_cnull //; by simplify_map_eq. }
    iIntros "!> (HPC & Hpc_a & Hr2 & Hr1)". iApply "Hφ".
    destruct wsealed as [ [z | sb0 | k t p g b e a | ot sb] π].
    1-3: iLeft; rewrite unseal_word_not_sealed //; iFrame; done.
    rewrite /unseal_word /= Hpsr andb_true_r.
    destruct (get_tag_sealable sb && withinBounds bsr esr ot) eqn:Hvalid.
    - iRight; iLeft. apply andb_prop in Hvalid as [Htag Hwb]. rewrite and_tag_sealable_true.
      iExists ot, sb, π. iFrame; done.
    - iRight; iRight. rewrite and_tag_sealable_false.
      iExists ot, sb, π. iFrame; done.
  Qed.

  (** [UnSeal r1 r1 r2], the key in [r1], which receives the result: the
      three outcomes of [wp_unseal_unknown_sealed]. *)
  Lemma wp_unseal_unknown_sealed_dst_key {dq : dfrac} E pc_p pc_g pc_b pc_e pc_a pc_a' wi r1 r2
      psr gsr bsr esr asr wsealed :
    decodeInstrW wi.(lw) = UnSeal r1 r1 r2 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    permit_unseal psr = true →
    (bsr <= asr < esr)%ot →
    r1 ≠ r2 →
    r1 ≠ cnull →
    r2 ≠ cnull →

    {{{ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a ∗
        pc_a ↦ₐ{dq} wi ∗
        r1 ↦ᵣ[th] SealRange psr gsr bsr esr asr ∗
        r2 ↦ᵣ[th] wsealed }}}
      Instr Executable @[th] E
    {{{ retv, RET retv;
        (⌜retv = NextIV⌝ ∗
         PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a' ∗
         pc_a ↦ₐ{dq} wi ∗
         r1 ↦ᵣ[th] lclear_tag wsealed ∗
         r2 ↦ᵣ[th] wsealed ∗
         ⌜is_sealed wsealed.(lw) = false⌝) ∨
        (∃ ot wsb π,
           ⌜retv = NextIV⌝ ∗
           PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a' ∗
           pc_a ↦ₐ{dq} wi ∗
           r1 ↦ᵣ[th] WSealable (unseal_sb gsr wsb) @@? π ∗
           r2 ↦ᵣ[th] wsealed ∗
           ⌜wsealed = WSealed ot wsb @@? π⌝ ∗
           ⌜get_tag_sealable wsb = true⌝ ∗
           ⌜withinBounds bsr esr ot = true⌝) ∨
        ∃ ot sb π,
          ⌜retv = NextIV⌝ ∗
          PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a' ∗
          pc_a ↦ₐ{dq} wi ∗
          r1 ↦ᵣ[th] WSealable (clear_tag_sealable (unseal_sb gsr sb)) @@? π ∗
          r2 ↦ᵣ[th] wsealed ∗
          ⌜wsealed = WSealed ot sb @@? π⌝ ∗
          ⌜get_tag_sealable sb && withinBounds bsr esr ot = false⌝ }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpc_a' Hpsr Hsr Hr12 Hr1_null Hr2_null φ) "(HPC & Hpc_a & Hr1 & Hr2) Hφ".
    iApply (wp_regs_next_2 _ _ _ _ _ _ _ _ _ _ _ r1 (SealRange psr gsr bsr esr asr) r2 wsealed
              (unseal_word (SealRange psr gsr bsr esr asr) wsealed)
              with "[$HPC $Hpc_a $Hr1 $Hr2]");
      [exact Hinstr | rewrite /regs_instr_ok; split; [by apply sw_of_none | solve_writes_mshwmb] | exact Hvpc | exact Hpc_a'
      | exact Hr1_null | |].
    { intros Hne. apply unseal_next_ok; rewrite llookup_reg_not_cnull //; by simplify_map_eq. }
    iIntros "!> (HPC & Hpc_a & Hr1 & Hr2)". iApply "Hφ".
    destruct wsealed as [ [z | sb0 | k t p g b e a | ot sb] π].
    1-3: iLeft; rewrite unseal_word_not_sealed //; iFrame; done.
    rewrite /unseal_word /= Hpsr andb_true_r.
    destruct (get_tag_sealable sb && withinBounds bsr esr ot) eqn:Hvalid.
    - iRight; iLeft. apply andb_prop in Hvalid as [Htag Hwb]. rewrite and_tag_sealable_true.
      iExists ot, sb, π. iFrame; done.
    - iRight; iRight. rewrite and_tag_sealable_false.
      iExists ot, sb, π. iFrame; done.
  Qed.
  (** A load through a valid capability: the world supplies the quarantine
      witness of the loaded word, which makes the loaded word valid. *)
  Lemma wp_load_interp_imm (E : coPset) (imm : Z) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wsrc wdst : LWord)
    :
    decodeInstrW wi.(lw) = CLoad rdst rsrc imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

     {{{ thread_in th C
           ∗ interp W C wsrc
           ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ[th] wsrc
           ∗ rdst ↦ᵣ[th] wdst
           ∗ world_interp W C
     }}}
       Instr Executable @[th] E
       {{{ retv, RET retv;
           ( ⌜ retv = FaultedV ⌝ ∗
             PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a ∗
             pc_a ↦ₐ wi ∗
             (rsrc ↦ᵣ[th] wsrc ∨ rsrc ↦ᵣ[th] lclear_tag wsrc) ∗
             rdst ↦ᵣ[th] wdst ∗
             world_interp W C ) ∨
          ( ∃ p g b e a π ea wload,
           ⌜ wsrc = Cap p g b e a @@? π ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ[th] Cap p g b e a @@? π
           ∗ rdst ↦ᵣ[th] wload ∗ interp W C wload
           ∗ world_interp W C
           ∗ ⌜ readAllowed p = true ⌝
           ∗ ⌜(a + imm)%a = Some ea⌝
           ∗ ⌜ea ∈ₐ [b, e) ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' Hsrc_null Hdst_null φ)
      "(#Hth & #Hinterp_src & HPC & Hi & Hsrc & Hdst & Hworld_interp)".
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
      iApply (wp_load_fail_tag_imm _ _ _ _ _ _ _ _ _ _ _ _ (Cap⁻ p g b e a @@? π) with "[$HPC $Hi $Hmap]"); eauto.
      { rewrite llookup_reg_not_cnull //. by simplify_map_eq. }
      iNext; iIntros "(HPC & Hi & Hmap)".
      iDestruct (regs_of_map_2 with "Hmap") as "[Hdst Hsrc]"; first done.
      iApply "Hφ". iLeft. by iFrame.
    }

    destruct (a + imm)%a as [ea|] eqn:Hea; cycle 1.
    {
      iDestruct (map_of_regs_2 with "Hdst Hsrc") as "[Hmap %Hne]".
      iApply (wp_load_fail_addr_imm _ _ _ _ _ _ _ _ _ _ _ _ (Cap p g b e a @@? π) with "[$HPC $Hi $Hmap]"); eauto.
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
    iDestruct (interp_cap_mem_or_exposed_mmio _ _ _ _ _ _ _ ea with "Hinterp_src")
      as %[ [Hmmio Hnexp] | (Hexp & -> & _ & _)]; [by eapply readAllowed_nonO|done| |].
    2: { (* An exposed device: the load gives an integer. *)
         rewrite /is_exposed_mmio_address in Hexp.
         iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %Hsrc_dst]".
         iDestruct (memMap_resource_1_dq with "Hi") as "Hmem".
         iApply (wp_load_success_timedev_imm (th := th) (CL := CL th) E pc_p pc_g pc_b pc_e pc_a
                   None rdst rsrc imm wi _ _ (DfracOwn 1) p g b e a ea
                   with "[$HPC $Hmem $Hmap]").
         { exact Hdecode_wi. }
         { exact Hcorrect_pc. }
         { rewrite /regs_of /operands_of !dom_insert_L; set_solver+. }
         { by simplify_map_eq. }
         { split_and!; [|done..].
           rewrite llookup_reg_not_cnull //. by simplify_map_eq. }
         { intros v Hv. rewrite llookup_reg_not_cnull // in Hv. by simplify_map_eq. }
         { exact Hexp. }
         { by rewrite /incrementPC /incrementPC_gen Hpca'. }
         iNext. iIntros (z) "(HPC & Hmem & Hmap)".
         iDestruct (memMap_resource_1_dq with "Hmem") as "Hi".
         rewrite linsert_reg_not_cnull // (insert_insert_ne _ rdst rsrc) // insert_insert_eq.
         iDestruct (regs_of_map_2 with "Hmap") as "(Hsrc & Hdst)"; first done.
         iApply "Hφ"; iRight. iExists p, g, b, e, a, None, ea, (lword_of_word (WInt z)).
         iFrame "∗%". iSplit; first done. iSplit; first done. iApply interp_int. }
    iDestruct (read_allowed_inv _ _ ea with "Hth Hinterp_src")
      as (p' P Hflows Hpers) "(#Hrel & Hzcond & #Hrcond & Hwcond)";[solve_addr|done|auto|..].
    iDestruct (open_world_interp_cases W C π ea p' P p g with "Hrel Hworld_interp")
      as "[(%ρ & %Hρwl & #Hpart & Hworld_interp & (%w & WorldRes)) | (%ι & -> & #Hq & Hworld_interp)]";
      [done|..].
    2: { (* A tombstone: the load faults on the tag. *)
         iDestruct (interp_cap_has_authority with "Hinterp_src") as %Hauth;
           [by eapply readAllowed_nonO|exact Hwb|].
         iApply (wp_load_quar_imm with "[$HPC $Hi $Hsrc $Hq]"); [eauto|eauto|exact Hauth|done|].
         iNext. iIntros "(HPC & Hi & Hsrc)".
         iApply "Hφ". iLeft. by iFrame. }
    iDestruct (pc_open_acc with "WorldRes") as "[ (>Ha & Hinterp) WorldRes ]".
    iDestruct (region_cell_cases with "Ha") as "[Ha | (%z & [-> [-> ->] ] & Hcell)]"; cycle 1.
    { (* The region holds a zone cell, which holds an integer: the load reads half of it *)
      iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ ea with "Hinterp_src") as %Hnot_shadow;
        [by eapply readAllowed_nonO|done|].
      iDestruct (zone_cell_v_unfold with "Hcell") as "[Htok Hhalf]".
      iApply (wp_load_witness_imm_one_inbounds_dq with "[$HPC $Hi $Hdst $Hsrc $Hhalf]"); eauto.
      iNext; iIntros "(HPC & Hi & Hdst & Hsrc & Hhalf)".
      iDestruct ("WorldRes" with "[Htok Hhalf $Hinterp]") as "WorldRes".
      { iApply region_cell_zone. rewrite zone_cell_v_unfold. iFrame. }
      iDestruct (pc_close with "Hworld_interp Hpart WorldRes") as "Hworld_interp"; first done.
      iApply "Hφ"; iRight. iExists p, g, b, e, a, None, ea, _. iFrame "∗%".
      iSplit; first done. iSplit; first done. iApply interp_lload_word_int. }
    iDestruct (addr_key_pointsto with "Ha") as "[Ha Hshare]".

    iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ ea with "Hinterp_src") as %Hnot_shadow;
      [by eapply readAllowed_nonO|done|].
    iPoseProof load_witness_plain_intro as "Hwit".
    iDestruct (address_neq with "Ha Hi") as %Hne.
    (* CLoad rdst rsrc imm. *)
    iDestruct (key_share_deref with "Hshare") as (dw Hdw) "[Hdw Hshare]".
    iApply (wp_load_choice_next_2 (th := th) (CL := CL th) (pc_π := None)
              (W := (load_witness_res LoadPlain ∗ deref_witness_res dw)%I)
              with "[$HPC $Hi $Hdst $Hsrc $Ha $Hwit $Hdw]");
      [exact Hdecode_wi | solve_mem_instr_ok | apply CLoad_member | apply cload_next_ok
      | apply load_choice_sep_l, load_choice_witness
      | apply live_witness_sep_r, deref_witness_live; exact Hdw
      | exact Hcorrect_pc | exact Hpca' | exact Hdst_null | exact Hsrc_null | done | exact Hea
      | exact Hra_src | exact Hwb | done |].
    iIntros "!>" (loadv') "(%Hpost & HPC & Hi & Hdst & Hsrc & Ha & [_ Hdw])".
    iDestruct ("Hshare" with "Hdw") as "Hshare".
    pose proof (pc_content_persistent ρ W C P w Hpers).
    iDestruct "Hinterp" as "#HφV".
    iDestruct (pc_content_rcond with "Hrcond HφV") as "#Hnormal_p'".
    iAssert (interp_in_mem p W C w)%I as "#Hnormal".
    { iEval (rewrite /interp_in_mem /= /interp_in_mem_pre).
      iApply (interp_weakening_word_load W C p p' w with "Hth"); first exact Hflows.
      iEval (rewrite /interp_in_mem_pre) in "Hnormal_p'".
      iExact "Hnormal_p'". }
    iDestruct (interp_in_mem_load_post with "Hnormal") as "#Hload_interp"; first exact Hpost.
    iDestruct (addr_key_pointsto_join with "Ha Hshare") as "Ha".
    iDestruct ("WorldRes" with "[Ha $HφV]") as "WorldRes"; first by iApply region_cell_pointsto.
    iDestruct (pc_close with "Hworld_interp Hpart WorldRes") as "Hworld_interp"; first done.
    iApply "Hφ"; iRight. iExists p, g, b, e, a, π, ea, loadv'. iFrame "∗#%".
    iPureIntro. split; first done. solve_addr.
  Qed.

  (** The fault cases of [wp_load_interp_same_open]: the opsem gives the load as
      a fault, and the registers and the memory are unchanged. *)
  #[local] Ltac load_same_fault :=
    iApply (wp_instr_faulted_1 with "[$HPC $Hsrc $Hi]"); [done | done | | ];
    [ intros ? ? ? ? ? s1 Hrr; rewrite /exec /= /lookup_reg Hrr /= decide_False //;
      destruct s1; cbn; try done
    | iIntros "!> (HPC & Hsrc & Hi)"; iApply "Hφ"; iLeft; by iFrame ].

  (** The key that a load through [w] reads, when it reads, is not in [s]. *)
  Definition load_key_closed (w : LWord) (s : list LAddr) : Prop :=
    ∀ p g b e a, w.(lw) = Cap p g b e a → withinBounds b e a = true →
      addr_key w.(lprov) a ∉ s.

  (** A load through a safe word into the register that holds it, over a
      world open on [s], when the loaded key is not in [s]: it faults, or
      it loads a safe word. *)
  Lemma wp_load_interp_same_open (E : coPset) (W : WORLD) (C : CmptName) (s : list LAddr)
    (r : RegName) (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wsrc : LWord) (dq : dfrac) :
    decodeInstrW wi.(lw) = CLoad r r 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r ≠ cnull →
    load_key_closed wsrc s →
    {{{ thread_in th C ∗ interp W C wsrc ∗
        PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a ∗
        pc_a ↦ₐ{dq} wi ∗
        r ↦ᵣ[th] wsrc ∗
        world_interp_open W C s }}}
      Instr Executable @[th] E
    {{{ retv, RET retv;
        ( ⌜retv = FaultedV⌝ ∗
          PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a ∗
          pc_a ↦ₐ{dq} wi ∗
          (r ↦ᵣ[th] wsrc ∨ r ↦ᵣ[th] lclear_tag wsrc) ∗
          world_interp_open W C s ) ∨
        ( ∃ wload,
          ⌜retv = NextIV⌝ ∗
          PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a' ∗
          pc_a ↦ₐ{dq} wi ∗
          r ↦ᵣ[th] wload ∗ interp W C wload ∗
          world_interp_open W C s ) }}}.
  Proof.
    iIntros (Hdecode Hcorrect_pc Hpca' Hr Hclosed φ)
      "(#Hth & #Hinterp_src & HPC & Hi & Hsrc & Hworld_interp) Hφ".
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
    iDestruct (interp_cap_mem_or_exposed_mmio _ _ _ _ _ _ _ a with "Hinterp_src")
      as %[ [Hmmio Hnexp] | (Hexp & -> & _ & _)]; [by eapply readAllowed_nonO|done| |].
    2: { (* An exposed device: the load gives an integer. *)
         rewrite /is_exposed_mmio_address in Hexp.
         iDestruct (map_of_regs_1 with "Hsrc") as "Hmap".
         iDestruct (memMap_resource_1_dq with "Hi") as "Hmem".
         iApply (wp_load_success_timedev (th := th) (CL := CL th) E pc_p pc_g pc_b pc_e pc_a
                   None r r wi _ _ dq p g b e a
                   with "[$HPC $Hmem $Hmap]").
         { exact Hdecode. }
         { exact Hcorrect_pc. }
         { rewrite /regs_of /operands_of dom_insert_L; set_solver+. }
         { by simplify_map_eq. }
         { split_and!; [|done..].
           rewrite llookup_reg_not_cnull //. by simplify_map_eq. }
         { intros v Hv. rewrite llookup_reg_not_cnull // in Hv. by simplify_map_eq. }
         { exact Hexp. }
         { by rewrite /incrementPC /incrementPC_gen Hpca'. }
         iNext. iIntros (z) "(HPC & Hmem & Hmap)".
         iDestruct (memMap_resource_1_dq with "Hmem") as "Hi".
         rewrite linsert_reg_not_cnull // insert_insert_eq.
         iDestruct (regs_of_map_1 with "Hmap") as "Hsrc".
         iApply "Hφ"; iRight. iExists (lword_of_word (WInt z)).
         iFrame "∗%". iSplit; first done. iApply interp_int. }
    iDestruct (read_allowed_inv _ _ a with "Hth Hinterp_src")
      as (p' P Hflows Hpers) "(#Hrel & Hzcond & #Hrcond & Hwcond)"; [solve_addr | done | auto |..].
    iDestruct (open_world_interp_next_cases W C s π a p' P p g
                with "Hrel Hworld_interp")
      as "[(%ρ & %Hρwl & #Hpart & Hworld_interp & (%w & WorldRes)) | (%ι & -> & #Hq & Hworld_interp)]";
      [done | exact Hnin_s |..].
    2: { (* A tombstone: the load faults on the tag. *)
         iDestruct (interp_cap_has_authority with "Hinterp_src") as %Hauth;
           [by eapply readAllowed_nonO|exact Hwb|].
         iApply (wp_load_quar_imm with "[$HPC $Hi $Hsrc $Hq]"); [eauto|eauto|exact Hauth|done|].
         iNext. iIntros "(HPC & Hi & Hsrc)".
         iApply "Hφ". iLeft. by iFrame. }
    iDestruct (pc_open_acc with "WorldRes") as "[ (>Ha & Hinterp) WorldRes ]".
    iDestruct (region_cell_cases with "Ha") as "[Ha | (%z & [-> [-> ->] ] & Hcell)]"; cycle 1.
    { (* The region holds a zone cell, which holds an integer: the load reads half of it *)
      iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ a with "Hinterp_src") as %Hnot_shadow;
        [by eapply readAllowed_nonO|done|].
      iDestruct (zone_cell_v_unfold with "Hcell") as "[Htok Hhalf]".
      iApply (wp_load_witness_imm_same_inbounds_dq with "[$HPC $Hi $Hsrc $Hhalf]"); eauto.
      { by rewrite addr_add_0. }
      iNext; iIntros "(HPC & Hi & Hsrc & Hhalf)".
      iDestruct ("WorldRes" with "[Htok Hhalf $Hinterp]") as "WorldRes".
      { iApply region_cell_zone. rewrite zone_cell_v_unfold. iFrame. }
      iDestruct (pc_close_next with "Hworld_interp Hpart WorldRes") as "Hworld_interp";
        [exact Hnin_s|done|].
      iApply "Hφ"; iRight. iExists _. iFrame "∗%".
      iSplit; first done. iApply interp_lload_word_int. }
    iDestruct (addr_key_pointsto with "Ha") as "[Ha Hshare]".
    iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ a with "Hinterp_src") as %Hnot_shadow;
      [by eapply readAllowed_nonO | done |].
    iPoseProof load_witness_plain_intro as "Hwit".
    iDestruct (pointsto_ne with "Ha Hi") as %Hne.
    iDestruct (key_share_deref with "Hshare") as (dw Hdw) "[Hdw Hshare]".
    (* CLoad r r 0. *)
    iApply (wp_load_choice_next_1 (th := th) (CL := CL th) (pc_π := None)
              (W := (load_witness_res LoadPlain ∗ deref_witness_res dw)%I)
              with "[$HPC $Hi $Hsrc $Ha $Hwit $Hdw]");
      [exact Hdecode | solve_mem_instr_ok | apply CLoad_member | apply cload_next_ok
      | apply load_choice_sep_l, load_choice_witness
      | apply live_witness_sep_r, deref_witness_live; exact Hdw
      | exact Hcorrect_pc | exact Hpca' | exact Hr | done | apply addr_add_0 | exact Hra
      | exact Hwb | done |].
    iIntros "!>" (loadv') "(%Hpost & HPC & Hi & Hsrc & Ha & [_ Hdw])".
    iDestruct ("Hshare" with "Hdw") as "Hshare".
    pose proof (pc_content_persistent ρ W C P w Hpers).
    iDestruct "Hinterp" as "#HφV".
    iDestruct (pc_content_rcond with "Hrcond HφV") as "#Hnormal_p'".
    iAssert (interp_in_mem p W C w)%I as "#Hnormal".
    { iEval (rewrite /interp_in_mem /= /interp_in_mem_pre).
      iApply (interp_weakening_word_load W C p p' w with "Hth"); first exact Hflows.
      iEval (rewrite /interp_in_mem_pre) in "Hnormal_p'".
      iExact "Hnormal_p'". }
    iDestruct (interp_in_mem_load_post with "Hnormal") as "#Hload_interp"; first exact Hpost.
    iDestruct (addr_key_pointsto_join with "Ha Hshare") as "Ha".
    iDestruct ("WorldRes" with "[Ha $HφV]") as "WorldRes"; first by iApply region_cell_pointsto.
    iDestruct (pc_close_next with "Hworld_interp Hpart WorldRes") as "Hworld_interp";
      [exact Hnin_s|done|].
    iApply "Hφ"; iRight. iExists loadv'. iFrame "∗#%". done.
  Qed.

  Lemma wp_load_interp_cap_imm (E : coPset) (imm : Z) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId)
    (wi wdst : LWord)
    :
    decodeInstrW wi.(lw) = CLoad rdst rsrc imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

     {{{ thread_in th C
           ∗ interp W C (Cap p g b e a @@? π)
           ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ[th] (Cap p g b e a @@? π)
           ∗ rdst ↦ᵣ[th] wdst
           ∗ world_interp W C
     }}}
       Instr Executable @[th] E
       {{{ retv, RET retv;
           ( ⌜ retv = FaultedV ⌝ ∗
             PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a ∗
             pc_a ↦ₐ wi ∗
             (rsrc ↦ᵣ[th] Cap p g b e a @@? π ∨ rsrc ↦ᵣ[th] lclear_tag (Cap p g b e a @@? π)) ∗
             rdst ↦ᵣ[th] wdst ∗
             world_interp W C ) ∨
          (∃ ea wload,
              ⌜ retv = NextIV ⌝
           ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ[th] (Cap p g b e a @@? π)
           ∗ rdst ↦ᵣ[th] wload ∗ interp W C wload
           ∗ world_interp W C
           ∗ ⌜ readAllowed p = true ⌝
           ∗ ⌜(a + imm)%a = Some ea⌝
           ∗ ⌜ea ∈ₐ [b, e) ⌝
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

  Lemma load_read_retained {dq : dfrac} E W C
    pc_p pc_g pc_b pc_e pc_a pc_a' dst src (wi wd : LWord) b e a (raw : LWord) :
    is_shadow_address a = false →
    decodeInstrW wi.(lw) = CLoad dst src 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull → src ≠ cnull →
    {{{ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ[th] wd ∗ src ↦ᵣ[th] Cap RW Global b e a ∗ a ↦ₐ raw ∗
        world_interp W C }}}
      Instr Executable @[th] E
    {{{ actual, RET NextIV;
        ⌜load_heap raw actual⌝ ∗
        PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ[th] actual ∗ src ↦ᵣ[th] Cap RW Global b e a ∗
        a ↦ₐ raw ∗ world_interp W C }}}.
  Proof.
    iIntros (Hshadow Hinstr Hvpc Hbounds Hpc Hdst Hsrc Φ)
      "(HPC & Hi & Hdst & Hsrc & Ha & Hregion) HΦ".
    iPoseProof load_witness_plain_intro as "Hwit".
    iDestruct (pointsto_ne with "Ha Hi") as %Hne.
    iApply (wp_load_choice_next_2 (th := th) (CL := CL th) (pc_π := None) (W := load_witness_res LoadPlain)
              with "[$HPC $Hi $Hdst $Hsrc $Ha $Hwit]");
      [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply cload_next_ok
      | apply load_choice_witness | by apply live_witness_no_id | exact Hvpc | exact Hpc
      | exact Hdst | exact Hsrc | done | apply addr_add_0 | done | exact Hbounds | done |].
    iIntros "!>" (actual) "(%Hpost & HPC & Hi & Hdst & Hsrc & Ha & _)".
    pose proof (load_post_plain_load_heap RW raw actual Hpost) as Hloaded.
    rewrite lload_word_RW in Hloaded.
    iApply ("HΦ" $! actual). iSplitR; first done. iFrame.
  Qed.

End wp_interp.
