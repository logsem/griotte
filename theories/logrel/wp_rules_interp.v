From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Export logrel region_invariants.
From griotte Require Import world_ghost_theory.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Import rules rules_deref_quar proofmode monotone.
From griotte Require Import map_simpl register_tactics proofmode.

Section wp_interp.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    {cthreads : CmptThreads}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> (leibnizO LWord) -n> iPropO Σ).
  #[local] Notation V := (interpO Σ).
  #[local] Notation K := (contO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

  Lemma lload_word_RW v : lload_word RW v = v.
  Proof. by destruct v as [ [] ?]. Qed.

  (** A load of 0 reads 0, which is safe. *)
  Lemma interp_lload_word_int W C p :
    ⊢ interp W C (lload_word p (lword_of_word (WInt 0))).
  Proof.
    iApply interp_untagged. rewrite /lload_word /lift_word /load_word /=. by repeat case_match.
  Qed.

  (** The registers after a store to a cell of the zone. *)
  Lemma hwm_res_at_after (hb h : Z) (x : Addr) :
    mshwmb ↦ₜ[th] hb -∗
    mshwm ↦ₜ[th] hwm_after x hb h -∗
    hwm_res_at hb.
  Proof. iIntros "Hb Hh". rewrite /hwm_after. case_decide; iExists _; iFrame. Qed.

  (** Accesses retain the original current address and report their checked
      effective address. *)

  (** Two regions of a key outside the heap whose cell is held: same part,
      same permission. *)
  Lemma region_rel_part_agree_open {dq : dfrac} W C s a ρ1 ρ2 p1 p2 P1 P2 w :
    world_interp_open W C s -∗ a ↦ₐ{dq} w -∗
    region_rel_part ρ1 W C (LNonHeap a) p1 P1 -∗
    region_rel_part ρ2 W C (LNonHeap a) p2 P2 -∗
    world_interp_open W C s ∗ a ↦ₐ{dq} w ∗ ⌜ρ1 = ρ2 ∧ p1 = p2⌝.
  Proof.
    iIntros "Hw Ha #H1 #H2".
    destruct ρ1, ρ2; rewrite /region_rel_part /region_rel_g /region_rel_l.
    - iDestruct (rel_g_agree with "H1 H2") as "[% _]". by iFrame.
    - iDestruct "H2" as "(_ & %HT & _)". iExFalso.
      iApply (world_interp_open_rel_g_temporary_cell with "Hw H1 Ha"). done.
    - iDestruct "H1" as "(_ & %HT & _)". iExFalso.
      iApply (world_interp_open_rel_g_temporary_cell with "Hw H2 Ha"). done.
    - iDestruct "H1" as "(H1 & _)". iDestruct "H2" as "(H2 & _)".
      iDestruct (rel_l_agree with "H1 H2") as "[% _]". by iFrame.
  Qed.

  (** The part of a region reached through a capability: a Global one is not
      reached through a write-local capability. *)
  Lemma region_rel_part_of W C k p' P p g :
    region_rel W C k p' P p g -∗
    ∃ ρ, ⌜ρ = InGlobal → isWL p = false⌝ ∗ region_rel_part ρ W C k p' P.
  Proof.
    rewrite /region_rel. iIntros "#H".
    destruct (isWL p) eqn:Hwl.
    { iExists InLocal. iSplit; [by iPureIntro|done]. }
    destruct g.
    { iExists InGlobal. iSplit; [by iPureIntro|done]. }
    iDestruct "H" as "[H|H]".
    - iExists InGlobal. iSplit; [by iPureIntro|done].
    - iExists InLocal. iSplit; [by iPureIntro|done].
  Qed.

  (** Reading the content of an opened region: a Global region is read at
      the empty world. *)
  Lemma pc_content_rcond {CL : CritLink Σ} ρ W C P p' w :
    rcond P C p' interp -∗ pc_content ρ W C P w -∗ interp_in_mem_pre W C p' interp w.
  Proof.
    iIntros "#Hrc HP". destruct ρ; cbn.
    - iDestruct ("Hrc" with "HP") as "H". rewrite /interp_in_mem_pre.
      by iApply interp_g_any_world.
    - by iApply "Hrc".
  Qed.

  (** Writing a safe word into an opened region: a Global region is written
      through a capability that is not write-local. *)
  (** A word stored through a capability that is not write-local is not
      local. *)
  Lemma lstore_word_nonlocal p v :
    isWL p = false → isLocalWord (lstore_word p v).(lw) = false.
  Proof.
    intros Hwl. destruct (canStore p v.(lw)) eqn:Hcs.
    - rewrite lstore_word_canStore //. by eapply canStore_global_nonisWL.
    - assert (lstore_word p v = lclear_tag v) as ->.
      { by rewrite /lstore_word /lclear_tag /lift_word /store_word Hcs. }
      rewrite lw_lclear_tag. destruct v as [v ?]; cbn.
      destruct_word v; cbn; try done. by destruct sb.
  Qed.

  Lemma pc_content_wcond {CL : CritLink Σ} ρ W C P p v :
    (ρ = InGlobal → isWL p = false) →
    (if isWL p then wcond P C interp else wcond_nwl P C interp) -∗
    interp W C v -∗ pc_content ρ W C P (lstore_word p v).
  Proof.
    iIntros (Hwl) "#Hwc #Hv". destruct ρ; cbn.
    - rewrite Hwl //. iApply ("Hwc" with "[%]").
      { by apply lstore_word_nonlocal, Hwl. }
      iApply (interp_store_g with "Hv"). by apply Hwl.
    - destruct (isWL p) eqn:Hp.
      + iApply "Hwc". by iApply interp_lstore_word.
      + iApply ("Hwc" with "[%]"); first by apply lstore_word_nonlocal.
        by iApply interp_lstore_word.
  Qed.

  Lemma pc_content_wcond_z {CL : CritLink Σ} ρ W C P p z :
    (if isWL p then wcond P C interp else wcond_nwl P C interp) -∗ pc_content ρ W C P (WInt z).
  Proof.
    iIntros "#Hwc". destruct (isWL p); destruct ρ; cbn;
      iApply "Hwc"; try done; iApply interp_int.
  Qed.

  (** Opening the key of a capability address, with keys [s] open: the
      region of its part, or a tombstone, in which case the world is
      unchanged. *)
  Lemma open_world_interp_next_cases W C s π a p' P p g :
    persistent_cond P →
    addr_key π a ∉ s →
    region_rel W C (addr_key π a) p' P p g -∗ world_interp_open W C s -∗
    (∃ ρ, ⌜ρ = InGlobal → isWL p = false⌝ ∗ region_rel_part ρ W C (addr_key π a) p' P ∗
       world_interp_open W C ({[ addr_key π a ]} ∪ s) ∗
       ▷ (∃ v, pc_open W C (addr_key π a) p' P v ρ))
    ∨ (∃ ι, ⌜π = Some ι⌝ ∗ ι ⊒ AQuar ∗ world_interp_open W C s).
  Proof.
    iIntros (Hpers Hnin) "#Hrel Hw".
    assert (∀ x, Persistent (safeGC P x)) as HpersG by (intros x; apply (Hpers (_, _, _))).
    assert (∀ x, Persistent (safeC P x)) as HpersL by (intros x; apply Hpers).
    iDestruct (region_rel_part_of with "Hrel") as (ρ Hρ) "#Hpart".
    destruct ρ.
    - iPoseProof "Hpart" as "Hg". rewrite /region_rel_part /region_rel_g.
      destruct (decide (std W !! addr_key π a = Some Temporary)) as [HT|HnT].
      + iDestruct (world_interp_open_rel_g_temporary with "Hw Hg")
          as "[Hw (%a' & %ι & %Hk & #Hq)]"; [done|done|].
        iRight. iExists ι. destruct π as [ι'|]; [|by rewrite addr_key_None in Hk].
        rewrite addr_key_Some in Hk. injection Hk as -> ->. by iFrame "Hq Hw".
      + iDestruct (open_world_interp_permanent with "Hw Hg") as "[Hw Hres]"; [done|done|].
        iDestruct (heap_key_open_cases with "Hres") as "[Hres|(%a' & %ι & %Hk & #Hq)]".
        * iLeft. iExists InGlobal. iFrame "Hw Hpart %". iNext.
          iDestruct "Hres" as (v) "Hres". iExists v.
          iApply (pc_open_intro W C _ p' P v InGlobal with "Hres"). by intros _.
        * iRight. iExists ι. destruct π as [ι'|]; [|by rewrite addr_key_None in Hk].
          rewrite addr_key_Some in Hk Hnin HnT |- *. injection Hk as -> ->.
          iSplit; first done. iFrame "Hq".
          iApply (close_world_interp_next_quarantined_heap_g with "Hq Hw Hg"); done.
    - iPoseProof "Hpart" as "(Hl & %HT & _)".
      iDestruct (open_world_interp_temporary with "Hw Hl") as "[Hw Hres]"; [done|done|].
      iDestruct (heap_key_open_cases with "Hres") as "[Hres|(%a' & %ι & %Hk & #Hq)]".
      + iLeft. iExists InLocal. iFrame "Hw Hpart". iSplit; [iPureIntro; by intros ?|].
        iNext. iDestruct "Hres" as (v) "Hres". iExists v.
        iApply (pc_open_intro W C _ p' P v InLocal with "Hres"). by intros ?.
      + iRight. iExists ι. destruct π as [ι'|]; [|by rewrite addr_key_None in Hk].
        rewrite addr_key_Some in Hk Hnin HT |- *. injection Hk as -> ->.
        iSplit; first done. iFrame "Hq".
        iApply (close_world_interp_next_quarantined_heap_l with "Hq Hw Hl"); done.
  Qed.

  Lemma open_world_interp_cases W C π a p' P p g :
    persistent_cond P →
    region_rel W C (addr_key π a) p' P p g -∗ world_interp W C -∗
    (∃ ρ, ⌜ρ = InGlobal → isWL p = false⌝ ∗ region_rel_part ρ W C (addr_key π a) p' P ∗
       world_interp_open W C [addr_key π a] ∗
       ▷ (∃ v, pc_open W C (addr_key π a) p' P v ρ))
    ∨ (∃ ι, ⌜π = Some ι⌝ ∗ ι ⊒ AQuar ∗ world_interp W C).
  Proof.
    iIntros (Hpers) "#Hrel Hw". iEval (rewrite open_world_interp_empty) in "Hw".
    iDestruct (open_world_interp_next_cases with "Hrel Hw")
      as "[(%ρ & H1 & H2 & Hw & H4)|(%ι & H1 & H2 & Hw)]"; [done|set_solver|..].
    - iLeft. iExists ρ. iFrame "H1 H2 H4".
      rewrite (world_interp_open_permutation W C ({[addr_key π a]} ∪ []) [addr_key π a]);
        [done|set_solver].
    - iRight. iExists ι. iFrame "H1 H2". by rewrite open_world_interp_empty.
  Qed.

  Lemma wp_store_interp_imm {dq : dfrac} (E : coPset) (imm : Z) (W : WORLD) (C : CmptName) (hb : Z) (rsrc rdst : RegName)
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
           ∗ hwm_res_at hb
     }}}
       Instr Executable @[th] E
       {{{ retv, RET retv;
           ( ⌜ retv = FaultedV ⌝ ∗
             PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a ∗
             pc_a ↦ₐ{dq} wi ∗
             rsrc ↦ᵣ[th] wsrc ∗
             (rdst ↦ᵣ[th] wdst ∨ rdst ↦ᵣ[th] lclear_tag wdst) ∗
             world_interp W C ∗
             hwm_res_at hb ) ∨
          ( ∃ p g b e a π ea,
           ⌜ wdst = Cap p g b e a @@? π ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rsrc ↦ᵣ[th] wsrc
           ∗ rdst ↦ᵣ[th] Cap p g b e a @@? π
           ∗ world_interp W C
           ∗ hwm_res_at hb
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

    iDestruct (write_allowed_inv _ _ ea with "Hinterp_dst")
      as (p' P Hflows Hpers) "(#Hrel & Hzcond & #Hwcond & Hrcond)";[solve_addr|auto|..].
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
    iDestruct (region_cell_cases with "Ha") as "[Ha | ([-> [-> ->]] & Hcell)]".
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
      iPureIntro. split; first done. solve_addr.
    - (* The region holds a zone cell: the zone store *)
      iDestruct "Hhwm" as (h) "[Hb Hh]".
      iAssert (deref_res None 1%Qp)%I as "Hdw"; first by rewrite /deref_res.
      iApply (wp_store_zone_reg_imm with "[$HPC $Hi $Hsrc $Hdst $Hcell $Hb $Hh $Hdw]"); eauto.
      iNext; iIntros "(HPC & Hi & Hsrc & Hdst & Ha & Hb & Hh & _)".
      iDestruct ("WorldRes" with "[Ha $Hinterp']") as "WorldRes";
        first by iApply region_cell_nonheap.
      iDestruct (pc_close with "Hworld_interp Hpart WorldRes") as "Hworld_interp"; first done.
      iDestruct (hwm_res_at_after with "Hb Hh") as "Hhwm".
      iApply "Hφ"; iRight. iExists p, g, b, e, a, None, ea. iFrame "∗%".
      iPureIntro. split; first done. solve_addr.
  Qed.

  Lemma wp_store_interp {dq : dfrac} (E : coPset) (W : WORLD) (C : CmptName) (hb : Z) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wsrc wdst : LWord)
    :
    decodeInstrW wi.(lw) = Store rdst (inr rsrc) 0 →
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
           ∗ hwm_res_at hb
     }}}
       Instr Executable @[th] E
       {{{ retv, RET retv;
           ( ⌜ retv = FaultedV ⌝ ∗
             PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a ∗
             pc_a ↦ₐ{dq} wi ∗
             rsrc ↦ᵣ[th] wsrc ∗
             (rdst ↦ᵣ[th] wdst ∨ rdst ↦ᵣ[th] lclear_tag wdst) ∗
             world_interp W C ∗
             hwm_res_at hb ) ∨
          ( ∃ p g b e a π,
           ⌜ wdst = Cap p g b e a @@? π ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rsrc ↦ᵣ[th] wsrc
           ∗ rdst ↦ᵣ[th] Cap p g b e a @@? π
           ∗ world_interp W C
           ∗ hwm_res_at hb
           ∗ ⌜ writeAllowed p = true ⌝
           ∗ ⌜a ∈ₐ [b, e) ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ?? φ) "Hpre Hφ".
    iApply (wp_store_interp_imm with "Hpre"); eauto.
    iNext. iIntros (ret) "[Hfail | Hsucc]"; iApply "Hφ"; first (iLeft; iExact "Hfail").
    iRight.
    iDestruct "Hsucc" as (p g b e a π ea) "(? & ? & ? & ? & ? & ? & ? & ? & ? & %Hea & %Hb)".
    rewrite addr_add_0 in Hea. injection Hea as <-.
    iExists p, g, b, e, a, π. by iFrame.
  Qed.

  Lemma wp_store_interp_cap_imm {dq : dfrac} (E : coPset) (imm : Z) (W : WORLD) (C : CmptName) (hb : Z) (rsrc rdst : RegName)
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
           ∗ hwm_res_at hb
     }}}
       Instr Executable @[th] E
       {{{ retv, RET retv;
           ( ⌜ retv = FaultedV ⌝ ∗
             PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a ∗
             pc_a ↦ₐ{dq} wi ∗
             rsrc ↦ᵣ[th] wsrc ∗
             (rdst ↦ᵣ[th] Cap p g b e a @@? π ∨ rdst ↦ᵣ[th] lclear_tag (Cap p g b e a @@? π)) ∗
             world_interp W C ∗
             hwm_res_at hb ) ∨
          (∃ ea, ⌜ retv = NextIV ⌝
           ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rsrc ↦ᵣ[th] wsrc
           ∗ rdst ↦ᵣ[th] Cap p g b e a @@? π
           ∗ world_interp W C
           ∗ hwm_res_at hb
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

  Lemma wp_store_interp_cap {dq : dfrac} (E : coPset) (W : WORLD) (C : CmptName) (hb : Z) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId)
    (wi wsrc : LWord)
    :
    decodeInstrW wi.(lw) = Store rdst (inr rsrc) 0 →
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
           ∗ hwm_res_at hb
     }}}
       Instr Executable @[th] E
       {{{ retv, RET retv;
           ( ⌜ retv = FaultedV ⌝ ∗
             PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a ∗
             pc_a ↦ₐ{dq} wi ∗
             rsrc ↦ᵣ[th] wsrc ∗
             (rdst ↦ᵣ[th] Cap p g b e a @@? π ∨ rdst ↦ᵣ[th] lclear_tag (Cap p g b e a @@? π)) ∗
             world_interp W C ∗
             hwm_res_at hb ) ∨
          (⌜ retv = NextIV ⌝
           ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rsrc ↦ᵣ[th] wsrc
           ∗ rdst ↦ᵣ[th] Cap p g b e a @@? π
           ∗ world_interp W C
           ∗ hwm_res_at hb
           ∗ ⌜ writeAllowed p = true ⌝
           ∗ ⌜a ∈ₐ [b, e) ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ? ? φ) "Hpre Hφ".
    iApply (wp_store_interp_cap_imm with "Hpre");eauto.
    iNext. iIntros (ret) "[Hfail | Hsucc]"; iApply "Hφ"; first (iLeft; iExact "Hfail").
    iRight.
    iDestruct "Hsucc" as (ea) "(? & ? & ? & ? & ? & ? & ? & ? & %Hea & %Hb)".
    rewrite addr_add_0 in Hea. injection Hea as <-. by iFrame.
  Qed.

  Lemma wp_store_interp_z_imm {dq : dfrac} (E : coPset) (imm : Z) (W : WORLD) (C : CmptName) (hb : Z) (rdst : RegName)
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
           ∗ hwm_res_at hb
     }}}
       Instr Executable @[th] E
       {{{ retv, RET retv;
           ( ⌜ retv = FaultedV ⌝ ∗
             PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a ∗
             pc_a ↦ₐ{dq} wi ∗
             (rdst ↦ᵣ[th] wdst ∨ rdst ↦ᵣ[th] lclear_tag wdst) ∗
             world_interp W C ∗
             hwm_res_at hb ) ∨
          ( ∃ p g b e a π ea,
           ⌜ wdst = Cap p g b e a @@? π ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rdst ↦ᵣ[th] Cap p g b e a @@? π
           ∗ world_interp W C
           ∗ hwm_res_at hb
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

    iDestruct (write_allowed_inv _ _ ea with "Hinterp_dst")
      as (p' P Hflows Hpers) "(#Hrel & Hzcond & #Hwcond & Hrcond)";[solve_addr|auto|..].
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
    iDestruct (region_cell_cases with "Ha") as "[Ha | ([-> [-> ->]] & Hcell)]".
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
      iPureIntro. split; first done. solve_addr.
    - (* The region holds a zone cell: the zone store *)
      iDestruct "Hhwm" as (h) "[Hb Hh]".
      iAssert (deref_res None 1%Qp)%I as "Hdw"; first by rewrite /deref_res.
      iApply (wp_store_zone_z_imm with "[$HPC $Hi $Hdst $Hcell $Hb $Hh $Hdw]"); eauto.
      iNext; iIntros "(HPC & Hi & Hdst & Ha & Hb & Hh & _)".
      iDestruct ("WorldRes" with "[Ha $Hinterp']") as "WorldRes";
        first by iApply region_cell_nonheap.
      iDestruct (pc_close with "Hworld_interp Hpart WorldRes") as "Hworld_interp"; first done.
      iDestruct (hwm_res_at_after with "Hb Hh") as "Hhwm".
      iApply "Hφ"; iRight. iExists p, g, b, e, a, None, ea. iFrame "∗%".
      iPureIntro. split; first done. solve_addr.
  Qed.

  Lemma wp_store_interp_z {dq : dfrac} (E : coPset) (W : WORLD) (C : CmptName) (hb : Z) (rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wdst : LWord) (z : Z)
    :
    decodeInstrW wi.(lw) = Store rdst (inl z) 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rdst ≠ cnull ->

     {{{ interp W C wdst
           ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rdst ↦ᵣ[th] wdst
           ∗ world_interp W C
           ∗ hwm_res_at hb
     }}}
       Instr Executable @[th] E
       {{{ retv, RET retv;
           ( ⌜ retv = FaultedV ⌝ ∗
             PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a ∗
             pc_a ↦ₐ{dq} wi ∗
             (rdst ↦ᵣ[th] wdst ∨ rdst ↦ᵣ[th] lclear_tag wdst) ∗
             world_interp W C ∗
             hwm_res_at hb ) ∨
          ( ∃ p g b e a π,
           ⌜ wdst = Cap p g b e a @@? π ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rdst ↦ᵣ[th] Cap p g b e a @@? π
           ∗ world_interp W C
           ∗ hwm_res_at hb
           ∗ ⌜ writeAllowed p ⌝
           ∗ ⌜a ∈ₐ [b, e) ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ? φ) "Hpre Hφ".
    iApply (wp_store_interp_z_imm with "Hpre"); eauto.
    iNext. iIntros (ret) "[Hfail | Hsucc]"; iApply "Hφ"; first (iLeft; iExact "Hfail").
    iRight.
    iDestruct "Hsucc" as (p g b e a π ea) "(? & ? & ? & ? & ? & ? & ? & ? & %Hea & %Hb)".
    rewrite addr_add_0 in Hea. injection Hea as <-.
    iExists p, g, b, e, a, π. by iFrame.
  Qed.

  Lemma wp_store_interp_z_cap_imm {dq : dfrac} (E : coPset) (imm : Z) (W : WORLD) (C : CmptName) (hb : Z) (rdst : RegName)
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
           ∗ hwm_res_at hb
     }}}
       Instr Executable @[th] E
       {{{ retv, RET retv;
           ( ⌜ retv = FaultedV ⌝ ∗
             PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a ∗
             pc_a ↦ₐ{dq} wi ∗
             (rdst ↦ᵣ[th] Cap p g b e a @@? π ∨ rdst ↦ᵣ[th] lclear_tag (Cap p g b e a @@? π)) ∗
             world_interp W C ∗
             hwm_res_at hb ) ∨
          (∃ ea, ⌜ retv = NextIV ⌝
           ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rdst ↦ᵣ[th] Cap p g b e a @@? π
           ∗ world_interp W C
           ∗ hwm_res_at hb
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

  Lemma wp_store_interp_z_cap {dq : dfrac} (E : coPset) (W : WORLD) (C : CmptName) (hb : Z) (rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId)
    (wi : LWord) (z : Z)
    :
    decodeInstrW wi.(lw) = Store rdst (inl z) 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rdst ≠ cnull ->

     {{{  interp W C (Cap p g b e a @@? π)
           ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rdst ↦ᵣ[th] (Cap p g b e a @@? π)
           ∗ world_interp W C
           ∗ hwm_res_at hb
     }}}
       Instr Executable @[th] E
       {{{ retv, RET retv;
           ( ⌜ retv = FaultedV ⌝ ∗
             PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a ∗
             pc_a ↦ₐ{dq} wi ∗
             (rdst ↦ᵣ[th] Cap p g b e a @@? π ∨ rdst ↦ᵣ[th] lclear_tag (Cap p g b e a @@? π)) ∗
             world_interp W C ∗
             hwm_res_at hb ) ∨
          (⌜ retv = NextIV ⌝
           ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ{dq} wi
           ∗ rdst ↦ᵣ[th] Cap p g b e a @@? π
           ∗ world_interp W C
           ∗ hwm_res_at hb
           ∗ ⌜ writeAllowed p ⌝
           ∗ ⌜a ∈ₐ [b, e) ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' ? φ) "Hpre Hφ".
    iApply (wp_store_interp_z_cap_imm with "Hpre");eauto.
    iNext. iIntros (ret) "[Hfail | Hsucc]"; iApply "Hφ"; first (iLeft; iExact "Hfail").
    iRight.
    iDestruct "Hsucc" as (ea) "(? & ? & ? & ? & ? & ? & ? & %Hea & %Hb)".
    rewrite addr_add_0 in Hea. injection Hea as <-. by iFrame.
  Qed.

  (** The loads of [n] cells, safe in the world, through a safe capability
      with read permission, from its cursor: each load below the end opens
      the cell in the world, with the status witness of the world's heap
      provenance, and closes it as is. The loaded words are safe. *)
  Lemma world_interp_cells_load_acc (W : WORLD) (C : CmptName)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId) (n : nat) :
    readAllowed p = true →
    (b <= a)%a →
    π = None →
    thread_in th C -∗
    interp W C (Cap p g b e a @@? π) -∗
    cells_load_acc (λ _ ls, world_interp W C ∗ [∗ list] v ∈ ls, interp W C v)%I p e a π n.
  Proof.
    iIntros (Hra Hb ->) "#Hth #Hinterp_src".
    iIntros "!>" (i ls Hi Hie) "[Hworld_interp #Hls]".
    set (ea := a ^+ i).
    assert (ea ∈ₐ [b, e)) as Hbounds by (subst ea; solve_addr).
    assert (withinBounds b e ea = true) as Hwb by (apply withinBounds_true_iff; solve_addr).
    iDestruct (read_allowed_inv _ _ ea with "Hth Hinterp_src")
      as (p' P Hflows Hpers) "(#Hrel & Hzcond & #Hrcond & Hwcond)"; [solve_addr | auto |].
    iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ ea with "Hinterp_src") as %Hnot_shadow;
      [by eapply readAllowed_nonO | done |].
    iDestruct (open_world_interp_cases W C None ea p' P p g with "Hrel Hworld_interp")
      as "[(%ρ & %Hρwl & #Hpart & Hworld_interp & (%v & WorldRes)) | (%ι & % & _)]";
      [done | | done].
    iDestruct (pc_open_acc with "WorldRes") as "[ (>Ha & Hinterp) WorldRes]".
    iDestruct (region_cell_cases with "Ha") as "[Ha | ([_ [-> ->]] & Hcell)]"; cycle 1.
    { (* The region holds a zone cell, which holds 0: the load reads half of it *)
      iDestruct (zone_cell_unfold with "Hcell") as "[Htok Hhalf]".
      iPoseProof (load_witness_of_intro W (lword_of_word (WInt 0))) as "Hwit".
      iDestruct (key_share_deref None ea with "[]") as (dw Hdw) "[Hdw _]"; first done.
      iModIntro.
      iExists (lword_of_word (WInt 0)), (DfracOwn (1/2)),
        (load_witness_of W (lword_of_word (WInt 0))), dw.
      iFrame "Hhalf Hwit Hdw". iSplit; first done. iSplit; first done.
      iIntros "!>" (v' Hpost) "Hhalf _ _".
      pose proof (pc_content_persistent InLocal W C P (lword_of_word (WInt 0)) Hpers).
      iDestruct "Hinterp" as "#HφV".
      iDestruct (pc_content_rcond with "Hrcond HφV") as "#Hnormal_p'".
      iAssert (interp_in_mem p W C (lword_of_word (WInt 0)))%I as "#Hnormal".
      { iEval (rewrite /interp_in_mem /= /interp_in_mem_pre).
        iApply (interp_weakening_word_load W C p p' (lword_of_word (WInt 0)) with "Hth");
          first exact Hflows.
        iEval (rewrite /interp_in_mem_pre) in "Hnormal_p'".
        iExact "Hnormal_p'". }
      iDestruct (interp_in_mem_load_post with "Hnormal") as "#Hv'"; first exact Hpost.
      iDestruct ("WorldRes" with "[Htok Hhalf $HφV]") as "WorldRes".
      { iApply region_cell_zone. rewrite zone_cell_unfold. iFrame. }
      iModIntro. iSplitL.
      - iApply (pc_close with "Hworld_interp Hpart WorldRes"); done.
      - rewrite ?big_sepL_app /=. iFrame "Hls Hv'". }
    iDestruct (addr_key_pointsto with "Ha") as "[Ha Hshare]".
    iPoseProof (load_witness_of_intro W v) as "Hwit".
    iDestruct (key_share_deref with "Hshare") as (dw Hdw) "[Hdw Hshare]".
    iModIntro. iExists v, (DfracOwn 1), (load_witness_of W v), dw.
    iFrame "Ha Hwit Hdw". iSplit; first done. iSplit; first done.
    iIntros "!>" (v' Hpost) "Ha _ Hdw".
    iDestruct ("Hshare" with "Hdw") as "Hshare".
    pose proof (pc_content_persistent ρ W C P v Hpers).
    iDestruct "Hinterp" as "#HφV".
    iDestruct (pc_content_rcond with "Hrcond HφV") as "#Hnormal_p'".
    iAssert (interp_in_mem p W C v)%I as "#Hnormal".
    { iEval (rewrite /interp_in_mem /= /interp_in_mem_pre).
      iApply (interp_weakening_word_load W C p p' v with "Hth"); first exact Hflows.
      iEval (rewrite /interp_in_mem_pre) in "Hnormal_p'".
      iExact "Hnormal_p'". }
    iDestruct (interp_in_mem_load_post with "Hnormal") as "#Hv'"; first exact Hpost.
    iDestruct (addr_key_pointsto_join None with "Ha Hshare") as "Ha".
    iDestruct ("WorldRes" with "[Ha $HφV]") as "WorldRes"; first by iApply region_cell_pointsto.
    iModIntro. iSplitL.
    - iApply (pc_close with "Hworld_interp Hpart WorldRes"); done.
    - rewrite ?big_sepL_app /=. iFrame "Hls Hv'".
  Qed.

  (** A Global region whose cell is held is not a Temporary key of the
      local world, even with keys open. *)
  Lemma world_interp_open_rel_g_cell_not_temporary W C s k p φ w :
    world_interp_open W C s -∗ k ↪ᵍ[C]{p} φ -∗ k ↦ₖ w -∗
    world_interp_open W C s ∗ k ↦ₖ w ∗ ⌜std W !! k ≠ Some Temporary⌝.
  Proof.
    iIntros "Hw #Hr Hk".
    destruct (decide (std W !! k = Some Temporary)) as [HT|HnT]; last by iFrame.
    iExFalso.
    iEval (rewrite world_interp_open_eq /world_interp_open_def open_region_many_eq
      /open_region_many_def /world_interp_open_gl) in "Hw".
    iDestruct "Hw" as "[Hg _]".
    iDestruct (g_open with "Hg Hr") as "[_ (%φ' & _ & _ & Hb & _)]".
    { rewrite elem_of_open_g. naive_solver. }
    rewrite /body_g. destruct k as [a0|a0 ι]; cbn.
    - iDestruct "Hb" as (v) "(_ & Hv & _)".
      iApply (heap_pointsto_valid_2 (LNonHeap a0) (LNonHeap a0) with "Hv Hk"). done.
    - iDestruct "Hb" as "[(%v & _ & Hv & _)|#Hq]".
      + iApply (heap_pointsto_valid_2 (LHeap a0 ι) (LHeap a0 ι) with "Hv Hk"). done.
      + iApply (heap_pointsto_quar_false with "Hk Hq").
  Qed.

  (** The stores of [ws] through a safe capability of the object [ι], from
      its cursor [a], in the world. The first cell is opened before the
      stores, and stays open until the world closes: its status share
      refutes the tombstones of the other cells of [ι]. When the first cell
      is a tombstone, [ι] is quarantined. *)
  Lemma world_interp_cells_store_acc_heap (W : WORLD) (C : CmptName)
    (p : Perm) (g : Locality) (b e a : Addr) (ι : AId) (ws : list LWord) :
    writeAllowed p = true →
    (b <= a)%a →
    (a < e)%a →
    interp W C (Cap p g b e a @@? Some ι) -∗
    ([∗ list] v ∈ ws, interp W C v) -∗
    world_interp W C -∗
    ◇ ((ι ⊒ AQuar ∗ world_interp W C) ∨
       ∃ D : nat → iProp Σ,
         D 0 ∗
         cells_store_acc D p e a (Some ι) ws ∗
         ▷ (∀ i, D i -∗ world_interp W C)).
  Proof.
    iIntros (Hwa Hb Hae) "#Hinterp_dst #Hws Hworld_interp".
    assert (withinBounds b e (a ^+ 0) = true) as Hwb0
      by (apply withinBounds_true_iff; solve_addr).
    iDestruct (write_allowed_inv _ _ (a ^+ 0) with "Hinterp_dst")
      as (p0 P0 Hflows0 Hpers0) "(#Hrel0 & _ & #Hwcond0 & _)";
      [solve_addr | by rewrite Hwa |].
    assert (isO p0 = false) as HnO0.
    { apply writeAllowed_nonO. by eapply writeAllowed_flowsto. }
    iDestruct (open_world_interp_cases W C (Some ι) (a ^+ 0) p0 P0 p g
                 with "Hrel0 Hworld_interp")
      as "[(%ρ0 & %Hρ0wl & #Hpart0 & Hworld_open & (%v0 & Hres0))
          | (%ι' & %Hι' & #Hq & Hworld_interp)]";
      [done |..]; cycle 1.
    { injection Hι' as <-. iModIntro. iLeft. by iFrame "Hq Hworld_interp". }
    set (k0 := addr_key (Some ι) (a ^+ 0)).
    pose proof (pc_content_persistent ρ0 W C P0 v0 Hpers0).
    iDestruct (pc_open_acc with "Hres0") as "[ (>Hk0 & #Hφ0) _]".
    iDestruct (region_cell_heap with "Hk0") as "Hk0".
    iAssert (world_interp_open W C [k0] ∗ k0 ↦ₖ v0 ∗
             ⌜ρ0 = InGlobal → std W !! k0 ≠ Some Temporary⌝)%I
      with "[Hworld_open Hk0]" as "(Hworld_open & Hk0 & %HnT0)".
    { destruct ρ0; last by iFrame.
      iDestruct (world_interp_open_rel_g_cell_not_temporary with "Hworld_open Hpart0 Hk0")
        as "($ & $ & %HnT)". by iPureIntro. }
    iPoseProof (pc_open_rebuild ρ0 W C k0 p0 P0 with "Hpart0") as "#Hreb"; [done|done|].
    iModIntro. iRight.
    iExists (λ i, world_interp_open W C [k0] ∗
      match i with
      | 0 => k0 ↦ₖ v0
      | S _ => ∃ v, k0 ↦ₖ v ∗ pc_content ρ0 W C P0 v
      end)%I.
    iFrame "Hworld_open Hk0".
    iSplitR.
    - iIntros "!>" (i Hi Hie) "(Hworld_open & Hk)".
      set (ea := a ^+ i).
      assert (withinBounds b e ea = true) as Hwb
        by (apply withinBounds_true_iff; subst ea; solve_addr).
      iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ ea with "Hinterp_dst") as %Hnot_shadow;
        [by apply writeAllowed_nonO | done |].
      (* The store of [ws !!! i] into an open cell [k] of the world *)
      iAssert (∀ (k : LAddr) ρ (P : interpO Σ) v,
        ⌜k = addr_key (Some ι) ea⌝ -∗
        ⌜ρ = InGlobal → isWL p = false⌝ -∗
        ▷ (if isWL p then wcond P C interp else wcond_nwl P C interp) -∗
        k ↦ₖ v -∗
        ∃ q, ea ↦ₐ v ∗ deref_res (Some ι) q ∗
          ▷ (ea ↦ₐ lstore_word p (ws !!! i) -∗ deref_res (Some ι) q -∗
             k ↦ₖ lstore_word p (ws !!! i) ∗
             pc_content ρ W C P (lstore_word p (ws !!! i))))%I as "Hstore".
      { iIntros (k ρ P v -> Hρwl) "#Hwcond Hk".
        iDestruct (addr_key_pointsto with "Hk") as "[Ha Hshare]".
        iDestruct (key_share_deref with "Hshare") as (dw Hdw) "[Hdw Hshare]".
        iEval (rewrite deref_witness_res_deref_res -Hdw) in "Hdw".
        iExists (deref_share dw). iFrame "Ha Hdw".
        iIntros "!> Ha Hdw".
        iEval (rewrite Hdw -deref_witness_res_deref_res) in "Hdw".
        iDestruct ("Hshare" with "Hdw") as "Hshare".
        iDestruct (addr_key_pointsto_join with "Ha Hshare") as "$".
        iApply (pc_content_wcond with "Hwcond"); first done.
        destruct (lookup_lt_is_Some_2 ws i) as [wi Hwi]; first lia.
        rewrite (list_lookup_total_correct _ _ _ Hwi).
        by iApply (big_sepL_lookup with "Hws"). }
      destruct i as [|j].
      + iDestruct ("Hstore" $! k0 ρ0 P0 v0 with "[//] [//] Hwcond0 Hk")
          as (q) "(Ha & Hdw & Hclose)".
        iModIntro. iExists v0, q. iFrame "Ha Hdw". iSplit; first done.
        iIntros "!> Ha Hdw". iModIntro. iFrame "Hworld_open".
        iExists _. iApply ("Hclose" with "Ha Hdw").
      + iDestruct "Hk" as (vk) "[Hk Hck]".
        iDestruct (write_allowed_inv _ _ ea with "Hinterp_dst")
          as (p' P Hflows Hpers) "(#Hrel & _ & #Hwcond & _)";
          [subst ea; solve_addr | by rewrite Hwa |].
        assert (addr_key (Some ι) ea ∉ [k0]) as Hnotin.
        { rewrite /k0 /ea !addr_key_Some list_elem_of_singleton.
          intros Heq. injection Heq as Heq. solve_addr. }
        iDestruct (open_world_interp_next_cases W C [k0] (Some ι) ea p' P p g
                     with "Hrel Hworld_open")
          as "[(%ρ & %Hρwl & #Hpart & Hworld_open & (%v & Hres)) | (%ι' & %Hι' & #Hq & _)]";
          [done | exact Hnotin |..]; cycle 1.
        { injection Hι' as <-. iExFalso.
          iEval (rewrite /k0 addr_key_Some) in "Hk".
          iApply (heap_pointsto_quar_false with "Hk Hq"). }
        iDestruct (pc_open_acc_forall with "Hpart Hres") as "[ (>Hki & _) Hcl]".
        iDestruct (region_cell_heap with "Hki") as "Hki".
        iDestruct ("Hstore" $! (addr_key (Some ι) ea) ρ P v
                    with "[//] [//] Hwcond Hki")
          as (q) "(Ha & Hdw & Hclose)".
        iModIntro. iExists v, q. iFrame "Ha Hdw". iSplit; first done.
        iIntros "!> Ha Hdw".
        iDestruct ("Hclose" with "Ha Hdw") as "[Hki Hres]".
        iDestruct ("Hcl" with "[$Hres Hki]") as "Hres".
        { by iApply region_cell_pointsto. }
        iModIntro. iSplitL "Hworld_open Hres"; last by iExists vk; iFrame "Hk Hck".
        iApply (pc_close_next with "Hworld_open Hpart Hres"); done.
    - iIntros "!>" (i) "(Hworld_open & Hk)".
      destruct i as [|j].
      + iApply (pc_close with "Hworld_open Hpart0 [Hk]"); first done.
        iApply "Hreb". by iFrame "Hk Hφ0".
      + iDestruct "Hk" as (v) "Hk".
        iApply (pc_close with "Hworld_open Hpart0 [Hk]"); first done.
        by iApply "Hreb".
  Qed.

  (** The loads of [n] cells through a safe capability of the object [ι],
      from its cursor [a], in the world. As for the stores, the first cell
      is opened before the loads and stays open: its status share refutes
      the tombstones of the other cells of [ι]. The loaded words are
      safe. *)
  Lemma world_interp_cells_load_acc_heap (W : WORLD) (C : CmptName)
    (p : Perm) (g : Locality) (b e a : Addr) (ι : AId) (n : nat) :
    readAllowed p = true →
    (b <= a)%a →
    (a < e)%a →
    thread_in th C -∗
    interp W C (Cap p g b e a @@? Some ι) -∗
    world_interp W C -∗
    ◇ ((ι ⊒ AQuar ∗ world_interp W C) ∨
       ∃ L : nat → list LWord → iProp Σ,
         L 0 [] ∗
         cells_load_acc L p e a (Some ι) n ∗
         ▷ (∀ i ls, L i ls -∗ world_interp W C ∗ [∗ list] v ∈ ls, interp W C v)).
  Proof.
    iIntros (Hra Hb Hae) "#Hth #Hinterp_src Hworld_interp".
    assert (withinBounds b e (a ^+ 0) = true) as Hwb0
      by (apply withinBounds_true_iff; solve_addr).
    iDestruct (read_allowed_inv _ _ (a ^+ 0) with "Hth Hinterp_src")
      as (p0 P0 Hflows0 Hpers0) "(#Hrel0 & _ & #Hrcond0 & _)";
      [solve_addr | by rewrite Hra |].
    assert (isO p0 = false) as HnO0.
    { apply readAllowed_nonO. by eapply readAllowed_flowsto. }
    iDestruct (open_world_interp_cases W C (Some ι) (a ^+ 0) p0 P0 p g
                 with "Hrel0 Hworld_interp")
      as "[(%ρ0 & %Hρ0wl & #Hpart0 & Hworld_open & (%v0 & Hres0))
          | (%ι' & %Hι' & #Hq & Hworld_interp)]";
      [done |..]; cycle 1.
    { injection Hι' as <-. iModIntro. iLeft. by iFrame "Hq Hworld_interp". }
    set (k0 := addr_key (Some ι) (a ^+ 0)).
    pose proof (pc_content_persistent ρ0 W C P0 v0 Hpers0).
    iDestruct (pc_open_acc with "Hres0") as "[ (>Hk0 & #Hφ0) _]".
    iDestruct (region_cell_heap with "Hk0") as "Hk0".
    iAssert (world_interp_open W C [k0] ∗ k0 ↦ₖ v0 ∗
             ⌜ρ0 = InGlobal → std W !! k0 ≠ Some Temporary⌝)%I
      with "[Hworld_open Hk0]" as "(Hworld_open & Hk0 & %HnT0)".
    { destruct ρ0; last by iFrame.
      iDestruct (world_interp_open_rel_g_cell_not_temporary with "Hworld_open Hpart0 Hk0")
        as "($ & $ & %HnT)". by iPureIntro. }
    iPoseProof (pc_open_rebuild ρ0 W C k0 p0 P0 with "Hpart0") as "#Hreb"; [done|done|].
    iModIntro. iRight.
    iExists (λ _ ls, world_interp_open W C [k0] ∗ k0 ↦ₖ v0 ∗
      [∗ list] v ∈ ls, interp W C v)%I.
    iFrame "Hworld_open Hk0". iSplitR; first done.
    iSplitR.
    - iIntros "!>" (i ls Hi Hie) "(Hworld_open & Hk0 & #Hls)".
      set (ea := a ^+ i).
      assert (withinBounds b e ea = true) as Hwb
        by (apply withinBounds_true_iff; subst ea; solve_addr).
      iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ ea with "Hinterp_src") as %Hnot_shadow;
        [by apply readAllowed_nonO | done |].
      (* The load of an open cell [k] of the world *)
      iAssert (∀ (k : LAddr) ρ (P : interpO Σ) p' v,
        ⌜k = addr_key (Some ι) ea⌝ -∗
        ⌜PermFlowsTo p p'⌝ -∗
        ⌜persistent_cond P⌝ -∗
        ▷ rcond P C p' interp -∗
        ▷ pc_content ρ W C P v -∗
        k ↦ₖ v -∗
        ∃ dw, ⌜Some ι = deref_id dw⌝ ∗ ea ↦ₐ v ∗ deref_witness_res dw ∗
          ▷ (∀ v', ⌜load_post (load_witness_of W v) p v v'⌝ -∗
                   ea ↦ₐ v -∗ deref_witness_res dw -∗
                   k ↦ₖ v ∗ interp W C v'))%I as "Hload".
      { iIntros (k ρ P p' v -> Hflows Hpers) "#Hrcond HφV Hk".
        pose proof (pc_content_persistent ρ W C P v Hpers).
        iDestruct "HφV" as "#HφV".
        iDestruct (addr_key_pointsto with "Hk") as "[Ha Hshare]".
        iDestruct (key_share_deref with "Hshare") as (dw Hdw) "[Hdw Hshare]".
        iExists dw. iFrame "Ha Hdw". iSplit; first done.
        iIntros "!>" (v' Hpost) "Ha Hdw".
        iDestruct ("Hshare" with "Hdw") as "Hshare".
        iDestruct (pc_content_rcond with "Hrcond HφV") as "#Hnormal_p'".
        iAssert (interp_in_mem p W C v)%I as "#Hnormal".
        { iEval (rewrite /interp_in_mem /= /interp_in_mem_pre).
          iApply (interp_weakening_word_load W C p p' v with "Hth"); first exact Hflows.
          iEval (rewrite /interp_in_mem_pre) in "Hnormal_p'".
          iExact "Hnormal_p'". }
        iDestruct (interp_in_mem_load_post with "Hnormal") as "#Hv'"; first exact Hpost.
        iDestruct (addr_key_pointsto_join with "Ha Hshare") as "Ha".
        by iFrame "Ha Hv'". }
      destruct i as [|j].
      + iDestruct ("Hload" $! k0 ρ0 P0 p0 v0 with "[//] [//] [//] Hrcond0 Hφ0 Hk0")
          as (dw Hdw) "(Ha & Hdw & Hclose)".
        iPoseProof (load_witness_of_intro W v0) as "Hwit".
        iModIntro. iExists v0, (DfracOwn 1), (load_witness_of W v0), dw.
        iFrame "Ha Hdw Hwit". iSplit; first done. iSplit; first done.
        iIntros "!>" (v' Hpost) "Ha _ Hdw".
        iDestruct ("Hclose" with "[//] Ha Hdw") as "[Hk0 #Hv']".
        iModIntro. iFrame "Hworld_open Hk0".
        by iFrame "Hls Hv'".
      + iDestruct (read_allowed_inv _ _ ea with "Hth Hinterp_src")
          as (p' P Hflows Hpers) "(#Hrel & _ & #Hrcond & _)";
          [subst ea; solve_addr | by rewrite Hra |].
        assert (addr_key (Some ι) ea ∉ [k0]) as Hnotin.
        { rewrite /k0 /ea !addr_key_Some list_elem_of_singleton.
          intros Heq. injection Heq as Heq. solve_addr. }
        iDestruct (open_world_interp_next_cases W C [k0] (Some ι) ea p' P p g
                     with "Hrel Hworld_open")
          as "[(%ρ & %Hρwl & #Hpart & Hworld_open & (%v & Hres)) | (%ι' & %Hι' & #Hq & _)]";
          [done | exact Hnotin |..]; cycle 1.
        { injection Hι' as <-. iExFalso.
          iEval (rewrite /k0 addr_key_Some) in "Hk0".
          iApply (heap_pointsto_quar_false with "Hk0 Hq"). }
        pose proof (pc_content_persistent ρ W C P v Hpers).
        iDestruct (pc_open_acc with "Hres") as "[ (>Hki & #Hφ) Hcl]".
        iDestruct (region_cell_heap with "Hki") as "Hki".
        iDestruct ("Hload" $! (addr_key (Some ι) ea) ρ P p' v
                    with "[//] [//] [//] Hrcond Hφ Hki")
          as (dw Hdw) "(Ha & Hdw & Hclose)".
        iPoseProof (load_witness_of_intro W v) as "Hwit".
        iModIntro. iExists v, (DfracOwn 1), (load_witness_of W v), dw.
        iFrame "Ha Hdw Hwit". iSplit; first done. iSplit; first done.
        iIntros "!>" (v' Hpost) "Ha _ Hdw".
        iDestruct ("Hclose" with "[//] Ha Hdw") as "[Hki #Hv']".
        iModIntro. iFrame "Hk0 Hls Hv'".
        iApply (pc_close_next with "Hworld_open Hpart [Hcl Hki]"); [done | done |].
        iApply ("Hcl" with "[Hki $Hφ]"). by iApply region_cell_pointsto.
    - iIntros "!>" (i ls) "(Hworld_open & Hk0 & $)".
      iApply (pc_close with "Hworld_open Hpart0 [Hk0]"); first done.
      iApply "Hreb". by iFrame "Hk0 Hφ0".
  Qed.

  Lemma wp_unseal_unknown {dq : dfrac} E pc_p pc_g pc_b pc_e pc_a pc_a' wi r1 r2 wsealr wsealed  :
    decodeInstrW wi.(lw) = UnSeal r2 r1 r2 →
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
              ∗ r1 ↦ᵣ[th] wsealr
              ∗ r2 ↦ᵣ[th] lclear_tag wsealed
              ∗ ⌜ is_sealr wsealr.(lw) && is_sealed wsealed.(lw) = false ⌝)
          ∨ (∃ psr gsr bsr esr asr πsr ot wsb π,
              ⌜ retv = NextIV ⌝
              ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ{dq} wi
              ∗ r1 ↦ᵣ[th] wsealr
              ∗ r2 ↦ᵣ[th] WSealable (unseal_sb gsr wsb) @@? π
              ∗ ⌜ wsealr = SealRange psr gsr bsr esr asr @@? πsr ⌝
              ∗ ⌜ permit_unseal psr = true ⌝
              ∗ ⌜ wsealed = WSealed ot wsb @@? π ⌝
              ∗ ⌜ get_tag_sealable wsb = true ⌝
              ∗ ⌜ withinBounds bsr esr ot = true ⌝ )
          ∨ ∃ tsr psr gsr bsr esr asr πsr ot sb π,
              ⌜ retv = NextIV ⌝
              ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a'
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

    iDestruct (read_allowed_inv _ _ ea with "Hth Hinterp_src")
      as (p' P Hflows Hpers) "(#Hrel & Hzcond & #Hrcond & Hwcond)";[solve_addr|auto|..].
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
    iDestruct (region_cell_cases with "Ha") as "[Ha | ([-> [-> ->]] & Hcell)]"; cycle 1.
    { (* The region holds a zone cell, which holds 0: the load reads half of it *)
      iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ ea with "Hinterp_src") as %Hnot_shadow;
        [by eapply readAllowed_nonO|done|].
      iDestruct (zone_cell_unfold with "Hcell") as "[Htok Hhalf]".
      iApply (wp_load_witness_imm_one_inbounds_dq with "[$HPC $Hi $Hdst $Hsrc $Hhalf]"); eauto.
      iNext; iIntros "(HPC & Hi & Hdst & Hsrc & Hhalf)".
      iDestruct ("WorldRes" with "[Htok Hhalf $Hinterp]") as "WorldRes".
      { iApply region_cell_zone. rewrite zone_cell_unfold. iFrame. }
      iDestruct (pc_close with "Hworld_interp Hpart WorldRes") as "Hworld_interp"; first done.
      iApply "Hφ"; iRight. iExists p, g, b, e, a, None, ea, _. iFrame "∗%".
      iSplit; first done. iSplit; first done. iApply interp_lload_word_int. }
    iDestruct (addr_key_pointsto with "Ha") as "[Ha Hshare]".

    iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ ea with "Hinterp_src") as %Hnot_shadow;
      [by eapply readAllowed_nonO|done|].
    iPoseProof (load_witness_of_intro W w) as "Hwit".
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
         iDestruct ("WorldRes" with "[Ha $Hinterp]") as "WorldRes"; first by iApply region_cell_pointsto.
         iDestruct (pc_close with "Hworld_interp Hpart WorldRes") as "Hworld_interp"; first done.
         iApply "Hφ". iLeft. by iFrame. }
    destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)].
    destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0').
    rewrite lookup_insert_eq in Hsrc0'. injection Hsrc0' as <- <- <- <- <- <-.
      rewrite Hea in Haddr. injection Haddr as <-.
    rewrite lookup_insert_ne // lookup_insert_eq in Hl. injection Hl as <-.
    pose proof (pc_content_persistent ρ W C P w Hpers).
    iDestruct "Hinterp" as "#HφV".
    iDestruct (pc_content_rcond with "Hrcond HφV") as "#Hnormal_p'".
    iAssert (interp_in_mem p W C w)%I as "#Hnormal".
    { iEval (rewrite /interp_in_mem /= /interp_in_mem_pre).
      iApply (interp_weakening_word_load W C p p' w with "Hth"); first exact Hflows.
      iEval (rewrite /interp_in_mem_pre) in "Hnormal_p'".
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
    iDestruct ("WorldRes" with "[Ha $HφV]") as "WorldRes"; first by iApply region_cell_pointsto.
    iDestruct (pc_close with "Hworld_interp Hpart WorldRes") as "Hworld_interp"; first done.
    iApply "Hφ"; iRight. iExists p, g, b, e, a, π, ea, loadv'. iFrame "∗#%".
    iPureIntro. split; first done. solve_addr.
  Qed.

  Lemma wp_load_interp (E : coPset) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wsrc wdst : LWord)
    :
    decodeInstrW wi.(lw) = CLoad rdst rsrc 0 →
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
          ( ∃ p g b e a π wload,
           ⌜ wsrc = Cap p g b e a @@? π ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ[th] Cap p g b e a @@? π
           ∗ rdst ↦ᵣ[th] wload ∗ interp W C wload
           ∗ world_interp W C
           ∗ ⌜ readAllowed p = true ⌝
           ∗ ⌜a ∈ₐ [b, e) ⌝
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
    ∀ p g b e a, w.(lw) = Cap p g b e a → withinBounds b e a = true →
      addr_key w.(lprov) a ∉ s.

  (** [wp_load_interp_same] over a world open on [s], when the loaded key
      is not in [s]. *)
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
    iDestruct (read_allowed_inv _ _ a with "Hth Hinterp_src")
      as (p' P Hflows Hpers) "(#Hrel & Hzcond & #Hrcond & Hwcond)"; [solve_addr | auto |..].
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
    iDestruct (region_cell_cases with "Ha") as "[Ha | ([-> [-> ->]] & Hcell)]"; cycle 1.
    { (* The region holds a zone cell, which holds 0: the load reads half of it *)
      iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ a with "Hinterp_src") as %Hnot_shadow;
        [by eapply readAllowed_nonO|done|].
      iDestruct (zone_cell_unfold with "Hcell") as "[Htok Hhalf]".
      iApply (wp_load_witness_imm_same_inbounds_dq with "[$HPC $Hi $Hsrc $Hhalf]"); eauto.
      { by rewrite addr_add_0. }
      iNext; iIntros "(HPC & Hi & Hsrc & Hhalf)".
      iDestruct ("WorldRes" with "[Htok Hhalf $Hinterp]") as "WorldRes".
      { iApply region_cell_zone. rewrite zone_cell_unfold. iFrame. }
      iDestruct (pc_close_next with "Hworld_interp Hpart WorldRes") as "Hworld_interp"; [done|done|].
      iApply "Hφ"; iRight. iExists _. iFrame "∗%".
      iSplit; first done. iApply interp_lload_word_int. }
    iDestruct (addr_key_pointsto with "Ha") as "[Ha Hshare]".
    iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ a with "Hinterp_src") as %Hnot_shadow;
      [by eapply readAllowed_nonO | done |].
    iPoseProof (load_witness_of_intro W w) as "Hwit".
    iDestruct (map_of_regs_1 with "Hsrc") as "Hmap".
    iDestruct (memMap_resource_2ne_apply_dq with "Hi Ha") as "[Hmem %Hpc_a]".
    iDestruct (key_share_deref with "Hshare") as (dw Hdw) "[Hdw Hshare]".
    iAssert (▷ ([∗ map] k↦revoked ∈ (∅ : ShadowTbl), k ↦ₛ□ revoked))%I
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
         iDestruct ("WorldRes" with "[Ha $Hinterp]") as "WorldRes"; first by iApply region_cell_pointsto.
         iDestruct (pc_close_next with "Hworld_interp Hpart WorldRes") as "Hworld_interp";
           [exact Hnin_s|done|].
         iApply "Hφ". iLeft. by iFrame. }
    destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)].
    destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0').
    rewrite lookup_insert_eq in Hsrc0'. injection Hsrc0' as <- <- <- <- <- <-.
    rewrite addr_add_0 in Haddr. injection Haddr as <-.
    rewrite lookup_insert_ne // lookup_insert_eq in Hl. injection Hl as <-.
    pose proof (pc_content_persistent ρ W C P w Hpers).
    iDestruct "Hinterp" as "#HφV".
    iDestruct (pc_content_rcond with "Hrcond HφV") as "#Hnormal_p'".
    iAssert (interp_in_mem p W C w)%I as "#Hnormal".
    { iEval (rewrite /interp_in_mem /= /interp_in_mem_pre).
      iApply (interp_weakening_word_load W C p p' w with "Hth"); first exact Hflows.
      iEval (rewrite /interp_in_mem_pre) in "Hnormal_p'".
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
    iDestruct ("WorldRes" with "[Ha $HφV]") as "WorldRes"; first by iApply region_cell_pointsto.
    iDestruct (pc_close_next with "Hworld_interp Hpart WorldRes") as "Hworld_interp";
      [exact Hnin_s|done|].
    iApply "Hφ"; iRight. iExists loadv'. iFrame "∗#%". done.
  Qed.

  (** A load through a safe word into the register that holds it: it
      faults, or it loads a safe word ([wp_load_interp] for one register,
      with any fraction of the instruction). *)
  Lemma wp_load_interp_same (E : coPset) (W : WORLD) (C : CmptName) (r : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wsrc : LWord) (dq : dfrac) :
    decodeInstrW wi.(lw) = CLoad r r 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r ≠ cnull →
    {{{ thread_in th C ∗ interp W C wsrc ∗
        PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a ∗
        pc_a ↦ₐ{dq} wi ∗
        r ↦ᵣ[th] wsrc ∗
        world_interp W C }}}
      Instr Executable @[th] E
    {{{ retv, RET retv;
        ( ⌜retv = FaultedV⌝ ∗
          PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a ∗
          pc_a ↦ₐ{dq} wi ∗
          (r ↦ᵣ[th] wsrc ∨ r ↦ᵣ[th] lclear_tag wsrc) ∗
          world_interp W C ) ∨
        ( ∃ wload,
          ⌜retv = NextIV⌝ ∗
          PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a' ∗
          pc_a ↦ₐ{dq} wi ∗
          r ↦ᵣ[th] wload ∗ interp W C wload ∗
          world_interp W C ) }}}.
  Proof.
    iIntros (Hdecode Hcorrect_pc Hpca' Hr φ)
      "(#Hth & #Hinterp_src & HPC & Hi & Hsrc & Hworld_interp) Hφ".
    iApply (wp_load_interp_same_open _ _ _ []
             with "[$Hth $HPC $Hi $Hsrc $Hinterp_src Hworld_interp]"); try done.
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

  Lemma wp_load_interp_cap (E : coPset) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId)
    (wi wdst : LWord)
    :
    decodeInstrW wi.(lw) = CLoad rdst rsrc 0 →
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
          (∃ wload,
              ⌜ retv = NextIV ⌝
           ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ[th] (Cap p g b e a @@? π)
           ∗ rdst ↦ᵣ[th] wload ∗ interp W C wload
           ∗ world_interp W C
           ∗ ⌜ readAllowed p = true ⌝
           ∗ ⌜a ∈ₐ [b, e) ⌝
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
        region W C }}}
      Instr Executable @[th] E
    {{{ actual, RET NextIV;
        ⌜load_heap raw actual⌝ ∗
        PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ[th] actual ∗ src ↦ᵣ[th] Cap RW Global b e a ∗
        a ↦ₐ raw ∗ region W C }}}.
  Proof.
    iIntros (Hshadow Hinstr Hvpc Hbounds Hpc Hdst Hsrc Φ)
      "(HPC & Hi & Hdst & Hsrc & Ha & Hregion) HΦ".
    iPoseProof (load_witness_of_intro W raw) as "Hwit".
    iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %Hsrc_dst]".
    iDestruct (memMap_resource_2ne_apply_dq with "Hi Ha") as "[Hmem %Hpc_a]".
    iAssert (▷ ([∗ map] k↦revoked ∈ (∅ : ShadowTbl), k ↦ₛ□ revoked))%I
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
