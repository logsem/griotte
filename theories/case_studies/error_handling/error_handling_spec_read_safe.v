From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode map_simpl register_tactics.
From griotte Require Import logrel rules rules_trap_cause rules_deref_quar.
From griotte Require Import region_invariants_revocation wp_rules_interp interp_weakening.
From griotte Require Import switcher_base.
From griotte Require Import
  error_handling_spec_states error_handling_spec_read_blocks error_handling_spec_handler_blocks
  error_handling_spec_handler error_handling_spec_read.

(** * The entry [stats_read] for an unknown caller

    The export of [stats_read] satisfies [ot_switcher_prop]: for any
    pointer that is safe ([interp]), [stats_read] returns a safe word.
    - When the load succeeds, the pointer is a valid capability of the
      caller's world, and the loaded word is safe; the callee revokes its
      stack and returns.
    - When it faults, with its exact fault, the callee does not revoke: it
      opens (borrows) the [ErrorState] slot from its world, and lends it to
      the handler of [stats] ([stats_read_fault_safe]). The handler
      retries a bounds violation whose repaired base is outside the slot:
      the retried load runs in the world open at the slot, and its fault,
      if any, is not repairable, so it is unwound. Any other fault is
      unwound.
    - The return (count 0 or 2) and the unwind revoke the world open at the
      slot ([world_interp_revoke_stack_open]), which gives the same world
      as revoking it closed, and go through [switcher_ret_specification]. *)

Section Error_Handling_Read_Safe.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
    {statslayout : statsLayout} {statslayoutwf : statsLayoutWf}
  .

  (** ** The load through a safe pointer, over a world open on [s] *)

  (** The faults of the load through a safe pointer [wptr]: the failure of
      its checks, or, when they pass, [fault_default]. The logical view
      then holds the cell, so the fault is not an access fault. *)
  Definition stats_load_interp_fault (wptr : LWord) (f : fault) : Prop :=
    data_cap_check readAllowed PermitLoadViolation ca0 wptr.(lw) 0 = inl f ∨
    ((∃ ea, data_cap_check readAllowed PermitLoadViolation ca0 wptr.(lw) 0 = inr ea) ∧
     f = fault_default).

  (* TODO: move to opsem/griotte_opsem.v *)
  Lemma data_cap_check_lclear_tag perm_ok perm_code r (w : LWord) imm :
    data_cap_check perm_ok perm_code r (lclear_tag w).(lw) imm =
      inl (FaultCheri TagViolation (CheriGPR r)).
  Proof. destruct w as [w π]; by destruct w as [ | [ | ] | | ? [ | ] ]. Qed.

  (** [wp_load_interp_same_open] for a load whose checks pass: when it
      faults on a cell, the cell stays out of its region, so that the trap
      can read it; the region closes once the cell is given back. On a
      tombstone of a freed object, the register loses its tag and the load
      faults with no cell. *)
  Lemma stats_load_interp_open_cell (E : coPset) (W : WORLD) (C : CmptName) (s : list LAddr)
    (r : RegName) (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi : LWord) (dq : dfrac) (p : Perm) (g : Locality) (b e a : Addr) (π : option AId) :
    decodeInstrW wi.(lw) = CLoad r r 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r ≠ cnull →
    readAllowed p = true →
    withinBounds b e a = true →
    addr_key π a ∉ s →
    {{{ interp W C (Cap p g b e a @@? π) ∗
        PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a ∗
        pc_a ↦ₐ{dq} wi ∗
        r ↦ᵣ[th] (Cap p g b e a @@? π) ∗
        world_interp_open W C s }}}
      Instr Executable @[th] E
    {{{ retv, RET retv;
        ( ⌜retv = FaultedV⌝ ∗
          PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a ∗
          pc_a ↦ₐ{dq} wi ∗
          ( ( ∃ wa,
              ⌜is_shadow_address a = false⌝ ∗
              r ↦ᵣ[th] (Cap p g b e a @@? π) ∗
              a ↦ₐ wa ∗
              (a ↦ₐ wa -∗ world_interp_open W C s) ) ∨
            ( r ↦ᵣ[th] lclear_tag (Cap p g b e a @@? π) ∗
              world_interp_open W C s ) ) ) ∨
        ( ∃ wload,
          ⌜retv = NextIV⌝ ∗
          PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a' ∗
          pc_a ↦ₐ{dq} wi ∗
          r ↦ᵣ[th] wload ∗ interp W C wload ∗
          world_interp_open W C s ) }}}.
  Proof.
    iIntros (Hdecode Hcorrect_pc Hpca' Hr Hra Hwb Hnin_s φ)
      "(#Hinterp_src & HPC & Hi & Hsrc & Hworld_interp) Hφ".
    apply withinBounds_true_iff in Hwb as Hbounds.
    (* Open the region of [a], as [wp_load_interp_imm] *)
    iDestruct (read_allowed_inv _ _ a with "Hinterp_src")
      as (p' P Hflows Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & Hmono)"; [solve_addr | auto |..].
    iDestruct (readAllowed_valid_cap_implies _ _ _ _ _ _ _ a with "Hinterp_src")
      as %(ρ & Hρ & Hρ_not_revoked); [done | done |].
    iDestruct (open_world_interp_next_cases W C s π a p' (safeC P) ρ
                with "Hrel Hworld_interp")
      as "[(Hworld_interp & Hstate & (%w & WorldRes)) | (%ι & -> & #Hq & Hworld_interp)]";
      [done | exact Hnin_s | destruct ρ; auto; contradiction | exact Hρ |..].
    2: { (* A tombstone: the load faults on the tag *)
         iDestruct (interp_cap_has_authority with "Hinterp_src") as %Hauth;
           [by eapply readAllowed_nonO | exact Hwb |].
         iApply (wp_load_quar_imm with "[$HPC $Hi $Hsrc $Hq]");
           [eauto | eauto | exact Hauth | done |].
         iNext. iIntros "(HPC & Hi & Hsrc)".
         iApply "Hφ". iLeft. iFrame "HPC Hi". iSplit; first done.
         iRight. iFrame. }
    iDestruct (WorldRes_acc with "WorldRes") as "[ (>Ha & Hinterp) WorldRes ]".
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
    2: { (* The load faults: the cell stays out of its region, for the trap *)
         iDestruct (regs_of_map_1 with "Hmap") as "Hsrc".
         iDestruct (memMap_resource_2ne_dq with "Hmem") as "[Hi Ha]"; auto.
         iApply "Hφ". iLeft. iFrame "HPC Hi". iSplit; first done.
         iLeft. iExists w. iFrame "Hsrc Ha". iSplit; first done.
         iIntros "Ha".
         iDestruct (addr_key_pointsto_join with "Ha Hshare") as "Ha".
         iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
         iApply (close_world_interp_next with "Hworld_interp Hstate Hrel WorldRes"); eauto.
         destruct ρ; auto; contradiction. }
    destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)].
    destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0').
    rewrite lookup_insert_eq in Hsrc0'. injection Hsrc0' as <- <- <- <- <- <-.
    rewrite addr_add_0 in Haddr. injection Haddr as <-.
    rewrite lookup_insert_ne // lookup_insert_eq in Hl. injection Hl as <-.
    pose proof (Hpers (W, C, w)) as Hpers_w.
    iDestruct "Hinterp" as "#HφV /=".
    iDestruct ("Hrcond" with "HφV") as "#Hnormal_p'".
    iAssert (interp_in_mem p W C w)%I as "#Hnormal".
    { iEval (rewrite /interp_in_mem /= /interp_in_mem_pre).
      iApply (interp_weakening_word_load W C p p' w); first exact Hflows.
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
    iDestruct ("WorldRes" with "[$Ha $HφV]") as "WorldRes".
    iDestruct (close_world_interp_next with "Hworld_interp Hstate Hrel WorldRes")
      as "Hworld_interp"; eauto.
    { destruct ρ; auto; contradiction. }
    iApply "Hφ"; iRight. iExists loadv'. iFrame "∗#%". done.
  Qed.


  (** The load of [stats_read] through a safe pointer, in a world open on
      [s] that does not hold its address: it faults with an exact fault of
      [stats_load_interp_fault], or it loads a safe word. The register of a
      fault holds the pointer, or the pointer without its tag when it names
      a freed object. When the checks
      of the pointer pass, the trap reads the cell of its address
      ([wp_trap_fault_frac] with the instruction and the cell), so that the
      fault is [fault_default]. *)
  Lemma stats_read_load_interp_open_spec (W : WORLD) (C : CmptName) (s : list LAddr)
    (wptr : LWord) :
    load_key_closed wptr s →
    PC ↦ₚ[th] stats_pcc stats_load_addr ∗
    ca0 ↦ᵣ[th] wptr ∗
    interp W C wptr ∗
    world_interp_open W C s ∗
    codefrag_pers STATS_pcc_b stats_code ∗
    ( (∀ f wf, ⌜wf = wptr ∨ wf = lclear_tag wptr⌝ -∗
        ⌜stats_load_interp_fault wf f⌝ -∗
        ca0 ↦ᵣ[th] wf -∗
        world_interp_open W C s -∗
        trap_safe_cause (stats_load_mcause f) (stats_load_mtval wf f)
          (stats_pcc stats_load_addr) ⊤ (HO th)) ∧
      ▷ (∀ wload,
           PC ↦ₚ[th] stats_pcc stats_release_addr -∗
           ca0 ↦ᵣ[th] wload -∗
           interp W C wload -∗
           world_interp_open W C s -∗
           safe[th]) )
    ⊢ safe[th].
  Proof.
    iIntros (Hclosed) "(HPC & Hca0 & #Hinterp & Hworld & #Hcode_stats & Hcont)".
    iDestruct (stats_load_instr_pers with "Hcode_stats") as "#Hinstr".
    pose proof stats_code_bounds_layout as (HsubBounds & Hpc_shadow & Hpc_nonheap).
    iDestruct (codefrag_contiguous_region_pers with "Hcode_stats") as %Hpc_contiguous;
    cbn [length map encodeInstrsW] in Hpc_contiguous.
    stats_unfold_code.
    rewrite /stats_pcc /stats_load_addr /stats_release_addr.
    (* Block 2: the load *)
    focus_block (stats_block ".Lread_load") "Hcode_stats" of stats_blocks at STATS_pcc_b
      as a_load Ha_load "Hcode" "Hcont_code".
    assert (a_load = stats_load_addr) as Ha_load_eq
      by (rewrite /stats_load_addr; offsets_compute; solve_addr).
    destruct (data_cap_check readAllowed PermitLoadViolation ca0 wptr.(lw) 0)
      as [f | ea] eqn:Hcheck.
    - (* The checks of the pointer fail *)
      (* CLoad ca0 ca0 0 *)
      iInstrApply "Hcode" (wp_load_interp_same_open _ W C s ca0)
        with "[$HPC $Hca0 $Hinterp $Hworld]"
        as (retv) "[(-> & HPC & Hca0 & Hworld) | (%wload & -> & HPC & Hca0 & #Hwload & Hworld)]".
      + (* The fault, exact: the instruction's cell suffices *)
        iDestruct "Hcont" as "[Hfailed _]".
        rewrite Ha_load_eq.
        iDestruct (big_sepM_singleton (λ a w, a ↦ₐ□ w)%I stats_load_addr stats_load_instr
                    with "Hinstr") as "Hlm".
        iDestruct "Hca0" as "[Hca0 | Hca0]".
        * iApply (stats_load_trap _ _ wptr {[stats_load_addr := stats_load_instr]} f
                   with "HPC Hca0 Hlm"); [by simplify_map_eq | | |].
          { apply stats_load_lfault; [by simplify_map_eq | done]. }
          { revert Hcheck. rewrite /data_cap_check.
            destruct (lw wptr) as [| [ [] | [] ] | ? [] | ? [ [] | [] ] ]; cbn;
              try (intros [=<-]; done).
            all: repeat case_match; intros [=<-]; done. }
          iIntros "Hca0 _".
          iApply ("Hfailed" $! f wptr with "[%] [%] Hca0 Hworld"); [by left | by left].
        * (* The pointer of a freed object, untagged *)
          iApply (stats_load_trap _ _ (lclear_tag wptr) {[stats_load_addr := stats_load_instr]}
                   with "HPC Hca0 Hlm"); [by simplify_map_eq | | |].
          { apply stats_load_lfault; [by simplify_map_eq | apply data_cap_check_lclear_tag]. }
          { done. }
          iIntros "Hca0 _".
          iApply ("Hfailed" with "[%] [%] Hca0 Hworld");
            [by right | left; apply data_cap_check_lclear_tag].
      + (* The load succeeds *)
        iDestruct "Hcont" as "[_ Hcont]".
        unfocus_block "Hcode" "Hcont_code" as "Hcode_stats".
        assert (a_load ^+ 1 = (STATS_pcc_b ^+ stats_label ".Lread_release")%a) as ->
          by (offsets_compute; solve_addr).
        iApply ("Hcont" with "HPC Hca0 Hwload Hworld").
    - (* The checks pass: a tagged capability that allows the load, in its bounds *)
      destruct wptr as [w π].
      assert (∃ p g b e a, w = Cap p g b e a ∧ readAllowed p = true ∧
                withinBounds b e a = true ∧ ea = a)
        as (p & g & b & e & a & -> & Hra & Hwb & ->).
      { revert Hcheck. rewrite /data_cap_check /=.
        destruct w as [z | [ [] p g b e a | ] | | ]; cbn; try (intros [=]; fail).
        1: { destruct (readAllowed p) eqn:Hra; last (intros [=]).
             rewrite addr_add_0. destruct (withinBounds b e a) eqn:Hwb; last (intros [=]).
             intros [= <-]. by exists p, g, b, e, a. }
        all: repeat case_match; intros [=]. }
      pose proof (Hclosed p g b e a eq_refl Hwb) as Hnin_s. cbn in Hnin_s.
      (* CLoad ca0 ca0 0 *)
      iInstrApply "Hcode" (stats_load_interp_open_cell _ W C s ca0)
        with "[$HPC $Hca0 $Hinterp $Hworld]"
        as (retv) "[(-> & HPC & [(%wa & %Hnot_shadow & Hca0 & Ha & Hclose_a) |
                                 (Hca0 & Hworld)]) |
                    (%wload & -> & HPC & Hca0 & #Hwload & Hworld)]".
      + (* The fault, exact: the trap reads the instruction and the cell *)
        iDestruct "Hcont" as "[Hfailed _]".
        rewrite Ha_load_eq.
        (* The cell is not the instruction's: the instruction is persistent *)
        destruct (decide (a = stats_load_addr)) as [-> | Hne].
        { iDestruct (pointsto_valid_2 with "Ha Hinstr") as %[Hv _].
          by apply dfrac_valid_own_l in Hv. }
        set (lm := <[stats_load_addr := (DfracDiscarded, stats_load_instr)]>
                     {[a := (DfracOwn 1, wa)]} : gmap Addr (dfrac * LWord)).
        assert (lfault (stats_pcc stats_load_addr) {[ca0 := Cap p g b e a @@? π]}
                  (snd <$> lm) = fault_default) as Hlfault.
        { pose proof stats_load_pc_correct as Hpc.
          rewrite /lfault /lview /trap_fault /=. rewrite /= in Hpc. rewrite Hpc.
          rewrite /lm !lookup_fmap lookup_insert_eq /=
            ?decode_encode_instrW_inv ?decode_encode_instr_inv /instr_fault /load_fault.
          rewrite /lookup_reg /= !lookup_fmap lookup_insert_eq /=.
          destruct (decide (ca0 = cnull)) as [Hc | _]; first done.
          rewrite /data_cap_check Hra addr_add_0 Hwb Hnot_shadow.
          destruct (is_revoker_address a); first done.
          rewrite /= !lookup_fmap lookup_insert_ne // lookup_singleton_eq /=.
          destruct (heap_cap_base (lw wa)) as [base|] eqn:Hbase; last done.
          by destruct (heap_shadow_lookup base (heap_cap_base_heap _ _ Hbase)) as [? ->]. }
        iAssert ([∗ map] a ↦ qx ∈ lm, a ↦ₐ{qx.1} qx.2)%I with "[Ha]" as "Hlm".
        { rewrite /lm big_sepM_insert; last by simplify_map_eq.
          rewrite big_sepM_singleton. iFrame "Hinstr Ha". }
        iDestruct (big_sepM_singleton (λ r w, r ↦ᵣ w)%I ca0 _ with "Hca0") as "Hregs".
        iTrap cause with "Hregs" "Hlm".
        { split; last by rewrite Hlfault.
          intros p0 g0 b0 e0 a0 wi Hpc Hwi. rewrite /stats_pcc /= in Hpc.
          injection Hpc as <- <- <- <- <-.
          rewrite /lm lookup_fmap lookup_insert_eq in Hwi. injection Hwi as <-.
          rewrite /stats_load_instr /= ?decode_encode_instrW_inv ?decode_encode_instr_inv /=
            dom_singleton_L.
          set_solver. }
        iDestruct (big_sepM_singleton (λ r w, r ↦ᵣ w)%I ca0 _ with "Hregs") as "Hca0".
        rewrite /lm big_sepM_insert; last by simplify_map_eq.
        iDestruct "Hlm" as "[_ Hlm]". rewrite big_sepM_singleton.
        iDestruct ("Hclose_a" with "Hlm") as "Hworld".
        iSpecialize ("Hfailed" $! fault_default (Cap p g b e a @@? π)
                       with "[%] [%] Hca0 Hworld").
        { by left. }
        { right. split; [by eexists | done]. }
        iApply (trap_safe_cause_mono with "Hfailed").
        * intros c [Hok ->]. split; first done. by rewrite lcause_lfault Hlfault.
        * intros v (f' & Hok & ->). rewrite /stats_load_mtval.
          assert ((snd <$> lm) !! stats_load_addr = Some stats_load_instr) as Hlm_instr
            by (by rewrite /lm lookup_fmap lookup_insert_eq).
          destruct (stats_load_fault_ok _ _ f' Hlm_instr Hok) as [-> | [Hstrip ->] ];
            [left; by rewrite Hlfault | by right].
      + (* A tombstone: the pointer of a freed object, untagged, faults *)
        iDestruct "Hcont" as "[Hfailed _]".
        rewrite Ha_load_eq.
        iDestruct (big_sepM_singleton (λ a w, a ↦ₐ□ w)%I stats_load_addr stats_load_instr
                    with "Hinstr") as "Hlm".
        iApply (stats_load_trap _ _ (lclear_tag (Cap p g b e a @@? π))
                 {[stats_load_addr := stats_load_instr]}
                 with "HPC Hca0 Hlm"); [by simplify_map_eq | | |].
        { apply stats_load_lfault; [by simplify_map_eq | apply data_cap_check_lclear_tag]. }
        { done. }
        iIntros "Hca0 _".
        iApply ("Hfailed" with "[%] [%] Hca0 Hworld");
          [by right | left; apply data_cap_check_lclear_tag].
      + (* The load succeeds *)
        iDestruct "Hcont" as "[_ Hcont]".
        unfocus_block "Hcode" "Hcont_code" as "Hcode_stats".
        assert (a_load ^+ 1 = (STATS_pcc_b ^+ stats_label ".Lread_release")%a) as ->
          by (offsets_compute; solve_addr).
        iApply ("Hcont" with "HPC Hca0 Hwload Hworld").
  Qed.

  (** ** The faults of the load *)

  (** A repairable exact fault of the load names [ca0], which holds a
      tagged capability. *)
  Lemma stats_load_repairable_ca0 (wptr : LWord) (f : fault) (c v : Z) :
    stats_load_interp_fault wptr f →
    stats_load_mcause f c →
    stats_load_mtval wptr f v →
    stats_repairable c v →
    mtval_reg_field v = reg_index ca0 ∧
    ∃ p g b e a π, wptr = MkLWord (Cap p g b e a) π.
  Proof.
    intros Hf [_ ->] [-> | [_ ->] ] Hrep.
    2: { exfalso. destruct Hrep as (_ & Hcode & _).
         rewrite /= mtval_code_field_encode in Hcode. by apply (inj cause_code_num) in Hcode. }
    destruct (stats_repairable_fault f Hrep) as (r & -> & _).
    destruct Hf as [Hcheck | [_ Hdef] ]; last done.
    destruct wptr as [w π]; cbn in Hcheck.
    destruct w as [z | [ [] p g b e a | ] | | ]; cbn in Hcheck;
      repeat case_match; simplify_eq.
    all: split; [by rewrite /= mtval_reg_field_encode cheri_reg_num_gpr |
                 by eexists _, _, _, _, _, _].
  Qed.

  (** The retried load is not repaired again: its address, the base, is in
      bounds. *)
  Lemma stats_retry_fault_not_repairable (t : bool) (p : Perm) (g : Locality) (b e : Addr)
    (π : option AId) (f : fault) (c v : Z) :
    (b < e)%a →
    stats_load_interp_fault (MkLWord (WCap t p g b e b) π) f →
    stats_load_mcause f c →
    stats_load_mtval (MkLWord (WCap t p g b e b) π) f v →
    ¬ stats_repairable c v.
  Proof.
    intros Hbe Hf Hc Hv Hrep.
    destruct Hc as [_ ->]. destruct Hv as [-> | [_ ->] ].
    2: { destruct Hrep as (_ & Hcode & _). rewrite /= mtval_code_field_encode in Hcode.
         by apply (inj cause_code_num) in Hcode. }
    destruct (stats_repairable_fault f Hrep) as (r & -> & _).
    destruct Hf as [Hcheck | [_ Hdef] ]; last done.
    rewrite /data_cap_check /= in Hcheck. destruct t; last done.
    destruct (readAllowed p); last done.
    rewrite addr_add_0 in Hcheck.
    rewrite (_ : withinBounds b e b = true) in Hcheck;
      [done | apply withinBounds_true_iff; solve_addr].
  Qed.

  (** ** The return and the unwind *)

  (** The return of [stats_read] to an unknown caller, once the callee's
      stack is revoked: [switcher_ret_specification], with safe return
      values. *)
  Lemma stats_read_ret_logrel (W0 : WORLD) (C : CmptName)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) (rmap : LReg)
    (b_stk e_stk : Addr) (l : list LAddr) (stk_mem : list LWord) :
    frame_match Ws Cs cstk W0 C →
    csp_sync cstk b_stk e_stk →
    extract_temporaries_condition W0 (l ++ (LNonHeap <$> finz.seq_between b_stk e_stk)) →
    (∀ r, is_Some (rmap !! r)) →
    na_inv (tpool th) Ntstack trusted_stack_inv -∗
    switcher_static -∗
    interp W0 C (rmap !!! ca0) -∗
    interp W0 C (rmap !!! ca1) -∗
    PC ↦ₚ[th] Cap XSRW_ Local b_switcher e_switcher a_switcher_return -∗
    registers_pointsto rmap -∗
    [[ b_stk , e_stk ]] ↦ₐ [[ stk_mem ]] -∗
    ◯(CSTK)[th] cstk -∗
    interp_continuation cstk Ws Cs -∗
    world_interp (revoke W0) C -∗
    ▷ RevokedResources W0 C l -∗
    na_own (tpool th) ⊤ -∗
    safe[th].
  Proof.
    iIntros (Hframe_match Hsync_csp Hl_unk Hfull)
      "#Hinv_switcher #Hswitcher_static #Hinterp_ca0 #Hinterp_ca1 HPC Hregs Hstk Hcstk HK
       Hworld_C Hrevoked_l Hna".
    destruct Hl_unk as [Hnodup Htemps].
    set (Wfixed := close_list (l ++ (LNonHeap <$> finz.seq_between b_stk e_stk)) (revoke W0)).
    assert (related_sts_pub_world W0 Wfixed) as Hrelated_pub_W0_Wfixed.
    { subst Wfixed. apply related_pub_revoke_close_list; exact Htemps. }
    iAssert (▷ RevokedResources Wfixed C l)%I with "[Hrevoked_l]" as "Hrevoked_l".
    { iNext. iApply (RevokedResources_mono_pub W0 Wfixed C l l Hrelated_pub_W0_Wfixed
                      with "Hrevoked_l"). }
    iDestruct (registers_pointsto_ret_spec with "Hregs") as (rest) "(%Hdom_rest & Hcsp & Hca0 & Hca1 & Hrest)";
      first exact Hfull.
    iApply (switcher_ret_specification W0 (revoke W0) C rest e_stk b_stk l stk_mem
              cstk Ws Cs
             with "[$Hinv_switcher $Hswitcher_static $Hstk $Hcstk $HK $Hworld_C $Hna $HPC
                    $Hrevoked_l $Hrest $Hca0 $Hca1 $Hcsp]").
    { exact Hrelated_pub_W0_Wfixed. }
    { exact Hdom_rest. }
    { exact Hframe_match. }
    { exact Hsync_csp. }
    { exact Hnodup. }
    { intros a Ha; apply Htemps; done. }
    iSplit.
    - iApply (monotone.interp_monotone_same_heap W0 with "[] Hinterp_ca0"); done.
    - iApply (monotone.interp_monotone_same_heap W0 with "[] Hinterp_ca1"); done.
  Qed.

  (** The unwind of [stats_read] for an unknown caller, from the world open
      at the [ErrorState] slot: close [stats_inv], revoke the world with
      the slot that the unwind gives back, and return [ECOMPARTMENTFAIL]
      through [switcher_ret_specification]. *)
  Lemma stats_read_unwind_open (W0 : WORLD) (C : CmptName) (cstk : CSTK)
    (Ws : list WORLD) (Cs : list CmptName) (rfault : LReg)
    (b_stk e_stk cur : Addr) (lv : list LWord) :
    let es := (cur ^+ (- ErrorState_size)) in
    frame_match Ws Cs cstk W0 C →
    csp_sync cstk b_stk e_stk →
    (b_stk <= es)%a →
    (cur <= e_stk)%a →
    rfault !!! csp = lword_of_word (Cap RWL Local b_stk e_stk cur) →
    na_inv (tpool th) Ntstack trusted_stack_inv -∗
    switcher_static -∗
    interp W0 C (Cap RWL Local b_stk e_stk cur) -∗
    world_interp_open W0 C (LNonHeap <$> finz.seq_between es cur) -∗
    ▷ StackOpenWorldResources interp W0 C (finz.seq_between es cur) lv -∗
    interp_continuation cstk Ws Cs -∗
    (▷ stats_inv ∗ na_own (tpool th) (⊤ ∖ ↑Nstats) ={⊤}=∗ na_own (tpool th) ⊤) -∗
    unwind_cont (⊤ ∖ ↑Nstats) cstk (error_state_area rfault ∗ stats_inv).
  Proof.
    intros es Hframe_match Hsync_csp Hb_es Hcur_e Hcsp.
    iIntros "#Hinv_switcher #Hswitcher_static #Hinterp_csp Hworld_open Hslot_res HK Hclose".
    iIntros (n rmap Hfull Hca0 Hca1) "HPC Hregs Hcstk [Harea Hinv] Hna".
    iMod ("Hclose" with "[$Hinv $Hna]") as "Hna".
    rewrite /error_state_area Hcsp /=.
    iDestruct "Harea" as (ws) "[%Hws Hslot]".
    (* Revoke the world open at the slot: the whole stack comes back *)
    iMod (world_interp_revoke_stack_open W0 C b_stk e_stk cur es cur lv ws
            with "[$Hinterp_csp $Hworld_open $Hslot_res $Hslot]")
      as (l) "(%Hl_unk & Hworld_C & _ & _ & >[%stk_mem Hstk] & Hrevoked_l & _)";
      [done | done |].
    iApply (stats_read_ret_logrel W0 C (cstack_set_top_count cstk n) Ws Cs rmap
              b_stk e_stk l stk_mem
             with "Hinv_switcher Hswitcher_static [] [] HPC Hregs Hstk Hcstk [HK] Hworld_C
                   Hrevoked_l Hna").
    { by apply frame_match_set_top_count. }
    { by rewrite csp_sync_set_top_count. }
    { exact Hl_unk. }
    { exact Hfull. }
    { rewrite (lookup_total_correct _ _ _ Hca0). iApply interp_int. }
    { rewrite (lookup_total_correct _ _ _ Hca1). iApply interp_int. }
    { by rewrite interp_cont_set_top_count. }
  Qed.

  (** The export of [stats_read] is safe: it satisfies [ot_switcher_prop]
      in any world, for any compartment. *)
  Lemma stats_read_entry_point_spec
    (g_tbl : Locality) (W : WORLD) (C : CmptName) :
    STATS_pcc_b ≠ b_switcher →
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static ∗
    stats_static ∗
    na_inv (tpool th) Nstats stats_inv
    -∗
    ot_switcher_prop W C
      (Cap RO g_tbl b_stats_exp_tbl e_stats_exp_tbl stats_read_exp_tbl_addr).
  Proof.
    iIntros (Hswitcher)
      "(#Hinv_switcher & #Hswitcher_static & #Hstatic & #Hinv_stats)".
    iPoseProof "Hstatic" as "Hstatic'". iNamed "Hstatic'".
    pose proof stats_exp_tbl_size as Hstats_exp_tbl_size.
    rewrite /length_stats_exports_tbl /stats_nb_exports in Hstats_exp_tbl_size.
    iExists g_tbl, b_stats_exp_tbl, e_stats_exp_tbl, stats_read_exp_tbl_addr,
      STATS_pcc_b, STATS_pcc_e, STATS_cgp_b, STATS_cgp_e, stats_read_nargs,
      stats_read_min_stack, (Z.of_nat stats_read_pcc_off), InterruptDisabled,
      (Z.of_nat stats_handler_pcc_off), ExportTable_no_handler.
    iFrame "Htbl_pcc Htbl_cgp Htbl_eh Htbl_ehs Htbl_read".
    iSplit; first done.
    iSplit; first (iPureIntro; exact stats_exp_tbl_disjoint_from_shadow).
    iSplit.
    { iPureIntro. rewrite /stats_read_exp_tbl_addr /stats_read_exp_tbl_off /stats_entry_read.
      solve_addr. }
    iSplit.
    { iPureIntro. rewrite /stats_read_exp_tbl_addr /stats_read_exp_tbl_off /stats_entry_read.
      solve_addr. }
    iSplit.
    { iPureIntro. rewrite /stats_read_exp_tbl_addr /stats_read_exp_tbl_off /stats_entry_read.
      solve_addr. }
    iSplit; first (iPureIntro; rewrite /stats_read_nargs; lia).
    iSplit; first (iPureIntro; rewrite /stats_read_min_stack; lia).
    iSplit.
    { iPureIntro.
      pose proof STATS_size_imports as Hsize_imports.
      pose proof STATS_size_code as Hsize_code.
      rewrite stats_read_pcc_off_eq. cbn in Hsize_code. solve_addr. }
    iSplit.
    { iPureIntro. eapply disjoint_from_shadow_not_in.
      - exact stats_exp_tbl_disjoint_from_shadow.
      - apply withinBounds_true_iff.
        rewrite /stats_read_exp_tbl_addr /stats_read_exp_tbl_off /stats_entry_read; solve_addr. }
    iSplit.
    { iPureIntro. eapply disjoint_from_shadow_not_in.
      - exact stats_exp_tbl_disjoint_from_shadow.
      - apply withinBounds_true_iff; solve_addr. }
    iSplit.
    { iPureIntro. eapply disjoint_from_shadow_not_in.
      - exact stats_exp_tbl_disjoint_from_shadow.
      - apply withinBounds_true_iff; solve_addr. }
    iSplit; first (iPureIntro; exact STATS_pcc_base_not_heap).
    iSplit; first (iPureIntro; exact STATS_cgp_base_not_heap).
    iIntros "!> %W0 %Hpriv_W_W0 !> %cstk %Ws %Cs %rmap %b_stk %e_stk".
    iIntros "(HK & %Hframe_match & %Htop_tbl & HPC & Hregister_state & Hrmap & Hworld_C &
      %Hsync_csp & %Hminstk & Hcstk & Hna)".
    iDestruct "Hregister_state" as
      "(%Hfull & %Hcgp & [%mie_ret %Hcra] & %Hcsp & #Hinterp_csp & #Hinterp_rmap & _)".
    set (cur := stk_start_a b_stk e_stk).
    destruct Htop_tbl as (Hframes & Htbl & Hcount & Htbl_ok).
    rewrite /stats_read_min_stack in Hminstk.
    set (wret :=
      Sentry (ret_kind mie_ret) XSRW_ Local b_switcher e_switcher a_switcher_return).
    destruct (Hfull ca0) as [wptr Hwptr].
    iAssert (interp W0 C wptr) as "#Hinterp_wptr".
    { iApply "Hinterp_rmap"; iPureIntro; last exact Hwptr.
      rewrite /stats_read_nargs /dom_arg_rmap /=. set_solver+. }
    (* The cell of the frame's table holds the table *)
    pose proof (tf_export_tbl_ok_nonzero _ Htbl_ok) as Htbl_set.

    (* Open [stats_inv], take the lock *)
    iApply (stats_read_take_open rmap with "Hinv_stats Hstatic HPC Hrmap Hna"); [done | done |].
    iNext. iIntros "HPC Hregs Hlock Hna Hclose".
    set (rtake := <[ct0:=lword_of_word (WInt 0)]> (rmap : LReg)).
    assert (∀ r, is_Some (rtake !! r)) as Hfull_take.
    { intros r. rewrite /rtake lookup_insert_is_Some'. by right. }
    assert (rtake !! cgp = Some stats_wcgp) as Hcgp_take.
    { by rewrite /rtake lookup_insert_ne. }
    assert (rtake !!! csp = lword_of_word (Cap RWL Local b_stk e_stk cur)) as Hcsp_take.
    { rewrite /rtake lookup_total_alt. by simplify_map_eq. }
    assert (rtake !!! cra = lword_of_word wret) as Hcra_take.
    { rewrite /rtake lookup_total_alt. by simplify_map_eq. }
    assert (rtake !! ca0 = Some wptr) as Hca0_take.
    { by rewrite /rtake lookup_insert_ne. }
    clearbody rtake.
    iDestruct (registers_pointsto_extract _ ca0 with "Hregs") as "[Hca0 Hregs]"; first exact Hca0_take.
    (* The slot of the [ErrorState], below the cursor of the stack *)
    set (es := cur ^+ (- ErrorState_size)).
    assert ((b_stk <= es)%a ∧ (es + 16)%a = Some cur ∧ (cur <= e_stk)%a) as
      (Hb_es & Hes_cur & Hcur_e).
    { rewrite /es /cur /stk_start_a /ErrorState_size /StackEntry_reserved_space in Hminstk |- *.
      split_and!; solve_addr. }
    iDestruct (interp_cap_regions with "Hinterp_csp") as %[Hcsp_mmio _]; first done.
    pose proof (disjoint_from_mmio_shadow _ _ Hcsp_mmio) as Hstk_shadow.

    set (slot := finz.seq_between es cur).
    (* The load, in the world open on nothing *)
    iEval (rewrite open_world_interp_empty) in "Hworld_C".
    iApply (stats_read_load_interp_open_spec W0 C [] wptr
             with "[$HPC $Hca0 $Hinterp_wptr $Hworld_C $Hcode_stats
                    Hregs Hlock Hna Hclose Hcstk HK]").
    { intros p0 g0 b0 e0 a0 _ _. apply not_elem_of_nil. }
    iSplit.
    - (* The load faults, with its exact fault [f]: borrow the slot, lend it *)
      iIntros (f wf Hwf Hf) "Hca0 Hworld_C".
      iDestruct ("Hregs" with "Hca0") as "Hregs".
      iAssert (interp W0 C wf) as "#Hinterp_wf".
      { destruct Hwf as [-> | ->]; [iExact "Hinterp_wptr" | iApply interp_clear_tag]. }
      set (rfault := <[ca0:=wf]> rtake).
      assert (∀ r, is_Some (rfault !! r)) as Hfull_fault.
      { intros r. rewrite /rfault lookup_insert_is_Some'. right. apply Hfull_take. }
      assert (rfault !! cgp = Some stats_wcgp) as Hcgp_fault.
      { by rewrite /rfault lookup_insert_ne. }
      assert (rfault !!! csp = lword_of_word (Cap RWL Local b_stk e_stk cur)) as Hcsp_fault.
      { by rewrite /rfault lookup_total_insert_ne. }
      assert (rfault !!! cra = lword_of_word wret) as Hcra_fault.
      { by rewrite /rfault lookup_total_insert_ne. }
      assert (rfault !! ca0 = Some wf) as Hca0_fault.
      { by rewrite /rfault lookup_insert_eq. }
      clearbody rfault.
      iApply trap_safe_fupd. iSplitL; last by iIntros "!> %Hv".
      iDestruct (open_world_interp_opening_resources W0 C slot [] Local b_stk e_stk cur
                  with "[$Hinterp_csp Hworld_C]")
        as "[Hworld_open (%lv & Hslot & Hslot_res)]".
      { apply finz_seq_between_NoDup. }
      { apply Forall_forall. intros x Hx%elem_of_finz_seq_between. solve_addr. }
      { set_solver. }
      { by rewrite fmap_nil. }
      iEval (rewrite app_nil_r) in "Hworld_open".
      iDestruct (big_sepL2_length with "Hslot") as %Hlen_lv.
      iModIntro.
      iApply (stats_read_fault_safe _ _ cstk rfault Local b_stk e_stk cur
               with "Hinv_switcher Hswitcher_static Hstatic Hregs Hcstk Hna Hlock [Hslot] [-]").
      { by intros c [Hok _]. }
      1-3: done.
      { by apply lookup_total_correct. }
      { rewrite Hcra_fault. apply jalr_target_ok_switcher_return_sentry. }
      { rewrite /ErrorState_size. solve_addr. }
      { done. }
      { apply (disjoint_from_shadow_weaken b_stk e_stk es cur); [done | done | exact Hstk_shadow]. }
      { done. }
      { by rewrite Hcount. }
      { rewrite Hcount /MAX_FAULTS_PER_COMPARTMENT_CALL. lia. }
      { exact Htbl_set. }
      { intros c v Hc Hv Hrep.
        destruct (stats_load_repairable_ca0 _ _ _ _ Hf Hc Hv Hrep)
          as [Hreg (p0 & g0 & b0 & e0 & a0 & π0 & ->)].
        exists ca0, p0, g0, b0, e0, a0, π0. split; [by rewrite Hreg | exact Hca0_fault]. }
      { rewrite /error_state_area Hcsp_fault /=. iExists lv. iFrame "Hslot".
        iPureIntro. rewrite -Hlen_lv /slot finz_seq_between_length /finz.dist /ErrorState_size.
        solve_addr. }
      iIntros (c v Hc Hv). iNext. rewrite /stats_fault_conts. iSplit.
      + (* Retry: the base is outside the slot *)
        iIntros (Hretries r' p' g' b' e' a' π' w' [Hidx Hr'] Hbe' Hout' Hw') "Hlock Harea".
        destruct (stats_load_repairable_ca0 _ _ _ _ Hf Hc Hv (proj1 Hretries))
          as [Hreg _].
        rewrite Hreg in Hidx. apply (inj reg_index) in Hidx as ->.
        rewrite Hca0_fault in Hr'. injection Hr' as ->.
        set (wrep := stats_repair_word w').
        set (rretry := stats_retry_regs rfault ca0 w').
        iAssert (interp W0 C wrep) as "#Hinterp_wrep".
        { destruct Hw' as [-> | [_ ->] ]; rewrite /wrep /=.
          - by rewrite (interp_cap_cur_addr W0 C true p' g' b' e' b' a' π').
          - by iApply interp_untagged. }
        assert (load_key_closed wrep (LNonHeap <$> slot)) as Hclosed.
        { intros p1 g1 b1 e1 a1 Hw1 _.
          destruct Hw' as [-> | [_ ->] ]; cbn in Hw1; simplify_eq.
          destruct π' as [ι|]; cbn; rewrite list_elem_of_fmap.
          - by intros (x & [=] & _).
          - intros (x & [= ->] & Hx). rewrite elem_of_finz_seq_between in Hx.
            rewrite /stats_outside_slot Hcsp_fault /= in Hout'.
            rewrite /es /ErrorState_size in Hx Hes_cur Hout'. solve_addr. }
        assert (rretry !!! csp = rfault !!! csp) as Hcsp_retry.
        { rewrite /rretry /stats_retry_regs !lookup_total_alt. by simplify_map_eq. }
        iIntros (_) "HPC Hregs Hcstk Hna".
        iDestruct (registers_pointsto_extract _ ca0 with "Hregs") as "[Hca0 Hregs]";
          first by rewrite /rretry /stats_retry_regs lookup_insert_eq.
        (* The retried load, in the world open at the slot *)
        iApply (stats_read_load_interp_open_spec W0 C (LNonHeap <$> slot) wrep
                 with "[$HPC $Hca0 $Hinterp_wrep $Hworld_open $Hcode_stats
                        Hregs Hlock Hna Hclose Hcstk HK Hslot_res Harea]");
          first exact Hclosed.
        iSplit.
        * (* It faults: not repairable, unwind at count 2 *)
          iIntros (f2 wf2 Hwf2 Hf2) "Hca0 Hworld_open".
          iDestruct ("Hregs" with "Hca0") as "Hregs".
          set (rretry2 := <[ca0:=wf2]> rretry).
          assert (rretry2 !!! csp = rfault !!! csp) as Hcsp_retry2.
          { by rewrite /rretry2 lookup_total_insert_ne // Hcsp_retry. }
          set (cstk2 := cstack_set_top_count cstk (top_error_count cstk + 2)).
          iApply (stats_read_fault_safe _ _ cstk2 rretry2 Local b_stk e_stk cur
                   with "Hinv_switcher Hswitcher_static Hstatic Hregs Hcstk Hna Hlock [Harea] [-]").
          { by intros c2 [Hok _]. }
          { done. }
          { intros r. rewrite /rretry2 /rretry /stats_retry_regs !lookup_insert_is_Some'.
            by right; right; right. }
          { by rewrite Hcsp_retry2. }
          { rewrite /rretry2 /rretry /stats_retry_regs !lookup_total_insert_ne //.
            by apply lookup_total_correct. }
          { rewrite /rretry2 /rretry /stats_retry_regs !lookup_total_insert_ne // Hcra_fault.
            apply jalr_target_ok_switcher_return_sentry. }
          { rewrite /ErrorState_size. solve_addr. }
          { done. }
          { apply (disjoint_from_shadow_weaken b_stk e_stk es cur);
              [done | done | exact Hstk_shadow]. }
          { by rewrite /cstk2 top_export_tbl_set_count. }
          { by rewrite /cstk2 top_error_count_set_count Hcount. }
          { rewrite /cstk2 top_error_count_set_count Hcount /MAX_FAULTS_PER_COMPARTMENT_CALL. lia. }
          { by rewrite /cstk2 top_tframe_set_count. }
          { intros c2 v2 Hc2 Hv2 Hrep2. exfalso.
            destruct Hw' as [-> | [_ ->] ]; destruct Hwf2 as [-> | ->];
              rewrite /wrep /= in Hf2 Hv2;
              (eapply (stats_retry_fault_not_repairable _ _ _ b' e' π' f2 c2 v2);
               [done | exact Hf2 | exact Hc2 | exact Hv2 | exact Hrep2]). }
          { rewrite /error_state_area Hcsp_retry2. iExact "Harea". }
          iIntros (c2 v2 Hc2 Hv2). iNext. rewrite /stats_fault_conts. iSplit.
          { iIntros ([Hrep2 _]). exfalso.
            destruct Hw' as [-> | [_ ->] ]; destruct Hwf2 as [-> | ->];
              rewrite /wrep /= in Hf2 Hv2;
              (eapply (stats_retry_fault_not_repairable _ _ _ b' e' π' f2 c2 v2);
               [done | exact Hf2 | exact Hc2 | exact Hv2 | exact Hrep2]). }
          iIntros (_).
          iApply (stats_read_unwind_open W0 C cstk2 Ws Cs rretry2 b_stk e_stk cur lv
                   with "Hinv_switcher Hswitcher_static Hinterp_csp Hworld_open Hslot_res
                         [HK] Hclose").
          { by apply frame_match_set_top_count. }
          { by rewrite csp_sync_set_top_count. }
          { done. }
          { done. }
          { by rewrite Hcsp_retry2. }
          { by rewrite interp_cont_set_top_count. }
        * (* It succeeds: release, revoke the world open at the slot, return at count 2 *)
          iNext. iIntros (wload) "HPC Hca0 #Hinterp_wload Hworld_open".
          iDestruct ("Hregs" with "Hca0") as "Hregs".
          (* Revoke the world open at the slot: the whole stack comes back *)
          rewrite /error_state_area Hcsp_fault /=.
          iDestruct "Harea" as (ws) "[%Hws Hslot]".
          iMod (world_interp_revoke_stack_open W0 C b_stk e_stk cur es cur lv ws
                  with "[$Hinterp_csp $Hworld_open $Hslot_res $Hslot]")
            as (l) "(%Hl_unk & Hworld_C & _ & _ & >[%stk_mem Hstk] & Hrevoked_l & _)";
            [done | done |].
          iApply (stats_read_release_close with "Hstatic HPC Hregs Hlock Hna Hclose").
          { intros r. rewrite !lookup_insert_is_Some'. by right; right; right. }
          { rewrite /rretry /stats_retry_regs. by simplify_map_eq. }
          { rewrite lookup_total_insert_ne // /rretry /stats_retry_regs
              !lookup_total_insert_ne // Hcra_fault.
            apply jalr_target_ok_switcher_return_sentry. }
          iNext. iIntros "HPC Hregs Hna".
          set (M := <[ca1:=lword_of_word (WInt 0)]> (<[ca0:=wload]> rretry)).
          assert (<[ca0:=wload]> rretry !!! cra = lword_of_word wret) as Hret_cra.
          { rewrite -Hcra_fault !lookup_total_alt /rretry /stats_retry_regs. by simplify_map_eq. }
          iEval (rewrite Hret_cra /=) in "HPC".
          iApply (stats_read_ret_logrel W0 C _ Ws Cs M b_stk e_stk l stk_mem
                   with "Hinv_switcher Hswitcher_static [] [] HPC Hregs Hstk Hcstk [HK]
                         Hworld_C Hrevoked_l Hna").
          { by apply frame_match_set_top_count. }
          { by rewrite csp_sync_set_top_count. }
          { exact Hl_unk. }
          { intros r. rewrite /M !lookup_insert_is_Some'. by right; right; right; right. }
          { rewrite /M lookup_total_alt. by simplify_map_eq. }
          { rewrite /M lookup_total_alt. simplify_map_eq. iApply interp_int. }
          { by rewrite interp_cont_set_top_count. }
      + (* Unwind *)
        iIntros (_).
        iApply (stats_read_unwind_open W0 C cstk Ws Cs rfault b_stk e_stk cur lv
                 with "Hinv_switcher Hswitcher_static Hinterp_csp Hworld_open Hslot_res HK Hclose");
          [done | done | done | done | exact Hcsp_fault].
    - (* The load succeeds: revoke the stack, release, and return *)
      iNext. iIntros (wload) "HPC Hca0 #Hinterp_wload Hworld_C".
      iEval (rewrite -open_world_interp_empty) in "Hworld_C".
      iDestruct ("Hregs" with "Hca0") as "Hregs".
      iMod (world_interp_revoke_stack with "[$Hinterp_csp $Hworld_C]")
        as (l) "(%Hl_unk & Hworld_C & _ & _ & Hstk & Hrevoked_l & _)".
      iApply (stats_read_release_close with "Hstatic HPC Hregs Hlock Hna Hclose").
      { intros r. rewrite lookup_insert_is_Some'. by right. }
      { by rewrite lookup_insert_ne. }
      { rewrite lookup_total_insert_ne // Hcra_take. apply jalr_target_ok_switcher_return_sentry. }
      iNext. iIntros "HPC Hregs Hna".
      iDestruct "Hstk" as (stk_mem) "Hstk".
      set (M := <[ca1:=lword_of_word (WInt 0)]> (<[ca0:=wload]> rtake)).
      assert (<[ca0:=wload]> rtake !!! cra = lword_of_word wret) as Hret_cra.
      { rewrite -Hcra_take !lookup_total_alt. by simplify_map_eq. }
      iEval (rewrite Hret_cra /=) in "HPC".
      iApply (stats_read_ret_logrel W0 C cstk Ws Cs M b_stk e_stk l
               with "Hinv_switcher Hswitcher_static [] [] HPC Hregs Hstk Hcstk HK Hworld_C
                     Hrevoked_l Hna").
      { exact Hframe_match. }
      { exact Hsync_csp. }
      { exact Hl_unk. }
      { intros r. rewrite /M !lookup_insert_is_Some'. by right; right. }
      { rewrite /M lookup_total_alt. by simplify_map_eq. }
      { rewrite /M lookup_total_alt. simplify_map_eq. iApply interp_int. }
  Qed.

End Error_Handling_Read_Safe.
