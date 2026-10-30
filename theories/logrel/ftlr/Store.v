From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Export logrel monotone.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Import rules_Store rules_deref_quar wp_rules_interp.
From griotte Require Import map_simpl register_tactics.
Import CoreWPNotations.
Import uPred.


Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {cthreads : CmptThreads} {CL : CritLink Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  #[local] Notation D := (interpO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (D).

  (** Two regions of the same key outside the heap, in the same part, have
      the same contents, one step later. *)
  Lemma region_rel_part_pc_content_agree ρ W C a p1 p2 P1 P2 :
    region_rel_part ρ W C (LNonHeap a) p1 P1 -∗
    region_rel_part ρ W C (LNonHeap a) p2 P2 -∗
    ∀ v, ▷ (pc_content ρ W C P1 v ≡ pc_content ρ W C P2 v).
  Proof.
    iIntros "#H1 #H2" (v). destruct ρ; rewrite /region_rel_part /region_rel_g /region_rel_l /pc_content.
    - iDestruct (rel_g_agree with "H1 H2") as "[_ Heq]". iApply ("Heq" $! (C, v)).
    - iDestruct "H1" as "(H1 & _)". iDestruct "H2" as "(H2 & _)".
      iDestruct (rel_l_agree with "H1 H2") as "[_ Heq]". iApply ("Heq" $! (W, C, v)).
  Qed.

  (** The write condition of a store into the PC's region through a
      register: the region's predicate holds of the stored word. *)
  Definition pc_store_cond W C ρ (P : D) (p : Perm) : iProp Σ :=
    □ ∀ v, interp W C v -∗ pc_content ρ W C P (lstore_word p v).

  (* A decision procedure that does not unfold [reg_allows_store_imm], so that
     the definitions below can be rewritten under [(a + imm)%a]. *)
  #[local] Instance reg_allows_store_imm_dec regs r imm p g b e a ea :
    Decision (reg_allows_store_imm regs r imm p g b e a ea) | 0.
  Proof. rewrite /reg_allows_store_imm. apply _. Defined.

  Lemma store_prov_eq (imm : Z) {regs r p0 g0 b0 e0 a0 ea π}:
    reg_allows_store_imm regs r imm p0 g0 b0 e0 a0 ea →
    read_reg_prov regs r π →
    regs !! r = Some (Cap p0 g0 b0 e0 a0 @@? π).
  Proof. intros (Hinr0 & _) Hπ. by apply read_reg_prov_cap. Qed.

  Lemma store_inr_eq (imm : Z) {regs r p0 g0 b0 e0 a0 ea t1 p1 g1 b1 e1 a1}:
    reg_allows_store_imm regs r imm p0 g0 b0 e0 a0 ea →
    read_reg_inr regs r t1 p1 g1 b1 e1 a1 →
    p0 = p1 ∧ g0 = g1 ∧ b0 = b1 ∧ e0 = e1 ∧ a0 = a1.
  Proof.
    intros Hrar H3.
    destruct Hrar as (Hinr0 & _).
    destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hinr0) as (_ & π & Hr).
    rewrite /read_reg_inr Hr in H3. by inversion H3.
  Qed.

  Lemma interp_hpf_eq {dq : dfrac} (imm : Z) (W : WORLD) (C : CmptName) P (regs : leibnizO LReg)
    (r1 : RegName) p g b e a pc_a pc_p pc_p' ρ w_pc :
    read_reg_prov regs r1 None
    → reg_allows_store_imm regs r1 imm p g b e a pc_a
    → PermFlowsTo pc_p pc_p'
    → (∀ (r1 : RegName) v, ⌜regs !! r1 = Some v⌝ → interp W C v)
    -∗ region_rel_part ρ W C (LNonHeap pc_a) pc_p' P
    -∗ world_interp_open W C [LNonHeap pc_a]
    -∗ pc_a ↦ₐ{dq} w_pc
    -∗ world_interp_open W C [LNonHeap pc_a] ∗ pc_a ↦ₐ{dq} w_pc ∗
       ⌜PermFlowsTo p pc_p' ∧ (ρ = InGlobal → isWL p = false)⌝ ∗
       ▷ pc_store_cond W C ρ P p.
  Proof.
    intros Hπ Hrar Hfl.
    pose proof (store_prov_eq imm Hrar Hπ) as Hr1.
    destruct Hrar as (_ & Hadd & Hwa & Hwb).
    iIntros "Hreg #Hinva Hw Ha".
    iDestruct ("Hreg" $! r1 _ Hr1) as "Hr1".
    iDestruct (write_allowed_inv _ _ pc_a with "Hr1")
      as (p'' P'' Hflp'' Hcond_pers'') "(Hrel'' & Hzcond'' & #Hwcond'' & Hrcond'')"; auto.
    { apply andb_true_iff in Hwb as [Hle Hge].
      split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
    iDestruct (region_rel_part_of with "Hrel''") as (ρ'' Hρ'') "#Hpart''".
    iDestruct (region_rel_part_agree_open _ _ _ pc_a with "Hw Ha Hinva Hpart''")
      as "($ & $ & %Heq)".
    destruct Heq as [<- ->].
    iDestruct (region_rel_part_pc_content_agree with "Hpart'' Hinva") as "#Heq".
    iSplit; first done.
    iNext. iIntros "!>" (v) "#Hv".
    iDestruct (pc_content_wcond with "Hwcond'' Hv") as "HP"; first exact Hρ''.
    by iRewrite ("Heq" $! (lstore_word p v)) in "HP".
  Qed.

  (** A register's capability allows a store to one address only. *)
  Lemma reg_allows_store_imm_det (imm : Z) {regs r p g b e a ea p1 g1 b1 e1 a1 ea1} :
    reg_allows_store_imm regs r imm p g b e a ea →
    reg_allows_store_imm regs r imm p1 g1 b1 e1 a1 ea1 →
    p1 = p ∧ g1 = g ∧ b1 = b ∧ e1 = e ∧ a1 = a ∧ ea1 = ea.
  Proof.
    intros (Hd1 & Hadd1 & _) (Hd2 & Hadd2 & _). rewrite Hd1 in Hd2.
    injection Hd2 as <- <- <- <- <-.
    rewrite Hadd1 in Hadd2. by injection Hadd2 as <-.
  Qed.

  (** The store case. The target's region holds a points-to, stored by the
      ordinary rule, or a zone cell, stored by the zone store, which moves
      MSHWM. The fetch uses half of the PC's cell, except for a store to
      the PC's own zone cell, which takes the fetch half and the token. *)
   Lemma store_case (imm : Z) (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
     (p p' : Perm) (g : Locality) (b e a : Addr) (w : LWord)
     (ρ : region_part) (dst : RegName) (src : Z + RegName) (P : D) :
     ftlr_instr W C regs p p' g b e a w (Store dst src imm) ρ P.
   Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hi.
    iIntros (hb) "@".

    iDestruct (pc_open_acc_forall with "Hinva WorldRes") as "[ (>Hpc & Hinterp) WorldRes ]".

    pose proof Hsome as Hsome'.
    assert (∃ t0 p0 g0 b0 e0 a0 π0,
               read_reg_inr regs dst t0 p0 g0 b0 e0 a0 ∧
               read_reg_prov regs dst π0)
      as (t0 & p0 & g0 & b0 & e0 & a0 & π0 & HVdst & HVπ).
    {
      specialize Hsome' with dst as Hdst.
      destruct Hdst as [wdst Hsomedst].
      unfold read_reg_inr, read_reg_prov. rewrite Hsomedst.
      destruct wdst as [ [|[ t0 p0 g0 b0 e0 a0|] | | ] π0];
        try (exists true,p,g,b,e,a,None; done).
      by repeat eexists.
    }
    assert (∃ storev, lword_of_argument regs src = Some storev)
      as [storev Hwoa].
    { destruct src as [z|r].
      - by eexists.
      - destruct (Hsome' r) as [wr Hwr].
        exists (if decide (r = cnull) then lnull else wr).
        rewrite /lword_of_argument /llookup_reg. by case_decide.
    }
    iAssert (⌜∀ p1 g1 b1 e1 a1 ea1,
      reg_allows_store_imm regs dst imm p1 g1 b1 e1 a1 ea1 →
      is_shadow_address ea1 = false⌝)%I as %Hnonshadow.
    { iIntros (p1 g1 b1 e1 a1 ea1 (Hdst & Hadd & Hwa & Hwb)).
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hdst) as (Hdst_null & π1 & Hdst').
      iApply (interp_cap_not_shadow with "[Hreg]"); eauto using writeAllowed_nonO.
      by iApply "Hreg".
    }
    assert (regs_of (Store dst src imm) ⊆ dom regs) as Hregs_dom.
    { rewrite /subseteq /map_subseteq. intros rr _. rewrite elem_of_dom. apply Hsome. }
    iAssert (interp W C storev) as "#HVstorev".
    { iApply (interp_lword_of_argument with "Hreg"); eauto. }

    assert ((∃ ea, (a0 + imm)%a = Some ea ∧ reg_allows_store_imm regs dst imm p0 g0 b0 e0 a0 ea) ∨
            ¬ (∃ ea, (a0 + imm)%a = Some ea ∧ reg_allows_store_imm regs dst imm p0 g0 b0 e0 a0 ea))
      as Hcase.
    { destruct (a0 + imm)%a as [ea|] eqn:Hea.
      - destruct (decide (reg_allows_store_imm regs dst imm p0 g0 b0 e0 a0 ea)) as [Hal|Hal].
        + left. by exists ea.
        + right. intros (ea' & Hea' & Hal'). by simplify_eq.
      - right. by intros (ea' & Hea' & _). }
    destruct Hcase as [(ea & Hea & Hallows) | Hnallows]; cycle 1.
    { (* The store faults: the fetch uses half of the PC's cell *)
      iDestruct (region_cell_fetch with "Hpc") as "[Ha Hrest]".
      iDestruct (key_share_deref None a with "[]") as (dw Hdw) "[Hdw _]"; first done.
      iApply (wp_store_imm_fetch _ _ _ _ _ _ _ _ _ _ _ ∅ _ _ dw
               with "[$HPC $Ha $Hdw $Hmap]"); eauto.
      { exists t0, p0, g0, b0, e0, a0, storev. split; first done. split; first done.
        destruct (Some_dec (a0 + imm)%a) as [ [ea Hea] | Hea];
          rewrite /reg_allows_store_imm Hea; [|done].
        case_decide as Hal; last done. exfalso. apply Hnallows. exists ea. split; first done.
        rewrite /reg_allows_store_imm Hea. done. }
      iNext. iIntros (lpc' mem' retv) "(%HSpec & HPC & Ha & _ & _ & Hmap)".
      destruct HSpec as [p1 g1 b1 e1 a1 ea1 storev1 oldv1 _ _ _ Hlookup1 _ _ _
                        |p1 g1 b1 e1 a1 ea1 heap_a1 z1 π1 old1 _ Hallow1 Hsh1 _ _ _ _ _
                        | _ _ _ ->].
      - by rewrite lookup_empty in Hlookup1.
      - exfalso. by rewrite (Hnonshadow _ _ _ _ _ _ Hallow1) in Hsh1.
      - iDestruct ("Hrest" with "Ha") as "Hpc".
        iDestruct ("WorldRes" with "[$Hpc $Hinterp]") as "WorldRes".
        iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.
        iNext. iApply (ftlr_post_fault with "HPC Hmap Hhwm Hreg Hworld_interp"); eauto. }

    pose proof (store_prov_eq imm Hallows HVπ) as Hdst.
    pose proof Hallows as (_ & _ & Hwa & Hwb).
    destruct (decide (addr_key π0 ea = LNonHeap a)) as [Hkey|Hkey].
    - (* A store to the PC's own address: the register's write condition *)
      destruct (addr_key_pc _ _ _ Hkey) as [-> ->].
      iDestruct (region_cell_fetch with "Hpc") as "[Ha Hrest]".
      iDestruct (interp_hpf_eq imm W C P regs dst p0 g0 b0 e0 a0 a p p' ρ w
                  with "Hreg Hinva Hworld_interp Ha")
        as "(Hworld_interp & Ha & [%Hflp %Hρwl] & #Hstcond)"; eauto.
      iDestruct ("Hrest" with "Ha") as "Hpc".
      iAssert (▷ pc_content ρ W C P (lstore_word p0 storev))%I as "HPstored".
      { iNext. by iApply "Hstcond". }
      iDestruct (region_cell_cases ρ None a w with "Hpc") as "[Ha | ([_ [-> ->]] & Hcell)]".
      + (* The PC's region holds the points-to *)
        iEval (rewrite addr_key_None key_pointsto_nonheap) in "Ha".
        iApply (wp_store_imm (CL := link_core) _ _ _ _ _ _ _ _ _ _ _ (<[a:=w]> ∅)
                 with "[$HPC $Hmap Ha]"); eauto.
        { by rewrite lookup_insert_eq. }
        { exists t0, p0, g0, b0, e0, a0, storev. split; first done. split; first done.
          rewrite /reg_allows_store_imm Hea. case_decide; last done.
          eexists. by rewrite lookup_insert_eq. }
        { iNext. by iApply memMap_resource_1. }
        iNext. iIntros (lpc' mem' retv) "(%HSpec & HPC & Hmem & Hmap)".
        destruct HSpec as [p1 g1 b1 e1 a1 ea1 storev1 oldv1 Harg1 Hallow1 Hsh1 Hlookup1 -> _ Hincr
                          |p1 g1 b1 e1 a1 ea1 heap_a1 z1 π1 old1 _ Hallow1 Hsh1 _ _ _ _ _
                          | -> _ _ ->].
        * destruct (reg_allows_store_imm_det imm Hallows Hallow1) as (-> & -> & -> & -> & -> & ->).
          rewrite Hwoa in Harg1. injection Harg1 as <-.
          rewrite insert_insert_eq -memMap_resource_1.
          apply incrementPC_Some_inv in Hincr
            as (tpc & ppc & gpc & bpc & epc & apc & apc' & πpc & HPCeq & Hapc' & ->).
          injection HPCeq as <- <- <- <- <- <- <-.
          iNext.
          iDestruct ("WorldRes" with "[Hmem $HPstored]") as "WorldRes".
          { iApply (region_cell_nonheap ρ a with "Hmem"). }
          iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.
          iApply (ftlr_post_next with "HPC Hmap Hhwm [] [] Hworld_interp"); auto.
          iApply "IH". iApply (interp_next_PC with "Hinv_interp"); eauto.
        * exfalso. by rewrite (Hnonshadow _ _ _ _ _ _ Hallow1) in Hsh1.
        * rewrite -memMap_resource_1.
          iDestruct ("WorldRes" with "[Hmem $Hinterp]") as "WorldRes".
          { iApply (region_cell_nonheap ρ a with "Hmem"). }
          iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.
          iNext. iApply (ftlr_post_fault with "HPC Hmap Hhwm Hreg Hworld_interp"); eauto.
      + (* The PC's region holds a zone cell: the zone store to the instruction's own cell *)
        iDestruct (zone_cell_unfold with "Hcell") as "[Htok Hhalf]".
        iDestruct "Hhwm" as (h) "[Hb Hh]".
        iDestruct (key_share_deref None a with "[]") as (dw Hdw) "[Hdw _]"; first done.
        iApply (wp_store_zone_pc_gen with "[$HPC $Hhalf $Htok $Hb $Hh $Hdw $Hmap]");
          eauto.
        { intros p1 g1 b1 e1 a1 ea1 Hallow1.
          by destruct (reg_allows_store_imm_det imm Hallows Hallow1) as (_ & _ & _ & _ & _ & ->). }
        iNext. iIntros (lpc' mem' retv) "(%HSpec & HPC & Hb & Hres & _ & Hmap)".
        destruct HSpec as [p1 g1 b1 e1 a1 ea1 storev1 oldv1 Harg1 Hallow1 Hsh1 Hlookup1 -> _ Hincr
                          |p1 g1 b1 e1 a1 ea1 heap_a1 z1 π1 old1 _ Hallow1 Hsh1 _ _ _ _ _
                          | -> _ _ ->].
        * destruct (reg_allows_store_imm_det imm Hallows Hallow1) as (-> & -> & -> & -> & -> & ->).
          rewrite Hwoa in Harg1. injection Harg1 as <-.
          iDestruct "Hres" as "[Hmem Hh]".
          rewrite insert_singleton_eq big_sepM_singleton.
          apply incrementPC_Some_inv in Hincr
            as (tpc & ppc & gpc & bpc & epc & apc & apc' & πpc & HPCeq & Hapc' & ->).
          injection HPCeq as <- <- <- <- <- <- <-.
          iNext.
          iDestruct ("WorldRes" with "[Hmem $HPstored]") as "WorldRes".
          { iApply (region_cell_nonheap InLocal a with "Hmem"). }
          iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.
          iDestruct (hwm_res_at_after with "Hb Hh") as "Hhwm".
          iApply (ftlr_post_next with "HPC Hmap Hhwm [] [] Hworld_interp"); auto.
          iApply "IH". iApply (interp_next_PC with "Hinv_interp"); eauto.
        * exfalso. by rewrite (Hnonshadow _ _ _ _ _ _ Hallow1) in Hsh1.
        * iDestruct "Hres" as "(Hhalf & Htok & Hh)".
          iDestruct ("WorldRes" with "[Hhalf Htok $Hinterp]") as "WorldRes".
          { iApply region_cell_zone. rewrite zone_cell_unfold. iFrame. }
          iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.
          iNext. iApply (ftlr_post_fault with "HPC Hmap [Hb Hh] Hreg Hworld_interp"); eauto.
          iExists h. iFrame.
    - (* A store to another key: open its region *)
      iAssert (interp W C (Cap p0 g0 b0 e0 a0 @@? π0)) as "#Hvdst".
      { iApply ("Hreg" $! dst _ Hdst). }
      apply andb_prop in Hwb as [Hle Hge].
      iDestruct (write_allowed_inv _ _ ea with "Hvdst")
        as (p'' P'' Hflp'' Hcond_pers'') "(#Hrel'' & _ & #Hwcond'' & _)"; auto
      ; first (split; [by apply Z.leb_le | by apply Z.ltb_lt]).
      assert (withinBounds b0 e0 ea = true) as Hbounds.
      { by rewrite /withinBounds Hle Hge. }
      (* The fetch uses half of the PC's cell *)
      iDestruct (region_cell_fetch with "Hpc") as "[Ha Hrest]".
      iDestruct (open_world_interp_next_cases W C [LNonHeap a] π0 ea p'' P'' p0 g0
                  with "Hrel'' Hworld_interp")
        as "[(%ρ' & %Hρwl & #Hpart & Hworld_interp & (%w0 & WorldRes0))
            | (%ι & -> & #Hq & Hworld_interp)]"; [done|set_solver|..].
      2: { (* A tombstone: the store faults on the tag of the address. *)
           iDestruct (interp_cap_has_authority with "Hvdst") as %Hauth;
             [by eapply writeAllowed_nonO|exact Hbounds|].
           iDestruct (big_sepM_insert_acc with "Hmap") as "[Hdstr Hmap]"; first exact Hdst.
           iApply (wp_store_quar_imm (CL := link_core) with "[$HPC $Ha $Hdstr $Hq]"); eauto.
           iNext. iIntros "(HPC & Ha & Hdstr)".
           iDestruct ("Hmap" with "Hdstr") as "Hmap".
           iDestruct ("Hrest" with "Ha") as "Hpc".
           iDestruct ("WorldRes" with "[$Hpc $Hinterp]") as "WorldRes".
           iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.
           iApply (ftlr_post_fault with "HPC Hmap Hhwm [] Hworld_interp").
           { intros r'. rewrite lookup_insert_is_Some'. by right. }
           iIntros (r' v Hv). destruct (decide (r' = dst)) as [->|Hne].
           - rewrite lookup_insert_eq in Hv. injection Hv as <-. iApply interp_clear_tag.
           - rewrite lookup_insert_ne // in Hv. by iApply "Hreg". }
      iDestruct (pc_open_acc_forall with "Hpart WorldRes0") as "[ (>Hea & HP0) Hclose0]".
      iAssert (▷ pc_content ρ' W C P'' (lstore_word p0 storev))%I as "HP''stored".
      { iNext. by iApply (pc_content_wcond with "Hwcond'' HVstorev"). }
      assert (addr_key π0 ea ∉ [LNonHeap a]) as Hnin by set_solver.
      iDestruct (region_cell_cases with "Hea") as "[Hea | ([-> [-> ->]] & Hcell)]".
      + (* The target's region holds the points-to *)
        iDestruct (addr_key_pointsto with "Hea") as "[Hea Hshare]".
        iDestruct (key_share_deref with "Hshare") as (dw Hdw) "[Hdw Hshare]".
        iApply (wp_store_imm_fetch _ _ _ _ _ _ _ _ _ _ _ (<[ea:=w0]> ∅) _ _ dw
                 with "[$HPC $Ha $Hdw $Hmap Hea]"); eauto.
        { exists t0, p0, g0, b0, e0, a0, storev. split; first done. split; first done.
          rewrite /reg_allows_store_imm Hea. case_decide; last done.
          eexists. by rewrite lookup_insert_eq. }
        { iNext. by iApply memMap_resource_1. }
        iNext. iIntros (lpc' mem' retv) "(%HSpec & HPC & Ha & Hmem & Hdw & Hmap)".
        iDestruct ("Hshare" with "Hdw") as "Hshare".
        destruct HSpec as [p1 g1 b1 e1 a1 ea1 storev1 oldv1 Harg1 Hallow1 Hsh1 Hlookup1 -> _ Hincr
                          |p1 g1 b1 e1 a1 ea1 heap_a1 z1 π1 old1 _ Hallow1 Hsh1 _ _ _ _ _
                          | -> _ _ ->].
        * destruct (reg_allows_store_imm_det imm Hallows Hallow1) as (-> & -> & -> & -> & -> & ->).
          rewrite Hwoa in Harg1. injection Harg1 as <-.
          rewrite insert_insert_eq -memMap_resource_1.
          apply incrementPC_Some_inv in Hincr
            as (tpc & ppc & gpc & bpc & epc & apc & apc' & πpc & HPCeq & Hapc' & ->).
          injection HPCeq as <- <- <- <- <- <- <-.
          iNext.
          iDestruct (addr_key_pointsto_join with "Hmem Hshare") as "Hea".
          iDestruct ("Hclose0" with "[Hea $HP''stored]") as "Hres0".
          { by iApply region_cell_pointsto. }
          iDestruct (pc_close_next with "Hworld_interp Hpart Hres0") as "Hworld_interp"; [done|done|].
          iDestruct ("Hrest" with "Ha") as "Hpc".
          iDestruct ("WorldRes" with "[$Hpc $Hinterp]") as "WorldRes".
          iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.
          iApply (ftlr_post_next with "HPC Hmap Hhwm [] [] Hworld_interp"); auto.
          iApply "IH". iApply (interp_next_PC with "Hinv_interp"); eauto.
        * exfalso. by rewrite (Hnonshadow _ _ _ _ _ _ Hallow1) in Hsh1.
        * rewrite -memMap_resource_1.
          iDestruct (addr_key_pointsto_join with "Hmem Hshare") as "Hea".
          iDestruct ("Hclose0" with "[Hea $HP0]") as "Hres0".
          { by iApply region_cell_pointsto. }
          iDestruct (pc_close_next with "Hworld_interp Hpart Hres0") as "Hworld_interp"; [done|done|].
          iDestruct ("Hrest" with "Ha") as "Hpc".
          iDestruct ("WorldRes" with "[$Hpc $Hinterp]") as "WorldRes".
          iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.
          iNext. iApply (ftlr_post_fault with "HPC Hmap Hhwm Hreg Hworld_interp"); eauto.
      + (* The target's region holds a zone cell: the zone store *)
        iDestruct "Hhwm" as (h) "[Hb Hh]".
        iDestruct (key_share_deref None ea with "[]") as (dw Hdw) "[Hdw _]"; first done.
        iApply (wp_store_zone_gen with "[$HPC $Ha $Hcell $Hb $Hh $Hdw $Hmap]");
          eauto.
        { intros p1 g1 b1 e1 a1 ea1 Hallow1.
          by destruct (reg_allows_store_imm_det imm Hallows Hallow1) as (_ & _ & _ & _ & _ & ->). }
        iNext. iIntros (lpc' mem' retv) "(%HSpec & HPC & Ha & Hb & Hres & _ & Hmap)".
        destruct HSpec as [p1 g1 b1 e1 a1 ea1 storev1 oldv1 Harg1 Hallow1 Hsh1 Hlookup1 -> _ Hincr
                          |p1 g1 b1 e1 a1 ea1 heap_a1 z1 π1 old1 _ Hallow1 Hsh1 _ _ _ _ _
                          | -> _ _ ->].
        * destruct (reg_allows_store_imm_det imm Hallows Hallow1) as (-> & -> & -> & -> & -> & ->).
          rewrite Hwoa in Harg1. injection Harg1 as <-.
          iDestruct "Hres" as "[Hmem Hh]".
          rewrite insert_singleton_eq big_sepM_singleton.
          apply incrementPC_Some_inv in Hincr
            as (tpc & ppc & gpc & bpc & epc & apc & apc' & πpc & HPCeq & Hapc' & ->).
          injection HPCeq as <- <- <- <- <- <- <-.
          iNext.
          iDestruct ("Hclose0" with "[Hmem $HP''stored]") as "Hres0".
          { iApply (region_cell_nonheap InLocal ea with "Hmem"). }
          iDestruct (pc_close_next with "Hworld_interp Hpart Hres0") as "Hworld_interp"; [done|done|].
          iDestruct ("Hrest" with "Ha") as "Hpc".
          iDestruct ("WorldRes" with "[$Hpc $Hinterp]") as "WorldRes".
          iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.
          iDestruct (hwm_res_at_after with "Hb Hh") as "Hhwm".
          iApply (ftlr_post_next with "HPC Hmap Hhwm [] [] Hworld_interp"); auto.
          iApply "IH". iApply (interp_next_PC with "Hinv_interp"); eauto.
        * exfalso. by rewrite (Hnonshadow _ _ _ _ _ _ Hallow1) in Hsh1.
        * iDestruct "Hres" as "[Hcell Hh]".
          iDestruct ("Hclose0" with "[Hcell $HP0]") as "Hres0".
          { by iApply region_cell_zone. }
          iDestruct (pc_close_next with "Hworld_interp Hpart Hres0") as "Hworld_interp"; [done|done|].
          iDestruct ("Hrest" with "Ha") as "Hpc".
          iDestruct ("WorldRes" with "[$Hpc $Hinterp]") as "WorldRes".
          iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.
          iNext. iApply (ftlr_post_fault with "HPC Hmap [Hb Hh] Hreg Hworld_interp"); eauto.
          iExists h. iFrame.
  Qed.

End fundamental.
