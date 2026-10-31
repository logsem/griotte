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
    iIntros "#H1 #H2" (v). destruct ρ; rewrite /region_rel_part /region_rel_perm /region_rel_l /pc_content.
    - iDestruct (rel_perm_agree with "H1 H2") as "[_ Heq]". iApply ("Heq" $! (C, v)).
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

  Lemma interp_hpf_eq (imm : Z) (W : WORLD) (C : CmptName) P (regs : leibnizO LReg) (r1 : RegName)
    p g b e a pc_a pc_p pc_p' ρ w_pc :
    read_reg_prov regs r1 None
    → reg_allows_store_imm regs r1 imm p g b e a pc_a
    → PermFlowsTo pc_p pc_p'
    → (∀ (r1 : RegName) v, ⌜regs !! r1 = Some v⌝ → interp W C v)
    -∗ region_rel_part ρ W C (LNonHeap pc_a) pc_p' P
    -∗ world_interp_open W C [LNonHeap pc_a]
    -∗ pc_a ↦ₐ w_pc
    -∗ world_interp_open W C [LNonHeap pc_a] ∗ pc_a ↦ₐ w_pc ∗
       ⌜PermFlowsTo p pc_p' ∧ (ρ = InPerm → isWL p = false)⌝ ∗
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

  (** The stored word is valid: it is an immediate or a register's word. *)
  (* Description of what the resources are supposed to look like
     after opening the region if we need to,
     but before closing the region up again*)
  Definition region_open_resources
    (W : WORLD) (C : CmptName)
    (k : LAddr) (ls : list LAddr) (pw p : Perm)
    (v : LWord) (P : D) (has_later : bool): iProp Σ :=
    (∃ ρ,
        ⌜ρ = InPerm → isWL pw = false⌝
        ∗ region_rel_part ρ W C k p P
        ∗ world_interp_open W C ({[k]} ∪ ls)
        ∗ if_later_P has_later (pc_content ρ W C P v)
        ∗ if_later_P has_later (key_share k)
        ∗ if_later_P has_later
            (∀ v', k ↦ₖ v' ∗ pc_content ρ W C P v' -∗ pc_open W C k p P v' ρ))%I.

  Definition allow_store_res (imm : Z) W C r1 r2 (regs : LReg) pc_a (pc_p : Perm) (ρ : region_part)
    (P : D) (has_later : bool) :=
    (∃ t p g b e a π storev,
        ⌜read_reg_inr regs r1 t p g b e a⌝
        ∗ ⌜read_reg_prov regs r1 π⌝
        ∗ ⌜lword_of_argument regs r2 = Some storev⌝
        ∗ match (a + imm)%a with
          | None => world_interp_open W C [LNonHeap pc_a]
          | Some ea => if decide (reg_allows_store_imm regs r1 imm p g b e a ea)
          then (if decide (addr_key π ea = LNonHeap pc_a)
                then world_interp_open W C [LNonHeap pc_a] ∗ ⌜PermFlowsTo p pc_p⌝ ∗
                       ⌜ρ = InPerm → isWL p = false⌝ ∗
                       if_later_P has_later (pc_store_cond W C ρ P p)
                else ∃ p' (P':D) w,
                    ⌜PermFlowsTo p p'⌝
                    ∗ ⌜ persistent_cond P' ⌝
                    ∗ ⌜ea ≠ pc_a⌝
                    ∗ ▷ ea ↦ₐ w
                    ∗ if_later_P has_later (zcond P' C)
                    ∗ (if writeAllowed p
                       then if_later_P has_later
                              (if isWL p then wcond_wl P' C interp else wcond_nwl P' C interp)
                       else True)
                    ∗ (region_open_resources W C (addr_key π ea) [LNonHeap pc_a] p p' w P' has_later))
          else world_interp_open W C [LNonHeap pc_a]
          end)%I.

  Definition allow_store_mem (imm : Z) W C r1 r2 (regs : LReg) pc_a (pc_p : Perm) (ρ : region_part)
    (P : D) pc_w (mem : LMem) (has_later : bool) :=
    (∃ t p g b e a π storev,
        ⌜read_reg_inr regs r1 t p g b e a⌝
        ∗ ⌜read_reg_prov regs r1 π⌝
        ∗ ⌜lword_of_argument regs r2 = Some storev⌝
        ∗ match (a + imm)%a with
          | None => ⌜mem = <[pc_a:=pc_w]> ∅⌝ ∗ world_interp_open W C [LNonHeap pc_a]
          | Some ea => if decide (reg_allows_store_imm regs r1 imm p g b e a ea)
          then (if decide (addr_key π ea = LNonHeap pc_a)
                then ⌜mem = <[pc_a:=pc_w]> ∅⌝ ∗ world_interp_open W C [LNonHeap pc_a] ∗ ⌜PermFlowsTo p pc_p⌝ ∗
                       ⌜ρ = InPerm → isWL p = false⌝ ∗
                       if_later_P has_later (pc_store_cond W C ρ P p)
                else ∃ p' (P':D) w,
                    ⌜PermFlowsTo p p'⌝
                    ∗ ⌜ persistent_cond P' ⌝
                    ∗ ⌜ea ≠ pc_a⌝
                    ∗ if_later_P has_later (zcond P' C)
                    ∗ (if writeAllowed p
                       then if_later_P  has_later
                              (if isWL p then wcond_wl P' C interp else wcond_nwl P' C interp)
                       else True)
                    ∗ ⌜mem = <[ea:=w]> (<[pc_a:=pc_w]> ∅)⌝
                    ∗ (region_open_resources W C (addr_key π ea) [LNonHeap pc_a] p p' w P' has_later))
          else  ⌜mem = <[pc_a:=pc_w]> ∅⌝ ∗ world_interp_open W C [LNonHeap pc_a]
          end)%I.

  Lemma create_store_res (imm : Z)
    (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (r1 : RegName) (r2 : Z + RegName)
    (t0 : bool) (p0 : Perm) (g0 : Locality) (b0 e0 a0 : Addr) (π0 : option AId)
    (storev : LWord) (P:D) (w_pc : LWord) (ρ : region_part) :
    read_reg_inr regs r1 t0 p0 g0 b0 e0 a0
    → read_reg_prov regs r1 π0
    → PermFlowsTo p p'
    → lword_of_argument regs r2 = Some storev
    → interp W C (Cap p g b e a @@? None)
    -∗ (∀ (r1 : RegName) v, ⌜regs !! r1 = Some v⌝ → interp W C v)
    -∗ region_rel_part ρ W C (LNonHeap a) p' P
    -∗ world_interp_open W C [LNonHeap a]
    -∗ a ↦ₐ w_pc
    -∗ ◇ ((allow_store_res imm W C r1 r2 regs a p' ρ P true
          ∗ a ↦ₐ w_pc)
         ∨ (∃ ι wd, ⌜regs !! r1 = Some wd⌝ ∗ ⌜has_authority wd.(lw)⌝ ∗
              ⌜wd.(lprov) = Some ι⌝ ∗ ι ⊒ AQuar ∗
              world_interp_open W C [LNonHeap a] ∗ a ↦ₐ w_pc)).
  Proof.
    iIntros (HVr1 Hπ Hfl Hwoa) "#HVPCr #Hreg #Hinva Hworld_interp Hapc".
    rewrite /allow_store_res.
    destruct (a0 + imm)%a as [ea0|] eqn:Hea.
    2: { iModIntro. iLeft. iFrame "Hapc". iExists t0,p0,g0,b0,e0,a0,π0,storev. iFrame "%".
         rewrite Hea. by iFrame. }
    destruct (decide (reg_allows_store_imm regs
                        r1 imm p0 g0 b0 e0 a0 ea0)) as [Hallows|Hallows]; cycle 1.
    { iModIntro. iLeft. iFrame "Hapc". iExists t0,p0,g0,b0,e0,a0,π0,storev. iFrame "%".
      rewrite Hea decide_False //. }
    pose proof (store_prov_eq imm Hallows Hπ) as Hsrc.
    destruct (decide (addr_key π0 ea0 = LNonHeap a)) as [Hkey|Hkey].
    { (* The PC's region: already open. *)
      destruct (addr_key_pc _ _ _ Hkey) as [-> ->].
      iDestruct (interp_hpf_eq imm W C P regs r1 p0 g0 b0 e0 a0 a
        p p' ρ w_pc with "Hreg Hinva Hworld_interp Hapc")
        as "(Hworld_interp & Hapc & [%Hflp %Hwlp] & Hcond)"; eauto.
      iModIntro. iLeft. iFrame "Hapc". iExists t0,p0,g0,b0,e0,a0,None,storev. iFrame "%".
      rewrite Hea decide_True // decide_True //. by iFrame. }
    pose proof Hallows as (Hrinr & Hadd & Hwa & Hwb).
    apply andb_prop in Hwb as [Hle Hge].
    iAssert (interp W C (Cap p0 g0 b0 e0 a0 @@? π0)) as "#Hvsrc".
    { iApply ("Hreg" $! r1 _ Hsrc). }
    iDestruct (write_allowed_inv _ _ ea0 with "Hvsrc")
      as (p'' P'' Hflp'' Hcond_pers'') "(#Hrel'' & Hzcond'' & Hwcond'' & _)"; auto
    ; first (split; [by apply Z.leb_le | by apply Z.ltb_lt]).
    assert (withinBounds b0 e0 ea0 = true) as Hbounds.
    { by rewrite /withinBounds Hle Hge. }
    (* Another key: open its region, a cell or a tombstone. *)
    iDestruct (open_world_interp_next_cases _ _ _ π0 ea0 p'' P'' p0 g0 with "Hrel'' Hworld_interp")
      as "[(%ρ' & %Hρwl' & #Hpart' & Hworld & WorldRes0) | (%ι & -> & #Hq & Hworld)]"; [done| |..].
    { apply not_elem_of_cons; split; last apply not_elem_of_nil. done. }
    2: { iDestruct (interp_cap_has_authority with "Hvsrc") as %Hauth;
           [by eapply writeAllowed_nonO|exact Hbounds|].
         iModIntro. iRight. iExists ι, _. iFrame "Hq Hworld Hapc". by iPureIntro. }
    iDestruct "WorldRes0" as (w0) "WorldRes0".
    iDestruct (pc_open_acc_forall with "Hpart' WorldRes0") as "[ [Hea0 HP0] Hclose0]".
    iEval (rewrite addr_key_pointsto) in "Hea0".
    iDestruct "Hea0" as "[Hea0 Hshare]".
    iDestruct "Hea0" as ">Hea0".
    (* Its address is not the PC's: both points-to are full. *)
    iDestruct (address_neq with "Hea0 Hapc") as %Hne.
    iModIntro. iLeft. iFrame "Hapc".
    iExists t0,p0,g0,b0,e0,a0,π0,storev. iFrame "%". rewrite Hea.
    rewrite decide_True // decide_False //.
    iExists p'',P'',w0.
    rewrite Hwa.
    iFrame "Hea0 Hzcond'' Hwcond''".
    iSplit; first done. iSplit; first done. iSplit; first done.
    iExists ρ'. by iFrame "Hpart' Hworld Hshare HP0 Hclose0 %".
  Qed.

  Lemma store_res_implies_mem_map (imm : Z)
    (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p' : Perm) (ρ : region_part) (P : D) (a : Addr) (w : LWord) (r1 : RegName) (r2 : Z + RegName) :
    allow_store_res imm W C r1 r2 regs a p' ρ P true
    -∗ a ↦ₐ w
    -∗ ∃ mem0 : LMem,
        allow_store_mem imm W C r1 r2 regs a p' ρ P w mem0 true
        ∗ ▷ ([∗ map] a0↦w0 ∈ mem0, a0 ↦ₐ w0).
  Proof.
    iIntros "HStoreRes Ha".
    iDestruct "HStoreRes" as (t1 p1 g1 b1 e1 a1 π1 storev) "(%Hread & %Hπ & %Harg & HStoreRes)".
    destruct (a1 + imm)%a as [ea1|] eqn:Hea.
    2: {
      iExists (<[a:=w]> ∅).
      iSplitL "HStoreRes"; last (iNext; by iApply memMap_resource_1).
      iExists t1,p1,g1,b1,e1,a1,π1,storev. iFrame "%". rewrite Hea. by iFrame.
    }
    case_decide as Hallows.
    - case_decide as Hkey.
      + iExists (<[a:=w]> ∅).
        iSplitL "HStoreRes"; last (iNext; by iApply memMap_resource_1).
        iExists t1,p1,g1,b1,e1,a1,π1,storev. iFrame "%". rewrite Hea.
        rewrite decide_True // decide_True //. by iFrame.
      + iDestruct "HStoreRes" as (p0' P0' w0 Hflp' HpersP0' Hne)
          "(HStoreCh & #Hzcond & #Hwcond & HStoreRest)".
        iExists (<[ea1:=w0]> (<[a:=w]> ∅)).
        iSplitL "HStoreRest".
        { iExists t1,p1,g1,b1,e1,a1,π1,storev. iFrame "%". rewrite Hea.
          rewrite decide_True // decide_False //.
          iExists p0',P0',w0. iFrame "∗#%"; done. }
        iNext. iApply memMap_resource_2ne; auto; iFrame.
    - iExists (<[a:=w]> ∅).
      iSplitL "HStoreRes"; last (iNext; by iApply memMap_resource_1).
      iExists t1,p1,g1,b1,e1,a1,π1,storev. iFrame "%". rewrite Hea.
      rewrite decide_False //. by iFrame.
  Qed.

  Lemma mem_map_implies_pure_conds (imm : Z)
    (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p' : Perm) (ρ : region_part) (P : D) (a : Addr)
    (w : LWord) (r1 : RegName) (r2 : Z + RegName) (mem0 : LMem) :
    allow_store_mem imm W C r1 r2 regs a p' ρ P w mem0 true
    -∗ ⌜mem0 !! a = Some w⌝
    ∗ ⌜allow_store_map_or_true_imm r1 r2 imm regs mem0⌝.
  Proof.
    iIntros "HStoreMem".
    iDestruct "HStoreMem" as (t1 p1 g1 b1 e1 a1 π1 storev) "(%Hread & %Hπ & %Harg & HStoreRes)".
    destruct (a1 + imm)%a as [ea1|] eqn:Hea.
    2: {
      iDestruct "HStoreRes" as "[-> _]". iSplitR; first by simplify_map_eq.
      iPureIntro. exists t1,p1,g1,b1,e1,a1,storev. repeat split; auto.
      by rewrite /reg_allows_store_imm Hea.
    }
    case_decide as Hallows.
    - case_decide as Hkey.
      + destruct (addr_key_pc _ _ _ Hkey) as [-> ->].
        iDestruct "HStoreRes" as "[-> _]".
        iSplitR; first by simplify_map_eq.
        iPureIntro. exists t1,p1,g1,b1,e1,a1,storev. repeat split; auto.
        rewrite /reg_allows_store_imm Hea.
        case_decide; last done. exists w. by simplify_map_eq.
      + iDestruct "HStoreRes" as (p0' P0' w0 Hflp' HpersP0' Hne) "(_ & _ & -> & _)".
        iSplitR; first by simplify_map_eq.
        iPureIntro. exists t1,p1,g1,b1,e1,a1,storev. repeat split; auto.
        rewrite /reg_allows_store_imm Hea.
        case_decide; last done. exists w0. by simplify_map_eq.
    - iDestruct "HStoreRes" as "[-> _]".
      iSplitR; first by simplify_map_eq.
      iPureIntro. exists t1,p1,g1,b1,e1,a1,storev. repeat split; auto.
      rewrite /reg_allows_store_imm Hea.
      case_decide as Hdec; last done.
      exfalso. apply Hallows. by rewrite /reg_allows_store_imm Hea.
  Qed.

  (* Note that we turn in all information that we might have on the current PC value, so that in the proof of the ftlr case itself, we do not have to worry about whether the PC was written to or not when we close the last location pc_a in the region *)
   Lemma mem_map_recover_res (imm : Z)
     (W : WORLD) (C : CmptName) (regs : LReg)
     (pc_w : LWord) (r1 : RegName) (r2 : Z + RegName) (p0 pc_p pc_p' : Perm)
     (g0 pc_g : Locality) (b0 e0 a0 ea0 pc_b pc_e pc_a : Addr)
     (mem0 : LMem) (oldv storev : LWord) (ρ : region_part) (P:D):
     lword_of_argument regs r2 = Some storev
    → reg_allows_store_imm regs r1 imm p0 g0 b0 e0 a0 ea0
    → mem0 !! ea0 = Some oldv
    → allow_store_mem imm W C r1 r2 regs pc_a pc_p' ρ P pc_w mem0 false
    -∗ (∀ (r1 : RegName) v, ⌜regs !! r1 = Some v⌝ → interp W C v)
    -∗ interp W C (Cap pc_p pc_g pc_b pc_e pc_a @@? None)
    -∗ pc_content ρ W C P pc_w
    -∗ ([∗ map] a0↦w0 ∈ <[ea0 := lstore_word p0 storev]> mem0, a0 ↦ₐ w0)
    -∗ ∃ v,
        world_interp_open W C [LNonHeap pc_a]
        ∗ pc_a ↦ₐ v
        ∗ pc_content ρ W C P v.
   Proof.
    iIntros (Hwoa Hras Ha0)
      "HStoreMem #Hreg #HVPCr Hpc_w Hmem".
    iDestruct "HStoreMem" as (t1 p1 g1 b1 e1 a1 π1 storev1) "(%Hread & %Hπ & %Harg & HStoreRes)".
    destruct (store_inr_eq imm Hras Hread) as (<- & <- &<- &<- &<-).
    rewrite Hwoa in Harg; injection Harg as <-.
    pose proof (store_prov_eq imm Hras Hπ) as Hsrc.
    pose proof Hras as (_ & Hea & Hwa & Hwb).
    rewrite Hea.
    case_decide as Hallows; last by exfalso.
    iAssert (interp W C storev) as "#HVstorev".
    { iApply (interp_lword_of_argument with "Hreg"); eauto. }
    case_decide as Hkey.
    + destruct (addr_key_pc _ _ _ Hkey) as [-> ->].
      iDestruct "HStoreRes" as "(-> & HStoreRes & % & %Hwlp & #Hcond)".
      rewrite insert_insert_eq -memMap_resource_1.
      iExists (lstore_word p0 storev). iFrame.
      by iApply "Hcond".
    + iExists pc_w.
      iDestruct "HStoreRes"
        as (p' P' w' Hflp' HpersP' Hne) "(#Hzcond' & #Hwcond' & -> & HStoreRes)".
      rewrite lookup_insert_eq in Ha0; inversion Ha0; clear Ha0; subst.
      iDestruct "HStoreRes" as (ρ1 Hρ1) "(#Hpart1 & Hworld_interp & _ & Hshare & Hclose1)".
      rewrite insert_insert_eq memMap_resource_2ne; last auto.
      iDestruct "Hmem" as  "[Ha1 Hpc_a]".
      iDestruct (addr_key_pointsto_join with "Ha1 Hshare") as "Ha1".
      iFrame.
      rewrite Hwa.
      iDestruct (pc_content_wcond with "Hwcond' HVstorev") as "HP'storev"; first exact Hρ1.
      iDestruct ("Hclose1" with "[$Ha1 $HP'storev]") as "Hres1".
      iApply (pc_close_next with "Hworld_interp Hpart1 Hres1"); [|done].
      apply not_elem_of_cons; split; last apply not_elem_of_nil. done.
   Qed.

  (** On a fault, memory is unchanged: the regions opened for the store close
      with their original contents. *)
  #[local] Lemma mem_map_recover_res_fault (imm : Z)
    (W : WORLD) (C : CmptName) (regs : LReg)
    (pc_w : LWord) (r1 : RegName) (r2 : Z + RegName) (pc_p' : Perm) (ρ : region_part)
    (P : D) (pc_a : Addr) (mem0 : LMem) :
    allow_store_mem imm W C r1 r2 regs pc_a pc_p' ρ P pc_w mem0 false -∗
    ([∗ map] a0↦w0 ∈ mem0, a0 ↦ₐ w0) -∗
    world_interp_open W C [LNonHeap pc_a] ∗ pc_a ↦ₐ pc_w.
  Proof.
    iIntros "HStoreMem Hmem".
    iDestruct "HStoreMem" as (t1 p1 g1 b1 e1 a1 π1 storev1) "(%Hread & %Hπ & %Harg & HStoreRes)".
    destruct (a1 + imm)%a as [ea1|] eqn:Hea.
    2: { iDestruct "HStoreRes" as "[-> $]". rewrite -memMap_resource_1. iFrame. }
    case_decide as Hallows.
    2: { iDestruct "HStoreRes" as "[-> $]". rewrite -memMap_resource_1. iFrame. }
    case_decide as Hkey.
    - iDestruct "HStoreRes" as "(-> & $ & _)". rewrite -memMap_resource_1. iFrame.
    - iDestruct "HStoreRes"
        as (p' P' w' Hflp' HpersP' Hne) "(_ & _ & -> & HStoreRes)".
      iDestruct "HStoreRes"
        as (ρ1 Hρ1) "(#Hpart1 & Hworld_interp & HV & Hshare & Hclose1)".
      rewrite memMap_resource_2ne; last auto.
      iDestruct "Hmem" as "[Ha1 $]".
      iDestruct (addr_key_pointsto_join with "Ha1 Hshare") as "Ha1".
      iDestruct ("Hclose1" with "[$Ha1 $HV]") as "Hres1".
      iApply (pc_close_next with "Hworld_interp Hpart1 Hres1"); [|done].
      apply not_elem_of_cons; split; last apply not_elem_of_nil. done.
  Qed.

  Lemma allow_store_mem_later (imm : Z)
    (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (a : Addr) (w : LWord) r1 r2 (p' : Perm) (ρ : region_part) (P : D) (mem0 : LMem) :
    allow_store_mem imm W C r1 r2 regs a p' ρ P w mem0 true
    -∗ ▷ allow_store_mem imm W C r1 r2 regs a p' ρ P w mem0 false.
  Proof.
    iIntros "HStoreMem".
    iDestruct "HStoreMem" as (t1 p1 g1 b1 e1 a1 π1 storev1) "(% & % & % & HStoreRes)".
    do 8 (iApply later_exist_2; iExists _).
    do 3 (iApply later_sep_2; iSplitR; auto).
    destruct (a1 + imm)%a; last by iFrame.
    case_decide; last iFrame.
    case_decide.
    { iDestruct "HStoreRes" as "(-> & Hw & % & % & Hcond)". iNext. by iFrame. }
    iDestruct "HStoreRes" as (p0 P0 w0 Hp'O Hpers Hne) "(#Hzcond & #Hwcond & -> & HStoreMem)".
    repeat (iApply later_exist_2; iExists _).
    repeat (iApply later_sep_2; iSplitR; auto).
    iDestruct (if_later with "Hwcond") as "Hwcond'"; eauto.
  Qed.

   Lemma store_case (imm : Z) (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
     (p p' : Perm) (g : Locality) (b e a : Addr) (w : LWord)
     (ρ : region_part) (dst : RegName) (src : Z + RegName) (P : D) :
     ftlr_instr W C regs p p' g b e a w (Store dst src imm) ρ P.
   Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hi.
    iIntros "@".

    iDestruct (pc_open_acc_forall with "Hinva WorldRes") as " [ (>Ha & Hinterp) WorldRes ]".

    pose proof Hsome as Hsome'.

    (* Initializing the names for the values of Hsrc now, to instantiate the existentials in step 1 *)
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

    (* Step 1: open the region, if necessary,
       and store all the resources obtained from the region in allow_store_res imm *)
    iMod (create_store_res imm with "Hinv_interp Hreg Hinva Hworld_interp Ha")
      as "[ [HStoreRes Ha] | (%ι & %wd & %Hwd & %Hauth & %Hι & #Hq & Hworld_interp & Ha)]"; eauto.
    2: { (* A tombstone: the store faults on the tag of the address. *)
         iDestruct (big_sepM_insert_acc with "Hmap") as "[Hdst Hmap]"; first exact Hwd.
         iApply (wp_store_quar_imm (CL := link_core) with "[$HPC $Ha $Hdst $Hq]"); eauto.
         iNext. iIntros "(HPC & Ha & Hdst)".
         iDestruct ("Hmap" with "Hdst") as "Hmap".
         iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
         iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.
         iApply (ftlr_post_fault with "HPC Hmap [] Hworld_interp").
         { intros r'. rewrite lookup_insert_is_Some'. by right. }
         iIntros (r' v Hv). destruct (decide (r' = dst)) as [->|Hne].
         - rewrite lookup_insert_eq in Hv. injection Hv as <-. iApply interp_clear_tag.
         - rewrite lookup_insert_ne // in Hv. by iApply "Hreg". }
    (* Clear helper values; they exist in the existential now *)
    clear HVdst HVπ t0 p0 g0 b0 e0 a0 π0 Hwoa storev.

    (* Step2: derive the concrete map of memory we need,
       and any spatial predicates holding over it *)
    iDestruct (store_res_implies_mem_map imm W  with "HStoreRes Ha") as (mem) "[HStoreMem HMemRes]".

    (* Step 3:  derive the non-spatial conditions over the memory map*)
    iDestruct (mem_map_implies_pure_conds imm with "HStoreMem") as %(HReadPC & HStoreAP); auto.

    iAssert (⌜∀ p0 g0 b0 e0 a0 ea0,
      reg_allows_store_imm regs dst imm p0 g0 b0 e0 a0 ea0 →
      is_shadow_address ea0 = false⌝)%I as %Hnonshadow.
    { iIntros (p0 g0 b0 e0 a0 ea0 (Hdst & Hadd & Hwa & Hwb)).
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hdst) as (Hdst_null & π0 & Hdst').
      iApply (interp_cap_not_shadow with "[Hreg]"); eauto using writeAllowed_nonO.
      by iApply "Hreg".
    }
    iApply (wp_store_imm (CL := link_core) with "[$HPC $Hmap $HMemRes]"); eauto.
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply Hsome. }
    iDestruct (allow_store_mem_later imm with "HStoreMem") as "HStoreMem".

    iNext. iIntros (lpc' mem' retv). iDestruct 1 as (HSpec) "(HPC & Hmem & Hmap)".

    destruct HSpec as [p1 g1 b1 e1 a1 ea1 storev1 oldv1
        Harg1 Hallow1 Hshadow1 Hlookup1 -> Hshadow_eq1 Hincr
      |p0 g0 b0 e0 a0 ea0 heap_a0 z0 π0 old_status0 Harg0 Hallow0 Hshadow0 Htranslate0
        Hold0 Hmem_eq0 Hshadow_eq0 Hincr0|].
    { apply incrementPC_Some_inv in Hincr
        as (tpc & ppc & gpc & bpc & epc & apc & apc' & πpc & HPC & Hapc' & ->).
      injection HPC as <- <- <- <- <- <- <-.
      iNext.

      (* Step 4: return all the resources we had in order to close the second location
         in the region, in the cases where we need to *)
      iDestruct (mem_map_recover_res imm
                  with "HStoreMem Hreg Hinv_interp Hinterp Hmem")
        as (w') "(Hworld_interp & Ha & HSVInterp)"; eauto.

      iDestruct ("WorldRes" with "[$Ha $HSVInterp]") as "WorldRes".
      iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.
      iApply (ftlr_post_next with "HPC Hmap [] [] Hworld_interp"); auto.
      iApply "IH". iApply (interp_next_PC with "Hinv_interp"); eauto.
    }
    { exfalso. pose proof (Hnonshadow p0 g0 b0 e0 a0 ea0 Hallow0). congruence. }
    { subst mem'.
      iDestruct (mem_map_recover_res_fault imm with "HStoreMem Hmem") as "[Hworld_interp Ha]".
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.
      iNext. iApply (ftlr_post_fault with "HPC Hmap Hreg Hworld_interp"); eauto. }
  Qed.

End fundamental.
