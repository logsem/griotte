From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Export logrel monotone.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Import rules_Store wp_rules_interp.
From griotte Require Import map_simpl register_tactics.
Import uPred.


Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation D := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LReg) -n> iPropO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (D).

  Definition wcond' (P : D) C p g b e a (regs : LReg) : iProp Σ
    := (if decide (writeAllowed_a_in_lregs (<[PC:= WCap true p g b e a @@? None]> regs) a)
        then □ (∀ W0 (w : LWord), interp W0 C w -∗ P W0 C w)
        else emp)%I.
  Instance wcond'_pers P C p g b e a r: Persistent (wcond' P C p g b e a r).
  Proof. intros. rewrite /wcond'. case_decide;apply _. Qed.

  (* A decision procedure that does not unfold [reg_allows_store_imm], so that
     the definitions below can be rewritten under [(a + imm)%a]. *)
  #[local] Instance reg_allows_store_imm_dec regs r imm p g b e a ea :
    Decision (reg_allows_store_imm regs r imm p g b e a ea) | 0.
  Proof. rewrite /reg_allows_store_imm. apply _. Defined.

  Lemma store_prov_eq (imm : Z) {regs r p0 g0 b0 e0 a0 ea π}:
    reg_allows_store_imm regs r imm p0 g0 b0 e0 a0 ea →
    read_reg_prov regs r π →
    regs !! r = Some (WCap true p0 g0 b0 e0 a0 @@? π).
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
    p g b e a pc_a pc_p pc_g pc_b pc_e pc_p':
    read_reg_prov (<[PC:=WCap true pc_p pc_g pc_b pc_e pc_a @@? None]> regs) r1 None
    → reg_allows_store_imm (<[PC:=WCap true pc_p pc_g pc_b pc_e pc_a @@? None]> regs) r1 imm p g b e a pc_a
    → PermFlowsTo pc_p pc_p'
    → (∀ (r1 : RegName) v, ⌜r1 ≠ PC⌝ → ⌜regs !! r1 = Some v⌝ → interp W C v)
    -∗ rel C (LNonHeap pc_a) pc_p' P
    -∗ ⌜PermFlowsTo p pc_p'⌝.
  Proof.
    intros Hπ Hrar Hfl.
    pose proof (store_prov_eq imm Hrar Hπ) as Hr1.
    destruct Hrar as (_ & Hadd & Hwa & Hwb).
    destruct (decide (r1 = PC)) as [->|Hne].
    - rewrite lookup_insert_eq in Hr1. simplify_eq. iIntros. done.
    - rewrite lookup_insert_ne // in Hr1.
      iIntros "Hreg #Hinva".
      iDestruct ("Hreg" $! r1 _ Hne Hr1) as "Hr1".
      iDestruct (write_allowed_inv _ _ pc_a with "Hr1")
        as (p'' P'' Hflp'' Hcond_pers'') "(Hrel'' & Hzcond'' & Hrcond'' & Hwcond'')"; auto.
      { apply andb_true_iff in Hwb as [Hle Hge].
        split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
      iDestruct (rel_agree _ _ _ _ p'' pc_p' with "[$Hinva $Hrel'']") as "[-> _]".
      done.
  Qed.

  (** The stored word is valid: it is an immediate or a register's word. *)
  Lemma interp_lword_of_argument W C (regs : LReg) (pc_w : LWord) arg v :
    lword_of_argument (<[PC:=pc_w]> regs) arg = Some v →
    interp W C pc_w
    -∗ (∀ (r : RegName) v, ⌜r ≠ PC⌝ → ⌜regs !! r = Some v⌝ → interp W C v)
    -∗ interp W C v.
  Proof.
    iIntros (Harg) "#Hpc #Hreg".
    apply lword_of_argument_Some_inv in Harg as [(z & -> & ->) | (r & -> & Hr)].
    { by iApply interp_untagged. }
    apply bind_Some in Hr as (wr & Hwr & Hv).
    destruct (decide (r = cnull)); simplify_eq; first by iApply interp_untagged.
    destruct (decide (r = PC)) as [->|Hne].
    - by rewrite lookup_insert_eq in Hwr; simplify_eq.
    - rewrite lookup_insert_ne // in Hwr. by iApply "Hreg".
  Qed.

  (* Description of what the resources are supposed to look like
     after opening the region if we need to,
     but before closing the region up again*)
  Definition region_open_resources
    (W : WORLD) (C : CmptName)
    (k : LAddr) (ls : list LAddr) (p : Perm) (φ: _ -> iProp Σ)
    (v : LWord) (P : D) (has_later : bool): iProp Σ :=
    (∃ ρ,
        sts_state_std C k ρ
        ∗ ⌜std W !! k = Some ρ⌝
        ∗ ⌜ρ ≠ Revoked⌝
        ∗ ⌜heap_key_live (heap_std W) k⌝
        ∗ world_interp_open W C (k :: ls)
        ∗ if_later_P
            has_later
            (monotonicity_guarantees_region C (safeC P) p v ρ )
        ∗ if_later_P has_later (key_share k)
        ∗ rel C k p φ)%I.

  Definition allow_store_res (imm : Z) W C r1 r2 (regs : LReg) pc_a (pc_p : Perm) (has_later : bool) :=
    (∃ t p g b e a π storev,
        ⌜read_reg_inr regs r1 t p g b e a⌝
        ∗ ⌜read_reg_prov regs r1 π⌝
        ∗ ⌜lword_of_argument regs r2 = Some storev⌝
        ∗ match (a + imm)%a with
          | None => world_interp_open W C [LNonHeap pc_a]
          | Some ea => if decide (reg_allows_store_imm regs r1 imm p g b e a ea)
          then (if decide (addr_key π ea = LNonHeap pc_a)
                then world_interp_open W C [LNonHeap pc_a] ∗ ⌜PermFlowsTo p pc_p⌝
                else ∃ p' (P':D) w,
                    ⌜PermFlowsTo p p'⌝
                    ∗ ⌜ persistent_cond P' ⌝
                    ∗ ⌜ea ≠ pc_a⌝
                    ∗ ▷ ea ↦ₐ w
                    ∗ if_later_P has_later (zcond P' C)
                    ∗ (if writeAllowed p
                       then if_later_P has_later (wcond P' C interp)
                       else True)
                    ∗ (if readAllowed p
                       then if_later_P has_later (rcond P' C p' interp)
                       else True)
                    ∗ monoReq W C (addr_key π ea) p' P'
                    ∗ (region_open_resources W C (addr_key π ea) [LNonHeap pc_a] p' (safeC P') w P' has_later))
          else world_interp_open W C [LNonHeap pc_a]
          end)%I.

  Definition allow_store_mem (imm : Z) W C r1 r2 (regs : LReg) pc_a (pc_p : Perm) pc_w (mem : LMem)
    (has_later : bool) :=
    (∃ t p g b e a π storev,
        ⌜read_reg_inr regs r1 t p g b e a⌝
        ∗ ⌜read_reg_prov regs r1 π⌝
        ∗ ⌜lword_of_argument regs r2 = Some storev⌝
        ∗ match (a + imm)%a with
          | None => ⌜mem = <[pc_a:=pc_w]> ∅⌝ ∗ world_interp_open W C [LNonHeap pc_a]
          | Some ea => if decide (reg_allows_store_imm regs r1 imm p g b e a ea)
          then (if decide (addr_key π ea = LNonHeap pc_a)
                then ⌜mem = <[pc_a:=pc_w]> ∅⌝ ∗ world_interp_open W C [LNonHeap pc_a] ∗ ⌜PermFlowsTo p pc_p⌝
                else ∃ p' (P':D) w,
                    ⌜PermFlowsTo p p'⌝
                    ∗ ⌜ persistent_cond P' ⌝
                    ∗ ⌜ea ≠ pc_a⌝
                    ∗ if_later_P has_later (zcond P' C)
                    ∗ (if writeAllowed p
                       then if_later_P  has_later (wcond P' C interp)
                       else True)
                    ∗ (if readAllowed p
                       then if_later_P  has_later (rcond P' C p' interp)
                       else True)
                    ∗ monoReq W C (addr_key π ea) p' P'
                    ∗ ⌜mem = <[ea:=w]> (<[pc_a:=pc_w]> ∅)⌝
                    ∗ (region_open_resources W C (addr_key π ea) [LNonHeap pc_a] p' (safeC P') w P' has_later))
          else  ⌜mem = <[pc_a:=pc_w]> ∅⌝ ∗ world_interp_open W C [LNonHeap pc_a]
          end)%I.

  Lemma create_store_res (imm : Z)
    (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (r1 : RegName) (r2 : Z + RegName)
    (t0 : bool) (p0 : Perm) (g0 : Locality) (b0 e0 a0 : Addr) (π0 : option AId)
    (storev : LWord) (P:D) (w_pc : LWord) :
    read_reg_inr (<[PC:= WCap true p g b e a @@? None]> regs) r1 t0 p0 g0 b0 e0 a0
    → read_reg_prov (<[PC:= WCap true p g b e a @@? None]> regs) r1 π0
    → PermFlowsTo p p'
    → lword_of_argument (<[PC:=WCap true p g b e a @@? None]> regs) r2 = Some storev
    → interp W C (WCap true p g b e a @@? None)
    -∗ (∀ (r1 : RegName) v, ⌜r1 ≠ PC⌝ → ⌜regs !! r1 = Some v⌝ → interp W C v)
    -∗ rel C (LNonHeap a) p' (safeC P)
    -∗ world_interp_open W C [LNonHeap a]
    -∗ a ↦ₐ w_pc
    -∗ ◇ (allow_store_res imm W C r1 r2 (<[PC:=WCap true p g b e a @@? None]> regs) a p' true
          ∗ a ↦ₐ w_pc).
  Proof.
    iIntros (HVr1 Hπ Hfl Hwoa) "#HVPCr #Hreg #Hinva Hworld_interp Hapc".
    rewrite /allow_store_res.
    destruct (a0 + imm)%a as [ea0|] eqn:Hea.
    2: { iModIntro. iFrame "Hapc". iExists t0,p0,g0,b0,e0,a0,π0,storev. iFrame "%".
         rewrite Hea. by iFrame. }
    destruct (decide (reg_allows_store_imm (<[PC:=WCap true p g b e a @@? None]> regs)
                        r1 imm p0 g0 b0 e0 a0 ea0)) as [Hallows|Hallows]; cycle 1.
    { iModIntro. iFrame "Hapc". iExists t0,p0,g0,b0,e0,a0,π0,storev. iFrame "%".
      rewrite Hea decide_False //. }
    pose proof (store_prov_eq imm Hallows Hπ) as Hsrc.
    destruct (decide (addr_key π0 ea0 = LNonHeap a)) as [Hkey|Hkey].
    { (* The PC's region: already open. *)
      destruct (addr_key_pc _ _ _ Hkey) as [-> ->].
      iDestruct (interp_hpf_eq imm W C (safeC P) regs r1 p0 g0 b0 e0 a0 a
        p g b e p' with "Hreg Hinva") as %Hflp; eauto.
      iModIntro. iFrame "Hapc". iExists t0,p0,g0,b0,e0,a0,None,storev. iFrame "%".
      rewrite Hea decide_True // decide_True //. by iFrame. }
    pose proof Hallows as (Hrinr & Hadd & Hwa & Hwb).
    apply andb_prop in Hwb as [Hle Hge].
    iAssert (interp W C (WCap true p0 g0 b0 e0 a0 @@? π0)) as "#Hvsrc".
    { destruct (decide (r1 = PC)) as [->|Hne].
      - rewrite lookup_insert_eq in Hsrc. simplify_eq. done.
      - rewrite lookup_insert_ne // in Hsrc. iApply ("Hreg" $! r1 _ Hne Hsrc).
    }
    iDestruct (write_allowed_inv _ _ ea0 with "Hvsrc")
      as (p'' P'' Hflp'' Hcond_pers'') "(Hrel'' & Hzcond'' & Hwcond'' & Hrcond'' & HmonoR'')"; auto
    ; first (split; [by apply Z.leb_le | by apply Z.ltb_lt]).
    assert (withinBounds b0 e0 ea0 = true) as Hbounds.
    { by rewrite /withinBounds Hle Hge. }
    iDestruct (writeAllowed_valid_cap_implies_at _ _ _ _ _ _ _ ea0 with "Hvsrc") as %HH; eauto.
    destruct HH as [ρ' [Hstd' Hnotrevoked'] ].
    iDestruct (interp_cap_addr_live with "Hvsrc") as %Hlive;
      eauto using writeAllowed_nonO.
    (* Another key: open its region. *)
    iDestruct (open_world_interp_next _ _ _ (addr_key π0 ea0) p'' _ ρ' with "Hrel'' Hworld_interp")
      as "(Hworld & Hstate' & [%w0 (?&Hea0&?&?)] )"; eauto.
    { apply not_elem_of_cons; split; last apply not_elem_of_nil. done. }
    { destruct ρ'; simplify_eq; [by left | by right]. }
    iEval (rewrite addr_key_pointsto) in "Hea0".
    iDestruct "Hea0" as "[Hea0 Hshare]".
    iDestruct "Hea0" as ">Hea0".
    (* Its address is not the PC's: both points-to are full. *)
    iDestruct (address_neq with "Hea0 Hapc") as %Hne.
    iModIntro. iFrame "Hapc".
    iExists t0,p0,g0,b0,e0,a0,π0,storev. iFrame "%". rewrite Hea.
    rewrite decide_True // decide_False //.
    iExists p'',P'',w0.
    rewrite Hwa.
    iAssert (if readAllowed p0 then ▷ rcond P'' C p'' interp else True)%I as "Hrcond0".
    { destruct (readAllowed p0) eqn:Hra''; last done.
      eapply readAllowed_flowsto in Hflp''; eauto.
      destruct (readAllowed p''); try done.
    }
    iFrame "∗#".
    iSplit; first done. iSplit; first done. iSplit; first done.
    iSplit; first done. iSplit; first done. iSplit; first done.
    iNext.
    rewrite mono_invariant_monotonicity_guarantees_region; eauto.
  Qed.

  Lemma store_res_implies_mem_map (imm : Z)
    (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p' : Perm) (a : Addr) (w : LWord) (r1 : RegName) (r2 : Z + RegName) :
    allow_store_res imm W C r1 r2 regs a p' true
    -∗ a ↦ₐ w
    -∗ ∃ mem0 : LMem,
        allow_store_mem imm W C r1 r2 regs a p' w mem0 true
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
          "(HStoreCh & #Hzcond & #Hwcond & #Hrcond & #HmonoR & HStoreRest)".
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
    (p' : Perm) (a : Addr)
    (w : LWord) (r1 : RegName) (r2 : Z + RegName) (mem0 : LMem) :
    allow_store_mem imm W C r1 r2 regs a p' w mem0 true
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
      + iDestruct "HStoreRes" as (p0' P0' w0 Hflp' HpersP0' Hne) "(_ & _ & _ & _ & -> & _)".
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

  Lemma monotonicity_guarantees_region_canStore
    (W : WORLD) (C : CmptName)
    (p : Perm) (w : LWord) (P : D)
    (a : LAddr) (ρ : region_type) :
    std W !! a = Some ρ
    -> ρ ≠ Revoked
    -> canStore p w.(lw) = true
    -> monoReq W C a p P
    -∗ monotonicity_guarantees_region C (safeC P) p w ρ.
  Proof.
    iIntros (Hstda Hrevoked HcanStore) "Hmono".
    rewrite /monoReq Hstda.
    destruct ρ; auto; cbn; [destruct (isWL p) ; [ | destruct (isDL p)]|].
    all: try iApply "Hmono"; auto.
  Qed.

  (* Note that we turn in all information that we might have on the monotonicity of the current PC value, so that in the proof of the ftlr case itself, we do not have to worry about whether the PC was written to or not when we close the last location pc_a in the region *)
   Lemma mem_map_recover_res (imm : Z)
     (W : WORLD) (C : CmptName) (regs : LReg)
     (pc_w : LWord) (r1 : RegName) (r2 : Z + RegName) (p0 pc_p pc_p' : Perm)
     (g0 pc_g : Locality) (b0 e0 a0 ea0 pc_b pc_e pc_a : Addr)
     (mem0 : LMem) (oldv storev : LWord) (ρ : region_type) (P:D):
     lword_of_argument (<[PC:= WCap true pc_p pc_g pc_b pc_e pc_a @@? None]> regs) r2 = Some storev
    → reg_allows_store_imm (<[PC:= WCap true pc_p pc_g pc_b pc_e pc_a @@? None]> regs) r1 imm p0 g0 b0 e0 a0 ea0
    → std W !! LNonHeap pc_a = Some ρ
    → mem0 !! ea0 = Some oldv
    -> ρ ≠ Revoked
    → allow_store_mem imm W C r1 r2 (<[PC:=WCap true pc_p pc_g pc_b pc_e pc_a @@? None]> regs) pc_a pc_p' pc_w mem0 false
    -∗ (∀ (r1 : RegName) v, ⌜r1 ≠ PC⌝ → ⌜regs !! r1 = Some v⌝ → interp W C v)
    -∗ interp W C (WCap true pc_p pc_g pc_b pc_e pc_a @@? None)
    -∗ P W C pc_w
    -∗ wcond' P C pc_p pc_g pc_b pc_e pc_a regs
    -∗ monoReq W C (LNonHeap pc_a) pc_p' P
    -∗ monotonicity_guarantees_region C (safeC P) pc_p' pc_w ρ
    -∗ ([∗ map] a0↦w0 ∈ <[ea0 := lstore_word p0 storev]> mem0, a0 ↦ₐ w0)
    -∗ ∃ v,
        world_interp_open W C [LNonHeap pc_a]
        ∗ pc_a ↦ₐ v
        ∗ P W C v
        ∗ monotonicity_guarantees_region C (safeC P) pc_p' v ρ.
   Proof.
    iIntros (Hwoa Hras Hstdst Ha0 Hρnrevoked)
      "HStoreMem #Hreg #HVPCr Hpc_w #Hwcond #HpcmonoV #Hpcmono Hmem".
    iDestruct "HStoreMem" as (t1 p1 g1 b1 e1 a1 π1 storev1) "(%Hread & %Hπ & %Harg & HStoreRes)".
    destruct (store_inr_eq imm Hras Hread) as (<- & <- &<- &<- &<-).
    rewrite Hwoa in Harg; injection Harg as <-.
    pose proof (store_prov_eq imm Hras Hπ) as Hsrc.
    pose proof Hras as (_ & Hea & Hwa & Hwb).
    rewrite Hea.
    case_decide as Hallows; last by exfalso.
    iAssert (interp W C storev) as "#HVstorev".
    { iApply (interp_lword_of_argument with "HVPCr Hreg"); eauto. }
    iAssert (interp W C (lstore_word p0 storev)) as "#HVstored".
    { by iApply interp_lstore_word. }
    case_decide as Hkey.
    + destruct (addr_key_pc _ _ _ Hkey) as [-> ->].
      iDestruct "HStoreRes" as "(-> & HStoreRes & %)".
      rewrite insert_insert_eq -memMap_resource_1.
      iExists (lstore_word p0 storev). iFrame. rewrite /wcond'.
      rewrite decide_True.
      2:{ eexists r1, _.
          split; first exact Hsrc.
          split; first done.
          split; first done. cbn. done.
      }
      iSplitR;[iApply "Hwcond";iFrame "#"|].
      iApply (monotonicity_guarantees_region_canStore with "HpcmonoV"); [exact Hstdst | done |].
      rewrite lw_lstore_word. by eapply canStore_store_word_flowsto.
    + iExists pc_w.
      iDestruct "HStoreRes"
        as (p' P' w' Hflp' HpersP' Hne) "(#Hzcond' & #Hwcond' & #Hrcond' & #HmonoR' & -> & HStoreRes)".
      rewrite lookup_insert_eq in Ha0; inversion Ha0; clear Ha0; subst.
      iDestruct "HStoreRes" as (ρ1) "(Hstate' & % & % & %Hlive & Hworld_interp & #HmonoV & Hshare & Hrel')".
      rewrite insert_insert_eq memMap_resource_2ne; last auto.
      iDestruct "Hmem" as  "[Ha1 Hpc_a]".
      iDestruct (addr_key_pointsto_join with "Ha1 Hshare") as "Ha1".
      iFrame.
      rewrite Hwa.
      iDestruct ("Hwcond'" with "HVstored") as "HP'storev".
      iDestruct (monotonicity_guarantees_region_canStore W C p' (lstore_word p0 storev) with "HmonoR'")
        as "HmonoR''"; [exact H | done | |].
      { rewrite lw_lstore_word. by eapply canStore_store_word_flowsto. }
      iDestruct (close_world_interp_next with "Hworld_interp Hstate' Hrel' [Ha1 HmonoR'']") as "$"; eauto.
      { apply not_elem_of_cons; split; last apply not_elem_of_nil. done. }
      { destruct ρ1; simplify_eq; naive_solver. }
      { iFrame "∗#%".
        iSplit.
        { iPureIntro ; clear -Hflp' Hwa; destruct p0,p'; cbn in *; try done.
          destruct rx, rx0, w, w0 ; cbn in *; try done. }
        rewrite mono_invariant_monotonicity_guarantees_region; eauto. }
   Qed.

  Lemma allow_store_mem_later (imm : Z)
    (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (a : Addr) (w : LWord) r1 r2 (p' : Perm) (mem0 : LMem) :
    allow_store_mem imm W C r1 r2 regs a p' w mem0 true
    -∗ ▷ allow_store_mem imm W C r1 r2 regs a p' w mem0 false.
  Proof.
    iIntros "HStoreMem".
    iDestruct "HStoreMem" as (t1 p1 g1 b1 e1 a1 π1 storev1) "(% & % & % & HStoreRes)".
    do 8 (iApply later_exist_2; iExists _).
    do 3 (iApply later_sep_2; iSplitR; auto).
    destruct (a1 + imm)%a; last by iFrame.
    case_decide; last iFrame.
    case_decide; first iFrame.
    iDestruct "HStoreRes" as (p0 P w0 Hp'O Hpers Hne) "(#Hzcond & #Hwcond & #Hrcond & #HmonoR & -> & HStoreMem)".
    repeat (iApply later_exist_2; iExists _).
    repeat (iApply later_sep_2; iSplitR; auto).
    + iDestruct (if_later with "Hwcond") as "Hwcond'"; eauto.
    + iDestruct (if_later with "Hrcond") as "Hrcond'"; eauto.
  Qed.

   Lemma store_case (imm : Z) (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
     (p p' : Perm) (g : Locality) (b e a : Addr) (w : LWord)
     (ρ : region_type) (dst : RegName) (src : Z + RegName) (P : D) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
     ftlr_instr W C regs p p' g b e a w (Store dst src imm) ρ P cstk Ws Cs.
   Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe Hworld_interp Hown Htframe".
    iIntros "Hstate HPC Hmap".
    iInsert "Hmap" PC.

    iDestruct (WorldRes_acc_forall with "WorldRes") as " [ (>Ha & Hinterp & HmonoV) WorldRes ]".

    (* To read out PC's name later, and needed when calling wp_store_imm *)
    assert(∀ x : RegName, is_Some (<[PC:=WCap true p g b e a @@? None]> regs !! x)) as Hsome'.
    {
      intros. destruct (decide (x = PC)); last by rewrite lookup_insert_ne.
      rewrite e0 lookup_insert_eq; unfold is_Some. by eexists.
    }

    (* Initializing the names for the values of Hsrc now, to instantiate the existentials in step 1 *)
    assert (∃ t0 p0 g0 b0 e0 a0 π0,
               read_reg_inr (<[PC:=WCap true p g b e a @@? None]> regs) dst t0 p0 g0 b0 e0 a0 ∧
               read_reg_prov (<[PC:=WCap true p g b e a @@? None]> regs) dst π0)
      as (t0 & p0 & g0 & b0 & e0 & a0 & π0 & HVdst & HVπ).
    {
      specialize Hsome' with dst as Hdst.
      destruct Hdst as [wdst Hsomedst].
      unfold read_reg_inr, read_reg_prov. rewrite Hsomedst.
      destruct wdst as [ [|[ t0 p0 g0 b0 e0 a0|] | | ] π0];
        try (exists true,p,g,b,e,a,None; done).
      by repeat eexists.
    }

    assert (∃ storev, lword_of_argument (<[PC:= WCap true p g b e a @@? None]> regs) src = Some storev)
      as [storev Hwoa].
    { destruct src as [z|r].
      - by eexists.
      - destruct (Hsome' r) as [wr Hwr].
        exists (if decide (r = cnull) then lnull else wr).
        by rewrite /lword_of_argument /llookup_reg Hwr.
    }

    (* Step 1: open the region, if necessary,
       and store all the resources obtained from the region in allow_store_res imm *)
    iMod (create_store_res imm with "Hinv_interp Hreg Hinva Hworld_interp Ha") as "[HStoreRes Ha]"; eauto.
    (* Clear helper values; they exist in the existential now *)
    clear HVdst HVπ t0 p0 g0 b0 e0 a0 π0 Hwoa storev.

    (* Step2: derive the concrete map of memory we need,
       and any spatial predicates holding over it *)
    iDestruct (store_res_implies_mem_map imm W  with "HStoreRes Ha") as (mem) "[HStoreMem HMemRes]".

    (* Step 3:  derive the non-spatial conditions over the memory map*)
    iDestruct (mem_map_implies_pure_conds imm with "HStoreMem") as %(HReadPC & HStoreAP); auto.

    iAssert (⌜∀ p0 g0 b0 e0 a0 ea0,
      reg_allows_store_imm (<[PC:=WCap true p g b e a @@? None]> regs) dst imm p0 g0 b0 e0 a0 ea0 →
      is_shadow_address ea0 = false⌝)%I as %Hnonshadow.
    { iIntros (p0 g0 b0 e0 a0 ea0 (Hdst & Hadd & Hwa & Hwb)).
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hdst) as (Hdst_null & π0 & Hdst').
      destruct (decide (dst = PC)) as [->|Hdst_pc].
      - rewrite lookup_insert_eq in Hdst'. simplify_eq.
        iApply (interp_cap_not_shadow with "Hinv_interp"); eauto using writeAllowed_nonO.
      - rewrite lookup_insert_ne // in Hdst'.
        iApply (interp_cap_not_shadow with "[Hreg]"); eauto using writeAllowed_nonO.
        by iApply "Hreg".
    }
    iApply (wp_store_imm with "[Hmap HMemRes]"); eauto.
    { by rewrite lookup_insert_eq. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. rewrite lookup_insert_is_Some'; eauto. }
    { iSplitR "Hmap"; auto. }
    iDestruct (if_dec_later with "Hwcond") as "Hwcond'";auto.
    iDestruct (allow_store_mem_later imm with "HStoreMem") as "HStoreMem".

    iNext. iIntros (regs' mem' retv). iDestruct 1 as (HSpec) "[Hmem Hmap]".

    destruct HSpec as [p1 g1 b1 e1 a1 ea1 storev1 oldv1
        Harg1 Hallow1 Hshadow1 Hlookup1 -> Hshadow_eq1 Hincr
      |p0 g0 b0 e0 a0 ea0 heap_a0 z0 π0 old_status0 Harg0 Hallow0 Hshadow0 Htranslate0
        Hold0 Hmem_eq0 Hshadow_eq0 Hincr0|].
    { apply incrementPC_Some_inv in Hincr
        as (tpc & ppc & gpc & bpc & epc & apc & apc' & πpc & HPC & Hapc' & ->).
      rewrite lookup_insert_eq in HPC. injection HPC as <- <- <- <- <- <- <-.
      iApply wp_pure_step_later; auto. iNext; iIntros "_".

      rewrite mono_invariant_eq.
      iDestruct (switch_monotonicity_formulation with "HmonoV") as "HmonoV"; [eauto..|].

      (* Step 4: return all the resources we had in order to close the second location
         in the region, in the cases where we need to *)
      iDestruct (mem_map_recover_res imm
                  with "HStoreMem Hreg Hinv_interp Hinterp [Hwcond'] [Hmono] [HmonoV] Hmem")
        as (w') "(Hworld_interp & Ha & HSVInterp & HmonoV)"; eauto.

      iDestruct (switch_monotonicity_formulation with "HmonoV") as "HmonoV"; auto.
      rewrite /monotonicity_guarantees_decide -mono_invariant_eq.

      iDestruct ("WorldRes" with "[$Ha $HSVInterp $HmonoV]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }
      rewrite insert_insert_eq.

      iApply ("IH" $! _ _ _ _ _ regs p g b e apc' None
               with "[%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]"); auto.
      iApply (interp_next_PC with "Hinv_interp"); eauto.
    }
    { exfalso. pose proof (Hnonshadow p0 g0 b0 e0 a0 ea0 Hallow0). congruence. }
    { iApply wp_pure_step_later; auto. iNext; iIntros "_". iApply wp_value; auto.  }
    Unshelve. all: auto.
  Qed.

End fundamental.
