From stdpp Require Import base.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From griotte Require Import world_ghost_theory.
From griotte Require Export logrel.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Import rules_Load wp_rules_interp.
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

  (** The witness the world supplies for the word that a load from [r] reads
      in [mem]: the quarantine witness for a quarantined identifier (§4.5). *)
  Definition load_witness_mem (W : WORLD) (regs : LReg) (r : RegName) (imm : Z) (mem : LMem)
    : load_witness :=
    match regs !! r with
    | Some (WCap _ _ _ _ _ a @@? _) =>
        match (a + imm)%a with
        | Some ea => match mem !! ea with
                    | Some v => load_witness_of W v
                    | None => LoadPlain
                    end
        | None => LoadPlain
        end
    | _ => LoadPlain
    end.

  Lemma load_witness_mem_eq W regs r imm mem p g b e a ea v :
    reg_allows_load_imm regs r imm p g b e a ea →
    mem !! ea = Some v →
    load_witness_mem W regs r imm mem = load_witness_of W v.
  Proof.
    intros (Hreg & Hadd & _ & _) Hv.
    destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hreg) as (_ & π & Hr).
    by rewrite /load_witness_mem Hr Hadd Hv.
  Qed.

  Lemma heap_provenance_load_witness_mem W regs r imm mem :
    heap_provenance (heap_std W) -∗ load_witness_res (load_witness_mem W regs r imm mem).
  Proof.
    iIntros "#Hprov". rewrite /load_witness_mem.
    destruct (regs !! r) as [ [ [|[t p g b e a|]| |] π]|]; try done.
    destruct (a + imm)%a as [ea|]; last done.
    destruct (mem !! ea) as [v|]; last done.
    by iApply heap_provenance_load_witness.
  Qed.

  (* A decision procedure that does not unfold [reg_allows_load_imm], so that
     the definitions below can be rewritten under [(a + imm)%a]. *)
  #[local] Instance reg_allows_load_imm_dec regs r imm p g b e a ea :
    Decision (reg_allows_load_imm regs r imm p g b e a ea) | 0.
  Proof. rewrite /reg_allows_load_imm. apply _. Defined.

  (* The necessary resources to close the region again,
     except for the points to predicate, which we will store separately
     The boolean bl can be used to keep track of whether or not we have applied a wp lemma *)
  Definition region_open_resources W C (k : LAddr) als p φ v (has_later : bool): iProp Σ :=
    (∃ ρ,
     sts_state_std C k ρ
    ∗ ⌜ρ ≠ Revoked⌝
    ∗ ⌜heap_key_live (heap_std W) k⌝
    ∗ world_interp_open W C (k :: als)
    ∗ if_later_P has_later (monotonicity_guarantees_region C φ p v ρ ∗ φ (W,C, v))
    ∗ if_later_P has_later (key_share k)
    ∗ rel C k p φ)%I.

  Lemma load_inr_eq (imm : Z) {regs r p0 g0 b0 e0 a0 ea t1 p1 g1 b1 e1 a1}:
    reg_allows_load_imm regs r imm p0 g0 b0 e0 a0 ea →
    read_reg_inr regs r t1 p1 g1 b1 e1 a1 →
    p0 = p1 ∧ g0 = g1 ∧ b0 = b1 ∧ e0 = e1 ∧ a0 = a1.
  Proof.
    intros Hrar H3.
    destruct Hrar as (Hinr0 & _).
    destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hinr0) as (_ & π & Hr).
    rewrite /read_reg_inr Hr in H3. by inversion H3.
  Qed.

  Lemma load_prov_eq (imm : Z) {regs r p0 g0 b0 e0 a0 ea π}:
    reg_allows_load_imm regs r imm p0 g0 b0 e0 a0 ea →
    read_reg_prov regs r π →
    regs !! r = Some (WCap true p0 g0 b0 e0 a0 @@? π).
  Proof. intros (Hinr0 & _) Hπ. by apply read_reg_prov_cap. Qed.

  (* Description of what the resources are supposed to look like
     after opening the region if we need to,
     but before closing the region up again*)
  Definition allow_load_res (imm : Z) W C r (regs : LReg) pc_a pc_p :=
    (∃ t p g b e a π, ⌜read_reg_inr regs r t p g b e a⌝ ∗ ⌜read_reg_prov regs r π⌝ ∗
    match (a + imm)%a with
    | None => world_interp_open W C [LNonHeap pc_a]
    | Some ea => if decide (reg_allows_load_imm regs r imm p g b e a ea)
    then (if decide (addr_key π ea = LNonHeap pc_a)
          then world_interp_open W C [LNonHeap pc_a] ∗ ⌜PermFlowsTo p pc_p⌝
          else ∃ w p' (P:D),
              ⌜PermFlowsTo p p'⌝
              ∗ ⌜persistent_cond P⌝
              ∗ ⌜ea ≠ pc_a⌝
              ∗ ▷ ea ↦ₐ w
              ∗ (region_open_resources W C (addr_key π ea) [LNonHeap pc_a] p' (safeC P) w true)
              ∗ ▷ rcond P C p' interp)
    else world_interp_open W C [LNonHeap pc_a] end)%I.

   Lemma interp_hpf_eq (imm : Z) (W : WORLD) (C : CmptName) P (regs : leibnizO LReg) (r1 : RegName)
    p g b e a pc_a pc_p pc_g pc_b pc_e pc_p' :
    read_reg_prov (<[PC:=WCap true pc_p pc_g pc_b pc_e pc_a @@? None]> regs) r1 None
    → reg_allows_load_imm (<[PC:=WCap true pc_p pc_g pc_b pc_e pc_a @@? None]> regs) r1 imm p g b e a pc_a
    → PermFlowsTo pc_p pc_p'
    → (∀ (r1 : RegName) v, ⌜r1 ≠ PC⌝ → ⌜regs !! r1 = Some v⌝ → (interp W C v))
    -∗ rel C (LNonHeap pc_a) pc_p' P
    -∗ ⌜PermFlowsTo p pc_p'⌝.
  Proof.
    intros Hπ Hrar Hfl.
    pose proof (load_prov_eq imm Hrar Hπ) as Hr1.
    destruct Hrar as (_ & Hadd & Hwa & Hwb).
    destruct (decide (r1 = PC)) as [->|Hne].
    - rewrite lookup_insert_eq in Hr1. simplify_eq. iIntros. done.
    - rewrite lookup_insert_ne // in Hr1.
      iIntros "Hreg #Hinva".
      iDestruct ("Hreg" $! r1 _ Hne Hr1) as "Hr1".
      iDestruct (read_allowed_inv _ _ pc_a with "Hr1")
        as (p'' P'' Hflp'' Hcond_pers'') "(Hrel'' & Hzcond'' & Hrcond'' & Hwcond'')"; auto.
      { apply andb_true_iff in Hwb as [Hle Hge].
        split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
      iDestruct (rel_agree _ _ _ _ p'' pc_p' with "[$Hinva $Hrel'']") as "[-> _]".
      done.
  Qed.

  Definition allow_load_mem (imm : Z) W C r (regs : LReg) pc_a pc_p pc_w (mem : LMem) (has_later: bool):=
    (∃ t p g b e a π, ⌜read_reg_inr regs r t p g b e a⌝ ∗ ⌜read_reg_prov regs r π⌝ ∗
    match (a + imm)%a with
    | None => ⌜mem = <[pc_a:=pc_w]> ∅⌝ ∗ world_interp_open W C [LNonHeap pc_a]
    | Some ea => if decide (reg_allows_load_imm regs r imm p g b e a ea)
    then (if decide (addr_key π ea = LNonHeap pc_a)
          then ⌜mem = <[pc_a:=pc_w]> ∅⌝ ∗ world_interp_open W C [LNonHeap pc_a] ∗ ⌜PermFlowsTo p pc_p⌝
          else ∃ w p' (P:D),
              ⌜PermFlowsTo p p'⌝
              ∗ ⌜persistent_cond P⌝
              ∗ ⌜ea ≠ pc_a⌝
              ∗ ⌜mem = <[ea:=w]> (<[pc_a:=pc_w]> ∅)⌝
              ∗ (region_open_resources W C (addr_key π ea) [LNonHeap pc_a] p' (safeC P) w has_later)
              ∗ if_later_P has_later (rcond P C p' interp))
    else ⌜mem = <[pc_a:=pc_w]> ∅⌝ ∗ world_interp_open W C [LNonHeap pc_a] end)%I.

  Lemma create_load_res (imm : Z)
    (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p_pc p_pc' : Perm) (g_pc : Locality) (b_pc e_pc a_pc : Addr)
    (src : RegName)
    (t : bool) (p : Perm) (g : Locality) (b e a : Addr) (π : option AId) (P:D) (w_pc : LWord) :
    read_reg_inr (<[PC:=WCap true p_pc g_pc b_pc e_pc a_pc @@? None]> regs) src t p g b e a
    → read_reg_prov (<[PC:=WCap true p_pc g_pc b_pc e_pc a_pc @@? None]> regs) src π
    → PermFlowsTo p_pc p_pc'
    → (∀ (r : RegName) (v : LWord), ⌜r ≠ PC⌝ → ⌜regs !! r = Some v⌝ → interp W C v)
    -∗ interp W C (WCap true p_pc g_pc b_pc e_pc a_pc @@? None)
    -∗ rel C (LNonHeap a_pc) p_pc' (safeC P)
    -∗ world_interp_open W C [LNonHeap a_pc]
    -∗ a_pc ↦ₐ w_pc
    -∗ ◇ (allow_load_res imm W C src (<[PC:= WCap true p_pc g_pc b_pc e_pc a_pc @@? None]> regs) a_pc p_pc'
          ∗ a_pc ↦ₐ w_pc).
  Proof.
    iIntros (HVsrc Hπ Hfl) "#Hreg #Hinterp_pc #Hinva Hworld_interp Hapc".
    rewrite /allow_load_res.
    destruct (a + imm)%a as [ea|] eqn:Hadd; cycle 1.
    { iModIntro. iFrame "Hapc". iExists t,p,g,b,e,a,π. iFrame "%". by rewrite Hadd. }
    destruct (decide (reg_allows_load_imm (<[PC:=WCap true p_pc g_pc b_pc e_pc a_pc @@? None]> regs)
                        src imm p g b e a ea)) as [Hallows|Hallows]; cycle 1.
    { iModIntro. iFrame "Hapc". iExists t,p,g,b,e,a,π. iFrame "%".
      rewrite Hadd. by rewrite decide_False. }
    pose proof (load_prov_eq imm Hallows Hπ) as Hsrc.
    destruct (decide (addr_key π ea = LNonHeap a_pc)) as [Hkey|Hkey].
    { (* The PC's region: already open. *)
      destruct (addr_key_pc _ _ _ Hkey) as [-> ->].
      iDestruct (interp_hpf_eq imm W C (safeC P) regs src p g b e a a_pc
        p_pc g_pc b_pc e_pc p_pc' with "Hreg Hinva") as %Hflp; eauto.
      iModIntro. iFrame "Hapc". iExists t,p,g,b,e,a,None. iFrame "%".
      rewrite Hadd. rewrite decide_True // decide_True //. by iFrame. }
    pose proof Hallows as (Hrinr & Hoff & Hra & Hwb).
    apply andb_prop in Hwb as [Hle Hge].
    iAssert (interp W C (WCap true p g b e a @@? π)) as "#Hvsrc".
    { destruct (decide (src = PC)) as [->|Hne].
      - rewrite lookup_insert_eq in Hsrc. simplify_eq. done.
      - rewrite lookup_insert_ne // in Hsrc. iApply ("Hreg" $! src _ Hne Hsrc).
    }
    iDestruct (read_allowed_inv _ _ ea with "Hvsrc")
      as (p0 P0 Hflp0 Hcond_pers0) "(Hrel0 & Hzcond0 & Hrcond0 & Hwcond0)"; auto
    ; first (split; [by apply Z.leb_le | by apply Z.ltb_lt]).
    assert (withinBounds b e ea = true) as Hbounds.
    { by rewrite /withinBounds Hle Hge. }
    iDestruct (readAllowed_valid_cap_implies _ _ _ _ _ _ _ ea with "Hvsrc") as %HH; eauto.
    destruct HH as (ρ0 & Hstd & Hnotrevoked).
    iDestruct (interp_cap_addr_live with "Hvsrc") as %Hlive;
      eauto using readAllowed_nonO.
    (* Another key: open its region. *)
    iDestruct (open_world_interp_next _ _ _ (addr_key π ea) p0 _ ρ0 with "Hrel0 Hworld_interp")
      as "(Hworld & Hstate' & [%w0 (HpO&Hea&HP0&Hmono)] )"; eauto.
    { apply not_elem_of_cons; split; last apply not_elem_of_nil. done. }
    { destruct ρ0; simplify_eq; [by left | by right]. }
    iEval (rewrite addr_key_pointsto) in "Hea".
    iDestruct "Hea" as "[Hea Hshare]".
    iDestruct "Hea" as ">Hea".
    (* Its address is not the PC's: both points-to are full. *)
    iDestruct (address_neq with "Hea Hapc") as %Hne.
    iModIntro. iFrame "Hapc".
    iExists t,p,g,b,e,a,π. iFrame "%". rewrite Hadd.
    rewrite decide_True // decide_False //.
    iExists w0,p0,P0.
    iSplit; first done. iSplit; first done. iSplit; first done.
    iFrame "Hea". iSplitR "Hrcond0"; last done.
    iExists ρ0. iFrame "Hstate' Hworld Hshare Hrel0 HP0".
    iSplit; first done. iSplit; first done.
    iNext.
    rewrite mono_invariant_monotonicity_guarantees_region; eauto.
  Qed.

  Lemma load_res_implies_mem_map (imm : Z)
    (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
      (p : Perm) (a : Addr) (w : LWord) (src : RegName):
    allow_load_res imm W C src regs a p
    -∗ a ↦ₐ w
    -∗ ∃ mem0 : LMem,
        allow_load_mem imm W C src regs a p w mem0 true
        ∗ ▷ ([∗ map] a0↦w ∈ mem0, a0 ↦ₐ w).
  Proof.
    iIntros "HLoadRes Ha".
    iDestruct "HLoadRes" as (t1 p1 g1 b1 e1 a1 π1) "(% & % & HLoadRes)".
    destruct (a1 + imm)%a as [ea|] eqn:Hadd.
    2: {
      iExists (<[a:=w]> ∅). iSplitL "HLoadRes".
      - iExists t1,p1,g1,b1,e1,a1,π1. iFrame "%". rewrite Hadd. by iFrame.
      - iNext. by iApply memMap_resource_1.
    }
    case_decide as Hallows; cycle 1.
    {
      iExists _.
      iSplitL "HLoadRes".
      + iExists t1,p1,g1,b1,e1,a1,π1. iFrame "%". rewrite Hadd.
        case_decide; first by exfalso. auto.
      + iNext. by iApply memMap_resource_1.
    }
    case_decide as Hkey.
    - iExists _.
      iSplitL "HLoadRes"; last (iNext; by iApply memMap_resource_1).
      iExists t1,p1,g1,b1,e1,a1,π1. iFrame "%". rewrite Hadd.
      case_decide; last by exfalso.
      case_decide; last by exfalso.
      by iFrame.
    - iDestruct "HLoadRes" as (w0 p' P Hp'O Hpers Hne) "[HLoadCh [HLoadRest #Hrcond] ]".
      iExists _.
      iSplitL "HLoadRest".
      + iExists t1,p1,g1,b1,e1,a1,π1. iFrame "%". rewrite Hadd.
        case_decide; last by exfalso.
        case_decide; first by exfalso.
        iExists w0,p',P.
        repeat (iSplit; auto).
      + iNext.
        iApply memMap_resource_2ne; auto; iFrame.
  Qed.

  Lemma mem_map_implies_pure_conds (imm : Z)
    (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
      (p : Perm) (a : Addr) (w : LWord) (src : RegName)
      (mem0 : LMem):
    allow_load_mem imm W C src regs a p w mem0 true
    -∗ ⌜mem0 !! a = Some w⌝ ∗ ⌜allow_load_map_or_true_imm src imm regs mem0⌝.
  Proof.
    iIntros "HLoadMem".
    iDestruct "HLoadMem" as (t1 p1 g1 b1 e1 a1 π1) "(%Hinr & % & HLoadRes)".
    destruct (a1 + imm)%a as [ea|] eqn:Hadd.
    2: {
      iDestruct "HLoadRes" as "[-> _]".
      iPureIntro. split; first by rewrite lookup_insert_eq.
      exists t1,p1,g1,b1,e1,a1. split; first done. by rewrite /reg_allows_load_imm Hadd.
    }
    case_decide as Hallows; cycle 1.
    {
      iDestruct "HLoadRes" as "[-> HLoadRes ]".
      iPureIntro. split; first by rewrite lookup_insert_eq.
      exists t1,p1,g1,b1,e1,a1. split; first done. rewrite /reg_allows_load_imm Hadd.
      case_decide as Hdec1; last done.
      exfalso. apply Hallows. by rewrite /reg_allows_load_imm Hadd.
    }
    case_decide as Hkey.
    - destruct (addr_key_pc _ _ _ Hkey) as [-> ->].
      iDestruct "HLoadRes" as "[-> HLoadRes]".
      iPureIntro. split; first by rewrite lookup_insert_eq.
      exists t1,p1,g1,b1,e1,a1. split; first done. rewrite /reg_allows_load_imm Hadd.
      case_decide as Hdec1; last done.
      exists w. by rewrite lookup_insert_eq.
    - iDestruct "HLoadRes" as (w0 p' P Hp'O Hpers Hne) "[-> _]".
      iPureIntro. split; first (rewrite lookup_insert_ne; auto; by rewrite lookup_insert_eq).
      exists t1,p1,g1,b1,e1,a1. split; first done. rewrite /reg_allows_load_imm Hadd.
      case_decide; last done.
      exists w0. by rewrite lookup_insert_eq.
  Qed.

  Lemma allow_load_mem_later (imm : Z)
    (W : WORLD) (C :CmptName) (regs : leibnizO LReg)
    (p : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (src : RegName) (mem0 : LMem):
    allow_load_mem imm W C src regs a p w mem0 true
    -∗ ▷ allow_load_mem imm W C src regs a p w mem0 false.
  Proof.
    iIntros "HLoadMem".
    iDestruct "HLoadMem" as (t0 p0 g0 b0 e0 a0 π0) "(% & % & HLoadMem)".
    do 7 (iApply later_exist_2; iExists _). iApply later_sep_2; iSplitR; auto.
    iApply later_sep_2; iSplitR; auto.
    destruct (a0 + imm)%a as [ea|] eqn:Hadd; last iFrame.
    case_decide; last iFrame.
    case_decide; first iFrame.
    iDestruct "HLoadMem" as (w0 p' P Hp'O Hpers Hne) "(-> & HLoadMem & #Hrcond)".
    do 3 (iApply later_exist_2; iExists _).
    do 4 (iApply later_sep_2; iSplitR; auto).
  Qed.

  Definition rcond' (P : D) (C : CmptName) p g b e a regs p' : iProp Σ
    := (if decide (readAllowed_a_in_lregs (<[PC:=WCap true p g b e a @@? None]> regs) a)
             then (rcond P C p' interp)
             else emp)%I.
  Instance rcond'_pers P C p g b e a regs p' : Persistent (rcond' P C p g b e a regs p' ).
  Proof. intros. rewrite /rcond'. case_decide;apply _. Qed.

  Lemma mem_map_recover_res (imm : Z)
    (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (pc_w : LWord) (src : RegName)
    (p_pc p_pc' : Perm) (g_pc : Locality) (b_pc e_pc a_pc : Addr)
    (p : Perm) (g : Locality) (b e a ea : Addr)
    (mem0 : LMem) (loadv : LWord) (P:D) :
    PermFlowsTo p_pc p_pc'
    -> reg_allows_load_imm (<[PC:=WCap true p_pc g_pc b_pc e_pc a_pc @@? None]> regs) src imm p g b e a ea
    -> mem0 !! ea = Some loadv
    -> interp W C (WCap true p_pc g_pc b_pc e_pc a_pc @@? None)
      -∗ (∀ r v, ⌜r ≠ PC⌝ → ⌜regs !! r = Some v⌝ → interp W C v)
         -∗ rcond' P C p_pc g_pc b_pc e_pc a_pc regs p_pc'
            -∗ P W C pc_w
               -∗ ([∗ map] a1↦w0 ∈ mem0, a1 ↦ₐ w0)
                  -∗ allow_load_mem imm W C src (<[PC:=WCap true p_pc g_pc b_pc e_pc a_pc @@? None]> regs) a_pc p_pc' pc_w mem0 false
                     -∗ world_interp_open W C [LNonHeap a_pc] ∗ a_pc ↦ₐ pc_w ∗ interp_in_mem p W C loadv.
  Proof.
    intros Hflpc Hrar Ha.
    iIntros "##Hinterp_pc Hreg #Hrcond Hw Hmem HLoadMem".
    iDestruct "HLoadMem" as (t1 p1 g1 b1 e1 a1 π1) "(%Hread & %Hπ & HLoadRes)".
    destruct (load_inr_eq imm Hrar Hread) as (<- & <- & <- & <- & <-).
    pose proof (load_prov_eq imm Hrar Hπ) as Hsrc.
    pose proof Hrar as (_ & Hoff & _).
    rewrite Hoff.
    case_decide as Hallows; last by exfalso.
    destruct Hallows as (Hrinr & Hadd & Hwa & Hwb).
    case_decide as Hkey.
    - destruct (addr_key_pc _ _ _ Hkey) as [-> ->].
      iDestruct "HLoadRes" as "(-> & $ & %Hfl')".
      rewrite lookup_insert_eq in Ha; inversion Ha; clear Ha; subst.
      rewrite -memMap_resource_1.
      iFrame.
      rewrite /rcond'.
      rewrite decide_True.
      2: { eexists src,_.
           split; first exact Hsrc.
           split; first done.
           split; first done. cbn. done.
      }
      iSpecialize ("Hrcond" with "Hw").
      rewrite /interp_in_mem_pre.
      rewrite /interp_in_mem /= /interp_in_mem_pre !filter_heap_load_word.
      iApply (interp_weakening_word_load W C p p_pc'); eauto.
    - iDestruct "HLoadRes"
        as (w p' P' Hflp'' HpersP' Hne) "(-> & HLoadRes & #Hrcond')".
      rewrite lookup_insert_eq in Ha; inversion Ha; clear Ha; subst.
      rewrite memMap_resource_2ne; last auto.
      iDestruct "Hmem" as "[Ha Hapc]"; iFrame.
      rewrite /persistent_cond in HpersP'.
      iDestruct "HLoadRes" as (ρ1) "(Hstate' & %Hnotrevoked & %Hlive & Hworld_interp & (Hfuture & #HV) & Hshare & Hrel')"
      ; cbn.
      iDestruct (addr_key_pointsto_join with "Ha Hshare") as "Ha".
      assert (isO p' = false) as HpO'.
      { eapply readAllowed_flowsto, readAllowed_nonO in Hflp''; auto. }
      iDestruct (close_world_interp_next with "Hworld_interp Hstate' Hrel' [Ha Hfuture]") as "$"; eauto.
      { apply not_elem_of_cons; split; last apply not_elem_of_nil. done. }
      { destruct ρ1; simplify_eq; naive_solver. }
      { iFrame "∗#%".
        rewrite mono_invariant_monotonicity_guarantees_region; eauto.
      }
      iDestruct ("Hrcond'" with "HV") as "HV'".
      iEval (rewrite /interp_in_mem /= /interp_in_mem_pre filter_heap_load_word).
      iApply (interp_weakening_word_load W C p p' (filter_heap W loadv));
        first exact Hflp''.
      iEval (rewrite /interp_in_mem_pre filter_heap_load_word) in "HV'".
      iExact "HV'".
  Qed.

  Lemma load_case (imm : Z) (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (ρ : region_type) (dst src : RegName) (P:D) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs p p' g b e a w (cload dst src imm) ρ P cstk Ws Cs.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe Hworld_interp Hown Htframe".
    iIntros "Hstate HPC Hmap".
    iInsert "Hmap" PC.

    iDestruct (WorldRes_acc with "WorldRes") as " [ (>Ha & Hinterp) WorldRes ]".

    iClear "Hwcond".
    iDestruct (if_dec_later with "Hrcond") as "Hrcond'"; iClear "Hrcond".

    assert (Persistent (▷ P W C w)) as HpersP.
    { apply later_persistent. specialize (Hpers (W,C,w)). auto. }
    iDestruct "Hinterp" as "#Hw".

    (* To read out PC's name later, and needed when calling wp_load *)
    assert(∀ x : RegName, is_Some (<[PC:=WCap true p g b e a @@? None]> regs !! x)) as Hsome'.
    {
      intros. destruct (decide (x = PC)); last by rewrite lookup_insert_ne.
      rewrite e0 lookup_insert_eq; unfold is_Some. by eexists.
    }

    (* Initializing the names for the values of Hsrc now,
       to instantiate the existentials in step 1 *)
    assert (∃ t0 p0 g0 b0 e0 a0 π0,
               read_reg_inr (<[PC:=WCap true p g b e a @@? None]> regs) src t0 p0 g0 b0 e0 a0 ∧
               read_reg_prov (<[PC:=WCap true p g b e a @@? None]> regs) src π0)
      as (t0 & p0 & g0 & b0 & e0 & a0 & π0 & HVsrc & HVπ).
    {
      specialize Hsome' with src as Hsrc.
      destruct Hsrc as [wsrc Hsomesrc].
      unfold read_reg_inr, read_reg_prov. rewrite Hsomesrc.
      destruct wsrc as [ [|[ t0 p0 g0 b0 e0 a0|] | | ] π0];
        try (exists true,p,g,b,e,a,None; done).
      by repeat eexists.
    }

    (* The world's heap provenance supplies the status witness of the
       load rule (§4.5). *)
    iDestruct (world_interp_open_heap_provenance with "Hworld_interp") as "[Hworld_interp #Hprov]".

    (* Step 1: open the region, if necessary, and store all the resources obtained from the region in allow_load_res imm *)
    iMod (create_load_res imm with "Hreg Hinv_interp Hinva Hworld_interp Ha") as "[HLoadRes Ha]"; eauto.
    (* Clear helper values; they exist in the existential now *)
    clear HVsrc HVπ t0 p0 g0 b0 e0 a0 π0.

    (* Step2: derive the concrete map of memory we need, and any spatial predicates holding over it *)
    iDestruct (load_res_implies_mem_map imm W  with "HLoadRes Ha") as (mem) "[HLoadMem HMemRes]".

    (* Step 3:  derive the non-spatial conditions over the memory map*)
    iDestruct (mem_map_implies_pure_conds imm with "HLoadMem") as %(HReadPC & HLoadAP); auto.

    (* Step 4: move the later outside, so that we can remove it after applying wp_load *)
    iDestruct (allow_load_mem_later imm with "HLoadMem") as "HLoadMem"; auto.

    iAssert (⌜∀ p0 g0 b0 e0 a0 ea0,
      reg_allows_load_imm (<[PC:=WCap true p g b e a @@? None]> regs) src imm p0 g0 b0 e0 a0 ea0 →
      is_mmio_address ea0 = false⌝)%I as %Hnonmmio.
    { iIntros (p0 g0 b0 e0 a0 ea0 (Hsrc & Hadd & Hra & Hwb)).
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc) as (Hsrc_null & π0 & Hsrc').
      destruct (decide (src = PC)) as [->|Hsrc_pc].
      - rewrite lookup_insert_eq in Hsrc'. simplify_eq.
        iApply (interp_cap_not_mmio with "Hinv_interp"); eauto using readAllowed_nonO.
      - rewrite lookup_insert_ne // in Hsrc'.
        iApply (interp_cap_not_mmio with "[Hreg]"); eauto using readAllowed_nonO.
        by iApply "Hreg".
    }

    iDestruct (heap_provenance_load_witness_mem W
                 (<[PC:=WCap true p g b e a @@? None]> regs) src imm mem with "Hprov") as "Hwit".
    iApply (wp_load_witness_imm with "[$HMemRes $Hwit $Hmap]"); eauto.
    { by rewrite lookup_insert_eq. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }
    { intros p0 g0 b0 e0 ea0 Hallow.
      destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 Hallow'].
      pose proof (Hnonmmio _ _ _ _ _ _ Hallow') as Hmmio.
      apply orb_false_iff in Hmmio as [-> ->].
      by eapply allow_load_implies_loadv_imm. }
    iNext. iIntros (regs' retv) "(%HSpec & Hmem & _ & Hmap)".
    destruct HSpec as [p0 g0 b0 e0 ea loadv loadv' Hallow Hsh Hl Hpost Hincr
                    |p0 g0 b0 e0 ea heap_a revoked Hallow Hsh
                    |p0 g0 b0 e0 ea Hallow Hrev
                    |Hfail].
    (* A valid capability never reaches the shadow region or the revoker. *)
    2,3: exfalso; destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 Hallow'];
         pose proof (Hnonmmio _ _ _ _ _ _ Hallow') as Hmmio;
         apply orb_false_iff in Hmmio as [? ?]; congruence.
    2: { iApply wp_pure_step_later; auto. iNext; iIntros "_".
         iApply wp_value; auto. }
    destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 Hallow'].

    (* Step 5: return all the resources we had in order to close the second location in the region, in the cases where we need to *)
    iDestruct (mem_map_recover_res imm with "Hinv_interp Hreg Hrcond' Hw Hmem HLoadMem") as
      "[Hworld_interp [Ha #Hnormal ] ]"; eauto.
    (* The world's witness makes the loaded word valid (§4.5). *)
    rewrite (load_witness_mem_eq _ _ _ _ _ _ _ _ _ _ _ _ Hallow' Hl) in Hpost.
    iDestruct (interp_in_mem_load_post with "Hnormal") as "#HLVInterp"; first exact Hpost.
    iApply wp_pure_step_later; auto. iNext; iIntros "_".
    apply incrementPC_Some_inv in Hincr as (tpc & ppc & gpc & bpc & epc & apc & apc' & πpc & HPC & Hapc' & ->).

    (* Exceptional success case: we do not apply the induction hypothesis in case we have a faulty PC*)
    destruct tpc; cycle 1.
    { iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]".
      { by rewrite lookup_insert_eq. }
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_notCorrectPC_tag with "HPC"); first done.
      iNext; iIntros "_".
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iApply wp_value; auto.
    }
    destruct (executeAllowed ppc) eqn:Hp'.
    2 : {
      iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]".
      { by rewrite lookup_insert_eq. }
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_notCorrectPC_perm with "[HPC]"); eauto. iIntros "!> _".
      iApply wp_pure_step_later; auto. iNext; iIntros "_". iApply wp_value.
      iIntros (a1); inversion a1.
    }

    iDestruct ("WorldRes" with "[$Ha $Hw]") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
    { destruct ρ;auto;contradiction. }

    iApply ("IH" $! _ _ _ _ _ (<[dst:=loadv']ₗ> (<[PC:=WCap true p g b e a @@? None]> regs))
             with "[%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]").
    { intros x6. rewrite /linsert_reg.
      rewrite lookup_insert_is_Some.
      destruct (decide (dst = x6)); [ auto | right; split; auto]. }
    (* Prove in the general case that the value relation holds for the register
       that was loaded to - unless it was the PC.*)
    { iIntros (ri wi Hri Hregs_ri).
      rewrite /linsert_reg in Hregs_ri.
      destruct (decide (ri = dst)).
      { subst ri. rewrite lookup_insert_eq in Hregs_ri. injection Hregs_ri as <-.
        destruct (decide (dst = cnull)); [by iApply interp_untagged | done]. }
      rewrite !lookup_insert_ne // in Hregs_ri. iApply "Hreg"; auto. }
    { iApply "Hmap". }
    iModIntro.
    rewrite /linsert_reg in HPC.
    destruct (decide (PC = dst)) as [<-|Hne]; cycle 1.
    + rewrite lookup_insert_ne // lookup_insert_eq in HPC.
      injection HPC as <- <- <- <- <- <-.
      iApply (interp_next_PC with "Hinv_interp"); eauto.
    + rewrite lookup_insert_eq in HPC. injection HPC as ->.
      iApply (interp_weakening with "IH HLVInterp"); eauto; try solve_addr; try done;
        try apply subseg_heap_base_same.
  Qed.

End fundamental.
