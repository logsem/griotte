From stdpp Require Import base.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From griotte Require Export logrel.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Import rules_Load.
From griotte Require Import map_simpl register_tactics.
Import uPred.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation D := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  (* The necessary resources to close the region again,
     except for the points to predicate, which we will store separately
     The boolean bl can be used to keep track of whether or not we have applied a wp lemma *)
  Definition region_open_resources W C a als p φ v (has_later : bool): iProp Σ :=
    (∃ ρ,
     sts_state_std C a ρ
    ∗ ⌜ρ ≠ Revoked⌝
    ∗ world_interp_open W C (a :: als)
    ∗ if_later_P has_later (monotonicity_guarantees_region C φ p v ρ ∗ φ (W,C, v))
    ∗ rel C a p φ)%I.

  Lemma load_inr_eq (imm : Z) {regs r p0 g0 b0 e0 a0 ea t1 p1 g1 b1 e1 a1}:
    reg_allows_load_imm regs r imm p0 g0 b0 e0 a0 ea →
    read_reg_inr regs r t1 p1 g1 b1 e1 a1 →
    p0 = p1 ∧ g0 = g1 ∧ b0 = b1 ∧ e0 = e1 ∧ a0 = a1.
  Proof.
    intros Hrar H3.
    pose (Hrar' := Hrar).
    destruct Hrar' as (Hinr0 & _).
    destruct (decide (r = cnull)); simplify_map_eq.
    { destruct (regs !! cnull) eqn:Hr ; simplify_map_eq. }
    rewrite /read_reg_inr Hinr0 in H3. by inversion H3.
  Qed.

  (* Description of what the resources are supposed to look like
     after opening the region if we need to,
     but before closing the region up again*)
  Definition allow_load_res (imm : Z) W C r (regs : Reg) pc_a pc_p :=
    (∃ t p g b e a, ⌜read_reg_inr regs r t p g b e a⌝ ∗
    match (a + imm)%a with
    | None => world_interp_open W C [pc_a]
    | Some ea => if decide (reg_allows_load_imm regs r imm p g b e a ea)
    then (if decide (ea ≠ pc_a)
          then ∃ w p' (P:D),
              ⌜PermFlowsTo p p'⌝
              ∗ ⌜persistent_cond P⌝
              ∗ ▷ ea ↦ₐ w
              ∗ (region_open_resources W C ea [pc_a] p' (safeC P) w true)
              ∗ ▷ rcond P C p' interp
          else world_interp_open W C [pc_a] ∗ ⌜PermFlowsTo p pc_p⌝)
    else world_interp_open W C [pc_a] end)%I.

   Lemma interp_hpf_eq (imm : Z) (W : WORLD) (C : CmptName) P (regs : leibnizO Reg) (r1 : RegName)
    p g b e a pc_a pc_p pc_g pc_b pc_e pc_p' :
    reg_allows_load_imm (<[PC:=WCap true pc_p pc_g pc_b pc_e pc_a]> regs) r1 imm p g b e a pc_a
    → PermFlowsTo pc_p pc_p'
    → (∀ (r1 : RegName) v, ⌜r1 ≠ PC⌝ → ⌜regs !! r1 = Some v⌝ → (interp W C v))
    -∗ rel C pc_a pc_p' P
    -∗ ⌜PermFlowsTo p pc_p'⌝.
  Proof.
    destruct (decide (r1 = PC)).
    - subst r1. iIntros ([? ?] ?). simplify_map_eq; auto.
    - iIntros ((Hsomer1 & Hadd & Hwa & Hwb) Hfl) "Hreg #Hinva".
      simplify_map_eq.
      assert (r1 ≠ cnull); simplify_map_eq.
      { intros -> ; simplify_map_eq. destruct (regs !! cnull) eqn:Hr; simplify_map_eq. }
      iDestruct ("Hreg" $! r1 _ n Hsomer1) as "Hr1"; eauto.
      iDestruct (read_allowed_inv _ _ pc_a with "Hr1")
        as (p'' P'' Hflp'' Hcond_pers'') "(Hrel'' & Hzcond'' & Hrcond'' & Hwcond'')"; auto.
      { apply andb_true_iff in Hwb as [Hle Hge].
        split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
      iDestruct (rel_agree _ _ _ _ p'' pc_p' with "[$Hinva $Hrel'']") as "[-> _]".
      done.
  Qed.

  Definition allow_load_mem (imm : Z) W C r (regs : Reg) pc_a pc_p pc_w (mem : Mem) (has_later: bool):=
    (∃ t p g b e a, ⌜read_reg_inr regs r t p g b e a⌝ ∗
    match (a + imm)%a with
    | None => ⌜mem = <[pc_a:=pc_w]> ∅⌝ ∗ world_interp_open W C [pc_a]
    | Some ea => if decide (reg_allows_load_imm regs r imm p g b e a ea)
    then (if decide (ea ≠ pc_a)
          then ∃ w p' (P:D),
              ⌜PermFlowsTo p p'⌝
              ∗ ⌜persistent_cond P⌝
              ∗ ⌜mem = <[ea:=w]> (<[pc_a:=pc_w]> ∅)⌝
              ∗ (region_open_resources W C ea [pc_a] p' (safeC P) w has_later)
              ∗ if_later_P has_later (rcond P C p' interp)
          else ⌜mem = <[pc_a:=pc_w]> ∅⌝ ∗ world_interp_open W C [pc_a] ∗ ⌜PermFlowsTo p pc_p⌝ )
    else ⌜mem = <[pc_a:=pc_w]> ∅⌝ ∗ world_interp_open W C [pc_a] end)%I.

  Lemma create_load_res (imm : Z)
    (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
    (p_pc p_pc' : Perm) (g_pc : Locality) (b_pc e_pc a_pc : Addr)
    (src : RegName)
    (t : bool) (p : Perm) (g : Locality) (b e a : Addr) (P:D):
    read_reg_inr (<[PC:=WCap true p_pc g_pc b_pc e_pc a_pc]> regs) src t p g b e a
    → PermFlowsTo p_pc p_pc'
    → (∀ (r : RegName) (v : Word), ⌜r ≠ PC⌝ → ⌜regs !! r = Some v⌝ → interp W C v)
    -∗ interp W C (WCap true p_pc g_pc b_pc e_pc a_pc)
    -∗ rel C a_pc p_pc' (safeC P)
    -∗ world_interp_open W C [a_pc]
    -∗ allow_load_res imm W C src (<[PC:= WCap true p_pc g_pc b_pc e_pc a_pc]> regs) a_pc p_pc'.
  Proof.
    iIntros (HVsrc Hfl) "#Hreg #Hinterp_pc #Hinva Hworld_interp".
    iFrame "%".
    rewrite /reg_allows_load_imm.
    destruct (a + imm)%a as [ea|] eqn:Hadd; last by iFrame.
    case_decide as Hallows; last by iFrame.
    case_decide as Haeq ; cycle 1.
    { simplify_eq; iFrame.
      iApply (interp_hpf_eq imm W C (safeC P) regs src p g b e a a_pc
        p_pc g_pc b_pc e_pc p_pc' with "Hreg Hinva"); eauto.
      rewrite /reg_allows_load_imm Hadd. exact Hallows.
    }
    destruct Hallows as (Hrinr & Hoff & Hra & Hwb).
    apply andb_prop in Hwb as [Hle Hge].

    assert (src ≠ cnull); simplify_map_eq.
    { intros -> ; simplify_map_eq. destruct (regs !! cnull) eqn:Hr; simplify_map_eq. }
    iAssert (interp W C (WCap true p g b e a)) as "#Hvsrc".
    { destruct (decide (src = PC)) as [->|Hne].
      - simplify_map_eq. done.
      - simplify_map_eq. iApply ("Hreg" $! src _ Hne Hrinr).
    }
    iDestruct (read_allowed_inv _ _ ea with "Hvsrc")
      as (p0 P0 Hflp0 Hcond_pers0) "(Hrel0 & Hzcond0 & Hrcond0 & Hwcond0)"; auto
    ; first (split; [by apply Z.leb_le | by apply Z.ltb_lt]).

    (* iDestruct (region_open_prepare with "Hr") as "Hr". *)
    iDestruct (readAllowed_valid_cap_implies _ _ _ _ _ _ _ ea with "Hvsrc") as %HH; eauto.
    { rewrite /withinBounds Hle Hge. auto. }
    destruct HH as (ρ0 & Hstd & Hnotrevoked).
    (* We can finally frame off Hsts here,
            since it is no longer needed after opening the region*)
    iDestruct (open_world_interp_next _ _ _ ea p0 _ ρ0 with "Hrel0 Hworld_interp")
      as "(Hworld & Hstate' & [%w0 (?&?&?&?)] )"; eauto.
    { apply not_elem_of_cons; split; auto. apply not_elem_of_nil. }
    { destruct ρ0; simplify_eq; [by left | by right]. }
    iExists w0,p0,P0.
    iFrame "∗#%".
    iNext.
    rewrite mono_invariant_monotonicity_guarantees_region; eauto.
  Qed.

  Lemma load_res_implies_mem_map (imm : Z)
    (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
      (p : Perm) (a : Addr) (w : Word) (src : RegName):
    allow_load_res imm W C src regs a p
    -∗ a ↦ₐ w
    -∗ ∃ mem0 : Mem,
        allow_load_mem imm W C src regs a p w mem0 true
        ∗ ▷ ([∗ map] a0↦w ∈ mem0, a0 ↦ₐ w).
  Proof.
    iIntros "HLoadRes Ha".
    iDestruct "HLoadRes" as (t1 p1 g1 b1 e1 a1) "[% HLoadRes]".
    rewrite /reg_allows_load_imm.
    destruct (a1 + imm)%a as [ea|] eqn:Hadd.
    2: {
      iExists (<[a:=w]> ∅). iSplitL "HLoadRes".
      - iExists t1,p1,g1,b1,e1,a1. iFrame "%". rewrite /reg_allows_load_imm Hadd. by iFrame.
      - iNext. by iApply memMap_resource_1.
    }
    case_decide as Hallows; cycle 1.
    {
      iExists _.
      iSplitL "HLoadRes".
      + iExists t1,p1,g1,b1,e1,a1. iSplitR; auto. rewrite /reg_allows_load_imm Hadd.
        case_decide; first by exfalso. auto.
      + iNext. by iApply memMap_resource_1.
    }
    case_decide as Haeq.
    - pose(Hallows' := Hallows).
      destruct Hallows' as (Hrinr & Hoff & Hra & Hwb).
      iDestruct "HLoadRes" as (w0 p' P Hp'O Hpers) "[HLoadCh [HLoadRest #Hrcond] ]".
      iExists _.
      iSplitL "HLoadRest".
      + iExists t1,p1,g1,b1,e1,a1. iFrame "%". rewrite /reg_allows_load_imm Hadd.
        case_decide; last by exfalso.
        case_decide; last by exfalso.
        iExists w0,p',P.
        repeat (iSplit; auto).
      + iNext.
        iApply memMap_resource_2ne; auto; iFrame.
    - iExists _.
      iSplitL "HLoadRes"; last (iNext; by iApply memMap_resource_1).
      iExists t1,p1,g1,b1,e1,a1. iFrame "%". rewrite /reg_allows_load_imm Hadd.
      case_decide; last by exfalso.
      case_decide; first by exfalso.
      by iFrame.
  Qed.

  Lemma mem_map_implies_pure_conds (imm : Z)
    (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
      (p : Perm) (a : Addr) (w : Word) (src : RegName)
      (mem0 : Mem):
    allow_load_mem imm W C src regs a p w mem0 true
    -∗ ⌜mem0 !! a = Some w⌝ ∗ ⌜allow_load_map_or_true_imm src imm regs mem0⌝.
  Proof.
    iIntros "HLoadMem".
    iDestruct "HLoadMem" as (t1 p1 g1 b1 e1 a1) "[% HLoadRes]".
    rewrite /reg_allows_load_imm.
    destruct (a1 + imm)%a as [ea|] eqn:Hadd.
    2: {
      iDestruct "HLoadRes" as "[-> _]".
      iSplitR; first by rewrite lookup_insert_eq.
      iExists t1,p1,g1,b1,e1,a1. iSplitR; auto. by rewrite /reg_allows_load_imm Hadd.
    }
    case_decide as Hallows; cycle 1.
    {
      iDestruct "HLoadRes" as "[-> HLoadRes ]".
      iSplitR; first by rewrite lookup_insert_eq.
      iExists t1,p1,g1,b1,e1,a1. iSplitR; auto. rewrite /reg_allows_load_imm Hadd.
      case_decide as Hdec1; last by done.
      done.
    }

    case_decide as Haeq.
    - pose(Hallows' := Hallows).
      destruct Hallows' as (Hrinr & Hoff & Hra & Hwb).
      (* case_decide as Haeq. *)
      iDestruct "HLoadRes" as (w0 p' P Hp'O Hpers) "[-> _]".
      iSplitR; first (rewrite lookup_insert_ne; auto; by rewrite lookup_insert_eq).
      iExists t1,p1,g1,b1,e1,a1. iSplitR; auto. rewrite /reg_allows_load_imm Hadd.
      case_decide; last by exfalso.
      iExists w0.
      by rewrite lookup_insert_eq.
    - subst a. iDestruct "HLoadRes" as "[-> HLoadRes]".
      iSplitR; first by rewrite lookup_insert_eq.
      iExists t1,p1,g1,b1,e1,a1. iSplitR; auto. rewrite /reg_allows_load_imm Hadd.
      case_decide as Hdec1; last by done.
      iExists w. by rewrite lookup_insert_eq.
  Qed.

  Lemma allow_load_mem_later (imm : Z)
    (W : WORLD) (C :CmptName) (regs : leibnizO Reg)
    (p : Perm) (g : Locality) (b e a : Addr)
    (w : Word) (src : RegName) (mem0 : Mem):
    allow_load_mem imm W C src regs a p w mem0 true
    -∗ ▷ allow_load_mem imm W C src regs a p w mem0 false.
  Proof.
    iIntros "HLoadMem".
    iDestruct "HLoadMem" as (t0 p0 g0 b0 e0 a0) "[% HLoadMem]".
    do 6 (iApply later_exist_2; iExists _). iApply later_sep_2; iSplitR; auto.
    rewrite /reg_allows_load_imm.
    destruct (a0 + imm)%a as [ea|] eqn:Hadd; last iFrame.
    case_decide; last iFrame.
    case_decide; last iFrame.
    iDestruct "HLoadMem" as (w0 p' P Hp'O Hpers) "(-> & HLoadMem & #Hrcond)".
    do 3 (iApply later_exist_2; iExists _).
    do 2 (iApply later_sep_2; iSplitR; auto).
  Qed.

  Definition rcond' (P : D) (C : CmptName) p g b e a regs p' : iProp Σ
    := (if decide (readAllowed_a_in_regs (<[PC:=WCap true p g b e a]> regs) a)
             then (rcond P C p' interp)
             else emp)%I.
  Instance rcond'_pers P C p g b e a regs p' : Persistent (rcond' P C p g b e a regs p' ).
  Proof. intros. rewrite /rcond'. case_decide;apply _. Qed.

  Lemma mem_map_recover_res (imm : Z)
    (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
    (pc_w : Word) (src : RegName)
    (p_pc p_pc' : Perm) (g_pc : Locality) (b_pc e_pc a_pc : Addr)
    (p : Perm) (g : Locality) (b e a ea : Addr)
    (mem0 : Mem) (loadv : Word) (P:D) :
    PermFlowsTo p_pc p_pc'
    -> reg_allows_load_imm (<[PC:=WCap true p_pc g_pc b_pc e_pc a_pc]> regs) src imm p g b e a ea
    -> mem0 !! ea = Some loadv
    -> interp W C (WCap true p_pc g_pc b_pc e_pc a_pc)
      -∗ (∀ r v, ⌜r ≠ PC⌝ → ⌜regs !! r = Some v⌝ → interp W C v)
         -∗ rcond' P C p_pc g_pc b_pc e_pc a_pc regs p_pc'
            -∗ P W C pc_w
               -∗ ([∗ map] a1↦w0 ∈ mem0, a1 ↦ₐ w0)
                  -∗ allow_load_mem imm W C src (<[PC:=WCap true p_pc g_pc b_pc e_pc a_pc]> regs) a_pc p_pc' pc_w mem0 false
                     -∗ world_interp_open W C [a_pc] ∗ a_pc ↦ₐ pc_w ∗ interp W C (load_word p loadv).
  Proof.
    intros Hflpc Hrar Ha.
    iIntros "##Hinterp_pc Hreg #Hrcond Hw Hmem HLoadMem".
    iDestruct "HLoadMem" as (t1 p1 g1 b1 e1 a1) "[%Hread HLoadRes]".
    destruct (load_inr_eq imm Hrar Hread) as (<- & <- & <- & <- & <-).
    pose proof Hrar as (_ & Hoff & _).
    rewrite /reg_allows_load_imm Hoff.
    rewrite /reg_allows_load_imm Hoff in Hrar.
    case_decide as Hallows; last by exfalso.
    destruct Hallows as (Hrinr & Hadd & Hwa & Hwb).
    assert (src ≠ cnull); simplify_map_eq.
    { intros -> ; simplify_map_eq. destruct (regs !! cnull) eqn:Hr; simplify_map_eq. }
    case_decide as Haeq; cycle 1.
    - iDestruct "HLoadRes" as "(-> & $ & %Hfl')".
      simplify_map_eq.
      rewrite -memMap_resource_1.
      iFrame.
      rewrite /rcond'.
      rewrite decide_True.
      2: { eexists src,_.
           split; first (simplify_map_eq; eauto).
           split; first done.
           cbn. congruence.
      }
      iApply interp_weakening_word_load; eauto.
      by iApply "Hrcond".
    - iDestruct "HLoadRes"
        as (w p' P' Hflp'' HpersP') "(-> & HLoadRes & #Hrcond')".
      rewrite lookup_insert_eq in Ha; inversion Ha; clear Ha; subst.
      rewrite memMap_resource_2ne; last auto.
      iDestruct "Hmem" as "[Ha Hapc]"; iFrame.
      rewrite /persistent_cond in HpersP'.
      iDestruct "HLoadRes" as (ρ1) "(Hstate' & %Hnotrevoked & Hworld_interp & (Hfuture & #HV) & Hrel')"
      ; cbn.

      assert (isO p' = false) as HpO'.
      { eapply readAllowed_flowsto, readAllowed_nonO in Hflp''; auto.
      }
      iDestruct (close_world_interp_next with "Hworld_interp Hstate' Hrel' [Ha Hfuture]") as "$"; eauto.
      { apply not_elem_of_cons; split; [auto|apply not_elem_of_nil]. }
      { destruct ρ1; simplify_eq; naive_solver. }
      { iFrame "∗#%".
        rewrite mono_invariant_monotonicity_guarantees_region; eauto.
      }
      iDestruct ("Hrcond'" with "HV") as "HV'".
      iApply interp_weakening_word_load; eauto.
  Qed.

  Lemma load_case (imm : Z) (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (dst src : RegName) (P:D) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs p p' g b e a w (Load dst src imm) ρ P cstk Ws Cs.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "#Halloc #IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe Hworld_interp Hown Htframe".
    iIntros "Hstate HPC Hmap".
    iInsert "Hmap" PC.

    iDestruct (WorldRes_acc with "WorldRes") as " [ (>Ha & Hinterp) WorldRes ]".

    iClear "Hwcond".
    iDestruct (if_dec_later with "Hrcond") as "Hrcond'"; iClear "Hrcond".

    assert (Persistent (▷ P W C w)) as HpersP.
    { apply later_persistent. specialize (Hpers (W,C,w)). auto. }
    iDestruct "Hinterp" as "#Hw".

    (* To read out PC's name later, and needed when calling wp_load *)
    assert(∀ x : RegName, is_Some (<[PC:=WCap true p g b e a]> regs !! x)) as Hsome'.
    {
      intros. destruct (decide (x = PC)); last by rewrite lookup_insert_ne.
      rewrite e0 lookup_insert_eq; unfold is_Some. by eexists.
    }

    (* Initializing the names for the values of Hsrc now,
       to instantiate the existentials in step 1 *)
    assert (∃ t0 p0 g0 b0 e0 a0, read_reg_inr (<[PC:=WCap true p g b e a]> regs) src t0 p0 g0 b0 e0 a0)
      as (t0 & p0 & g0 & b0 & e0 & a0 & HVsrc).
    {
      specialize Hsome' with src as Hsrc.
      destruct Hsrc as [wsrc Hsomesrc].
      unfold read_reg_inr. rewrite Hsomesrc.
      destruct wsrc as [|[ t0 p0 g0 b0 e0 a0|] | | ];
        try (exists true,p,g,b,e,a; done).
      by repeat eexists.
    }

    (* Step 1: open the region, if necessary, and store all the resources obtained from the region in allow_load_res imm *)
    iDestruct (create_load_res imm with "Hreg Hinv_interp Hinva Hworld_interp") as "HLoadRes"; eauto.
    (* Clear helper values; they exist in the existential now *)
    clear HVsrc t0 p0 g0 b0 e0 a0.

    (* Step2: derive the concrete map of memory we need, and any spatial predicates holding over it *)
    iDestruct (load_res_implies_mem_map imm W  with "HLoadRes Ha") as (mem) "[HLoadMem HMemRes]".

    (* Step 3:  derive the non-spatial conditions over the memory map*)
    iDestruct (mem_map_implies_pure_conds imm with "HLoadMem") as %(HReadPC & HLoadAP); auto.

    (* Step 4: move the later outside, so that we can remove it after applying wp_load *)
    iDestruct (allow_load_mem_later imm with "HLoadMem") as "HLoadMem"; auto.

    iAssert (⌜∀ p0 g0 b0 e0 a0 ea0,
      reg_allows_load_imm (<[PC:=WCap true p g b e a]> regs) src imm p0 g0 b0 e0 a0 ea0 →
      is_shadow_address ea0 = false⌝)%I as %Hnonshadow.
    { iIntros (p0 g0 b0 e0 a0 ea0 (Hsrc & Hadd & Hra & Hwb)).
      assert (src ≠ cnull) as Hsrc_null.
      { intros ->. simplify_map_eq.
        destruct (regs !! cnull) eqn:Hnull; rewrite Hnull in Hsrc; discriminate. }
      rewrite lookup_reg_not_cnull in Hsrc; last exact Hsrc_null.
      destruct (decide (src = PC)) as [->|Hsrc_pc].
      - rewrite lookup_insert_eq in Hsrc. inversion Hsrc; subst.
        iApply (interp_cap_not_shadow with "Hinv_interp"); eauto using readAllowed_nonO.
      - rewrite lookup_insert_ne in Hsrc; last done.
        iApply (interp_cap_not_shadow with "[Hreg]"); eauto using readAllowed_nonO.
        by iApply "Hreg".
    }
    iApply (wp_load_memory_imm with "[Hmap HMemRes]"); eauto.
    { by rewrite lookup_insert_eq. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. rewrite lookup_insert_is_Some'; eauto. }
    { iSplitR "Hmap"; auto. }
    iNext. iIntros (regs' retv). iDestruct 1 as (HSpec) "[Hmem Hmap]".

    destruct HSpec as [p0 g0 b0 e0 a0 ea0 loadv actualv Hreg_load Hmem_a Hactual Hincr|].
    { apply incrementPC_Some_inv in Hincr.
      destruct Hincr as (tpc&?&?&?&?&?&?&?&?&XX).
      iApply wp_pure_step_later; auto. iNext; iIntros "_".

      (* Step 5: return all the resources we had in order to close the second location in the region, in the cases where we need to *)
      iDestruct (mem_map_recover_res imm with "Hinv_interp Hreg Hrcond' Hw Hmem HLoadMem") as
        "[Hworld_interp [Ha #Hnormal ] ]"; eauto.
      iAssert (interp W C actualv) as "#HLVInterp".
      { destruct Hactual as [-> | ->]; first done. iApply interp_clear_tag. }

      (* Exceptional success case: we do not apply the induction hypothesis in case we have a faulty PC*)
      destruct tpc; cycle 1.
      { iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]".
        { subst. by rewrite lookup_insert_eq. }
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_notCorrectPC_tag with "HPC"); first done.
        iNext; iIntros "_".
        iApply wp_pure_step_later; auto. iNext; iIntros "_".
        iApply wp_value; auto.
      }
      destruct (executeAllowed x) eqn:Hp'.
      2 : {
        iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]".
        { subst. by rewrite lookup_insert_eq. }
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_notCorrectPC_perm with "[HPC]"); eauto. iIntros "!> _".
        iApply wp_pure_step_later; auto. iNext; iIntros "_". iApply wp_value.
        iIntros (a1); inversion a1.
      }

      iDestruct ("WorldRes" with "[$Ha $Hw]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      assert (is_Some (regs' !! csp)) as [? ?].
      { rewrite XX lookup_insert_ne//.
        destruct (decide (dst = csp));simplify_map_eq =>//. }
      iApply ("IH" $! _ _ _ _ _ regs' with "Halloc [%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]").
      { cbn. intros. subst regs'.
        rewrite lookup_insert_is_Some.
        destruct (decide (PC = x6)); [ auto | right; split; auto].
        rewrite lookup_insert_is_Some.
        destruct (decide (dst = x6)); [ auto | right; split; auto]. }
      (* Prove in the general case that the value relation holds for the register
         that was loaded to - unless it was the PC.*)
       { iIntros (ri wi Hri Hregs_ri).
        subst regs'.
        destruct (decide (ri = dst)).
        { simplify_map_eq.
          destruct (decide (dst = cnull)); [iApply interp_int|]; auto.
        }
        { simplify_map_eq; iApply "Hreg"; auto. }
       }
       { subst regs'. rewrite insert_insert_eq. iApply "Hmap". }
       {
        destruct (decide (PC = dst)); simplify_map_eq; cycle 1.
        + iApply (interp_next_PC with "Hinv_interp"); eauto.
        + iApply (interp_weakening with "IH HLVInterp"); eauto; try solve_addr; try done.
       }
    }
    { iApply wp_pure_step_later; auto.
      iNext; iIntros "_".
      iApply wp_value; auto. }
    Unshelve. all: auto.
  Qed.

End fundamental.
