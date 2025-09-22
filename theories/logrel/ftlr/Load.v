From stdpp Require Import base.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine Require Export logrel.
From cap_machine Require Import ftlr_base interp_weakening.
From cap_machine Require Import rules_Load.
From cap_machine.proofmode Require Import map_simpl register_tactics.
Import uPred.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {cstackg : CSTACKG Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
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
    ∗ open_region_many W C(a :: als)
    ∗ if_later_P has_later (monotonicity_guarantees_region C φ p v ρ ∗ φ (W,C, v))
    ∗ rel C a p φ)%I.

  Lemma load_inr_eq {regs r p0 g0 b0 e0 a0 p1 g1 b1 e1 a1}:
    reg_allows_load regs r p0 g0 b0 e0 a0 →
    read_reg_inr regs r p1 g1 b1 e1 a1 →
    p0 = p1 ∧ g0 = g1 ∧ b0 = b1 ∧ e0 = e1 ∧ a0 = a1.
  Proof.
    intros Hrar H3.
    pose (Hrar' := Hrar).
    destruct Hrar' as (Hinr0 & _). rewrite /read_reg_inr Hinr0 in H3. by inversion H3.
  Qed.

  (* Description of what the resources are supposed to look like
     after opening the region if we need to,
     but before closing the region up again*)
  Definition allow_load_res W C r (regs : Reg) pc_a pc_p :=
    (∃ p g b e a, ⌜read_reg_inr regs r p g b e a⌝ ∗
    if decide (reg_allows_load regs r p g b e a)
    then (if decide (a ≠ pc_a)
          then ∃ w p' (P:D),
              ⌜PermFlowsTo p p'⌝
              ∗ ⌜persistent_cond P⌝
              ∗ a ↦ₐ w
              ∗ (region_open_resources W C a [pc_a] p' (safeC P) w true)
              ∗ ▷ rcond P C p' interp
          else open_region W C pc_a ∗ ⌜PermFlowsTo p pc_p⌝)
    else open_region W C pc_a)%I.

   Lemma interp_hpf_eq (W : WORLD) (C : CmptName) P (regs : leibnizO Reg) (r1 : RegName)
    p g b e a pc_p pc_g pc_b pc_e pc_p' :
    reg_allows_load (<[PC:=WCap pc_p pc_g pc_b pc_e a]> regs) r1 p g b e a
    → PermFlowsTo pc_p pc_p'
    → (∀ (r1 : RegName) v, ⌜r1 ≠ PC⌝ → ⌜regs !! r1 = Some v⌝ → (interp W C v))
    -∗ rel C a pc_p' P
    -∗ ⌜PermFlowsTo p pc_p'⌝.
  Proof.
    destruct (decide (r1 = PC)).
    - subst r1. iIntros ([? ?] ?). simplify_map_eq; auto.
    - iIntros ((Hsomer1 & Hwa & Hwb) Hfl) "Hreg #Hinva".
      simplify_map_eq.
      iDestruct ("Hreg" $! r1 _ n Hsomer1) as "Hr1"; eauto.
      iDestruct (read_allowed_inv _ _ a with "Hr1")
        as (p'' P'' Hflp'' Hcond_pers'') "(Hrel'' & Hzcond'' & Hrcond'' & Hwcond'')"; auto.
      { apply andb_true_iff in Hwb as [Hle Hge].
        split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
      iDestruct (rel_agree _ _ _ _ p'' pc_p' with "[$Hinva $Hrel'']") as "[-> _]".
      done.
  Qed.

  Definition allow_load_mem W C r (regs : Reg) pc_a pc_p pc_w (mem : Mem) (has_later: bool):=
    (∃ p g b e a, ⌜read_reg_inr regs r p g b e a⌝ ∗
    if decide (reg_allows_load regs r p g b e a)
    then (if decide (a ≠ pc_a)
          then ∃ w p' (P:D),
              ⌜PermFlowsTo p p'⌝
              ∗ ⌜persistent_cond P⌝
              ∗ ⌜mem = <[a:=w]> (<[pc_a:=pc_w]> ∅)⌝
              ∗ (region_open_resources W C a [pc_a] p' (safeC P) w has_later)
              ∗ if_later_P has_later (rcond P C p' interp)
          else ⌜mem = <[pc_a:=pc_w]> ∅⌝ ∗ open_region W C pc_a ∗ ⌜PermFlowsTo p pc_p⌝ )
    else ⌜mem = <[pc_a:=pc_w]> ∅⌝ ∗ open_region W C pc_a)%I.

  Lemma create_load_res
    (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
    (p_pc p_pc' : Perm) (g_pc : Locality) (b_pc e_pc a_pc : Addr)
    (src : RegName)
    (p : Perm) (g : Locality) (b e a : Addr) (P:D):
    read_reg_inr (<[PC:=WCap p_pc g_pc b_pc e_pc a_pc]> regs) src p g b e a
    → PermFlowsTo p_pc p_pc'
    → (∀ (r : RegName) (v : Word), ⌜r ≠ PC⌝ → ⌜regs !! r = Some v⌝ → interp W C v)
    -∗ rel C a_pc p_pc' (safeC P)
    -∗ open_region W C a_pc
    -∗ sts_full_world W C
    -∗ (allow_load_res W C src (<[PC:= WCap p_pc g_pc b_pc e_pc a_pc]> regs) a_pc p_pc'
        ∗ sts_full_world W C).
  Proof.
    iIntros (HVsrc Hfl) "#Hreg #Hinva Hr Hsts".
    do 5 (iApply sep_exist_r; iExists _). iFrame "%".
    case_decide as Hallows; last by iFrame.
    case_decide as Haeq ; cycle 1.
    { simplify_eq; iFrame.
      iApply interp_hpf_eq; eauto.
    }
    destruct Hallows as (Hrinr & Hra & Hwb).
    apply andb_prop in Hwb as [Hle Hge].

    (* Unlike in the old proof, we now go the other way around,
            and prove that the source register could not have been the PC,
            since both addresses differ. This saves us some cases.*)
    assert (src ≠ PC) as n.
    { refine (addr_ne_reg_ne Hrinr _ Haeq). by rewrite lookup_insert. }
    simplify_map_eq.

    iDestruct ("Hreg" $! src _ n Hrinr) as "Hvsrc"; eauto.
    iDestruct (read_allowed_inv _ _ a with "Hvsrc")
      as (p0 P0 Hflp0 Hcond_pers0) "(Hrel0 & Hzcond0 & Hrcond0 & Hwcond0)"; auto
    ; first (split; [by apply Z.leb_le | by apply Z.ltb_lt]).

    iDestruct (region_open_prepare with "Hr") as "Hr".
    iDestruct (readAllowed_valid_cap_implies _ _ _ _ _ _ _ a with "Hvsrc") as %HH; eauto.
    { rewrite /withinBounds Hle Hge. auto. }
    destruct HH as (ρ0 & Hstd & Hnotrevoked).
    (* We can finally frame off Hsts here,
            since it is no longer needed after opening the region*)
    iDestruct (region_open_next _ _ _ _ a p0 ρ0 with "[$Hrel0 $Hr $Hsts]")
      as (w0) "($ & Hstate' & Hr & Ha0 & Hfuture & Hval & _)"; eauto.
    { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
    iExists w0,p0,P0.
    iFrame "∗#%".
  Qed.

  Lemma load_res_implies_mem_map
    (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
      (p : Perm) (a : Addr) (w : Word) (src : RegName):
    allow_load_res W C src regs a p
    -∗ a ↦ₐ w
    -∗ ∃ mem0 : Mem,
        allow_load_mem W C src regs a p w mem0 true
        ∗ ▷ ([∗ map] a0↦w ∈ mem0, a0 ↦ₐ w).
  Proof.
    iIntros "HLoadRes Ha".
    iDestruct "HLoadRes" as (p1 g1 b1 e1 a1) "[% HLoadRes]".
    case_decide as Hallows; cycle 1.
    {
      iExists _.
      iSplitL "HLoadRes".
      + iExists p1,g1,b1,e1,a1. iSplitR; auto.
        case_decide; first by exfalso. auto.
      + iNext. by iApply memMap_resource_1.
    }
    case_decide as Haeq.
    - pose(Hallows' := Hallows).
      destruct Hallows' as (Hrinr & Hra & Hwb).
      iDestruct "HLoadRes" as (w0 p' P Hp'O Hpers) "[HLoadCh [HLoadRest #Hrcond] ]".
      iExists _.
      iSplitL "HLoadRest".
      + iExists p1,g1,b1,e1,a1. iFrame "%".
        case_decide; last by exfalso.
        case_decide; last by exfalso.
        iExists w0,p',P.
        repeat (iSplit; auto).
      + iNext.
        iApply memMap_resource_2ne; auto; iFrame.
    - iExists _.
      iSplitL "HLoadRes"; last (iNext; by iApply memMap_resource_1).
      iExists p1,g1,b1,e1,a1. iFrame "%".
      case_decide; last by exfalso.
      case_decide; first by exfalso.
      by iFrame.
  Qed.

  Lemma mem_map_implies_pure_conds
    (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
      (p : Perm) (a : Addr) (w : Word) (src : RegName)
      (mem0 : Mem):
    allow_load_mem W C src regs a p w mem0 true
    -∗ ⌜mem0 !! a = Some w⌝ ∗ ⌜allow_load_map_or_true src regs mem0⌝.
  Proof.
    iIntros "HLoadMem".
    iDestruct "HLoadMem" as (p1 g1 b1 e1 a1) "[% HLoadRes]".
    case_decide as Hallows; cycle 1.
    {
      iDestruct "HLoadRes" as "[-> HLoadRes ]".
      iSplitR; first by rewrite lookup_insert.
      iExists p1,g1,b1,e1,a1. iSplitR; auto.
      case_decide as Hdec1; last by done.
      done.
    }

    case_decide as Haeq.
    - pose(Hallows' := Hallows).
      destruct Hallows' as (Hrinr & Hra & Hwb).
      (* case_decide as Haeq. *)
      iDestruct "HLoadRes" as (w0 p' P Hp'O Hpers) "[-> _]".
      iSplitR; first (rewrite lookup_insert_ne; auto; by rewrite lookup_insert).
      iExists p1,g1,b1,e1,a1. iSplitR; auto.
      case_decide; last by exfalso.
      iExists w0.
      by rewrite lookup_insert.
    - subst a. iDestruct "HLoadRes" as "[-> HLoadRes]".
      iSplitR; first by rewrite lookup_insert.
      iExists p1,g1,b1,e1,a1. repeat iSplitR; auto.
      case_decide as Hdec1; last by done.
      iExists w. by rewrite lookup_insert.
  Qed.

  Lemma allow_load_mem_later
    (W : WORLD) (C :CmptName) (regs : leibnizO Reg)
    (p : Perm) (g : Locality) (b e a : Addr)
    (w : Word) (src : RegName) (mem0 : Mem):
    allow_load_mem W C src regs a p w mem0 true
    -∗ ▷ allow_load_mem W C src regs a p w mem0 false.
  Proof.
    iIntros "HLoadMem".
    iDestruct "HLoadMem" as (p0 g0 b0 e0 a0) "[% HLoadMem]".
    do 5 (iApply later_exist_2; iExists _). iApply later_sep_2; iSplitR; auto.
    case_decide; last iFrame.
    case_decide; last iFrame.
    iDestruct "HLoadMem" as (w0 p' P Hp'O Hpers) "(-> & HLoadMem & #Hrcond)".
    do 3 (iApply later_exist_2; iExists _).
    do 2 (iApply later_sep_2; iSplitR; auto).
  Qed.

  Definition rcond' (P : D) (C : CmptName) p g b e a regs p' : iProp Σ
    := (if decide (readAllowed_a_in_regs (<[PC:=WCap p g b e a]> regs) a)
             then (rcond P C p' interp)
             else emp)%I.
  Instance rcond'_pers P C p g b e a regs p' : Persistent (rcond' P C p g b e a regs p' ).
  Proof. intros. rewrite /rcond'. case_decide;apply _. Qed.

  Lemma mem_map_recover_res
    (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
    (pc_w : Word) (src : RegName)
    (p_pc p_pc' : Perm) (g_pc : Locality) (b_pc e_pc a_pc : Addr)
    (p : Perm) (g : Locality) (b e a : Addr)
    (mem0 : Mem) (loadv : Word) (P:D) :
    PermFlowsTo p_pc p_pc'
    -> reg_allows_load (<[PC:=WCap p_pc g_pc b_pc e_pc a_pc]> regs) src p g b e a
    -> mem0 !! a = Some loadv
    -> interp W C (WCap p_pc g_pc b_pc e_pc a_pc)
      -∗ (∀ r v, ⌜r ≠ PC⌝ → ⌜regs !! r = Some v⌝ → interp W C v)
         -∗ rcond' P C p_pc g_pc b_pc e_pc a_pc regs p_pc'
            -∗ P W C pc_w
               -∗ ([∗ map] a1↦w0 ∈ mem0, a1 ↦ₐ w0)
                  -∗ allow_load_mem W C src (<[PC:=WCap p_pc g_pc b_pc e_pc a_pc]> regs) a_pc p_pc' pc_w mem0 false
                     -∗ open_region W C a_pc ∗ a_pc ↦ₐ pc_w ∗ interp W C (load_word p loadv).
  Proof.
    intros Hflpc Hrar Ha.
    iIntros "##Hinterp_pc Hreg #Hrcond Hw Hmem HLoadMem".
    iDestruct "HLoadMem" as (p1 g1 b1 e1 a1) "[%Hread HLoadRes]".
    destruct (load_inr_eq Hrar Hread) as (<- & <- & <- & <- & <-).
    case_decide as Hallows; last by exfalso.
    destruct Hallows as (Hrinr & Hwa & Hwb).
    case_decide as Haeq; cycle 1.
    - iDestruct "HLoadRes" as "(-> & $ & %Hfl')".
      simplify_map_eq.
      rewrite -memMap_resource_1.
      iFrame.
      rewrite /rcond'.
      rewrite decide_True.
      2: { eexists src,_.
           inversion Hrar.
           split;eauto.
           split;auto.
           split;auto.
           destruct H0.
           apply withinBounds_le_addr in H1; auto.
      }
      iApply interp_weakening_word_load; eauto.
      by iApply "Hrcond".
    - iDestruct "HLoadRes"
        as (w p' P' Hflp'' HpersP') "(-> & HLoadRes & #Hrcond')".
      rewrite lookup_insert in Ha; inversion Ha; clear Ha; subst.
      rewrite memMap_resource_2ne; last auto.
      iDestruct "Hmem" as "[Ha Hapc]"; iFrame.
      rewrite /persistent_cond in HpersP'.
      iDestruct "HLoadRes" as (ρ1) "(Hstate' & %Hnotrevoked & Hr & (Hfuture & #HV) & Hrel')"
      ; cbn.

      assert (isO p' = false) as HpO'.
      { eapply readAllowed_flowsto, readAllowed_nonO in Hflp''; auto.
      }
      iDestruct (region_close_next with "[$Hr $Ha $Hrel' $Hstate' $Hfuture]")
        as "Hr"; eauto.
      { apply not_elem_of_cons; split; [auto|apply not_elem_of_nil]. }
      iFrame.
      iDestruct (region_open_prepare with "Hr") as "$".
      iDestruct ("Hrcond'" with "HV") as "HV'".
      iApply interp_weakening_word_load; eauto.
  Qed.

  Lemma load_case (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (dst src : RegName) (P:D) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) (wstk : Word)
    (Nswitcher : namespace) :
    ftlr_instr W C regs p p' g b e a w (Load dst src) ρ P cstk Ws Cs wstk Nswitcher.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp HO Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono #HmonoV Hw Hcont %Hframe Hsts Hown Htframe".
    iIntros "Hr Hstate Ha HPC Hmap %Hcsp #Hswitcher".
    iInsert "Hmap" PC.
    iClear "Hwcond".
    iDestruct (if_dec_later with "Hrcond") as "Hrcond'"; iClear "Hrcond".

    assert (Persistent (▷ P W C w)) as HpersP.
    { apply later_persistent. specialize (Hpers (W,C,w)). auto. }
    iDestruct "Hw" as "#Hw".

    (* To read out PC's name later, and needed when calling wp_load *)
    assert(∀ x : RegName, is_Some (<[PC:=WCap p g b e a]> regs !! x)) as Hsome'.
    {
      intros. destruct (decide (x = PC)); last by rewrite lookup_insert_ne.
      rewrite e0 lookup_insert; unfold is_Some. by eexists.
    }

    (* Initializing the names for the values of Hsrc now,
       to instantiate the existentials in step 1 *)
    assert (∃ p0 g0 b0 e0 a0, read_reg_inr (<[PC:=WCap p g b e a]> regs) src p0 g0 b0 e0 a0)
      as [p0 [g0 [b0 [e0 [a0 HVsrc] ] ] ] ].
    {
      specialize Hsome' with src as Hsrc.
      destruct Hsrc as [wsrc Hsomesrc].
      unfold read_reg_inr. rewrite Hsomesrc.
      destruct wsrc as [|[ p0 g0 b0 e0 a0|] | | ]; try done.
      by repeat eexists.
    }

    (* Step 1: open the region, if necessary, and store all the resources obtained from the region in allow_load_res *)
    iDestruct (create_load_res with "Hreg Hinva Hr Hsts") as "[HLoadRes Hsts]"; eauto.
    (* Clear helper values; they exist in the existential now *)
    clear HVsrc p0 g0 b0 e0 a0.

    (* Step2: derive the concrete map of memory we need, and any spatial predicates holding over it *)
    iDestruct (load_res_implies_mem_map W  with "HLoadRes Ha") as (mem) "[HLoadMem HMemRes]".

    (* Step 3:  derive the non-spatial conditions over the memory map*)
    iDestruct (mem_map_implies_pure_conds with "HLoadMem") as %(HReadPC & HLoadAP); auto.

    (* Step 4: move the later outside, so that we can remove it after applying wp_load *)
    iDestruct (allow_load_mem_later with "HLoadMem") as "HLoadMem"; auto.

    iApply (wp_load with "[Hmap HMemRes]"); eauto.
    { by rewrite lookup_insert. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. rewrite lookup_insert_is_Some'; eauto. }
    { iSplitR "Hmap"; auto. }
    iNext. iIntros (regs' retv). iDestruct 1 as (HSpec) "[Hmem Hmap]".

    destruct HSpec as [ * Hreg_load Hmem_a Hincr|].
    { apply incrementPC_Some_inv in Hincr.
      destruct Hincr as (?&?&?&?&?&?&?&?&XX).
      iApply wp_pure_step_later; auto. iNext; iIntros "_".

      (* Step 5: return all the resources we had in order to close the second location in the region, in the cases where we need to *)
      iDestruct (mem_map_recover_res with "Hinv_interp Hreg Hrcond' Hw Hmem HLoadMem") as
        "[Hr [Ha #HLVInterp ] ]"; eauto.

      (* Exceptional success case: we do not apply the induction hypothesis in case we have a faulty PC*)
      destruct (executeAllowed x) eqn:Hp'.
      2 : {
        iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]".
        { subst. by rewrite lookup_insert. }
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_notCorrectPC_perm with "[HPC]"); eauto. iIntros "!> _".
        iApply wp_pure_step_later; auto. iNext; iIntros "_". iApply wp_value.
        iIntros (a1); inversion a1.
      }

      iDestruct (region_close with "[$Hstate $Ha $Hr $HmonoV]") as "Hr"; eauto.
      { destruct ρ;auto;contradiction. }
      assert (is_Some (regs' !! csp)) as [? ?].
      { rewrite XX lookup_insert_ne//.
        destruct (decide (dst = csp));simplify_map_eq =>//. }
      iApply ("IH" $! _ _ _ _ _ regs' with "[%] [] [Hmap] [//] [$Hr] [$Hsts] [$Hcont] [//] [$Hown] [$Htframe]").
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
        { by simplify_map_eq. }
        { simplify_map_eq; iApply "Hreg"; auto. }
       }
       { subst regs'. rewrite insert_insert. iApply "Hmap". }
       {
        destruct (decide (PC = dst)); simplify_map_eq; cycle 1.
        + iApply (interp_next_PC with "Hinv_interp"); eauto.
        + rewrite H.
          iApply (interp_weakening with "IH HLVInterp"); eauto; try solve_addr; try done.
       }
    }
    { iApply wp_pure_step_later; auto.
      iNext; iIntros "_".
      iApply wp_value; auto. }
    Unshelve. all: auto.
  Qed.

End fundamental.
