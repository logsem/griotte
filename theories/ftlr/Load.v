From stdpp Require Import base.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine.rules Require Import rules_Load.
From cap_machine.proofmode Require Import map_simpl register_tactics.
Import uPred.

Section fundamental.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ}
      {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
      {sealsg: sealStoreG Σ}
      {nainv: logrel_na_invs Σ}
      {MP: MachineParameters}
  .

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  (* The necessary resources to close the region again,
     except for the points to predicate, which we will store separately
     The boolean bl can be used to keep track of whether or not we have applied a wp lemma *)
  Definition region_open_resources W l ls p φ v (has_later : bool): iProp Σ :=
    (∃ ρ,
     sts_state_std l ρ
    ∗ ⌜ρ ≠ Revoked ∧ (∀ g, ρ ≠ Frozen g)⌝
    ∗ open_region_many (l :: ls) W
    ∗ if_later_P has_later (monotonicity_guarantees_region ρ v p φ
                  ∗ monotonicity_guarantees_regionFull ρ p φ
                  ∗ φ (W, v))
    ∗ rel l p φ)%I.

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
  Definition allow_load_res W r (regs : Reg) pc_a:=
    (∃ p g b e a, ⌜read_reg_inr regs r p g b e a⌝ ∗
    if decide (reg_allows_load regs r p g b e a ∧ a ≠ pc_a )
    then ∃ w p' (P:D),
        ⌜p' ≠ O⌝
        ∗ ⌜(∀ Wv, Persistent (P Wv.1 Wv.2))⌝
        ∗ a ↦ₐ w
        ∗ (region_open_resources W a [pc_a] p' (λ Wv, P Wv.1 Wv.2) w true)
        ∗ ▷ rcond P interp
    else open_region pc_a W)%I.

  Definition allow_load_mem W r (regs : Reg) pc_a pc_w (mem : Mem) (has_later: bool):=
    (∃ p g b e a, ⌜read_reg_inr regs r p g b e a⌝ ∗
    if decide (reg_allows_load regs r p g b e a ∧ a ≠ pc_a)
    then ∃ w p' (P:D),
        ⌜p' ≠ O⌝
        ∗ ⌜(∀ Wv, Persistent (P Wv.1 Wv.2))⌝
        ∗ ⌜mem = <[a:=w]> (<[pc_a:=pc_w]> ∅)⌝
        ∗ (region_open_resources W a [pc_a] p' (λ Wv, P Wv.1 Wv.2) w has_later)
        ∗ if_later_P has_later (rcond P interp)
    else  ⌜mem = <[pc_a:=pc_w]> ∅⌝ ∗ open_region pc_a W)%I.

  Lemma create_load_res:
    ∀ (W : WORLD) (regs : leibnizO Reg)
      (p : Perm) (g : Locality) (b e a : Addr)
      (src : RegName)
      (p0 : Perm) (g0 : Locality) (b0 e0 a0 : Addr),
      read_reg_inr (<[PC:=WCap p g b e a]> regs) src p0 g0 b0 e0 a0
      → (∀ (r : RegName) (v : Word), ⌜r ≠ PC⌝ → ⌜regs !! r = Some v⌝ → ((fixpoint interp1) W) v)
          -∗ open_region a W
          -∗ sts_full_world W
          -∗ allow_load_res W src (<[PC:= WCap p g b e a]> regs) a
          ∗ sts_full_world W.
  Proof.
    intros W regs p g b e a src p0 g0 b0 e0 a0 HVsrc.
    iIntros "#Hreg Hr Hsts".
    do 5 (iApply sep_exist_r; iExists _). iFrame "%".
    case_decide as Hdec; last iFrame.
    destruct Hdec as [Hallows Haeq].
    destruct Hallows as [Hrinr [Hra Hwb] ].
    apply andb_prop in Hwb as [Hle Hge].

    (* Unlike in the old proof, we now go the other way around,
            and prove that the source register could not have been the PC,
            since both addresses differ. This saves us some cases.*)
    assert (src ≠ PC) as n.
    { refine (addr_ne_reg_ne Hrinr _ Haeq). by rewrite lookup_insert. }
    simplify_map_eq.

    iDestruct ("Hreg" $! src _ n Hrinr) as "Hvsrc"; eauto.
    iDestruct (read_allowed_inv _ a0 with "Hvsrc")
      as (p' P Hflp' Hcond_pers) "(Hrel & Hzcond & Hrcond & Hwcond)"; auto
    ; first (split; [by apply Z.leb_le | by apply Z.ltb_lt]).

    iDestruct (region_open_prepare with "Hr") as "Hr".
    iDestruct (readAllowed_valid_cap_implies with "Hvsrc") as %HH; eauto.
    { rewrite /withinBounds Hle Hge. auto. }
    destruct HH as [ρ' [Hstd [Hnotrevoked' Hnotfrozen' ] ] ].
    (* We can finally frame off Hsts here,
            since it is no longer needed after opening the region*)
    iDestruct (region_open_next _ _ _ a0 p' ρ' with "[$Hrel $Hr $Hsts]")
      as (w0) "($ & Hstate' & Hr & Ha0 & Hfuture & HfutureFull & Hval)"; eauto.
    { intros [m' Hcontr]. specialize (Hnotfrozen' m'); contradiction. }
    { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
    iExists w0,p',P.
    iFrame "∗#".
    iSplitR;[iPureIntro ; destruct_perm p0; destruct_perm p'; done|].
    rewrite /persistent_cond in Hcond_pers.
    iSplitR; iPureIntro;done.
  Qed.

  Lemma load_res_implies_mem_map:
    ∀ (W : WORLD) (regs : leibnizO Reg)
      (a : Addr) (w : Word) (src : RegName),
    allow_load_res W src regs a
    -∗ a ↦ₐ w
    -∗ ∃ mem0 : Mem,
        allow_load_mem W src regs a w mem0 true
        ∗ ▷ ([∗ map] a0↦w ∈ mem0, a0 ↦ₐ w).
  Proof.
    intros W regs a w src.
    iIntros "HLoadRes Ha".
    iDestruct "HLoadRes" as (p1 g1 b1 e1 a1) "[% HLoadRes]".

    case_decide as Hdec. 1: destruct Hdec as [ Hallows Haeq ].
    -  pose(Hallows' := Hallows). destruct Hallows' as [Hrinr [Hra Hwb] ].
       iDestruct "HLoadRes" as (w0 p' P Hp'O Hpers) "[HLoadCh [HLoadRest #Hrcond] ]".
       iExists _.
       iSplitL "HLoadRest".
       + iExists p1,g1,b1,e1,a1. iSplitR; first auto.
         case_decide as Hdec1.
         2: apply not_and_r in Hdec1 as [|]; by exfalso.
         iExists w0,p',P.
         repeat (iSplit; auto).
       + iNext.
         iApply memMap_resource_2ne; auto; iFrame.
    - iExists _.
      iSplitL "HLoadRes".
      + iExists p1,g1,b1,e1,a1. iSplitR; auto.
        case_decide; first by exfalso. auto.
      + iNext. by iApply memMap_resource_1.
  Qed.

  Lemma mem_map_implies_pure_conds:
    ∀ (W : WORLD) (regs : leibnizO Reg)
      (a : Addr) (w : Word) (src : RegName)
      (mem0 : Mem),
    allow_load_mem W src regs a w mem0 true
    -∗ ⌜mem0 !! a = Some w⌝ ∗ ⌜allow_load_map_or_true src regs mem0⌝.
  Proof.
    iIntros (W regs a w src mem0) "HLoadMem".
    iDestruct "HLoadMem" as (p1 g1 b1 e1 a1) "[% HLoadRes]".
    case_decide as Hdec. 1: destruct Hdec as [ Hallows Haeq ].
    -  pose(Hallows' := Hallows). destruct Hallows' as [Hrinr [Hra Hwb] ].
       (* case_decide as Haeq. *)
       iDestruct "HLoadRes" as (w0 p' P Hp'O Hpers) "[-> _]".
       iSplitR. rewrite lookup_insert_ne; auto. by rewrite lookup_insert.
       iExists p1,g1,b1,e1,a1. iSplitR; auto.
       case_decide; last by exfalso.
       iExists w0.
       by rewrite lookup_insert.
    - iDestruct "HLoadRes" as "[-> HLoadRes ]".
      iSplitR. by rewrite lookup_insert.
      iExists p1,g1,b1,e1,a1. iSplitR; auto.
      case_decide as Hdec1; last by done.
      apply not_and_r in Hdec as [| <-%dec_stable]; first by exfalso.
      iExists w. by rewrite lookup_insert.
  Qed.

  Lemma allow_load_mem_later:
    ∀ (W : WORLD) (regs : leibnizO Reg)
      (p : Perm) (g : Locality) (b e a : Addr)
      (w : Word) (src : RegName) (mem0 : Mem),
    allow_load_mem W src regs a w mem0 true
    -∗ ▷ allow_load_mem W src regs a w mem0 false.
  Proof.
    iIntros (W regs p g b e a w src mem0) "HLoadMem".
    iDestruct "HLoadMem" as (p0 g0 b0 e0 a0) "[% HLoadMem]".
    do 5 (iApply later_exist_2; iExists _). iApply later_sep_2; iSplitR; auto.
    case_decide; last iFrame.
    iDestruct "HLoadMem" as (w0 p' P Hp'O Hpers) "(-> & HLoadMem & #Hrcond)".
    do 3 (iApply later_exist_2; iExists _).
    do 2 (iApply later_sep_2; iSplitR; auto).
  Qed.

  Lemma mem_map_recover_res:
    ∀ (W : WORLD) (regs : leibnizO Reg)
      (a : Addr) (w : Word) (src : RegName)
      (p0 : Perm) (g0 : Locality) (b0 e0 a0 : Addr)
      (mem0 : Mem) (loadv : Word),
    reg_allows_load regs src p0 g0 b0 e0 a0
    → mem0 !! a0 = Some loadv
    → allow_load_mem W src regs a w mem0 false
    -∗ ((fixpoint interp1) W) w
    -∗ ([∗ map] a0↦w ∈ mem0, a0 ↦ₐ w)
    -∗ open_region a W ∗ a ↦ₐ w ∗ ((fixpoint interp1) W) loadv.
  Proof.
    intros W regs a w src p0 g0 b0 e0 a0 mem0 loadv Hrar Ha0.
    iIntros "HLoadMem #Hw Hmem".
    iDestruct "HLoadMem" as (p1 g1 b1 e1 a1) "[%Hread HLoadRes]".
    destruct (load_inr_eq Hrar Hread) as (<- & <- & <- & <- & <-).
    case_decide as Hdec. destruct Hdec as [Hallows Heq].
    -  destruct Hallows as [Hrinr [Hra Hwb] ].
       iDestruct "HLoadRes" as (w0 p' P Hp'O Hpers) "(-> & HLoadRes & #Hrcond)".
       iDestruct "HLoadRes" as (ρ1) "(Hstate' & #Hrev & Hr & (Hfuture & HfutureFull & #HV) & Hrel')".
       iDestruct "Hrev" as %[Hnotrevoked Hnotfrozen ].
       rewrite memMap_resource_2ne; last auto. iDestruct "Hmem" as  "[Ha1 $]".
       iDestruct (region_close_next with "[$Hr $Ha1 $Hrel' $Hstate' $Hfuture $HfutureFull]")
         as "Hr"; eauto.
       { intros [m' Hm']; specialize (Hnotfrozen m'); contradiction. }
       { apply not_elem_of_cons; split; [auto|apply not_elem_of_nil]. }
       iDestruct (region_open_prepare with "Hr") as "$".
       simplify_map_eq.
       iApply "Hrcond". simpl. iFrame "#".
    - apply not_and_r in Hdec as [| <-%dec_stable].
      * by exfalso.
      * iDestruct "HLoadRes" as "[-> $ ]".
        rewrite -memMap_resource_1.
        rewrite lookup_insert in Ha0. inversion Ha0. by iFrame.
  Qed.


   Lemma load_case (W : WORLD) (regs : leibnizO Reg)
     (p p' : Perm) (g : Locality) (b e a : Addr)
     (w : Word) (ρ : region_type) (dst src : RegName) (P:D) :
    ftlr_instr W regs p p' g b e a w (Load dst src) ρ P.
  Proof.
    intros Hp Hsome i Hbae Hfp HO Hpers Hpwl Hregion Hnotrevoked Hnotfrozen Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #HmonoV #Hmono Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    iInsert "Hmap" PC.

    assert (Persistent (▷ P W w)) as HpersP.
    { apply later_persistent. specialize (Hpers (W,w)). auto. }
    iDestruct "Hw" as "#Hw".

    (* To read out PC's name later, and needed when calling wp_load *)
    assert(∀ x : RegName, is_Some (<[PC:=WCap p g b e a]> regs !! x)) as Hsome'.
    {
      intros. destruct (decide (x = PC)).
      rewrite e0 lookup_insert; unfold is_Some. by eexists.
      by rewrite lookup_insert_ne.
    }

    (* Initializing the names for the values of Hsrc now,
       to instantiate the existentials in step 1 *)
    assert (∃ p0 g0 b0 e0 a0, read_reg_inr (<[PC:=WCap p g b e a]> regs) src p0 g0 b0 e0 a0)
      as [p0 [g0 [b0 [e0 [a0 HVsrc] ] ] ] ].
    {
      specialize Hsome' with src as Hsrc.
      destruct Hsrc as [wsrc Hsomesrc].
      unfold read_reg_inr. rewrite Hsomesrc.
      destruct wsrc as [|[ p0 g0 b0 e0 a0|] | ]; try done.
      by repeat eexists.
    }

    (* Step 1: open the region, if necessary, and store all the resources obtained from the region in allow_load_res *)
    iDestruct (create_load_res with "Hreg Hr Hsts") as "[HLoadRes Hsts]"; eauto.
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

    destruct HSpec as [* ? ? Hincr|].
    { apply incrementPC_Some_inv in Hincr.
      destruct Hincr as (?&?&?&?&?&?&?&?&XX).
      iApply wp_pure_step_later; auto. iNext; iIntros "_".

      (* Step 5: return all the resources we had in order to close the second location in the region, in the cases where we need to *)
      iDestruct (mem_map_recover_res with "HLoadMem [] Hmem") as "[Hr [Ha #HLVInterp ] ]"; eauto.
      { by iApply "Hrcond". }

      (* Exceptional success case: we do not apply the induction hypothesis in case we have a faulty PC*)
      destruct (decide (x = RX ∨ x = RWX ∨ x = RWLX)) as [Hp'|Hp'].
      2 : {
        assert (x ≠ RX ∧ x ≠ RWX ∧ x ≠ RWLX). split; last split; by auto.
        iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]".
        { subst. by rewrite lookup_insert. }
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_notCorrectPC_perm with "[HPC]"); eauto. iIntros "!> _".
        iApply wp_pure_step_later; auto. iNext; iIntros "_". iApply wp_value.
        iIntros (a1); inversion a1.
      }

      iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
      { destruct ρ;auto;[|specialize (Hnotfrozen g1)];contradiction. }
      iApply ("IH" $! _ regs' with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]").
      { cbn. intros. subst regs'.
        rewrite lookup_insert_is_Some.
        destruct (decide (PC = x5)); [ auto | right; split; auto].
        rewrite lookup_insert_is_Some.
        destruct (decide (dst = x5)); [ auto | right; split; auto]. }
      (* Prove in the general case that the value relation holds for the register
         that was loaded to - unless it was the PC.*)
       { iIntros (ri wi Hri Hregs_ri).
        subst regs'.
        destruct (decide (ri = dst)).
        { by simplify_map_eq. }
        { simplify_map_eq; iApply "Hreg"; auto. }
       }
       { subst regs'. rewrite insert_insert. iApply "Hmap". }
       { destruct (decide (PC = dst)); simplify_eq.
         - destruct Hp' as [HRX | [HRWX | HRWLX] ]; auto.
           subst; simplify_map_eq.
           iDestruct (writeLocalAllowed_implies_local _ RWLX with "[HLVInterp]") as "%"; auto.
           destruct x0; unfold isLocal in *.
           all: try done.
           iPureIntro; do 2 right; auto; simplify_map_eq.
         - simplify_map_eq; iPureIntro; naive_solver.
       }
       {
        destruct (decide (PC = dst)); simplify_map_eq; cycle 1.
        iApply (interp_next_PC with "IH Hinv_interp"); eauto.
        iApply (interp_weakening with "IH HLVInterp"); eauto; try solve_addr; try done.
        naive_solver.
       }
    }
    { iApply wp_pure_step_later; auto.
      iNext; iIntros "_".
      iApply wp_value; auto. iIntros; discriminate. }
    Unshelve. all: auto.
  Qed.

End fundamental.
