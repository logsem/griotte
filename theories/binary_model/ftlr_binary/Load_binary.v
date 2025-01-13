From stdpp Require Import base.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine.binary_model Require Export logrel_binary.
From cap_machine.binary_model Require Import ftlr_base_binary.
From cap_machine.rules Require Import rules_Load.
From cap_machine.binary_model.rules_binary Require Import rules_binary_Load.
From cap_machine Require Import stdpp_extra.
Import uPred.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          {nainv: logrel_na_invs Σ} {cfgg : cfgSG Σ}
          `{MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (prodO (leibnizO Word) (leibnizO Word)) -n> iPropO Σ).
  Notation R := (WORLD -n> (prodO (leibnizO Reg) (leibnizO Reg)) -n> iPropO Σ).
  Implicit Types v : (prodO (leibnizO Word) (leibnizO Word)).
  Implicit Types interp : (D).

  (* The necessary resources to close the region again, except for the points to predicate, which we will store separately
   The boolean bl can be used to keep track of whether or not we have applied a wp lemma *)
  Definition region_open_resources W l ls φ (v : Word) (bl : bool): iProp Σ :=
    (∃ ρ,
     sts_state_std l ρ
    ∗ ⌜ρ ≠ Revoked ∧ (∀ g, ρ ≠ Monostatic g) ∧ (∀ w, ρ ≠ Uninitialized w)⌝
    ∗ open_region_many (l :: ls) W
    ∗ (if bl then monotonicity_guarantees_region ρ l v v φ ∗ φ (W, (v,v))
       else ▷ monotonicity_guarantees_region ρ l v v φ ∗  ▷ φ (W, (v,v)) )
    ∗ rel l φ)%I.

  Lemma load_inr_eq {regs r p0 g0 b0 e0 a0 p1 g1 b1 e1 a1}:
    reg_allows_load regs r p0 g0 b0 e0 a0 →
    read_reg_inr regs r p1 g1 b1 e1 a1 →
    p0 = p1 ∧ g0 = g1 ∧ b0 = b1 ∧ e0 = e1 ∧ a0 = a1.
  Proof.
      intros Hrar H3.
      pose (Hrar' := Hrar).
      destruct Hrar' as (Hinr0 & _). destruct H3 as [Hinr1 | Hinl1].
      * rewrite Hinr0 in Hinr1. inversion Hinr1.
        subst. auto.
      * destruct Hinl1 as [z Hinl1]. rewrite Hinl1 in Hinr0. by exfalso.
  Qed.

  (* Description of what the resources are supposed to look like after opening the region if we need to, but before closing the region up again*)
  Definition allow_load_res W r (regs : Reg) pc_a:=
    (∃ p g b e a, ⌜read_reg_inr regs r p g b e a⌝ ∗
    if decide (reg_allows_load regs r p g b e a ∧ a ≠ pc_a ) then
      ∃ w (P:D), ⌜(∀ Wv, Persistent (P Wv.1 Wv.2))⌝ ∗
                  a ↦ₐ w ∗ a ↣ₐ w ∗ (region_open_resources W a [pc_a] (λ Wv, P Wv.1 Wv.2) w false)
                  ∗ rcond P interp
      else open_region pc_a W)%I.

  Definition allow_load_mem W r (regs : Reg) pc_a pc_w (mem : Mem) (bl: bool):=
    (∃ p g b e a, ⌜read_reg_inr regs r p g b e a⌝ ∗
    if decide (reg_allows_load regs r p g b e a ∧ a ≠ pc_a) then
         ∃ w (P:D), ⌜(∀ Wv, Persistent (P Wv.1 Wv.2))⌝ ∗ ⌜mem = <[a:=w]> (<[pc_a:=pc_w]> ∅)⌝
                   ∗ (region_open_resources W a [pc_a] (λ Wv, P Wv.1 Wv.2) w bl)
                   ∗ (if bl then □ (∀ W (w : Word * Word), P W w -∗ interp W w) else rcond P interp)
    else  ⌜mem = <[pc_a:=pc_w]> ∅⌝ ∗ open_region pc_a W)%I.


  Lemma create_load_res:
    ∀ (W : WORLD) (r r' : leibnizO Reg) (p : Perm)
      (g : Locality) (b e a : Addr) (src : RegName) (p0 : Perm)
      (g0 : Locality) (b0 e0 a0 : Addr) E,
      read_reg_inr (<[PC:=inr (p, g, b, e, a)]> r) src p0 g0 b0 e0 a0
      → (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → ((fixpoint interp1) W) (r !r! r1,r' !r! r1))
          -∗ open_region a W
          -∗ sts_full_world W
          ={E}=∗ allow_load_res W src (<[PC:=inr (p, g, b, e, a)]> r) a
          ∗ sts_full_world W.
  Proof.
    intros W r r' p g b e a src p0 g0 b0 e0 a0 E HVsrc.
    iIntros "#Hreg Hr Hsts".
    do 5 (iApply sep_exist_r; iExists _). iFrame "%".
    case_decide as Hdec. 1: destruct Hdec as [Hallows Haeq].
    -  destruct Hallows as [Hrinr [Hra Hwb] ].
         apply andb_prop in Hwb as [Hle Hge].
         rewrite /leb_addr in Hle,Hge.

         (* Unlike in the old proof, we now go the other way around, and prove that the source register could not have been the PC, since both addresses differ. This saves us some cases.*)
         assert (src ≠ PC) as n. refine (addr_ne_reg_ne Hrinr _ Haeq). by rewrite lookup_insert.

         iDestruct ("Hreg" $! src n) as "Hvsrc".
         rewrite lookup_insert_ne in Hrinr; last by congruence.
         rewrite /RegLocate Hrinr.
         iDestruct (read_allowed_inv _ a0 with "Hvsrc") as "Hconds"; auto;
           first (split; [by apply Z.leb_le | by apply Z.ltb_lt]).
         rewrite /read_write_cond.
         iDestruct "Hconds" as "Hrel'".

         iDestruct (region_open_prepare with "Hr") as "Hr".
         iDestruct (readAllowed_valid_cap_implies with "Hvsrc") as %HH; eauto.
         { rewrite /withinBounds /leb_addr Hle Hge. auto. }
         destruct HH as [ρ' [Hstd [Hnotrevoked' [Hnotstatic' Hnotuninit'] ] ] ].
         (* We can finally frame off Hsts here, since it is no longer needed after opening the region*)
         destruct (writeAllowed p0).
       + iDestruct (region_open_next _ _ _ a0 RO ρ' with "[$Hrel' $Hr $Hsts]") as (w0 w1) "($ & Hstate' & Hr & Ha0 & Ha1 & Hfuture & Hval)"; eauto.
         { intros [g1 Hcontr]. specialize (Hnotstatic' g1); contradiction. }
         { intros [g1 Hcontr]. specialize (Hnotuninit' g1); contradiction. }
         { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
         simpl.
         iAssert (▷ ⌜w0 = w1⌝)%I as "#>HH".
         { iNext. iDestruct (interp_eq with "Hval") as %->. auto. }
         iDestruct "HH" as %->.
         iExists w1,interp. iFrame. iSplitR;[iPureIntro;apply _|]. iModIntro.
         rewrite /rcond. iSplit;auto. iExists ρ'. iFrame "%". iFrame. by iFrame "#". iSplit;auto.
         iNext; iModIntro. iIntros (W1 W2 z1 z2) "Heq". iClear "#". rewrite !fixpoint_interp1_eq.
         iDestruct "Heq" as %->. done.
       + iDestruct "Hrel'" as (P Hpers) "[Hcond Hrel']".
         iDestruct (region_open_next _ _ _ a0 RO ρ' with "[$Hrel' $Hr $Hsts]") as (w0 w1) "($ & Hstate' & Hr & Ha0 & Ha1 & Hfuture & Hval)"; eauto.
         { intros [g1 Hcontr]. specialize (Hnotstatic' g1); contradiction. }
         { intros [g1 Hcontr]. specialize (Hnotuninit' g1); contradiction. }
         { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
         iAssert (▷ ⌜w0 = w1⌝)%I as "#>HH".
         { iNext. iApply (interp_eq W). iDestruct "Hcond" as "[Hcont _]". iApply "Hcont". iFrame. }
         iDestruct "HH" as %->.
         iExists w1,P. iFrame. iSplitR;[iPureIntro;apply _|].
         rewrite /rcond. iModIntro. iSplit;auto. iExists ρ'. iFrame "%". iFrame. by iFrame "#".
    - iFrame. done.
  Qed.

  Lemma load_res_implies_mem_map:
    ∀ (W : WORLD) (r : leibnizO Reg)
       (a : Addr) (w : Word) (src : RegName),
      allow_load_res W src r a
      -∗ a ↦ₐ w
      -∗ a ↣ₐ w
      -∗ ∃ mem0 : Mem,
          allow_load_mem W src r a w mem0 false
          ∗ ▷ (([∗ map] a0↦w ∈ mem0, a0 ↦ₐ w)
          ∗ ([∗ map] a0↦w ∈ mem0, a0 ↣ₐ w)).
  Proof.
    intros W r a w src.
    iIntros "HLoadRes Ha Ha'".
    iDestruct "HLoadRes" as (p1 g1 b1 e1 a1) "[% HLoadRes]".

    case_decide as Hdec. 1: destruct Hdec as [ Hallows Haeq ].
    -  pose(Hallows' := Hallows). destruct Hallows' as [Hrinr [Hra Hwb] ].
          iDestruct "HLoadRes" as (w0 P Hpers) "[HLoadCh [HLoadCh' [HLoadRest #Hrcond] ] ]".
          iExists _.
          iSplitL "HLoadRest".
          + iExists p1,g1,b1,e1,a1. iSplitR; first auto.
            case_decide as Hdec1. 2: apply not_and_r in Hdec1 as [|]; by exfalso.
            iExists w0. iExists _. iSplitR; auto.
          + iNext. rewrite big_sepM_insert;[|rewrite lookup_insert_ne//]. iFrame.
            rewrite big_sepM_insert;[|auto]. iFrame. iSplit;[auto|].
            rewrite big_sepM_insert;[|rewrite lookup_insert_ne//]. iFrame.
            rewrite big_sepM_insert;[|auto]. iFrame.
            done.
    - iExists _.
      iSplitL "HLoadRes".
      + iExists p1,g1,b1,e1,a1. iSplitR; auto.
        case_decide; first by exfalso. auto.
      + iNext. rewrite big_sepM_insert;[|auto]. iFrame. iSplit;[auto|].
        rewrite big_sepM_insert;[|auto]. iFrame. done.
    Qed.

  Lemma mem_map_implies_pure_conds:
    ∀ (W : WORLD) (r : leibnizO Reg)
       (a : Addr) (w : Word) (src : RegName)
      (mem0 : Mem),
        allow_load_mem W src r a w mem0 false
        -∗ ⌜mem0 !! a = Some w⌝
          ∗ ⌜allow_load_map_or_true src r mem0⌝.
  Proof.
    iIntros (W r a w src mem0) "HLoadMem".
    iDestruct "HLoadMem" as (p1 g1 b1 e1 a1) "[% HLoadRes]".
    case_decide as Hdec. 1: destruct Hdec as [ Hallows Haeq ].
    -  pose(Hallows' := Hallows). destruct Hallows' as [Hrinr [Hra Hwb] ].
       (* case_decide as Haeq. *)
       iDestruct "HLoadRes" as (w0 P Hpers) "[-> _]".
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
    ∀ (W : WORLD) (r : leibnizO Reg) (p : Perm)
      (g : Locality) (b e a : Addr) (w : Word) (src : RegName)
      (mem0 : Mem),
      allow_load_mem W src r a w mem0 false
      -∗ ▷ allow_load_mem W src r a w mem0 true.
  Proof.
    iIntros (W r p g b e a w src mem0) "HLoadMem".
    iDestruct "HLoadMem" as (p0 g0 b0 e0 a0) "[% HLoadMem]".
    do 5 (iApply later_exist_2; iExists _). iApply later_sep_2; iSplitR; auto.
    case_decide.
      * iDestruct "HLoadMem" as (w0 P Hpers) "[-> [HLoadMem #[Hrcond _]] ]".
        do 2 (iApply later_exist_2; iExists _).
        do 2 (iApply later_sep_2; iSplitR; auto).
      * iFrame.
  Qed.

  Lemma mem_map_recover_res:
    ∀ (W : WORLD) (r : leibnizO Reg)
       (a : Addr) (w : Word) (src : RegName)  (p0 : Perm)
      (g0 : Locality) (b0 e0 a0 : Addr) (mem0 : Mem) (loadv : Word),
      reg_allows_load r src p0 g0 b0 e0 a0
      → mem0 !! a0 = Some loadv
      → allow_load_mem W src r a w mem0 true
        -∗ ((fixpoint interp1) W) (w,w)
        -∗ ([∗ map] a0↦w ∈ mem0, a0 ↦ₐ w)
        -∗ ([∗ map] a0↦w ∈ mem0, a0 ↣ₐ w)
        -∗ open_region a W ∗ a ↦ₐ w ∗ a ↣ₐ w ∗ ((fixpoint interp1) W) (loadv,loadv).
  Proof.
    intros W r a w src p0 g0 b0 e0 a0 mem0 loadv Hrar Ha0.
    iIntros "HLoadMem #Hw Hmem Hmem'".
    iDestruct "HLoadMem" as (p1 g1 b1 e1 a1) "[% HLoadRes]".
    destruct (load_inr_eq Hrar H0) as (<- & <- &<- &<- &<-).
    case_decide as Hdec. destruct Hdec as [Hallows Heq].
    -  destruct Hallows as [Hrinr [Hra Hwb] ].
       iDestruct "HLoadRes" as (w0 P Hpers) "[-> [HLoadRes #Hrcond] ]".
       iDestruct "HLoadRes" as (ρ1) "(Hstate' & #Hrev & Hr & (Hfuture & #HV) & Hrel')".
       iDestruct "Hrev" as %[Hnotrevoked [Hnotstatic Huninit] ].
       rewrite big_sepM_insert;[|rewrite lookup_insert_ne//].
       rewrite big_sepM_insert;[|auto].
       rewrite big_sepM_insert;[|rewrite lookup_insert_ne//].
       rewrite big_sepM_insert;[|auto].
       iDestruct "Hmem" as  "[ Ha1 [$ _]]".
       iDestruct "Hmem'" as  "[ Ha1' [$ _]]".
       iDestruct (region_close_next with "[$Hr $Ha1 $Ha1' $Hrel' $Hstate' $Hfuture]") as "Hr"; eauto.
       { intros [g Hg]; specialize (Hnotstatic g); contradiction. }
       { intros [g Hg]; specialize (Huninit g); contradiction. }
       { apply not_elem_of_cons; split; [auto|apply not_elem_of_nil]. }
       iDestruct (region_open_prepare with "Hr") as "$".
       rewrite lookup_insert in Ha0; inversion Ha0. subst. iApply "Hrcond". simpl. iFrame "#".
    - apply not_and_r in Hdec as [| <-%dec_stable].
      * by exfalso.
      * iDestruct "HLoadRes" as "[-> $ ]".
        rewrite big_sepM_insert//. iDestruct "Hmem" as "[Ha1 _]".
        rewrite big_sepM_insert//. iDestruct "Hmem'" as "[Ha2 _]".
        rewrite lookup_insert in Ha0. inversion Ha0. by iFrame.
  Qed.

  Lemma Load_spec_determ r dst src regs regs' mem0 retv retv' :
    Load_spec r dst src regs mem0 retv →
    Load_spec r dst src regs' mem0 retv' →
    (regs = regs' ∨ retv = FailedV) ∧ retv = retv'.
  Proof.
    intros Hspec1 Hspec2.
    inversion Hspec1; inversion Hspec2;subst; simplify_eq.
    - split;auto. inversion H0; inversion H4; simplify_map_eq. auto.
    - inversion H0; inversion X.
      + rewrite H3 in H5. inversion H5.
      + simplify_eq. destruct H4. destruct H6;congruence.
      + inversion H0; simplify_map_eq.
    - inversion H1; inversion X.
      + rewrite H0 in H5. inversion H5.
      + simplify_eq. destruct H4. destruct H6;congruence.
      + inversion H0; simplify_map_eq.
    - split;auto.
  Qed.

  Lemma load_case(W : WORLD) (r : prodO (leibnizO Reg) (leibnizO Reg)) (p : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst src : RegName) (P:D) :
    ftlr_instr W r p g b e a w (Load dst src) ρ P.
  Proof.
    intros Heqregs Hp Hsome i Hbae Hpers Hpwl Hregion Hnotrevoked Hnotmonostatic Hnotuninitialized Hi.
    iIntros "#Hspec #IH #Hinv #Hreg #Hinva #Hrcond #Hwcond Hmono Hw Hsts Hown".
    iIntros "Hr Hstate Ha Ha' HPC Hmap HsPC Hsmap Hj".
    assert (Persistent (▷ P W (w,w))).
    { apply later_persistent. specialize (Hpers (W,(w,w))). auto. }
    iDestruct "Hw" as "#Hw".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iDestruct ((big_sepM_delete _ _ PC) with "[HsPC Hsmap]") as "Hsmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.

    (* To read out PC's name later, and needed when calling wp_load *)
    assert(∀ x : RegName, is_Some (<[PC:=inr (p, g, b, e, a)]> r.1 !! x)) as Hsome'.
    {
      intros. destruct (decide (x = PC)).
      rewrite e0 lookup_insert; unfold is_Some. destruct Hsome with x. by eexists.
      rewrite lookup_insert_ne//. destruct Hsome with x;auto.
    }

    (* Initializing the names for the values of Hsrc now, to instantiate the existentials in step 1 *)
    assert (∃ p0 g0 b0 e0 a0 , read_reg_inr (<[PC:=inr (p, g, b, e, a)]> r.1) src p0 g0 b0 e0 a0) as [p0 [g0 [b0 [e0 [a0 HVsrc] ] ] ] ].
    {
      specialize Hsome' with src as Hsrc.
      destruct Hsrc as [wsrc Hsomesrc].
      unfold read_reg_inr. destruct wsrc. 2: destruct c,p0,p0,p0. all: repeat eexists.
      right. by exists z. by left.
    }

    (* Step 1: open the region, if necessary, and store all the resources obtained from the region in allow_load_res *)
    iMod (create_load_res with "Hreg Hr Hsts") as "[HLoadRes Hsts]"; eauto.
    (* Clear helper values; they exist in the existential now *)
    clear HVsrc p0 g0 b0 e0 a0.

    (* Step2: derive the concrete map of memory we need, and any spatial predicates holding over it *)
    iDestruct (load_res_implies_mem_map W  with "HLoadRes Ha Ha'") as (mem) "[HLoadMem [HMemRes HMemRes']]".

    (* Step 3:  derive the non-spatial conditions over the memory map*)
    iDestruct (mem_map_implies_pure_conds with "HLoadMem") as %(HReadPC & HLoadAP); auto.

    (* Step 4: move the later outside, so that we can remove it after applying wp_load *)
    iDestruct (allow_load_mem_later with "HLoadMem") as "HLoadMem"; auto.

    iApply (wp_load with "[Hmap HMemRes]"); eauto.
    { by rewrite lookup_insert. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. rewrite lookup_insert_is_Some'; eauto. destruct Hsome with rr;eauto. }
    { iSplitR "Hmap"; auto. }
    iNext. iIntros (regs' retv). iDestruct 1 as (HSpec) "[Hmem Hmap]".

    iMod (step_Load _ [SeqCtx] with "[Hsmap HMemRes' $Hj $Hspec]") as (retv' regs'') "(Hj&%&Hmem'&Hsmap)";eauto.
    { by rewrite lookup_insert. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. rewrite lookup_insert_is_Some'; eauto. destruct Hsome with rr;eauto. }
    { iSplitR "Hsmap"; auto. }
    simpl. specialize (Load_spec_determ _ _ _ _ _ _ _ _ HSpec H1) as [Heq ->].

    destruct HSpec as [* ? ? Hincr|].
    { apply incrementPC_Some_inv in Hincr.
      destruct Hincr as (?&?&?&?&?&?&?&?&?&?).
      iApply wp_pure_step_later; auto. iNext.
      iMod (do_step_pure _ [] with "[$Hspec $Hj]") as "Hs /=";auto.

      (* Step 5: return all the resources we had in order to close the second location in the region, in the cases where we need to *)
      iDestruct (mem_map_recover_res with "HLoadMem [] Hmem Hmem'") as "[Hr [Ha [Ha' #HLVInterp] ] ]"; eauto.
      { iDestruct "Hrcond" as "[Hrcond _]". iApply "Hrcond". iFrame "Hw". }

      (* Exceptional success case: we do not apply the induction hypothesis in case we have a faulty PC*)
      destruct (decide (x = RX ∨ x = RWX ∨ x = RWLX)).
      2 : {
        assert (x ≠ RX ∧ x ≠ RWX ∧ x ≠ RWLX). split; last split; by auto.
        iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]".
        { subst. by rewrite lookup_insert. }
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_notCorrectPC_perm with "[HPC]"); eauto. iIntros "!> _".
        iApply wp_pure_step_later; auto. iNext. iApply wp_value.
        iIntros (a1); inversion a1.
      }

      iDestruct (region_close with "[$Hstate $Hr $Ha $Ha' $Hmono]") as "Hr"; eauto.
      { destruct ρ;auto;[|specialize (Hnotmonostatic g1)|specialize (Hnotuninitialized p1)];contradiction. }
      destruct Heq as [<- | Hcontr];[|inversion Hcontr].
      iApply ("IH" $! _ (regs',regs') with "[] [Hmap] [Hsmap] [$Hr] [$Hsts] [$Hown] [$Hs]").
      { iSplit;auto.
        - iPureIntro. cbn. intros. subst regs'.
          rewrite lookup_insert_is_Some.
          split.
          all: destruct (decide (PC = x5)); [ auto | right; split; auto].
          all: rewrite lookup_insert_is_Some.
          all: destruct (decide (dst = x5)); [ auto | right; split; auto].

      (* Prove in the general case that the value relation holds for the register that was loaded to - unless it was the PC.*)
        - iIntros (ri Hri).
          subst regs'. simpl.
          erewrite locate_ne_reg; [ | | reflexivity]; auto.
          destruct (decide (ri = dst)).
          { subst ri.
            erewrite locate_eq_reg; [ | reflexivity]; auto.
          }
          { repeat (erewrite locate_ne_reg; [ | | reflexivity]; auto).
            iDestruct ("Hreg" with "[]") as "Hregs"; auto.
            rewrite /RegLocate.
            rewrite -!(lookup_insert_ne r.2 PC _ (inl 0%Z))// -Heqregs lookup_insert_ne//.
          }
      }
      { subst regs'. rewrite insert_insert. iApply "Hmap". }
      { subst regs'. rewrite insert_insert. iApply "Hsmap". }
      { destruct (decide (PC = dst)); simplify_eq.
        - destruct o as [HRX | [HRWX | HRWLX] ]; auto.
          subst; simplify_map_eq.
          iDestruct (writeLocalAllowed_implies_local _ RWLX with "[HLVInterp]") as "%"; auto.
          destruct x0; unfold isDirected in *. all: inversion H4.
          iPureIntro; do 2 right; auto.
        - simplify_map_eq. iPureIntro. naive_solver.
      }
      { iModIntro.
        destruct (decide (PC = dst)); simplify_eq.
        - simplify_map_eq. (* rewrite (fixpoint_interp1_eq W) *)
          iApply readAllowed_implies_region_conditions; auto. naive_solver.
        - (* iExists p'. *) simplify_map_eq. auto.
      }
    }
    { iApply wp_pure_step_later; auto. iNext. iApply wp_value; auto. iIntros; discriminate. }
    Unshelve. all: auto.
  Qed.

End fundamental.
