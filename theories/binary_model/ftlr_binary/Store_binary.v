From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.binary_model Require Export logrel_binary monotone_binary.
From cap_machine.binary_model Require Import ftlr_base_binary.
From cap_machine.rules Require Import rules_Store.
From cap_machine.binary_model.rules_binary Require Import rules_binary_Store.
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

  Lemma execcPC_implies_interp W p g b e a0:
    p = RX ∨ p = RWX ∨ p = RWLX ∧ g = Directed →
    region_conditions W p g b e -∗ ((fixpoint interp1) W) (inr (p, g, b, e, a0),inr (p, g, b, e, a0)).
  Proof.
    iIntros (Hp) "#HR".
    rewrite (fixpoint_interp1_eq _ (inr _,inr _)).
    (do 2 try destruct Hp as [ | Hp]). 3:destruct Hp.
    all:subst; auto. all: simpl. all: rewrite /region_conditions /=.
    all: iSplit;auto.
    iApply (big_sepL_mono with "HR").
    intros. iIntros "H". iDestruct (and_exist_r with "H") as (P) "((?&?)&?)". iExists _;iFrame.
  Qed.

  (* The necessary resources to close the region again, except for the points to predicate, which we will store separately *)
  Definition region_open_resources W l ls φ (v : Word): iProp Σ :=
    (∃ ρ,
        sts_state_std l ρ
    ∗ ⌜std W !! l = Some ρ⌝
    ∗ ⌜ρ ≠ Revoked⌝
    ∗ ⌜(∀ g, ρ ≠ Monostatic g)⌝
    ∗ ⌜(∀ w, ρ ≠ Uninitialized w)⌝
    ∗ open_region_many (l :: ls) W
    ∗ rel l φ)%I.

  Lemma store_inr_eq {regs r p0 g0 b0 e0 a0 p1 g1 b1 e1 a1 storev}:
    reg_allows_store regs r p0 g0 b0 e0 a0 storev →
    read_reg_inr regs r p1 g1 b1 e1 a1 →
    p0 = p1 ∧ g0 = g1 ∧ b0 = b1 ∧ e0 = e1 ∧ a0 = a1.
  Proof.
      intros Hrar H3.
      pose (Hrar' := Hrar).
      destruct Hrar' as (Hinr0 & _). destruct H3 as [Hinr1 | Hinl1].
      * rewrite Hinr0 in Hinr1. inversion Hinr1.
        subst;auto.
      * destruct Hinl1 as [z Hinl1]. rewrite Hinl1 in Hinr0. by exfalso.
  Qed.

  Lemma Store_spec_determ r dst src regs regs' mem0 mem0' mem0'' retv retv' :
    Store_spec r dst src regs mem0 mem0' retv →
    Store_spec r dst src regs' mem0 mem0'' retv' →
    (regs = regs' ∨ retv = FailedV) ∧ retv = retv' /\ (mem0' = mem0'' ∨ retv = FailedV).
  Proof.
    intros Hspec1 Hspec2.
    inversion Hspec1; inversion Hspec2; subst; simplify_eq; repeat split; auto; try congruence.
    - left. destruct H1. inv H7; try congruence.
    - destruct H1. inv X; try congruence.
      + rewrite H5 in H1. inv H1.
      + destruct H3; destruct H6; try congruence. inv H7. congruence.
      + destruct H3; try congruence. inv H8. congruence.
    - destruct H1. inv H3. inv H6. inv X;try congruence.
      + rewrite H6 in H1; inv H1.
      + rewrite H6 in H1; inv H1.
        destruct H8; congruence.
    - destruct H1. inv H3. inv H6. inv X; try congruence.
      + rewrite H6 in H1; inv H1.
      + inv H8; try congruence.
    - destruct H1. inv H2. inv H1. inv H4.
      inv X;try congruence.
      + rewrite H0 in H4. congruence.
      + inv H7;try congruence.
      + rewrite H4 in H0. inv H0.
        rewrite /word_of_argument in H7. destruct src;subst.
        * inv Hspec2. inv H9. rewrite H4 in H13. inv H13.
          inv H0. inv H7. inv H8.
        * inv Hspec2. inv H9. rewrite H4 in H13. inv H13.
          inv H0. destruct (r !! r0) eqn:Hr;inv H7;inv H13.
          revert H11; rewrite map_eq' =>H11.
          specialize (H11 a0 storev).
          rewrite lookup_insert in H11. destruct H11 as [H11 _].
          rewrite lookup_insert in H11. specialize (H11 eq_refl).
          inv H11. congruence.
  Qed.

  (* Description of what the resources are supposed to look like after opening the region if we need to, but before closing the region up again*)
  Definition allow_store_res W r1 r2 (regs : Reg) pc_a :=
    (∃ p g b e a storev, ⌜read_reg_inr regs r1 p g b e a⌝ ∗ ⌜word_of_argument regs r2 = Some storev⌝ ∗
    if decide (reg_allows_store regs r1 p g b e a storev ) then
      (if decide (a ≠ pc_a) then
         ∃ w, a ↦ₐ w ∗ a ↣ₐ w ∗ (region_open_resources W a [pc_a] interpC w)
         else open_region pc_a W )
      else open_region pc_a W)%I.

  Definition allow_store_mem W r1 r2 (regs : Reg) pc_a pc_w (mem : Mem):=
    (∃ p g b e a storev, ⌜read_reg_inr regs r1 p g b e a⌝ ∗ ⌜word_of_argument regs r2 = Some storev⌝ ∗
    if decide (reg_allows_store regs r1 p g b e a storev) then
      (if decide (a ≠ pc_a) then
         ∃ w, ⌜mem = <[a:=w]> (<[pc_a:=pc_w]> ∅)⌝ ∗
            (region_open_resources W a [pc_a] interpC w)
         else  ⌜mem = <[pc_a:=pc_w]> ∅⌝ ∗ open_region pc_a W)
    else  ⌜mem = <[pc_a:=pc_w]> ∅⌝ ∗ open_region pc_a W)%I.

  (* Lemma interp_hpf_eq (W : WORLD) (r : leibnizO Reg) (r1 : RegName) *)
  (*       p g b e a pc_p pc_g pc_b pc_e w storev: *)
  (*   reg_allows_store (<[PCE:=inr (pc_p, pc_g, pc_b, pc_e, a)]> r) r1 p g b e a storev *)
  (*   → (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → ((fixpoint interp1) W) (r !r! r1)) *)
  (*       -∗ read_write_cond a interp *)
  (*       -∗ ⌜PermFlows p pc_p'⌝. *)
  (* Proof. *)
  (*   destruct (decide (r1 = PC)). *)
  (*   - subst r1. iIntros ([? ?] ?). simplify_map_eq; auto. *)
  (*   - iIntros ((Hsomer1 & Hwa & Hwb & Hloc) Hfl) "Hreg Hinva". *)
  (*     iDestruct ("Hreg" $! r1 n) as "Hr1". simplify_map_eq. rewrite /RegLocate Hsomer1. *)
  (*     iDestruct (read_allowed_inv _ a with "Hr1") as (p'' Hfl') "#Harel'"; auto. *)
  (*     { apply andb_true_iff in Hwb as [Hle Hge]. *)
  (*       split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. } *)
  (*     { by apply writeA_implies_readA in Hwa as ->. } *)
  (*     rewrite /read_write_cond. *)
  (*     iDestruct (rel_agree a p'' pc_p' with "[$Hinva $Harel']") as "[-> _]". *)
  (*     done. *)
  (* Qed. *)

  Lemma create_store_res:
    ∀ (W : WORLD) (r r' : leibnizO Reg) (p : Perm)
      (g : Locality) (b e a : Addr) (r1 : RegName) (r2 : Z + RegName) (p0 : Perm)
      (g0 : Locality) (b0 e0 a0 : Addr)(storev : Word) (P:D) E,
      read_reg_inr (<[PC:=inr (p, g, b, e, a)]> r) r1 p0 g0 b0 e0 a0
      → word_of_argument (<[PC:=inr (p, g, b, e, a)]> r) r2 = Some storev
      → (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → ((fixpoint interp1) W) (r !r! r1,r' !r! r1))
          -∗ rel a (λ Wv, P Wv.1 Wv.2)
          -∗ open_region a W
          -∗ sts_full_world W
          ={E}=∗ allow_store_res W r1 r2 (<[PC:=inr (p, g, b, e, a)]> r) a
          ∗ sts_full_world W.
  Proof.
    intros W r r' p g b e a r1 r2 p0 g0 b0 e0 a0 storev P E HVr1 Hwoa.
    iIntros "#Hreg #Hinva Hr Hsts".
    do 6 (iApply sep_exist_r; iExists _). iFrame "%".
    case_decide as Hallows.
    -  case_decide as Haeq.
       * destruct Hallows as (Hrinr & Hra & Hwb & HLoc).
         apply andb_prop in Hwb as [Hle Hge].
         rewrite /leb_addr in Hle,Hge.
         assert (r1 ≠ PC) as n. refine (addr_ne_reg_ne Hrinr _ Haeq). by rewrite lookup_insert.

         iDestruct ("Hreg" $! r1 n) as "Hvsrc".
         rewrite lookup_insert_ne in Hrinr; last by congruence.
         rewrite /RegLocate Hrinr.
         iDestruct (read_allowed_inv _ a0 with "Hvsrc") as "Hrel'".
         { split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
         { by apply writeA_implies_readA in Hra as ->. }
         rewrite /read_write_cond.

         iDestruct (region_open_prepare with "Hr") as "Hr".
         iDestruct (readAllowed_valid_cap_implies with "Hvsrc") as %HH; eauto.
         { by apply writeA_implies_readA. }
         { rewrite /withinBounds /leb_addr Hle Hge. auto. }
         destruct HH as [ρ' [Hstd' [Hnotrevoked' [Hnotmonostatic' Hnotuninitialized'] ] ] ].
         (* We can finally frame off Hsts here, since it is no longer needed after opening the region*)
         rewrite Hra.
         (* TODO fix the following lemma so it does not need a permission *)
         iDestruct (region_open_next _ _ _ a0 RO ρ' with "[$Hrel' $Hr $Hsts]") as (w0 w1) "($ & Hstate' & Hr & Ha0 & Ha1 & Hfuture & #Hval)"; eauto.
         { intros [g1 Hcontr]. specialize (Hnotmonostatic' g1); contradiction. }
         { intros [g1 Hcontr]. specialize (Hnotuninitialized' g1); contradiction. }
         { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
         iAssert (▷ ⌜w0 = w1⌝)%I as "#>Heq".
         { iNext. simpl. iDestruct (interp_eq with "Hval") as %->. auto. }
         iDestruct "Heq" as %<-.
         iExists w0. iSplitL "Ha0"; auto. iSplitL "Ha1"; auto. unfold region_open_resources.
         iExists ρ'. iFrame "%". iFrame. by iFrame "#".
       * subst a0. iFrame. done.
    - iFrame. done.
  Qed.

  Lemma store_res_implies_mem_map:
    ∀ (W : WORLD) (r : leibnizO Reg)
       (a : Addr) (w : Word) (r1 : RegName) (r2 : Z + RegName),
      allow_store_res W r1 r2 r a
      -∗ a ↦ₐ w
      -∗ a ↣ₐ w
      -∗ ∃ mem0 : Mem,
          allow_store_mem W r1 r2 r a w mem0
              ∗ ▷ (([∗ map] a0↦w0 ∈ mem0, a0 ↦ₐ w0)
              ∗ ([∗ map] a0↦w0 ∈ mem0, a0 ↣ₐ w0)) .
  Proof.
    intros W r a w r1 r2.
    iIntros "HStoreRes Ha Ha'".
    iDestruct "HStoreRes" as (p1 g1 b1 e1 a1 storev) "(% & % & HStoreRes)".

    case_decide as Hallows.
    - case_decide as Haeq.
      ++ pose(Hallows' := Hallows). destruct Hallows as (Hrinr & Hra & Hwb & HLoc).
         iDestruct "HStoreRes" as (w0) "[HStoreCh [HstoreCh' HStoreRest]]".
         iExists _.
         iSplitL "HStoreRest".
        + iExists p1,g1,b1,e1,a1,storev. iFrame "%".
          case_decide; last by exfalso. case_decide; last by exfalso.
          iExists w0. iSplitR; auto.
        + iNext. rewrite big_sepM_insert;[|rewrite lookup_insert_ne//].
          rewrite big_sepM_insert;[|auto].
          iFrame. iSplitR;[auto|].
          rewrite big_sepM_insert;[|rewrite lookup_insert_ne//].
          rewrite big_sepM_insert;[|auto]. iFrame. done.
      ++ iExists _.
         iSplitL "HStoreRes".
        + iExists p1,g1,b1,e1,a1,storev. iFrame "%".
          case_decide; last by exfalso. case_decide; first by exfalso.
          iFrame. auto.
        + iNext. rewrite big_sepM_insert;auto. iFrame. iSplitR;auto.
          rewrite big_sepM_insert;auto.
    - iExists _.
      iSplitL "HStoreRes".
      + iExists p1,g1,b1,e1,a1,storev. iFrame "%".
        case_decide; first by exfalso. iFrame. auto.
      + iNext. rewrite big_sepM_insert;auto. iFrame. iSplitR;auto.
        rewrite big_sepM_insert;auto.
    Qed.

  Lemma mem_map_implies_pure_conds:
    ∀ (W : WORLD) (r : leibnizO Reg) (p : Perm)
      (g : Locality) (b e a : Addr) (w : Word) (r1 : RegName) (r2 : Z + RegName)
      (mem0 : Mem),
        allow_store_mem W r1 r2 r a w mem0
        -∗ ⌜mem0 !! a = Some w⌝
          ∗ ⌜allow_store_map_or_true r1 r2 r mem0⌝.
  Proof.
    iIntros (W r p g b e a w r1 r2 mem0) "HStoreMem".
    iDestruct "HStoreMem" as (p1 g1 b1 e1 a1 storev) "(% & % & HStoreRes)".
    case_decide as Hallows.
    - case_decide as Haeq.
      + pose(Hallows' := Hallows). destruct Hallows' as (Hrinr & Hra & Hwb & HLoc).
        (* case_decide as Haeq. *)
        iDestruct "HStoreRes" as (w0) "[% _]".
        iSplitR. subst. rewrite lookup_insert_ne; auto. by rewrite lookup_insert.
        iExists p1,g1,b1,e1,a1,storev.
        iPureIntro. repeat split; auto.
        case_decide; last by exfalso.
        exists w0. by simplify_map_eq.
      + subst a. iDestruct "HStoreRes" as "[-> HStoreRes]".
         iSplitR. by rewrite lookup_insert.
         iExists p1,g1,b1,e1,a1,storev. repeat iSplitR; auto.
         case_decide as Hdec1; last by done.
         iExists w.  by rewrite lookup_insert.
    - iDestruct "HStoreRes" as "[-> HStoreRes ]".
      iSplitR. by rewrite lookup_insert.
      iExists p1,g1,b1,e1,a1,storev. repeat iSplitR; auto.
      case_decide as Hdec1; last by done. by exfalso.
  Qed.

  Lemma storev_interp_mono W (r : Reg) (r1 : RegName) (r2 : Z + RegName) p g b e a ρ storev:
    word_of_argument r r2 = Some storev
     → reg_allows_store r r1 p g b e a storev
     → std W !! a = Some ρ
     → ((fixpoint interp1) W) (inr (p,g,b,e,a),inr (p,g,b,e,a))
       -∗ monotonicity_guarantees_region ρ a storev storev interpC.
   Proof.
     iIntros (Hwoa Hras Hststd) "HInt".
     destruct Hras as (Hrir & Hwa & Hwb & Hloc).
     destruct storev as [z | cap].
     - iApply (interp_monotone_generalZ with "[HInt]" ); eauto.
     - destruct r2. cbn in Hwoa; inversion Hwoa; by exfalso.
       destruct_cap cap. cbn in Hwoa.
       destruct (r !! r0); inversion Hwoa; clear Hwoa; subst w.
       rewrite /interpC. iDestruct (interp_monotone_generalW with "[HInt]" ) as "Htest"; eauto.
  Qed.

   Definition wcond' (P : D) p g b e a r : iProp Σ := (if decide (writeAllowed_in_r_a (<[PC:=inr (p, g, b, e, a)]> r) a) then □ (∀ W0 w, interp W0 w -∗ P W0 w) else emp)%I.
  Instance wcond'_pers : Persistent (wcond' P p g b e a r).
  Proof. intros. rewrite /wcond'. case_decide;apply _. Qed.
  (* Note that we turn in all information that we might have on the monotonicity of the current PC value, so that in the proof of the ftlr case itself, we do not have to worry about whether the PC was written to or not when we close the last location pc_a in the region *)
   Lemma mem_map_recover_res:
    ∀ (W : WORLD) (r : Reg)
       (pc_w : Word) (r1 : RegName) (r2 : Z + RegName) (p0 pc_p : Perm)
       (g0 pc_g : Locality) (b0 e0 a0 pc_b pc_e pc_a : Addr) (mem0 : Mem) (oldv storev : Word) (ρ : region_type) (P:D),
      word_of_argument (<[PC:=inr (pc_p, pc_g, pc_b, pc_e, pc_a)]> r) r2 = Some storev
      → reg_allows_store (<[PC:=inr (pc_p, pc_g, pc_b, pc_e, pc_a)]> r) r1 p0 g0 b0 e0 a0 storev
      → std W !! pc_a = Some ρ
      → mem0 !! a0 = Some oldv (*?*)
      → allow_store_mem W r1 r2 (<[PC:=inr (pc_p, pc_g, pc_b, pc_e, pc_a)]> r) pc_a pc_w mem0
        -∗ (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → ((fixpoint interp1) W) (r !r! r1,r !r! r1))
        -∗ ((fixpoint interp1) W) (inr(pc_p, pc_g, pc_b, pc_e, pc_a),inr(pc_p, pc_g, pc_b, pc_e, pc_a))
        -∗ P W (pc_w,pc_w)
        -∗ □ (∀ W0 w, P W0 w -∗ interp W0 w)
        -∗ wcond' P pc_p pc_g pc_b pc_e pc_a r
        -∗ monotonicity_guarantees_region ρ pc_a pc_w pc_w (λ Wv, P Wv.1 Wv.2)
        -∗ ([∗ map] a0↦w0 ∈ <[a0 := storev]> mem0, a0 ↦ₐ w0)
        -∗ ([∗ map] a0↦w0 ∈ <[a0 := storev]> mem0, a0 ↣ₐ w0)
        -∗ ∃ (v : Word), open_region pc_a W ∗ pc_a ↦ₐ v ∗ pc_a ↣ₐ v ∗ P W (v,v) ∗ monotonicity_guarantees_region ρ pc_a v v (λ Wv, P Wv.1 Wv.2).
   Proof.
    intros W r pc_w r1 r2 p0 pc_p g0 pc_g b0 e0 a0 pc_b pc_e pc_a mem0 oldv storev ρ P Hwoa Hras Hstdst Ha0.
    iIntros "HStoreMem #Hreg #HVPCr Hpc_w #Hrcond #Hwcond Hpcmono Hmem Hmem'".
    iDestruct "HStoreMem" as (p1 g1 b1 e1 a1 storev1) "[% [% HStoreRes] ]".
    destruct (store_inr_eq Hras H0) as (<- & <- &<- &<- &<-).
    rewrite Hwoa in H1; inversion H1; simplify_eq.
    case_decide as Hallows.
    - iAssert (((fixpoint interp1) W) (inr (p0,g0,b0,e0,a0), inr (p0,g0,b0,e0,a0)))%I with "[HVPCr Hreg]" as "#HVr1".
      { destruct Hras as [Hreg _]. destruct (decide (r1 = PC)).
        - subst r1. rewrite lookup_insert in Hreg; by inversion Hreg.
        - iSpecialize ("Hreg" $! r1 n). rewrite lookup_insert_ne in Hreg; last congruence. rewrite /RegLocate Hreg.
          done.
      }
      iAssert (((fixpoint interp1) W) (storev1,storev1))%I with "[HVPCr Hreg]" as "#HVstorev1".
      { destruct storev1.
        - repeat rewrite fixpoint_interp1_eq. by cbn.
        - destruct r2. cbn in Hwoa; inversion Hwoa; by exfalso.
          destruct_cap c. cbn in Hwoa.
          destruct (<[PC:=inr (pc_p, pc_g, pc_b, pc_e, pc_a)]> r !! r0) eqn:Hrr0; inversion Hwoa; clear Hwoa; subst w.
          destruct (decide (r0 = PC)).
          + subst r0. rewrite lookup_insert in Hrr0. by inversion Hrr0.
          + iSpecialize ("Hreg" $! r0 n).  rewrite lookup_insert_ne in Hrr0; last congruence. by rewrite /RegLocate Hrr0.
      }
      case_decide as Haeq.
      + iExists pc_w.
        destruct Hallows as [Hrinr [Hwa [Hwb Hloc] ] ].
        iDestruct "HStoreRes" as (w') "[-> HLoadRes]".
        rewrite lookup_insert in Ha0; inversion Ha0; clear Ha0; subst.
        iDestruct "HLoadRes" as (ρ1) "(Hstate' & % & % & % & % & Hr & Hrel')".
        rewrite !insert_insert !memMap_resource_2ne; last auto.
        rewrite big_sepM_insert;[|rewrite lookup_insert_ne//].
        rewrite big_sepM_insert;auto.
        iDestruct "Hmem" as  "[Ha1 [$ _]]".
        iDestruct "Hmem'" as  "[Ha2 $]".
        iDestruct (storev_interp_mono with "HVr1") as "Hr1Mono"; eauto.
        iDestruct (region_close_next with "[$Hr $Ha1 $Ha2 $Hrel' $Hstate' $HVstorev1 $Hr1Mono]") as "Hr"; eauto.
        { intros [g Hcontr]. specialize (H3 g). done. }
        { intros [g Hcontr]. specialize (H4 g). done. }
        { apply not_elem_of_cons; split; [auto|apply not_elem_of_nil]. }
        iDestruct (region_open_prepare with "Hr") as "$". iFrame.
       + subst a0. iDestruct "HStoreRes" as "[-> HStoreRes]".
         rewrite insert_insert -memMap_resource_1.
         rewrite big_sepM_insert;[|auto]. iDestruct "Hmem'" as "[Hmem' _]".
         rewrite lookup_insert in Ha0; inversion Ha0; simplify_eq.
         iExists storev1. iFrame. rewrite /wcond'.
         rewrite decide_True.
         iSplitR;[iApply "Hwcond";iFrame "#"|].
         iDestruct (storev_interp_mono with "HVr1") as "Hr1Mono"; eauto.
         rewrite /monotonicity_guarantees_region.
         destruct ρ;auto.
         { iModIntro. iIntros (W1 W2 Hrelated) "H". iApply "Hwcond". iApply "Hr1Mono". eauto. iApply "Hrcond". iFrame. }
         { iModIntro. iIntros (W1 W2 Hrelated) "H". iApply "Hwcond". iApply "Hr1Mono". eauto. iApply "Hrcond". iFrame. }
         rewrite /writeAllowed_in_r_a /RegLocate. exists r1. inversion Hras. rewrite H1. destruct H2. destruct H3.
         split;auto. simpl. apply orb_true_iff. left. auto. apply withinBounds_le_addr in H3. auto.
    - by exfalso.
   Qed.


   Lemma if_later {C} {eqdec: Decision C} (P:D) interp (Q Q' : iProp Σ) : (if (decide C) then ▷ Q else Q') -∗ ▷ (if (decide C) then Q else Q').
   Proof. iIntros "H". destruct (decide C);auto. Qed.

  Lemma store_case(W : WORLD) (r : prodO (leibnizO Reg) (leibnizO Reg)) (p : Perm) (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst : RegName) (src : Z + RegName) (P : D) :
    ftlr_instr W r p g b e a w (Store dst src) ρ P.
  Proof.
    intros Heqregs Hp Hsome i Hbae Hpers Hpwl Hregion Hnotrevoked Hnotmonostatic Hnotuninitialized Hi.
    iIntros "#Hspec #IH #Hinv #Hreg #Hinva #Hrcond #Hwcond Hmono Hw Hsts Hown".
    iIntros "Hr Hstate Ha Ha' HPC Hmap HsPC Hsmap Hj".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iDestruct ((big_sepM_delete _ _ PC) with "[HsPC Hsmap]") as "Hsmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.

    iDestruct (interp_reg_dupl with "[Hreg]") as "[_ Hreg']".
    { iSplit;eauto. iPureIntro. auto. }
    iSimpl in "Hreg'".

    (* To read out PC's name later, and needed when calling wp_load *)
    assert(∀ x : RegName, is_Some (<[PC:=inr (p, g, b, e, a)]> r.1 !! x)) as Hsome'.
    {
      intros. destruct (decide (x = PC)).
      rewrite e0 lookup_insert; unfold is_Some. by eexists.
      rewrite lookup_insert_ne//. destruct Hsome with x;eauto.
    }

    (* Initializing the names for the values of Hsrc now, to instantiate the existentials in step 1 *)
    assert (∃ p0 g0 b0 e0 a0 , read_reg_inr (<[PC:=inr (p, g, b, e, a)]> r.1) dst p0 g0 b0 e0 a0) as [p0 [g0 [b0 [e0 [a0 HVdst] ] ] ] ].
    {
      specialize Hsome' with dst as Hdst.
      destruct Hdst as [wdst Hsomedst].
      unfold read_reg_inr. destruct wdst. 2: destruct_cap c. all: repeat eexists.
      right. by exists z. by left.
    }

     assert (∃ storev, word_of_argument (<[PC:=inr (p, g, b, e, a)]> r.1) src = Some storev) as [storev Hwoa].
    { destruct src; cbn.
      - by exists (inl z).
      - specialize Hsome' with r0 as Hr0.
        destruct Hr0 as [wsrc Hsomer0].
        exists wsrc. by rewrite Hsomer0.
    }

    (* Step 1: open the region, if necessary, and store all the resources obtained from the region in allow_load_res *)
    iMod (create_store_res with "Hreg Hinva Hr Hsts") as "[HStoreRes Hsts]"; eauto.
    (* Clear helper values; they exist in the existential now *)
    clear HVdst p0 g0 b0 e0 a0 Hwoa storev.

    (* Step2: derive the concrete map of memory we need, and any spatial predicates holding over it *)
    iDestruct (store_res_implies_mem_map W  with "HStoreRes Ha Ha'") as (mem) "[HStoreMem [HMemRes HMemRes'] ]".

    (* Step 3:  derive the non-spatial conditions over the memory map*)
    iDestruct (mem_map_implies_pure_conds with "HStoreMem") as %(HReadPC & HStoreAP); auto.

    iApply (wp_store with "[Hmap HMemRes]"); eauto.
    { by rewrite lookup_insert. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. rewrite lookup_insert_is_Some'; eauto. destruct Hsome with rr;auto. }
    { iSplitR "Hmap"; auto. }
    rewrite /wcond.
    iDestruct (if_later with "Hwcond") as "Hwcond'";auto.
    iNext. iIntros (regs' mem' retv). iDestruct 1 as (HSpec) "[Hmem Hmap]".

    iMod (step_store _ [SeqCtx] with "[Hsmap HMemRes' $Hj $Hspec]") as (retv' regs'' mem'' Hspec') "(Hs & HMemRes' & Hsmap)";eauto.
    { by rewrite lookup_insert. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. rewrite lookup_insert_is_Some'; eauto. destruct Hsome with rr;auto. }
    { iSplitR "Hsmap"; auto. }

    specialize (Store_spec_determ _ _ _ _ _ _ _ _ _ _ HSpec Hspec') as [Heq1 [-> Heq2] ].

    destruct HSpec as [* ? ? ? -> Hincr|].
    { apply incrementPC_Some_inv in Hincr.
      destruct Hincr as (?&?&?&?&?&?&?&?&?&?).
      iApply wp_pure_step_later; auto. iNext.

      iMod (do_step_pure _ [] with "[$Hspec $Hs]") as "Hs /=";auto.
      destruct Heq1 as [<- | Hcontr];[|inversion Hcontr].
      destruct Heq2 as [<- | Hcontr];[|inversion Hcontr].

      (* From this, derive value relation for the current PC*)
      iDestruct (execcPC_implies_interp _ _ _ _ _ a  with "Hinv") as "HVPC"; eauto.

      iDestruct (switch_monotonicity_formulation with "Hmono") as "Hmono"; [eauto..|].

      (* assert that the PC *)

      (* Step 4: return all the resources we had in order to close the second location in the region, in the cases where we need to *)
      iDestruct (mem_map_recover_res with "HStoreMem Hreg' HVPC Hw [Hrcond] [Hwcond] Hmono [Hmem] [HMemRes']") as (w') "(Hr & Ha & Ha' & HSVInterp & Hmono)";eauto.
      { iDestruct "Hrcond" as "[Hrcond _]". auto. }

      iDestruct (switch_monotonicity_formulation with "Hmono") as "Hmono"; auto.

      iDestruct (region_close with "[$Hstate $Hr $Ha $Ha' $Hmono $HSVInterp]") as "Hr"; eauto.
      { destruct ρ;auto;[|specialize (Hnotmonostatic g1)|specialize (Hnotuninitialized p1)];contradiction. }
      simplify_map_eq.

      iApply ("IH" with "[] [Hmap] [Hsmap] [$Hr] [$Hsts] [$Hown] [$Hs]"); auto.
      { iSplit;eauto. iPureIntro. cbn. auto. }
      { rewrite insert_insert. iFrame. }
      { rewrite insert_insert -Heqregs. iFrame. }
    }
    { iApply wp_pure_step_later; auto. iNext. iApply wp_value; auto. iIntros; discriminate. }
    Unshelve. all: auto.
  Qed.

End fundamental.
