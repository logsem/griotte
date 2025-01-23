From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel monotone.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine.rules Require Import rules_Store.
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
      except for the points to predicate, which we will store separately *)
  (* Definition region_open_resources W l ls p φ (v : Word): iProp Σ := *)
  (*   (∃ ρ, *)
  (*       sts_state_std l ρ *)
  (*       ∗ ⌜std W !! l = Some ρ⌝ *)
  (*       ∗ ⌜ρ ≠ Revoked⌝ *)
  (*       ∗ ⌜(∀ g, ρ ≠ Frozen g)⌝ *)
  (*       ∗ open_region_many (l :: ls) W *)
  (*       ∗ rel l p φ)%I. *)


  Definition later_zcond (P : D) (has_later : bool) :=
    if has_later
    then (▷ □ ∀ W1 W2 (z : Z), P W1 (WInt z) -∗ P W2 (WInt z))%I
    else (□ ∀ W1 W2 (z : Z), P W1 (WInt z) -∗ P W2 (WInt z))%I.

  Definition later_wcond (P : D) (has_later : bool) :=
    if has_later
    then ( ▷ □ ∀ W (w : Word), interp W w -∗ P W w)%I
    else ( □ ∀ W (w : Word), interp W w -∗ P W w)%I.

  Definition later_rcond (P : D) (has_later : bool):=
    if has_later
    then ( ▷ □ ∀ W (w : Word), P W w -∗ interp W w)%I
    else ( □ ∀ W (w : Word), P W w -∗ interp W w)%I.

  Lemma P_zcond_monotone_generalZ
    (W : WORLD) (ρ : region_type) (p : Perm) (a : Addr) (z : Z) (P : D) :
    std W !! a = Some ρ →
    later_zcond P false -∗
    monotonicity_guarantees_region ρ (WInt z) p (λ Wv : WORLD * (leibnizO Word), (P Wv.1) Wv.2).
  Proof.
    unfold monotonicity_guarantees_region.
    iIntros (Hstd) "#Hzcond".
    destruct ρ;auto.
    - destruct (pwl p) eqn: HpwlP1 ; iModIntro; simpl; iIntros (W0 W1) "% HIW0".
      all: by iApply "Hzcond".
    - iModIntro; simpl; iIntros (W0 W1) "% HIW0".
      by iApply "Hzcond".
  Qed.

Lemma P_monotone_generalSd (W : WORLD) (ρ : region_type)
  (p p' : Perm) (g : Locality) (b e a : Addr)
  (ot : OType) (sb : Sealable) (P : D) :
  std W !! a = Some ρ →
  withinBounds b e a = true →
  PermFlows p p' →
  ((fixpoint interp1) W) (WCap p g b e a)
  -∗ ((fixpoint interp1) W) (WSealed ot sb)
  -∗ later_wcond P false
  -∗ monotonicity_guarantees_region ρ (WSealed ot sb) p' (λ Wv : WORLD * (leibnizO Word), (P Wv.1) Wv.2).
Proof.
  unfold monotonicity_guarantees_region.
  iIntros (Hstd Hwb Hfl') "#Hvdst #Hvsrc #Hwcond".
  destruct ρ;auto.
  - destruct (pwl p') eqn: Hpwlp' ; iModIntro; simpl; iIntros (W0 W1) "% HIW0".
    + iApply "Hwcond"; rewrite !fixpoint_interp1_eq; iEval (cbn) in "Hvsrc"; iEval (cbn); done.
    + iApply "Hwcond"; rewrite !fixpoint_interp1_eq; iEval (cbn) in "Hvsrc"; iEval (cbn); done.
  - iModIntro; simpl; iIntros (W0 W1) "% HIW0".
    iApply "Hwcond"; rewrite !fixpoint_interp1_eq; iEval (cbn) in "Hvsrc"; iEval (cbn); done.
Qed.

Lemma P_monotone_generalSr (W : WORLD) (ρ : region_type)
  (p p' : Perm) (g : Locality) (b e a : Addr)
  (sp : SealPerms) (sg : Locality) (sb se sa : OType) (P:D) :
  std W !! a = Some ρ →
  withinBounds b e a = true →
  PermFlows p p' →
  ((fixpoint interp1) W) (WCap p g b e a)
  -∗ ((fixpoint interp1) W) (WSealRange sp sg sb se sa)
  -∗ later_wcond P false
  -∗ monotonicity_guarantees_region ρ (WSealRange sp sg sb se sa) p' (λ Wv : WORLD * (leibnizO Word), (P Wv.1) Wv.2).
Proof.
  unfold monotonicity_guarantees_region.
  iIntros (Hstd Hwb Hfl') "#Hvdst #Hvsrc #Hwcond".
  destruct ρ;auto.
  - destruct (pwl p') eqn: Hpwlp' ; iModIntro; simpl; iIntros (W0 W1) "% HIW0".
    + iApply "Hwcond"; rewrite !fixpoint_interp1_eq; iEval (cbn) in "Hvsrc"; iEval (cbn); done.
    + iApply "Hwcond"; rewrite !fixpoint_interp1_eq; iEval (cbn) in "Hvsrc"; iEval (cbn); done.
  - iModIntro; simpl; iIntros (W0 W1) "% HIW0".
    iApply "Hwcond"; rewrite !fixpoint_interp1_eq; iEval (cbn) in "Hvsrc"; iEval (cbn); done.
Qed.

Lemma P_monotone_generalW (W : WORLD)  (ρ : region_type)
  (p p' p'' : Perm) (g g' : Locality) (b e a b' e' a' : Addr) (P:D) :
  std W !! a' = Some ρ →
  withinBounds b' e' a' = true →
  PermFlows p' p'' →
  canStore p' (WCap p g b e a) = true →
  ((fixpoint interp1) W) (WCap p' g' b' e' a')
  -∗ ((fixpoint interp1) W) (WCap p g b e a)
  -∗ later_wcond P false
  -∗ monotonicity_guarantees_region ρ (WCap p g b e a) p''
    (λ Wv : WORLD * (leibnizO Word), (P Wv.1) Wv.2).
Proof.
  unfold monotonicity_guarantees_region.
  iIntros (Hstd Hwb Hfl' Hconds) "#Hvdst #Hvsrc #Hwcond".
  destruct ρ;simpl;auto.
  - destruct (pwl p'') eqn: HpwlP'' ; iModIntro; simpl;auto; iIntros (W0 W1) "% HIW0".
    * iApply "Hwcond".
      iApply interp_monotone; eauto.
    * destruct g; first by iApply interp_monotone_nl.
    (* The below case is a contradiction, since if g is local,
      p' must be WL and p' flows into the non-WL p''*)
      destruct p' ; try (simpl in Hconds; by exfalso).
      all:destruct p'' eqn:Hp''v ; (by exfalso).
  - iModIntro; iIntros (W0 W1) "% HIW0".
    destruct g.
    + by iApply interp_monotone_nl.
    + (*Trick here: value relation leads to a contradiction if p' is WL,
        since then its region cannot be permanent *)
      iDestruct ( writeLocalAllowed_valid_cap_implies with "Hvdst" ) as %Ha; eauto.
      by rewrite Hstd in Ha.
Qed.

  Lemma monotonicity_guarantees_wf (P : D) ρ w p :
    later_rcond P false
    -∗ later_wcond P false
       -∗ monotonicity_guarantees_region
            ρ w p (λ Wv : WORLD * (leibnizO Word), (interp Wv.1) Wv.2)
          -∗ monotonicity_guarantees_region
               ρ w p (λ Wv : WORLD * (leibnizO Word), (P Wv.1) Wv.2).
  Proof.
    iIntros "#Hrcond #Hwcond HmonoV"; cbn.
    rewrite /monotonicity_guarantees_region.
    destruct ρ; auto.
    destruct (pwl p); auto; iDestruct "HmonoV" as "#HmonoV".
    - iModIntro. iIntros (W0 W1 Hrelated) "HP".
      iApply "Hwcond".
      iApply "HmonoV"; auto.
      iApply "Hrcond".
      done.
    - iModIntro. iIntros (W0 W1 Hrelated) "HP".
      iApply "Hwcond".
      iApply "HmonoV"; auto.
      iApply "Hrcond".
      done.
    - iDestruct "HmonoV" as "#HmonoV".
      iModIntro. iIntros (W0 W1 Hrelated) "HP".
      iApply "Hwcond".
      iApply "HmonoV"; auto.
      iApply "Hrcond".
      done.
    Qed.


  (* Lemma storev_P_mono W (r : Reg) (r1 : RegName) (r2 : Z + RegName) p g b e a p' ρ storev: *)
  (*    PermFlows p p' *)
  (*   -> word_of_argument r r2 = Some storev *)
  (*   → reg_allows_store r r1 p g b e a storev *)
  (*   → std W !! a = Some ρ *)
  (*   → (fixpoint interp1) W (WCap p g b e a) *)
  (*   (* -∗ (fixpoint interp1) W storev *) *)
  (*   (* -∗ later_zcond P false *) *)
  (*   (* -∗ (if writeAllowed p' then later_wcond P false else True) *) *)
  (*   (* -∗ (if readAllowed p' then later_rcond P false else True) *) *)
  (*   -∗ ∃ (P:D), *)
  (*       ⌜persistent_cond P⌝ *)
  (*       ∗ zcond P *)
  (*       ∗ rcond P interp *)
  (*       ∗ wcond P interp *)
  (*       ∗ monotonicity_guarantees_region ρ storev p' *)
  (*        (λ Wv : WORLD * (leibnizO Word), (P Wv.1) Wv.2). *)
  (* Proof. *)
  (*   iIntros (Hflp Hwoa Hras Hststd) "HInt". *)
  (*   destruct Hras as (Hrir & Hwa & Hwb & Hloc). *)
  (*   rewrite /monotonicity_guarantees_region. *)
  (*   destruct storev as [z | sb | ot sb ]. *)
  (*   (* - iApply (P_zcond_monotone_generalZ with "[HInt]" ); eauto. *) *)
  (*   (* - admit. *) *)
  (*   (* - rewrite /monotonicity_guarantees_region. *) *)
  (*   (*   destruct ρ;auto. *) *)
  (*   (*   2: { iModIntro; simpl; iIntros (W0 W1) "% HIW0". *) *)
  (*   (*        replace (writeAllowed p') with true; last admit. *) *)
  (*   (*        iApply "Hwcond". *) *)
  (*   (*        admit. *) *)
  (*   (*   } *) *)
  (* Abort. *)

  Lemma interp_hpf_eq (W : WORLD) P (regs : leibnizO Reg) (r1 : RegName)
    p g b e a pc_p pc_g pc_b pc_e pc_p' w storev:
    reg_allows_store (<[PC:=WCap pc_p pc_g pc_b pc_e a]> regs) r1 p g b e a storev
    → PermFlows pc_p pc_p'
    → (∀ (r1 : RegName) v, ⌜r1 ≠ PC⌝ → ⌜regs !! r1 = Some v⌝ → ((fixpoint interp1) W) v)
    -∗ rel a pc_p' P
    -∗ ⌜PermFlows p pc_p'⌝.
  Proof.
    destruct (decide (r1 = PC)).
    - subst r1. iIntros ([? ?] ?). simplify_map_eq; auto.
    - iIntros ((Hsomer1 & Hwa & Hwb & Hloc) Hfl) "Hreg #Hinva".
      simplify_map_eq.
      iDestruct ("Hreg" $! r1 _ n Hsomer1) as "Hr1"; eauto.
      iDestruct (read_allowed_inv _ a with "Hr1")
        as (p'' P'' Hflp'' Hcond_pers'') "(Hrel'' & Hzcond'' & Hrcond'' & Hwcond'')"; auto.
      { apply andb_true_iff in Hwb as [Hle Hge].
        split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
      { by apply writeA_implies_readA in Hwa as ->. }
      rewrite Hwa ; simpl.
      iDestruct (rel_agree a _ _ p'' pc_p' with "[$Hinva $Hrel'']") as "[-> _]".
      done.
  Qed.

  Lemma storev_interp_mono W (r : Reg) (r1 : RegName) (r2 : Z + RegName) p g b e a p' ρ storev:
     PermFlows p p'
    -> word_of_argument r r2 = Some storev
    → reg_allows_store r r1 p g b e a storev
    → std W !! a = Some ρ
    → ((fixpoint interp1) W) (WCap p g b e a)
    -∗ monotonicity_guarantees_region ρ storev p'
         (λ Wv : WORLD * (leibnizO Word), (interp Wv.1) Wv.2).
  Proof.
    iIntros (Hflp Hwoa Hras Hststd) "HInt".
    destruct Hras as (Hrir & Hwa & Hwb & Hloc).
    destruct storev as [z | sb | ot sb ].
    - iApply (interp_monotone_generalZ with "[HInt]" ); eauto.
    - destruct sb ;
        [ iApply (interp_monotone_generalW with "[HInt]" )
        | iApply (interp_monotone_generalSr with "[HInt]" )]
      ; eauto.
    - iApply (interp_monotone_generalSd with "[HInt]" ); eauto.
  Qed.

  Lemma storev_P_mono W P (r : Reg) (r1 : RegName) (r2 : Z + RegName) p g b e a p' ρ storev:
     PermFlows p p'
    -> word_of_argument r r2 = Some storev
    → reg_allows_store r r1 p g b e a storev
    → std W !! a = Some ρ
    → ((fixpoint interp1) W) (WCap p g b e a)
    -∗ later_rcond P false
    -∗ later_wcond P false
    -∗ monotonicity_guarantees_region ρ storev p'
         (λ Wv : WORLD * (leibnizO Word), (P Wv.1) Wv.2).
  Proof.
    iIntros (Hflp Hwoa Hras Hststd) "#HInt #Hrcond #Hwcond".
    iAssert
     (monotonicity_guarantees_region ρ storev p'
         (λ Wv : WORLD * (leibnizO Word), (interp Wv.1) Wv.2)) as "HmonoV".
    { iApply storev_interp_mono ; eauto. }
    iApply monotonicity_guarantees_wf; eauto.
  Qed.


  Definition region_open_resources W l ls p φ (v : Word): iProp Σ :=
    (∃ ρ,
        sts_state_std l ρ
        ∗ ⌜std W !! l = Some ρ⌝
        ∗ ⌜ρ ≠ Revoked⌝
        ∗ ⌜(∀ g, ρ ≠ Frozen g)⌝
        ∗ open_region_many (l :: ls) W
        ∗ rel l p φ)%I.

  Lemma store_inr_eq {regs r p0 g0 b0 e0 a0 p1 g1 b1 e1 a1 storev}:
    reg_allows_store regs r p0 g0 b0 e0 a0 storev →
    read_reg_inr regs r p1 g1 b1 e1 a1 →
    p0 = p1 ∧ g0 = g1 ∧ b0 = b1 ∧ e0 = e1 ∧ a0 = a1.
  Proof.
    intros Hrar H3.
    pose (Hrar' := Hrar).
    destruct Hrar' as (Hinr0 & _). rewrite /read_reg_inr Hinr0 in H3.
    by inversion H3.
  Qed.

  (* Lemma later_wcond_later_is_wcond (P:D) : *)
  (*   later_wcond true P ∗-∗ wcond P interp. *)
  (* Proof. *)
  (*   iSplit; iIntros ; cbn ; done. *)
  (* Qed. *)

  (* Description of what the resources are supposed to look like
     after opening the region if we need to,
     but before closing the region up again*)
  Definition allow_store_res W r1 r2 (regs : Reg) pc_a (pc_p : Perm) (has_later : bool) :=
    (∃ p g b e a storev,
        ⌜read_reg_inr regs r1 p g b e a⌝
        ∗ ⌜word_of_argument regs r2 = Some storev⌝
        ∗ if decide (reg_allows_store regs r1 p g b e a storev )
          then (if decide (a ≠ pc_a)
                then ∃ p' (P':D) w,
                    ⌜PermFlows p p'⌝
                    ∗ ⌜ persistent_cond P' ⌝
                    ∗ a ↦ₐ w
                    ∗ later_zcond P' has_later
                    ∗ (if writeAllowed p' then later_wcond P' has_later else True)
                    ∗ (if readAllowed p' then later_rcond P' has_later else True)
                    ∗ (region_open_resources W a [pc_a] p'
                         (λ Wv : WORLD * (leibnizO Word), (P' Wv.1) Wv.2) w)
                else open_region pc_a W ∗ ⌜PermFlows p pc_p⌝  )
          else open_region pc_a W)%I.

  Definition allow_store_mem W r1 r2 (regs : Reg) pc_a (pc_p : Perm) pc_w (mem : Mem)
    (has_later : bool) :=
    (∃ p g b e a storev, ⌜read_reg_inr regs r1 p g b e a⌝
                         ∗ ⌜word_of_argument regs r2 = Some storev⌝
                         ∗ if decide (reg_allows_store regs r1 p g b e a storev)
                           then (if decide (a ≠ pc_a)
                                 then ∃ p' (P':D) w,
                                     ⌜PermFlows p p'⌝
                                     ∗ ⌜ persistent_cond P' ⌝
                                     ∗ later_zcond P' has_later
                                     ∗ (if writeAllowed p' then later_wcond P' has_later else True)
                                     ∗ (if readAllowed p' then later_rcond P' has_later else True)
                                     ∗ ⌜mem = <[a:=w]> (<[pc_a:=pc_w]> ∅)⌝
                                     ∗ (region_open_resources W a [pc_a] p'
                                          (λ Wv : WORLD * (leibnizO Word), (P' Wv.1) Wv.2) w )
                                 else  ⌜mem = <[pc_a:=pc_w]> ∅⌝ ∗ open_region pc_a W  ∗ ⌜PermFlows p pc_p⌝)
                           else  ⌜mem = <[pc_a:=pc_w]> ∅⌝ ∗ open_region pc_a W)%I.

  Lemma create_store_res:
    ∀ (W : WORLD) (regs : leibnizO Reg)
      (p p' : Perm) (g : Locality) (b e a : Addr)
      (r1 : RegName) (r2 : Z + RegName)
      (p0 : Perm) (g0 : Locality) (b0 e0 a0 : Addr)
      (storev : Word) (P:D),
    read_reg_inr (<[PC:= WCap p g b e a]> regs) r1 p0 g0 b0 e0 a0
    → PermFlows p p'
    → word_of_argument (<[PC:=WCap p g b e a]> regs) r2 = Some storev
    → (∀ (r1 : RegName) v, ⌜r1 ≠ PC⌝ → ⌜regs !! r1 = Some v⌝ → ((fixpoint interp1) W) v)
    -∗ rel a p' (λ Wv : STS_std_states Addr region_type * (STS_states * STS_rels) * Word, P Wv.1 Wv.2)
    -∗ open_region a W
    -∗ sts_full_world W
    -∗ allow_store_res W r1 r2 (<[PC:=WCap p g b e a]> regs) a p' true
    ∗ sts_full_world W.
  Proof.
    intros W regs p p' g b e a r1 r2 p0 g0 b0 e0 a0 storev P HVr1 Hfl Hwoa.
    iIntros "#Hreg #Hinva Hr Hsts".
    do 6 (iApply sep_exist_r; iExists _).
    iFrame "%".
    case_decide as Hallows; last by iFrame.
    case_decide as Haeq.
    - destruct Hallows as (Hrinr & Hra & Hwb & HLoc).
      apply andb_prop in Hwb as [Hle Hge].
      assert (r1 ≠ PC) as n.
      { refine (addr_ne_reg_ne Hrinr _ Haeq). by rewrite lookup_insert. }

      simplify_map_eq.
      iDestruct ("Hreg" $! r1 _ n Hrinr) as "Hvsrc"; eauto.
      iDestruct (read_allowed_inv _ a0 with "Hvsrc")
        as (p'' P'' Hflp'' Hcond_pers'') "(Hrel'' & Hzcond'' & Hrcond'' & Hwcond'')"; auto
      ; first (split; [by apply Z.leb_le | by apply Z.ltb_lt]).
      { by apply writeA_implies_readA in Hra as ->. }

      iDestruct (region_open_prepare with "Hr") as "Hr".
      iDestruct (readAllowed_valid_cap_implies with "Hvsrc") as %HH; eauto.
      { by apply writeA_implies_readA. }
      { rewrite /withinBounds Hge; solve_addr. }

      rewrite Hra; simpl.
      destruct HH as [ρ' [Hstd' [Hnotrevoked' Hnotfrozen'] ] ].
      (* We can finally frame off Hsts here, since it is no longer needed after opening the region*)
      iDestruct (region_open_next _ _ _ a0 p'' ρ' with "[$Hrel'' $Hr $Hsts]")
        as (w0) "($ & Hstate' & Hr & Ha0 & Hfuture & Hval)"; eauto.
      { intros [g1 Hcontr];specialize (Hnotfrozen' g1); contradiction. }
      { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
      iExists p'',P''.
      iAssert ((if writeAllowed p'' then later_wcond P'' true else True)%I) as "Hwcond'".
      { destruct (writeAllowed p''); done. }
      iAssert ((if readAllowed p'' then later_rcond P'' true else True)%I) as "Hrcond'".
      { destruct (readAllowed p''); done. }

      iFrame "∗#".
      iSplitR;[iPureIntro ; destruct p0,p'; done|].
      iSplitR; try (iPureIntro; done).
    - simplify_eq; iFrame.
      iApply interp_hpf_eq; eauto.
  Qed.

  Lemma store_res_implies_mem_map:
    ∀ (W : WORLD) (regs : leibnizO Reg)
      (p' : Perm) (a : Addr) (w : Word) (r1 : RegName) (r2 : Z + RegName),
    allow_store_res W r1 r2 regs a p' true
    -∗ a ↦ₐ w
    -∗ ∃ mem0 : Mem,
        allow_store_mem W r1 r2 regs a p' w mem0 true
        ∗ ▷ ([∗ map] a0↦w0 ∈ mem0, a0 ↦ₐ w0).
  Proof.
    intros W regs p' a w r1 r2.
    iIntros "HStoreRes Ha".
    iDestruct "HStoreRes" as (p1 g1 b1 e1 a1 storev) "(% & % & HStoreRes)".
    case_decide as Hallows.
    - case_decide as Haeq.
      + pose(Hallows' := Hallows). destruct Hallows as (Hrinr & Hra & Hwb & HLoc).
        iDestruct "HStoreRes" as (p0' P0' w0 Hflp' HpersP0')
                                   "(HStoreCh & #Hzcond & #Hwcond & #Hrcond & HStoreRest)".
        iExists _.
        iSplitL "HStoreRest".
        ++ iExists p1,g1,b1,e1,a1,storev. iFrame "%".
           case_decide; last by exfalso. case_decide; last by exfalso.
           iExists p0',P0',w0.
           repeat (iSplitR; auto).
        ++ iNext; iApply memMap_resource_2ne; auto; iFrame.
      + iExists _.
        iSplitL "HStoreRes"; last (iNext; by iApply memMap_resource_1).
        iExists p1,g1,b1,e1,a1,storev. iFrame "%".
        case_decide; last by exfalso. case_decide; first by exfalso.
        iFrame; auto.
    - iExists _.
      iSplitL "HStoreRes"; last (iNext; by iApply memMap_resource_1).
      iExists p1,g1,b1,e1,a1,storev. iFrame "%".
      case_decide; first by exfalso. iFrame; auto.
  Qed.

  Lemma mem_map_implies_pure_conds:
    ∀ (W : WORLD) (regs : leibnizO Reg)
      (p p' : Perm) (g : Locality) (b e a : Addr)
      (w : Word) (r1 : RegName) (r2 : Z + RegName)
      (mem0 : Mem),
    allow_store_mem W r1 r2 regs a p' w mem0 true
    -∗ ⌜mem0 !! a = Some w⌝
    ∗ ⌜allow_store_map_or_true r1 r2 regs mem0⌝.
  Proof.
    iIntros (W regs p p' g b e a w r1 r2 mem0) "HStoreMem".
    iDestruct "HStoreMem" as (p1 g1 b1 e1 a1 storev) "(% & % & HStoreRes)".
    case_decide as Hallows.
    - case_decide as Haeq.
      + pose(Hallows' := Hallows). destruct Hallows' as (Hrinr & Hra & Hwb & HLoc).
        iDestruct "HStoreRes" as (p0' P0' w0 Hflp' HpersP0') "(_ & _ & _ & % & _)".
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


  Definition wcond' (P : D) p g b e a r : iProp Σ
    := (if decide (writeAllowed_in_r_a (<[PC:= WCap p g b e a]> r) a)
        then □ (∀ W0 (w : Word), interp W0 w -∗ P W0 w)
        else emp)%I.
  Instance wcond'_pers P p g b e a r: Persistent (wcond' P p g b e a r).
  Proof. intros. rewrite /wcond'. case_decide;apply _. Qed.

  (* Note that we turn in all information that we might have on the monotonicity of the current PC value, so that in the proof of the ftlr case itself, we do not have to worry about whether the PC was written to or not when we close the last location pc_a in the region *)
   Lemma mem_map_recover_res:
    ∀ (W : WORLD) (regs : Reg)
       (pc_w : Word) (r1 : RegName) (r2 : Z + RegName) (p0 pc_p pc_p' : Perm)
       (g0 pc_g : Locality) (b0 e0 a0 pc_b pc_e pc_a : Addr)
       (mem0 : Mem) (oldv storev : Word) (ρ : region_type) (P:D),
    word_of_argument (<[PC:= WCap pc_p pc_g pc_b pc_e pc_a]> regs) r2 = Some storev
    → reg_allows_store (<[PC:= WCap pc_p pc_g pc_b pc_e pc_a]> regs) r1 p0 g0 b0 e0 a0 storev
    → std W !! pc_a = Some ρ
    → mem0 !! a0 = Some oldv (*?*)
    → allow_store_mem W r1 r2 (<[PC:=WCap pc_p pc_g pc_b pc_e pc_a]> regs) pc_a pc_p'  pc_w mem0 false
    -∗ (∀ (r1 : RegName) v, ⌜r1 ≠ PC⌝ → ⌜regs !! r1 = Some v⌝ → ((fixpoint interp1) W) v)
    -∗ ((fixpoint interp1) W) (WCap pc_p pc_g pc_b pc_e pc_a)
    -∗ P W pc_w
    -∗ later_rcond P false
    -∗ wcond' P pc_p pc_g pc_b pc_e pc_a regs
    -∗ monotonicity_guarantees_region ρ pc_w pc_p' (λ Wv : WORLD * Word, P Wv.1 Wv.2)
    -∗ ([∗ map] a0↦w0 ∈ <[a0 := storev]> mem0, a0 ↦ₐ w0)
    -∗ ∃ v, open_region pc_a W ∗ pc_a ↦ₐ v ∗ P W v ∗ monotonicity_guarantees_region ρ v pc_p' (λ Wv : WORLD * Word, P Wv.1 Wv.2).
   Proof.
    intros W regs pc_w r1 r2 p0 pc_p pc_p' g0 pc_g b0 e0 a0 pc_b pc_e pc_a mem0 oldv storev ρ P Hwoa Hras Hstdst Ha0.
    iIntros "HStoreMem #Hreg #HVPCr Hpc_w #Hrcond #Hwcond Hpcmono Hmem".
    iDestruct "HStoreMem" as (p1 g1 b1 e1 a1 storev1) "[% [% HStoreRes] ]".
    destruct (store_inr_eq Hras H) as (<- & <- &<- &<- &<-).
    inversion H0; simplify_eq.
    case_decide as Hallows; last by exfalso.
    iAssert (((fixpoint interp1) W) (WCap p0 g0 b0 e0 a0))%I with "[HVPCr Hreg]" as "#HVr1".
    { destruct Hras as [Hreg _]. destruct (decide (r1 = PC)).
      - subst r1. rewrite lookup_insert in Hreg; by inversion Hreg.
      - simplify_map_eq.
        by iSpecialize ("Hreg" $! r1 _ n Hreg).
    }
    iAssert (((fixpoint interp1) W) storev)%I with "[HVPCr Hreg]" as "#HVstorev1".
    { destruct storev.
      - iEval (rewrite fixpoint_interp1_eq); by cbn.
      - destruct r2. cbn in Hwoa; inversion Hwoa; by exfalso.
        cbn in Hwoa.
        destruct (decide (r = PC)).
        + subst r; simplify_map_eq. done.
        + simplify_map_eq.
          iSpecialize ("Hreg" $! r _ n Hwoa).
          done.
      - destruct r2. cbn in Hwoa; inversion Hwoa; by exfalso.
        cbn in Hwoa.
        destruct (decide (r = PC)).
        + subst r; simplify_map_eq.
        + simplify_map_eq.
          iSpecialize ("Hreg" $! r _ n Hwoa).
          done.
    }
    case_decide as Haeq.
    + iExists pc_w.
      destruct Hallows as [Hrinr [Hwa [Hwb Hloc] ] ].
      iDestruct "HStoreRes" as (p' P' w' Hflp' HpersP') "(#Hzcond' & #Hwcond' & #Hrcond' & -> & HLoadRes)".
      rewrite lookup_insert in Ha0; inversion Ha0; clear Ha0; subst.
      iDestruct "HLoadRes" as (ρ1) "(Hstate' & % & % & % & Hr & #Hrel')".

      rewrite insert_insert memMap_resource_2ne; last auto.
      iDestruct "Hmem" as  "[Ha1 Hpc_a]".
      iFrame.
      
      (* iDestruct (storev_interp_mono with "HVr1") as "Hr1Mono"; eauto. *)
      iDestruct ((storev_P_mono _ P') with "[HVr1] [Hwcond'] [Hrcond']")
        as "HmonoP'"; eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
    iDestruct (region_close_next with "[$Hr $Ha1 $Hrel' $Hstate' HmonoP']") as "Hr"; eauto.
    { intros [g Hcontr]. specialize (H2 g). done. }
    { apply not_elem_of_cons; split; [auto|apply not_elem_of_nil]. }
    { iSplit.
      iPureIntro ; clear -Hflp' Hwa; destruct p0,p'; cbn in *; try done.
      iFrame "#".
      destruct (writeAllowed p') eqn:Hwa'; cycle 1.
      { destruct p0, p'; cbn in *; try congruence;  inv Hflp'. }
      by iDestruct ("Hwcond'" with "HVstorev1") as "HP'storev".
    }
    iDestruct (region_open_prepare with "Hr") as "$".
    + subst a0. iDestruct "HStoreRes" as "[-> [HStoreRes %]]".
      rewrite insert_insert -memMap_resource_1.
      rewrite lookup_insert in Ha0; inversion Ha0; simplify_eq.
      iExists storev. iFrame. rewrite /wcond'.
      rewrite decide_True.
      2:{
        rewrite /writeAllowed_in_r_a. eexists r1, _. inversion Hras.
        split. eassumption.
        destruct H1. destruct H2.
        split;auto.
        split;auto.
        destruct H2.
        apply withinBounds_le_addr in H2; auto.
      }
      iSplitR;[iApply "Hwcond";iFrame "#"|].
      iDestruct (storev_interp_mono with "HVr1") as "Hr1Mono"; eauto.
      rewrite /monotonicity_guarantees_region.
      destruct ρ;auto.
      { destruct (pwl pc_p'); iModIntro; iIntros (W1 W2 Hrelated) "H".
        all:iApply "Hwcond"; iApply "Hr1Mono"; eauto; iApply "Hrcond"; iFrame.
      }
      { destruct (pwl pc_p'); iModIntro; iIntros (W1 W2 Hrelated) "H".
        all:iApply "Hwcond"; iApply "Hr1Mono"; eauto; iApply "Hrcond"; iFrame.
      }
   Qed.

   Lemma if_later {C} {eqdec: Decision C} (Q Q' : iProp Σ) : (if (decide C) then ▷ Q else Q') -∗ ▷ (if (decide C) then Q else Q').
   Proof. iIntros "H". destruct (decide C);auto. Qed.

   Lemma if_later_bool (b : bool) (Q Q' : iProp Σ) : (if b then ▷ Q else Q') -∗ ▷ (if b then Q else Q').
   Proof. iIntros "H". destruct b;auto. Qed.

  Lemma allow_store_mem_later:
    ∀ (W : WORLD) (regs : leibnizO Reg)
      (a : Addr) (w : Word) r1 r2 (p' : Perm) (mem0 : Mem),
    allow_store_mem W r1 r2 regs a p' w mem0 true
    -∗ ▷ allow_store_mem W r1 r2 regs a p' w mem0 false.
  Proof.
    iIntros (W regs a w r1 r2 p' mem0) "HStoreMem".
    iDestruct "HStoreMem" as (p1 g1 b1 e1 a1 storev1) "[% [% HStoreRes] ]".
    do 6 (iApply later_exist_2; iExists _).
    iApply later_sep_2; iSplitR; auto.
    iApply later_sep_2; iSplitR; auto.
    case_decide; last iFrame.
    case_decide; last iFrame.
    iDestruct "HStoreRes" as (p0 P w0 Hp'O Hpers) "(#Hzcond & #Hwcond & #Hrcond & -> & HStoreMem)".
    repeat (iApply later_exist_2; iExists _).
    repeat (iApply later_sep_2; iSplitR; auto).
    iDestruct (if_later_bool with "Hwcond") as "Hwcond'"; eauto.
    iDestruct (if_later_bool with "Hrcond") as "Hrcond'"; eauto.
  Qed.

   Lemma store_case (W : WORLD) (regs : leibnizO Reg)
     (p p' : Perm) (g : Locality) (b e a : Addr) (w : Word)
     (ρ : region_type) (dst : RegName) (src : Z + RegName) (P : D) :
     ftlr_instr W regs p p' g b e a w (Store dst src) ρ P.
   Proof.
    intros Hp Hsome i Hbae Hfp HO Hpers Hpwl Hregion Hnotrevoked Hnotfrozen Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond Hmono Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    (* iDestruct (execCond_implies_region_conditions with "Hinv_interp") as "#Hinv"; eauto. *)
    iInsert "Hmap" PC.

    (* To read out PC's name later, and needed when calling wp_load *)
    assert(∀ x : RegName, is_Some (<[PC:=WCap p g b e a]> regs !! x)) as Hsome'.
    {
      intros. destruct (decide (x = PC)).
      rewrite e0 lookup_insert; unfold is_Some. by eexists.
        by rewrite lookup_insert_ne.
    }

    (* Initializing the names for the values of Hsrc now, to instantiate the existentials in step 1 *)
    assert (∃ p0 g0 b0 e0 a0 , read_reg_inr (<[PC:=WCap p g b e a]> regs) dst p0 g0 b0 e0 a0)
      as [ p0 [g0 [b0 [e0 [a0 HVdst] ] ] ] ].
    {
      specialize Hsome' with dst as Hdst.
      destruct Hdst as [wdst Hsomedst].
      unfold read_reg_inr. rewrite Hsomedst.
      destruct wdst as [|[ p0 g0 b0 e0 a0|] | ]; try done.
      by repeat eexists.
    }

    assert (∃ storev, word_of_argument (<[PC:= WCap p g b e a]> regs) src = Some storev)
      as [storev Hwoa].
    { destruct src; cbn.
      - by exists (WInt z).
      - specialize Hsome' with r as Hr.
        destruct Hr as [wsrc Hsomer].
        exists wsrc. by rewrite Hsomer.
    }

    (* Step 1: open the region, if necessary,
       and store all the resources obtained from the region in allow_load_res *)
    iDestruct (create_store_res with "Hreg Hinva Hr Hsts") as "[HStoreRes Hsts]"; eauto.
    (* Clear helper values; they exist in the existential now *)
    clear HVdst p0 g0 b0 e0 a0 Hwoa storev.

    (* Step2: derive the concrete map of memory we need,
       and any spatial predicates holding over it *)
    iDestruct (store_res_implies_mem_map W  with "HStoreRes Ha") as (mem) "[HStoreMem HMemRes]".

    (* Step 3:  derive the non-spatial conditions over the memory map*)
    iDestruct (mem_map_implies_pure_conds with "HStoreMem") as %(HReadPC & HStoreAP); auto.

    iApply (wp_store with "[Hmap HMemRes]"); eauto.
    { by rewrite lookup_insert. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. rewrite lookup_insert_is_Some'; eauto. }
    { iSplitR "Hmap"; auto. }
    rewrite /wcond.
    iDestruct (if_later with "Hwcond") as "Hwcond'";auto.
    iDestruct (allow_store_mem_later with "HStoreMem") as "HStoreMem".

    iNext. iIntros (regs' mem' retv). iDestruct 1 as (HSpec) "[Hmem Hmap]".

    destruct HSpec as [* ? ? ? -> Hincr|].
    { apply incrementPC_Some_inv in Hincr.
      destruct Hincr as (?&?&?&?&?&?&?&?&?).
      iApply wp_pure_step_later; auto. iNext; iIntros "_".

      (* From this, derive value relation for the current PC*)
      (* iDestruct (execcPC_implies_interp _ _ _ _ _ a  with "Hinv") as "HVPC"; eauto. *)

      iDestruct (switch_monotonicity_formulation with "Hmono") as "Hmono"; [eauto..|].

      (* assert that the PC *)

      (* Step 4: return all the resources we had in order to close the second location
         in the region, in the cases where we need to *)
      iDestruct (mem_map_recover_res
                  with "HStoreMem Hreg Hinv_interp Hw Hrcond [Hwcond] Hmono Hmem")
        as (w') "(Hr & Ha & HSVInterp & Hmono)"; eauto.

      iDestruct (switch_monotonicity_formulation with "Hmono") as "Hmono"; auto.

      iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono $HSVInterp]") as "Hr"; eauto.
      { destruct ρ;auto;[|ospecialize (Hnotfrozen _)];contradiction. }
      simplify_map_eq. rewrite insert_insert.

      iApply ("IH" with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]"); auto.
      iApply (interp_next_PC with "IH Hinv_interp"); eauto.
    }
    { iApply wp_pure_step_later; auto. iNext; iIntros "_". iApply wp_value; auto. iIntros; discriminate. }
    Unshelve. all: auto.
  Qed.

End fundamental.
