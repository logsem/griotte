From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine Require Import logrel fundamental interp_weakening addr_reg_sample rules proofmode monotone.
From cap_machine Require Import multiple_updates region_invariants_revocation region_invariants_allocation.
From stdpp Require Import base.
From cap_machine.proofmode Require Import map_simpl register_tactics proofmode.


Section Logrel_extra.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {cstackg : CSTACKG Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Notation CSTK := (leibnizO cstack).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

  Definition revoke_resources W C a :=
    (∃ v (φ : V) p,
        φ W C v
        ∗ (monotonicity_guarantees_region C (safeC φ) p v Temporary)
        ∗ mono_pub C (safeC φ)
        ∗ a ↦ₐ v
        ∗ zcond φ C
        ∗ rcond φ C p interp
        ∗ wcond φ C interp
        ∗ rel C a p (safeC φ)
        ∗ ⌜ PermFlowsTo RWL p ⌝
        ∗ ⌜ persistent_cond φ ⌝)%I.

  Definition closing_revoked_resources W C a :=
    (∃ (φ : V) p (Hpers : persistent_cond φ) ,
        φ W C (WInt 0)
        ∗ (monotonicity_guarantees_region C (safeC φ) p (WInt 0) Temporary)
        ∗ mono_pub C (safeC φ)
        ∗ zcond φ C
        ∗ rcond φ C p interp
        ∗ wcond φ C interp
        ∗ rel C a p (safeC φ)
        ∗ ⌜ PermFlowsTo RWL p ⌝)%I.
  Global Instance closing_revoked_persistent W C a : Persistent (closing_revoked_resources W C a).
  Proof.
    rewrite /closing_revoked_resources.
    apply bi.exist_persistent; intros φ.
    apply bi.exist_persistent; intros p.
    apply bi.exist_persistent; intros Hpers.
    repeat (apply bi.sep_persistent;try tc_solve).
    rewrite /persistent_cond in Hpers.
    specialize (Hpers (W,C,WInt 0)).
    tc_solve.
  Defined.

  Lemma close_revoked_resources W C a :
    revoke_resources W C a -∗ (∃ v, closing_revoked_resources W C a ∗ a ↦ₐ v).
  Proof.
    iIntros "H".
    iDestruct "H" as (w φ p) "(?&?&?&?&?&?&#Hwcond&?&?&%)".
    iFrame "∗#".
    iExists H.
    iSplit.
    { iApply "Hwcond"; iEval (rewrite fixpoint_interp1_eq); done. }
    rewrite /monotonicity_guarantees_region.
    destruct (isWL p); [|destruct (isDL p)].
    all: iModIntro; iIntros (W0 W1 ?) "?".
    all: iApply "Hwcond".
    all: iEval (rewrite fixpoint_interp1_eq); done.
  Qed.

  (* Lemma closing_resources_zeroed W C a v : *)
  (*   closing_revoked_resources W C a v -∗ *)
  (*   closing_revoked_resources W C a (WInt 0). *)
  (* Proof. *)
  (*   iIntros "H". *)
  (*   iDestruct "H" as (φ p Hpers) "(#Hmono&#HmonoR&#Hzcond&#Hrcond&#Hwcond&?&?)". *)
  (*   iExists φ, p, Hpers. *)
  (*   iFrame "∗#". *)
  (*   (* iSplit. *) *)
  (*   (* { iApply "Hwcond"; iEval (rewrite fixpoint_interp1_eq); done. } *) *)
  (*   rewrite /monotonicity_guarantees_region. *)
  (*   destruct (isWL p); [|destruct (isDL p)]. *)
  (*   all: iModIntro; iIntros (W0 W1 ?) "?". *)
  (*   all: iApply "Hwcond". *)
  (*   all: iEval (rewrite fixpoint_interp1_eq); done. *)
  (* Qed. *)

   Lemma update_region_revoked_temp_pwl_multiple' E W C la lv :
     NoDup la →
     Forall (eq (WInt 0)) lv ->

     sts_full_world W C -∗
     region W C -∗
     ([∗ list] a;v ∈ la;lv ,
        (closing_revoked_resources W C a
        ∗ ⌜(std W) !! a = Some Revoked ⌝)
        ∗ a ↦ₐ v
     )

     ={E}=∗

     region (std_update_multiple W la Temporary) C
     ∗ sts_full_world (std_update_multiple W la Temporary) C.
   Proof.
     generalize dependent lv; induction la
     ; iIntros (lv HNoDup Hlv) "Hworld Hregion Hl"; cbn.
     - by iFrame.
     - iDestruct (big_sepL2_length with "Hl") as "%Hlen_lv".
       destruct lv as [|v lv] ; first (by cbn in Hlen_lv).
       cbn in Hlen_lv; simplify_eq.
       apply NoDup_cons in HNoDup; destruct HNoDup as [Ha_la HNoDup].
       apply Forall_cons in Hlv; destruct Hlv as [<- Hlv].
       cbn.
       iDestruct "Hl" as "[( [Hclose %Hrevoke] & Ha) Hl]".
       (* iDestruct (big_sepL2_cons with "Hl") as "(Hclose & %Hrevoke & Ha)". *)
       iAssert (⌜ Forall (λ k : finz MemNum, std W !! k = Some Revoked) la ⌝)%I
         with "[Hl]" as "%Hrevoked".
       { rewrite !big_sepL2_sep.
         iDestruct "Hl" as "([_ Hl]&_)".
         rewrite big_sepL2_const_sepL_l.
         iDestruct "Hl" as "[_ %]".
         iPureIntro.
         by apply Forall_lookup.
       }
       pose proof (related_sts_pub_update_multiple_temp W la Hrevoked) as Hrelated.
       iDestruct "Hclose" as (???) "(Hφ & #Hmono & HmonoR & Hzcond & Hrcond & Hwcond & Hrel & %Hp )".
       rewrite /monotonicity_guarantees_region.
       opose proof (isWL_flowsto _ _ Hp _) as Hp'; first done.
       rewrite Hp'.
       iDestruct ("Hmono" with "[] [$]") as "Hφ"; eauto.
       iMod (IHla with "Hworld Hregion Hl") as "[Hregion Hworld]"; eauto.
       iMod (update_region_revoked_temp_pwl with "Hmono Hworld Hregion Ha Hφ Hrel")
         as "[Hregion Hworld]" ;auto.
       { rewrite std_sta_update_multiple_lookup_same_i; auto. }
       { eapply isO_flowsto; eauto. }
       by iFrame.
   Qed.

  Lemma read_allowed_inv' (W : WORLD) (C : CmptName) (a b e: Addr) p g l :
    readAllowed p →
    Forall (fun a' : Addr => (b <= a' < e)%a ) l ->
    ⊢ (interp W C (WCap p g b e a)) →
    [∗ list] a' ∈ l,
          (
            ∃ (p' : Perm) (P:V),
              ⌜ PermFlowsTo p p'⌝
              ∗ ⌜persistent_cond P⌝
              ∗ rel C a' p' (safeC P)
              ∗ ▷ zcond P C
              ∗ ▷ rcond P C p' interp
              ∗ (if writeAllowed p' then (▷ wcond P C interp) else True)
              ∗ monoReq W C a' p' P
          ).
  Proof.
    induction l; iIntros (Hra Hin) "#Hinterp"; first done.
    simpl.
    apply Forall_cons in Hin. destruct Hin as [Hin_a0 Hin].
    iDestruct (read_allowed_inv _ _ a0 with "Hinterp")
      as (p' P) "(%Hperm_flow & %Hpers_P & Hrel_P & Hzcond_P & Hrcond_P & Hwcond_P & HmonoV)"
    ; auto.
    iFrame "%#".
    iApply (IHl with "Hinterp"); eauto.
  Qed.

  Lemma writeLocalAllowed_valid_cap_implies (W : WORLD) (C : CmptName) p g b e a a':
    isWL p = true ->
    withinBounds b e a = true ->
    interp W C (WCap p g b e a') -∗
    ⌜std W !! a = Some Temporary⌝.
  Proof.
    intros Hp Hb. iIntros "Hinterp".
    eapply withinBounds_le_addr in Hb.
    rewrite fixpoint_interp1_eq interp1_eq; cbn.
    replace (isO p) with false.
    2: { eapply isWL_nonO in Hp ;done. }
    destruct (has_sreg_access p) eqn:HnXSR; auto.
    iDestruct "Hinterp" as "[Hinterp %Hloc]".
    iDestruct (extract_from_region_inv with "Hinterp")
             as (p' P' Hfl' Hpers') "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate)";eauto.
    by rewrite Hp in Hstate.
  Qed.

  Lemma writeLocalAllowed_valid_cap_implies' (W : WORLD) (C : CmptName) p g b e a l:
    isWL p = true ->
    Forall (fun a' : Addr => (b <= a' < e)%a ) l ->
    ⊢ (interp W C (WCap p g b e a)) →
    [∗ list] a' ∈ l, ⌜std W !! a' = Some Temporary⌝.
  Proof.
    induction l; iIntros (Hra Hin) "#Hinterp"; first done.
    simpl.
    apply Forall_cons in Hin; destruct Hin as [Hin_a0 Hin].
    iDestruct (writeLocalAllowed_valid_cap_implies with "Hinterp") as "$"; auto.
    { rewrite /withinBounds; solve_addr. }
    iApply (IHl with "Hinterp"); eauto.
  Qed.

  Lemma read_allowed_inv_full_cap (W : WORLD) (C : CmptName) (a b e: Addr) p g :
    readAllowed p →
    ⊢ (interp W C (WCap p g b e a)) →
    [∗ list] a' ∈ (finz.seq_between b e),
          (
            ∃ (p' : Perm) (P:V),
              ⌜ PermFlowsTo p p'⌝
              ∗ ⌜persistent_cond P⌝
              ∗ rel C a' p' (safeC P)
              ∗ ▷ zcond P C
              ∗ ▷ rcond P C p' interp
              ∗ (if writeAllowed p' then (▷ wcond P C interp) else True)
              ∗ monoReq W C a' p' P
          ).
  Proof.
    iIntros (Hra) "Hinterp".
    iApply (read_allowed_inv' with "Hinterp"); eauto.
    apply Forall_forall.
    intros a' Ha'.
    by apply elem_of_finz_seq_between.
  Qed.

  Lemma writeLocalAllowed_valid_cap_implies_full_cap (W : WORLD) (C : CmptName) p g b e a:
    isWL p = true ->
    ⊢ (interp W C (WCap p g b e a)) →
    [∗ list] a' ∈ (finz.seq_between b e), ⌜std W !! a' = Some Temporary⌝.
  Proof.
    iIntros (Hwl) "Hinterp".
    iApply (writeLocalAllowed_valid_cap_implies' with "Hinterp"); eauto.
    apply Forall_forall.
    intros a' Ha'.
    by apply elem_of_finz_seq_between.
  Qed.

  Lemma monotone_revoke_list_sts_full_world_keep_interp W C (l : list Addr) (l' : list Addr) :
    ⊢ ⌜NoDup l'⌝ → ⌜NoDup l⌝ → ⌜l' ⊆+ l⌝ →
    ([∗ list] a' ∈ l',
         ⌜(std W) !! a' = Some Temporary⌝ ∗
          (
            ∃ (p' : Perm) (P:V),
              ⌜ PermFlowsTo RWL p'⌝
              ∗ ⌜persistent_cond P⌝
              ∗ rel C a' p' (safeC P)
              ∗ ▷ zcond P C
              ∗ ▷ rcond P C p' interp
              ∗ (if writeAllowed p' then ▷ wcond P C interp else True)
              ∗ monoReq W C a' p' P
          ))
    ∗ sts_full_world W C ∗ region W C
    ==∗
    (sts_full_world (revoke_list l W) C
     ∗ region W C
     ∗ ([∗ list] a' ∈ l', ▷ revoke_resources W C a')).
  Proof.
   rewrite region_eq /region_def /=.
    iInduction (l) as [|x l] "IH" forall (l');
    iIntros (Hdup' Hdup Hsub) "(#Hrel' & Hfull & Hr)".
    - iFrame. apply submseteq_nil_r in Hsub as ->. repeat rewrite big_sepL_nil. done.
    - destruct (decide (x ∈ l')).
      + apply elem_of_list_split in e as [l1 [l2 Heq] ].
        rewrite Heq in Hsub.
        iRevert (Hsub Hdup Hdup'). rewrite Heq -Permutation_middle. iIntros (Hsub Hdup Hdup').
        apply NoDup_cons in Hdup as [Hnin Hdup].
        apply NoDup_cons in Hdup' as [Hnin' Hdup'].
        assert (x ∈ l') as Ha.
        { rewrite Heq. apply elem_of_app. right. apply elem_of_list_here. }
        apply elem_of_Permutation in Ha as [l'' Hleq].
        simpl. iDestruct "Hrel'" as "[ [%Htemp H] Hrel']".
        iDestruct "H" as (p' P) "(%Hpermflow_p' & %Hpers_p' & #Hx & #Hzcond & #Hrcond & #Hwcond & #Hmono)".
        iMod ("IH" with "[] [] [] [$Hrel' $Hfull $Hr]") as "(Hfull & Hr & Hl)"; auto.
        { iPureIntro. apply submseteq_cons_l in Hsub as [k' [Hperm Hsub] ].
          apply Permutation.Permutation_cons_inv in Hperm. etrans;eauto. rewrite Hperm. done. }
        rewrite /revoke_list /= /=.
        rewrite Htemp.
        rewrite rel_eq /rel_def.
        iDestruct "Hr" as (M Mρ) "(HM & % & #Hdom & Hpreds)".
        iDestruct "Hdom" as %Hdom.
        iDestruct "Hx" as (γpred) "#(Hγpred & Hφ)".
        iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq; auto.
        rewrite /region_map_def.
        rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete].
        iDestruct "Hpreds" as "[Ha Hpreds]".
        iDestruct "Ha" as (ρ Ha) "[Hstate Ha]".
        iDestruct (sts_full_state_std with "Hfull Hstate") as %Hlookup.
        simpl in Hlookup.
        simpl in Hlookup. subst. rewrite revoke_list_not_elem_of_lookup in Hlookup; auto.
        rewrite Htemp in Hlookup. inversion Hlookup. subst ρ.
        iMod (sts_update_std _ _ _ _ (Revoked) with "Hfull Hstate") as "[Hfull Hstate]".
        iDestruct (region_map_delete with "Hpreds") as "Hpreds".
        iDestruct (region_map_insert _ _ _ _ _ Revoked with "Hpreds") as "Hpreds";auto.
        iDestruct (big_sepM_insert _ _ x (γpred, p') with "[$Hpreds Hstate]") as "Hpreds"
        ; [apply lookup_delete|..]
        ; iClear "IH"
        ; iFrame "∗ #".
        iSplitR;[iPureIntro; apply lookup_insert|].
        iExists _ ;iSplit;auto.
        rewrite -HMeq.
        iModIntro. iSplitR.
        ++ iSplit; auto.
           iPureIntro. rewrite dom_insert_L.
           assert (x ∈ dom M) as Hin.
           { rewrite -Hdom. apply elem_of_dom. eauto. }
           revert Hin Hdom. clear; intros Hin Hdom. rewrite Hdom. set_solver.
        ++ iFrame "∗#%".
           iDestruct "Ha" as (γpred0 p0 φ0 Heq0 Hpers0) "(#Hsaved & Ha)".
           iDestruct "Ha" as (v Hne0) "(Hx & #HmonoV & #Hφ0)"; simplify_eq.
           iFrame "∗#%".
           destruct W as [ Wstd_sta Wloc].
           iDestruct (saved_pred_agree _ _ _ _ _ (Wstd_sta, Wloc, C, v) with "Hφ Hsaved") as "#Hφeq". iFrame.
           iDestruct (internal_eq_iff with "Hφeq") as "Hφeq'".
           iDestruct ("Hφeq'" with "Hφ0") as "HP"; iFrame "HP".
           rewrite rel_eq /rel_def; iFrame "Hγpred Hφ".
           rewrite /monotonicity_guarantees_region.
           iSplit.
           {
             destruct (isWL p0).
             +++ iApply future_pub_mono_eq_pred; auto.
             +++ destruct (isDL p0).
                 ++++ iApply future_borrow_mono_eq_pred; auto.
                 ++++ iApply future_priv_mono_eq_pred; auto.
           }
           iSplit.
           { rewrite /monoReq /=. rewrite Htemp.
             destruct p0.
             destruct rx,w,dl; cbn in *; try done.
           }
           { destruct p0.
             destruct rx,w; cbn in *; try done.
           }
      + apply NoDup_cons in Hdup as [Hnin Hdup].
        apply submseteq_cons_r in Hsub as [Hsub | [l'' [Hcontr _] ] ].
        2: { exfalso. apply n. rewrite Hcontr. apply elem_of_list_here. }
        iMod ("IH" with "[] [] [] [$Hrel' $Hfull $Hr]") as "(Hfull & Hr & Hl)"; auto.
        iDestruct "Hr" as (M Mρ) "(HM & #Hdom & #Hdom' & Hr)".
        iDestruct "Hdom" as %Hdom. iDestruct "Hdom'" as %Hdom'. iClear "IH".
        rewrite /revoke_list /=. destruct W as [ Wstd_sta Wloc].
        destruct (Wstd_sta !! x) eqn:Hsome.
        2: { iFrame. iModIntro. rewrite Hsome. iFrame. auto. }
        rewrite Hsome.
        destruct (decide (r = Temporary)).
        2: { destruct r; try contradiction; iFrame; iModIntro; iFrame; auto. }
        assert (is_Some (M !! x)) as [γp Hsomea].
        { apply elem_of_dom. rewrite -Hdom. rewrite elem_of_dom. eauto. }
        iDestruct (big_sepM_delete _ _ x with "Hr") as "[Hx Hr]"; eauto.
        iDestruct "Hx" as (ρ Ha) "[Hstate Hρ]".
        iDestruct (sts_full_state_std with "Hfull Hstate") as %Hlookup.
        iMod (sts_update_std _ _ _ _ (Revoked) with "Hfull Hstate") as "[Hfull Hstate]".
        iDestruct (region_map_delete with "Hr") as "Hpreds".
        simplify_map_eq.
        simpl in *. rewrite revoke_list_not_elem_of_lookup in Hlookup;auto.
        rewrite Hlookup in Hsome. inversion Hsome. subst.
        iDestruct (region_map_insert _ _ _ _ _ Revoked with "Hpreds") as "Hpreds";auto.
        iDestruct (big_sepM_delete _ _ x with "[Hstate $Hpreds Hρ]") as "Hr"; eauto.
        iExists Revoked; iSplitR; first (by iPureIntro ; simplify_map_eq).
        iFrame.
        iDestruct "Hρ" as (? ? ? ? ?) "[? _]". iExists _,_,_. repeat iSplit;eauto.
        iModIntro. iFrame.
        iSplit; auto.
        iPureIntro. rewrite dom_insert_L.
        assert (x ∈ dom M) as Hin.
        { rewrite -Hdom'. apply elem_of_dom. eauto. }
        revert Hin Hdom'. clear; intros Hin Hdom. rewrite Hdom. set_solver.
  Qed.

  Lemma monotone_revoke_sts_full_world_keep_interp W C (l : list Addr) :
    ⌜NoDup l⌝ -∗
    ([∗ list] a' ∈ l,
         ⌜(std W) !! a' = Some Temporary⌝ ∗
          (
            ∃ (p' : Perm) (P:V),
              ⌜ PermFlowsTo RWL p'⌝
              ∗ ⌜persistent_cond P⌝
              ∗ rel C a' p' (safeC P)
              ∗ ▷ zcond P C
              ∗ ▷ rcond P C p' interp
              ∗  (if writeAllowed p' then ▷ wcond P C interp else True)
              ∗ monoReq W C a' p' P
          ))
    ∗ sts_full_world W C ∗ region W C
    ==∗
    (sts_full_world (revoke W) C
     ∗ region W C
     ∗ ([∗ list] a' ∈ l, ▷ revoke_resources W C a')).
  Proof.
    iIntros (Hdup) "(Hl & Hfull & Hr)".
    rewrite revoke_list_dom.
    iAssert (⌜l ⊆+ (map_to_list (std W)).*1⌝)%I as %Hsub.
    { iClear "Hfull Hr". iInduction l as [| x l] "IH".
      - iPureIntro. apply submseteq_nil_l.
      - iDestruct "Hl" as "[ [Hin Hrel] Hl]".
        iDestruct "Hin" as %Hin. apply NoDup_cons in Hdup as [Hnin Hdup].
        iDestruct ("IH" with "[] Hl") as %Hsub; auto.
        iPureIntro.
        assert (x ∈ (map_to_list (std W)).*1) as Helem.
        { apply map_to_list_fst. exists Temporary. by apply elem_of_map_to_list. }
        apply elem_of_Permutation in Helem as [l' Hl']. rewrite Hl'.
        apply submseteq_skip. revert Hsub. rewrite Hl'; intros Hsub.
        apply submseteq_cons_r in Hsub as [Hsub | [l'' [Heq _] ] ]; auto.
        assert (x ∈ l) as Hcontr.
        { rewrite Heq. apply elem_of_list_here. }
        subst. contradiction.
    }
    iMod (monotone_revoke_list_sts_full_world_keep_interp _ _ (map_to_list (std W)).*1 l
            with "[] [] [] [Hl $Hfull $Hr]") as "(Hfull & Hr & Hi)"; auto.
    { iPureIntro. apply (NoDup_fst_map_to_list (M:=gmap Addr) (A:=region_type)). }
    by iFrame.
  Qed.

  (* revoke stack, with unknown p and φ *)
  Lemma monotone_revoke_stack W C b e a :
    let la := finz.seq_between b e in

    interp W C (WCap RWL Local b e a)
    ∗ sts_full_world W C
    ∗ region W C
    ==∗
    sts_full_world (revoke W) C
    ∗ region (revoke W) C
    ∗ ([∗ list] a ∈ la, ▷ revoke_resources W C a ∗ ⌜(std (revoke W)) !! a = Some Revoked⌝).
  Proof.
    iIntros (la) "(#Hinterp & HW & Hr)".
    iAssert (
       ([∗ list] a' ∈ la,
         ⌜(std W) !! a' = Some Temporary⌝ ∗
          (
            ∃ (p' : Perm) (P:V),
              ⌜ PermFlowsTo RWL p'⌝
              ∗ ⌜persistent_cond P⌝
              ∗ rel C a' p' (safeC P)
              ∗ ▷ zcond P C
              ∗ ▷ rcond P C p' interp
              ∗ (if writeAllowed p' then ▷ wcond P C interp else True)
              ∗ monoReq W C a' p' P
          ))%I
      ) with "[Hinterp]" as "Hl".
    {
      iDestruct (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp") as "Htmp"; first done.
      iDestruct (read_allowed_inv_full_cap with "Hinterp") as "H"; first done.
      iApply big_sepL_sep; iFrame "#".
    }
    iAssert (⌜Forall (λ a, std W !! a = Some Temporary) la⌝)%I as %Htemps.
    { iDestruct (big_sepL_sep with "Hl") as "[Htemps Hrel]".
      iDestruct (big_sepL_forall with "Htemps") as %Htemps.
      iPureIntro. apply Forall_lookup. done. }
    iMod (monotone_revoke_sts_full_world_keep_interp with "[] [$HW $Hr $Hl]") as "(HW & Hr & Hl')"; eauto.
    { iPureIntro ; subst la ; apply finz_seq_between_NoDup. }
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(HM & %Hdom & % & Hpreds)".
    iDestruct (monotone_revoke_region_def with "[] [$HW] [$Hpreds]") as "[Hpreds HW]"; auto.
    iModIntro. iFrame. iSplitR.
    - iPureIntro.
      rewrite /revoke in Hdom |- *.
      repeat (split;auto).
      by rewrite -revoke_dom_eq.
    - iApply big_sepL_sep. iFrame. iApply big_sepL_forall. iPureIntro.
      revert Htemps. rewrite (Forall_lookup _ la). intros Hl i a' Ha; auto.
      specialize (Hl i a' Ha).
      rewrite /revoke in Hdom, Hl |- *.
      by apply revoke_lookup_Monotemp.
  Qed.



End Logrel_extra.
