From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine Require Import ftlr_base interp_weakening.
From cap_machine Require Import logrel interp_weakening memory_region rules proofmode monotone.
From cap_machine Require Import multiple_updates region_invariants_revocation.
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
  .

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

  Lemma closing_revoked_from_rel_stack W C a :
    rel C a RWL interpC -∗ closing_revoked_resources W C a.
  Proof.
    iIntros "Hrel".
    iExists interp, RWL, persistent_cond_interp; cbn. iFrame.
    iSplit; first (iApply interp_int).
    iSplit; first (iApply future_pub_mono_interp_z).
    iSplit.
    { iIntros (v) "!>".
      iIntros (W0 W1 Hrelated) "Hinterp".
      rewrite /safeC /=.
      iApply monotone.interp_monotone; eauto.
    }
    iSplit; first (iApply zcond_interp).
    iSplit; first (iApply rcond_interp).
    iApply wcond_interp.
  Qed.

  Lemma mono_priv_closing_revoked_resources W W' c a :
    related_sts_priv_world W W' ->
    closing_revoked_resources W c a -∗
    closing_revoked_resources W' c a.
  Proof.
    iIntros (Hrelated) "(%&%&%&?&?&#Hmono&#Hzcond&#Hrcond&#Hwcond&?)".
    iExists _,_,Hpers; iFrame "∗#".
    iApply "Hzcond"; done.
  Qed.

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
       { eapply notisO_flowsfrom; eauto. }
       by iFrame.
   Qed.

  Lemma monotone_revoke_list_sts_full_world_keep_interp W C (l : list Addr) (l' l_unk : list Addr) :
    ⊢ ⌜NoDup (l_unk ++ l')⌝ → ⌜NoDup l⌝ → ⌜(l_unk ++ l') ⊆+ l⌝ →
    ⌜ Forall (λ a : finz MemNum, W.1 !! a = Some Temporary) l_unk ⌝ →
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
     ∗ ([∗ list] a' ∈ l', ▷ revoke_resources W C a')
     ∗ close_list_resources C W l_unk true
    ).
  Proof.
   rewrite region_eq /region_def /= /close_list_resources /close_addr_resources.
    iInduction (l) as [|x l] "IH" forall (l' l_unk)
    ; iIntros (Hdup' Hdup Hsub Htmp) "(#Hrel' & Hfull & Hr)".
    {
      iFrame.
      apply submseteq_nil_r in Hsub as Heq.
      destruct (app_eq_nil _ _ Heq) as [-> ->].
      repeat rewrite big_sepL_nil. done.
    }
    destruct (decide (x ∈ l'));[|destruct (decide (x ∈ l_unk))].
   - apply elem_of_list_split in e as [l1 [l2 Heq] ].
     rewrite Heq in Hsub.
     iRevert (Hsub Hdup Hdup'). rewrite Heq -Permutation_middle. iIntros (Hsub Hdup Hdup').
     apply NoDup_cons in Hdup as [Hnin Hdup].
     setoid_rewrite <- Permutation_middle in Hdup'.
     apply NoDup_cons in Hdup' as [Hnin' Hdup'].
     assert (x ∈ l') as Ha.
     { rewrite Heq. apply elem_of_app. right. apply elem_of_list_here. }
     apply elem_of_Permutation in Ha as [l'' Hleq].
     simpl. iDestruct "Hrel'" as "[ [%Htemp H] Hrel']".
     iDestruct "H" as (p' P) "(%Hpermflow_p' & %Hpers_p' & #Hx & #Hzcond & #Hrcond & #Hwcond & #Hmono)".
     iMod ("IH" with "[] [] [] [] [$Hrel' $Hfull $Hr]") as "(Hfull & Hr & Hl & Hl_unk)"; auto.
     { iPureIntro.
       apply submseteq_app_l in Hsub as [k' [Hperm Hsub] ].
       destruct Hsub as (Hk' & Hl_unk & Hsub).
       apply submseteq_app_l.
       apply submseteq_cons_l in Hsub as [k'' [Hperm' Hsub] ].
       eexists k',k''.
       repeat split; eauto.
       simplify_eq.
       setoid_rewrite Hperm' in Hk'.
       setoid_rewrite <- Permutation_middle in Hk'.
       apply Permutation.Permutation_cons_inv in Hk'.
       done.
     }
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
     { iSplitR;[iPureIntro; apply lookup_insert|]. iExists _ ;iSplit;auto. }
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
              ++++ iApply future_pub_mono_eq_pred; auto.
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
   - apply elem_of_list_split in e as [l1 [l2 Heq] ].
     rewrite Heq in Hsub.
     iRevert (Hsub Hdup Hdup').
     setoid_rewrite <- Permutation_middle.
     iIntros (Hsub Hdup Hdup').
     apply NoDup_cons in Hdup as [Hnin Hdup].
     rewrite Heq in Hdup'.
     setoid_rewrite <- Permutation_middle in Hdup'.
     apply NoDup_cons in Hdup' as [Hnin' Hdup'].
     assert (x ∈ l_unk) as Ha.
     { rewrite Heq. apply elem_of_app. right. apply elem_of_list_here. }
     pose proof Ha as Ha'.
     apply elem_of_Permutation in Ha as [l'' Hleq].
     rewrite Forall_forall in Htmp.
     iMod (region_rel_get _ _ x with "[$Hfull Hr]") as "(Hr & Hfull & #Hx)";[apply Htmp|..].
     { setoid_rewrite Hleq; set_solver+. }
     { rewrite region_eq /region_def. iFrame. }
     rewrite region_eq /region_def.
       rewrite -/app in Hdup', Hdup, Hnin'.
     iMod ("IH" with "[] [] [] [] [Hrel' $Hfull $Hr]") as "(Hfull & Hr & Hl & Hl_unk)"; auto.
     { iPureIntro.
       replace ((x :: l1 ++ l2) ++ l') with (x :: ((l1 ++ l2) ++ l')) in Hsub by set_solver.
       apply submseteq_cons_l in Hsub as [k'' [Hperm' Hsub'] ].
       apply Permutation.Permutation_cons_inv in Hperm'.
       by setoid_rewrite Hperm'.
     }
     { iPureIntro.
       apply Forall_forall.
       intros y Hy.
       apply Htmp.
       rewrite Heq.
       set_solver.
     }
     rewrite /revoke_list /= /=.
     rewrite Htmp; last done.
     rewrite rel_eq /rel_def.
     iDestruct "Hr" as (M Mρ) "(HM & % & #Hdom & Hpreds)".
     iDestruct "Hdom" as %Hdom.
     iDestruct "Hx" as (p' φ' Hpers) "Hx".
     iDestruct "Hx" as (γpred) "#(Hγpred & Hφ)".
     iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq; auto.
     rewrite /region_map_def.
     rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete].
     iDestruct "Hpreds" as "[Ha Hpreds]".
     iDestruct "Ha" as (ρ Ha) "[Hstate Ha]".
     iDestruct (sts_full_state_std with "Hfull Hstate") as %Hlookup.
     simpl in Hlookup.
     simpl in Hlookup. subst. rewrite revoke_list_not_elem_of_lookup in Hlookup; auto.
     rewrite Htmp in Hlookup; last done.
     inversion Hlookup. subst ρ.
     iMod (sts_update_std _ _ _ _ (Revoked) with "Hfull Hstate") as "[Hfull Hstate]".
     iDestruct (region_map_delete with "Hpreds") as "Hpreds".
     iDestruct (region_map_insert _ _ _ _ _ Revoked with "Hpreds") as "Hpreds";auto.
     iDestruct (big_sepM_insert _ _ x (γpred, p') with "[$Hpreds Hstate]") as "Hpreds"
     ; [apply lookup_delete|..]
     ; iClear "IH"
     ; iFrame "∗ #".
     { iSplitR;[iPureIntro; apply lookup_insert|]. iExists _ ;iSplit;auto. }
     iDestruct (big_sepL_app with "Hl_unk") as "[$ $]".
     rewrite -HMeq.
     iModIntro. iSplitR.
     { iSplit; auto.
        iPureIntro. rewrite dom_insert_L.
        assert (x ∈ dom M) as Hin.
        { rewrite -Hdom. apply elem_of_dom. eauto. }
        revert Hin Hdom. clear; intros Hin Hdom. rewrite Hdom. set_solver.
     }
     iSplitR;auto.
     iDestruct "Ha" as (γpred0 p0 φ0 Heq0 Hpers0) "(#Hsaved & Ha)".
     iDestruct "Ha" as (v Hne0) "(Hx & #HmonoV & #Hφ0)"; simplify_eq.
     iExists v; iFrame "%∗".
     destruct W as [ Wstd_sta Wloc].
     iDestruct (saved_pred_agree _ _ _ _ _ (Wstd_sta, Wloc, C, v) with "Hφ Hsaved") as "#Hφeq". iFrame.
     iDestruct (internal_eq_iff with "Hφeq") as "Hφeq'".
     iSplitL "HmonoV";[|by iNext; iApply "Hφeq'"].
     all: destruct (isWL p0).
     +++ iApply future_pub_mono_eq_pred; auto.
     +++ destruct (isDL p0).
         ++++ iApply future_pub_mono_eq_pred; auto.
         ++++ iApply future_priv_mono_eq_pred; auto.
   - apply NoDup_cons in Hdup as [Hnin Hdup].
     assert ( x ∉ (l_unk ++ l')) as n1 by set_solver+n n0.
     apply submseteq_cons_r in Hsub as [Hsub | [l'' [Hcontr _] ] ].
     2: { exfalso. apply n1.
          rewrite Hcontr. apply elem_of_list_here. }
     iMod ("IH" with "[] [] [] [] [$Hrel' $Hfull $Hr]") as "(Hfull & Hr & Hl & Hl')"; auto.
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
     { iExists Revoked; iSplitR; first (by iPureIntro ; simplify_map_eq).
       iFrame.
       iDestruct "Hρ" as (? ? ? ? ?) "[? _]".
       iExists _,_,_. repeat iSplit;eauto.
     }
     iModIntro. iFrame.
     iSplit; auto.
     iPureIntro. rewrite dom_insert_L.
     assert (x ∈ dom M) as Hin.
     { rewrite -Hdom'. apply elem_of_dom. eauto. }
     revert Hin Hdom'. clear; intros Hin Hdom; rewrite Hdom; set_solver.
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
    ∃ l_unk_temp,
      ⌜ NoDup (l_unk_temp ++ l) ∧ (forall (a : Addr), (std W) !! a = Some Temporary <-> a ∈ (l_unk_temp ++ l))⌝
    ∗ sts_full_world (revoke W) C
    ∗ region W C
    ∗ ([∗ list] a ∈ l, ▷ revoke_resources W C a)
    ∗ close_list_resources C W l_unk_temp true.
  Proof.
    iIntros (Hdup) "(Hl & Hfull & Hr)".
    rewrite revoke_list_dom.
    iAssert ( ⌜ Forall (λ a : finz MemNum, W.1 !! a = Some Temporary) l⌝ )%I with "[Hl]" as "%Htmp".
    { iDestruct (big_sepL_sep with "Hl") as "[% _]".
      iPureIntro; apply Forall_forall; intros a [k Ha]%elem_of_list_lookup; eapply H; done.
    }
    pose proof (extract_temps_split_world _ l Hdup Htmp) as (l_tmp_unk & Hnodup' & Hall_l).
    assert (l_tmp_unk ++ l ⊆+ (map_to_list W.1).*1) as Hsub.
    { revert Hall_l Hnodup' Htmp Hdup.
      generalize dependent l_tmp_unk.
      induction l as [| x l]; intros l_unk Hall Hnodup_all Hall_l Hnodup_l.
      + rewrite app_nil_r.
        rewrite app_nil_r in Hnodup_all, Hall.
        apply submseteq_dom;auto.
        apply Forall_forall.
        intros. by apply Hall.
      + setoid_rewrite <- Permutation_middle.
        specialize (IHl (x::l_unk)).
        apply NoDup_cons in Hnodup_l as [Hx Hdup_l].
        apply Forall_cons in Hall_l as [Ha_all Hall_l].
        setoid_rewrite <- Permutation_middle in Hnodup_all.
        setoid_rewrite <- Permutation_middle in Hall.
        apply IHl; auto.
    }
    iMod (monotone_revoke_list_sts_full_world_keep_interp _ _ (map_to_list (std W)).*1 l l_tmp_unk
            with "[] [] [] [] [Hl $Hfull $Hr]") as "(Hfull & Hr & Hi & Hi')"; auto.
    { iPureIntro. apply (NoDup_fst_map_to_list (M:=gmap Addr) (A:=region_type)). }
    { iPureIntro.
      apply Forall_forall.
      intros x Hx; apply Hall_l; set_solver+Hx.
    }
    iExists l_tmp_unk.
    iFrame "∗%".
    iModIntro.
    iSplit; done.
  Qed.

  (* revoke stack, with unknown p and φ *)
  Lemma monotone_revoke_stack W C b e a :
    let la := finz.seq_between b e in

    interp W C (WCap RWL Local b e a)
    ∗ sts_full_world W C
    ∗ region W C
    ==∗
    ∃ l_unk_temp,
      ⌜ NoDup (l_unk_temp ++ la) ∧ (forall (a : Addr), (std W) !! a = Some Temporary <-> a ∈ (l_unk_temp ++ la))⌝
    ∗ sts_full_world (revoke W) C
    ∗ region (revoke W) C
    ∗ ([∗ list] a ∈ la, ▷ revoke_resources W C a)
    ∗ ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) la⌝
    ∗ close_list_resources C W l_unk_temp true
    ∗ ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) l_unk_temp⌝.
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
    iMod (monotone_revoke_sts_full_world_keep_interp with "[] [$HW $Hr $Hl]") as (l_unk) "(% & HW & Hr & Hl' & Hl'')"; eauto.
    { iPureIntro ; subst la ; apply finz_seq_between_NoDup. }
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(HM & %Hdom & % & Hpreds)".
    iDestruct (monotone_revoke_region_def with "[] [$HW] [$Hpreds]") as "[Hpreds HW]"; auto.
    iModIntro. iFrame "∗%". iSplitR.
    - iPureIntro.
      rewrite /revoke in Hdom |- *.
      repeat (split;auto).
      by rewrite -revoke_dom_eq.
    - iSplit.
      + iPureIntro.
        eapply Forall_impl; eauto.
        by apply revoke_lookup_Monotemp.
      + iPureIntro.
        destruct H as (? & Hl').
        apply Forall_forall.
        intros x Hx.
        assert (x ∈ l_unk ++ la) as Hx' by set_solver+Hx.
        specialize (Hl' x).
        rewrite /revoke in Hdom, Hl' |- *.
        apply revoke_lookup_Monotemp.
        by apply Hl'.
  Qed.

  Lemma monotone_revoke_stack_alt W C b e a :
    let la := finz.seq_between b e in

    interp W C (WCap RWL Local b e a)
    ∗ sts_full_world W C
    ∗ region W C
    ==∗
    ∃ l_unk_temp,
      ⌜ NoDup (l_unk_temp ++ la) ∧ (forall (a : Addr), (std W) !! a = Some Temporary <-> a ∈ (l_unk_temp ++ la))⌝
      ∗ sts_full_world (revoke W) C
      ∗ region (revoke W) C
      ∗ ▷ ([∗ list] a ∈ la, closing_revoked_resources W C a)
      ∗ ▷ ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) la⌝
      ∗ ▷ (∃ stk_mem, [[ b , e ]] ↦ₐ [[ stk_mem ]])
      ∗ close_list_resources C W l_unk_temp true
      ∗ ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) l_unk_temp⌝.
  Proof.
    iIntros (la) "(#Hinterp & Hsts & Hr)".
    iMod (monotone_revoke_stack with "[$Hinterp $Hsts $Hr]") as (l) "($ & $ & $ & Hstk & $ & $ & $)".
    iModIntro.
    rewrite -bi.later_sep.
    iNext.
    iAssert (
        ([∗ list] a ∈ la,
           closing_revoked_resources W C a
           ∗ ∃ v, a ↦ₐ v
        )
      )%I with "[Hstk]" as "Hstk".
    {
      iApply (big_sepL_impl with "Hstk").
      iModIntro; iIntros (k x Hx) "Hrev".
      iDestruct (close_revoked_resources with "Hrev") as (v) "[$ $]".
    }
    { rewrite !big_sepL_sep.
      iDestruct "Hstk" as "(Hclose & Hv)".
      iFrame.
      by iApply region_addrs_exists.
    }
  Qed.

  Lemma opening_closing_resources W C a :
    opening_resources interp W C a -∗ (∃ v, ▷ closing_resources interp W C a v ∗ a ↦ₐ v).
  Proof.
    iIntros "H".
    iDestruct "H" as (w φ p ρ) "(?&?&?&?&?&?&?&?&?&?)".
    iFrame.
  Qed.

  Lemma closing_resources_zeroed W C a v :
    closing_resources interp W C a v -∗
    closing_resources interp W C a (WInt 0).
  Proof.
    iIntros "H".
    iDestruct "H" as (φ p ρ) "(?&Hφ&#Hmono&#Hwcond&#Hrcond&?&?&?&?)".
    iExists φ, p, ρ.
    iFrame "∗#".
    iSplit.
    { iApply "Hrcond"; iEval (rewrite fixpoint_interp1_eq); done. }
    rewrite /monotonicity_guarantees_region.
    destruct ρ; auto ; [destruct (isWL p); [|destruct (isDL p)] |].
    all: iModIntro; iIntros (W0 W1 ?) "?".
    all: iApply "Hrcond".
    all: iEval (rewrite fixpoint_interp1_eq); done.
  Qed.

  Lemma region_open_list_interp_gen (W : WORLD) (C : CmptName)
    (la la' : list Addr) (g : Locality) (b e a : Addr) :
    NoDup la ->
    Forall (fun a' : Addr => (b <= a' < e)%a ) la ->
    la ## la' ->

    interp W C (WCap RWL g b e a)
    ∗ open_region_many W C la'
    ∗ sts_full_world W C -∗

      open_region_many W C (la++la')
      ∗ sts_full_world W C
      ∗ ([∗ list] a ∈ la, opening_resources interp W C a)
  .
  Proof.
    induction la; intros Hnodup Hin Hdis ;
      iIntros "(#Hinterp & Hr & Hsts)"; cbn in * |- *.
    - by iFrame.
    - apply Forall_cons in Hin; destruct Hin as [Hin_a0 Hin].
      apply NoDup_cons in Hnodup; destruct Hnodup as [Hnotin Hnodup].
      pose proof (disjoint_cons _ _ _ Hdis) as Ha_notin_l'.
      eapply disjoint_weak in Hdis.
      iDestruct (IHla with "[$Hinterp $Hr $Hsts]") as "IH"; eauto.
      iDestruct "IH" as "(Hr & Hsts & Hopen_res)".
      iDestruct (read_allowed_inv _ _ a0 with "Hinterp")
        as (p' P) "(%Hperm_flow & %Hpers_P & Hrel_P & Hzcond_P & Hrcond_P & Hwcond_P & HmonoV)"
      ; auto.
      assert (writeAllowed p' = true) as ->.
      {eapply writeAllowed_flowsto; eauto. }
      iDestruct (readAllowed_valid_cap_implies with "Hinterp") as (ρ) "[%HWa %Hρ]"; auto.
      { by eapply withinBounds_true_iff. }
      iDestruct (region_open_next with "[$Hr $Hrel_P $Hsts]") as "Ha"; eauto.
      {
        intros Hcontra.
        apply elem_of_app in Hcontra. destruct Hcontra as [Hcontra|Hcontra]
        ; [set_solver+Hcontra Hnotin|set_solver+Hcontra Ha_notin_l'].
      }
      iDestruct "Ha" as (va) "(Hsts & Hsts_std_a & Hr & Hv_a & #Hmono_a & Hφ_a & %Hp_a)".
      pose proof (Hpers_P (W,C,va)); iDestruct "Hφ_a" as "#Hφ_a".
      iAssert (▷ P W C (WInt 0))%I as "Hφ_a'".
      { iNext.
        rewrite /rcond /wcond.
        iDestruct "Hwcond_P" as "#Hwcond_P".
        iApply "Hwcond_P".
        iEval (rewrite fixpoint_interp1_eq); done.
      }
      iAssert (▷ monotonicity_guarantees_region C (safeC P) p' (WInt 0) ρ)%I as "Hmono_a'".
      { iNext.
        rewrite /monotonicity_guarantees_region.
        destruct ρ; auto ; [destruct (isWL p'); [|destruct (isDL p')] |].
        all: iModIntro; iIntros (W0 W1 ?) "?".
        all: iDestruct "Hwcond_P" as "#Hwcond_P"; iApply "Hwcond_P".
        all: iEval (rewrite fixpoint_interp1_eq); done.
      }
      cbn.
      iFrame "∗#%".
      iSplit; iPureIntro.
      + eapply notisDRO_flowsfrom; eauto.
      + eapply notisDL_flowsfrom; eauto.
  Qed.

  Lemma region_close_list_interp_gen (W : WORLD) (C : CmptName)
  (lv : list Word)
  (la la' : list Addr):

    NoDup la ->
    la ## la' ->
    length lv = length la ->

    open_region_many W C (la++la')
    ∗ ([∗ list] a ; v ∈ la ; lv, a ↦ₐ v ∗ closing_resources interp W C a v)
    -∗ open_region_many W C la'
  .
  Proof.
    generalize dependent lv.
    induction la; intros lv Hnodup Hdis Hlen_lv
    ; iIntros "(Hr & Hclose_res)"; cbn in * |- *.
    - by iFrame.
    - destruct lv as [| v lv ]; simplify_eq.
      cbn.
      iDestruct "Hclose_res" as "[ [Ha Hclose_res_a] Hclose_res ]".
      iDestruct "Hclose_res_a"
        as (? ? ?) "(Hstd & Hφ & Hmono & _ & _ & Hrel & %Hrevoked & %Hp & %Hp' & %Hp'' & %Hpers)".
      apply NoDup_cons in Hnodup; destruct Hnodup as [Hnotin Hnodup].
      pose proof (disjoint_cons _ _ _ Hdis) as Ha_notin_l'.
      eapply disjoint_weak in Hdis.
      iDestruct (region_close_next with "[$Hstd $Hr $Ha $Hmono $Hφ $Hrel]") as "Hr"; eauto.
      {
        intros Hcontra.
        apply elem_of_app in Hcontra. destruct Hcontra as [Hcontra|Hcontra]
        ; [set_solver+Hcontra Hnotin|set_solver+Hcontra Ha_notin_l'].
      }
      iDestruct (IHla with "[$Hr $Hclose_res]") as "IH"; eauto.
  Qed.

  Lemma closing_resources_interp W C a w :
    closing_resources interp W C a w -∗ interp W C w.
    iIntros "H".
    iDestruct "H" as (???) "(Hstd&Hφ&Hmono&Hrcond&Hrel&?&?&%&%&%&%)".
    destruct p.
    destruct dl,dro; try done; by iApply "Hrcond".
  Qed.

End Logrel_extra.
