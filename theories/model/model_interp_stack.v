From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules logrel monotone interp_weakening.
From cap_machine Require Import sts_multiple_updates region_invariants_revocation.
From cap_machine Require Import memory_region proofmode map_simpl register_tactics.
From cap_machine Require Export world_ghost_theory stack_world_resources.

Section WorldInterpStack.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

  (*** World Interpretation for Safe Stack *)

  (** This file is part of the model.
      It proves some properties about the world in presence of a safe-to-share stack pointer.

     They are not meant to be understood or used by a Griotte user. *)

  (* Opening the world from a safe-to-share stack region gives [StackOpenWorldResources] *)
  Lemma region_open_list_interp_gen (W : WORLD) (C : CmptName)
    (la la' : list Addr) (g : Locality) (b e a : Addr) :
    NoDup la ->
    Forall (fun a' : Addr => (b <= a' < e)%a ) la ->
    la ## la' ->

    interp W C (WCap RWL g b e a) ∗
    open_region_many W C la' ∗
    sts_full_world W C
    -∗
    open_region_many W C (la++la') ∗
    sts_full_world W C ∗
    (∃ lv, ([∗ list] a;v ∈ la;lv, a ↦ₐ v) ∗
           ▷ StackOpenWorldResources interp W C la lv
    ).
  Proof.
    induction la; intros Hnodup Hin Hdis ;
      iIntros "(#Hinterp & Hr & Hsts)"; cbn in * |- *.
    - iFrame.
      iExists []; rewrite /StackOpenWorldResources /StackWorldResources; iSplit; iFrame; [|iNext; iSplit]; try done.
    - apply Forall_cons in Hin; destruct Hin as [Hin_a0 Hin].
      apply NoDup_cons in Hnodup; destruct Hnodup as [Hnotin Hnodup].
      pose proof (disjoint_cons _ _ _ Hdis) as Ha_notin_l'.
      eapply disjoint_weak in Hdis.
      iDestruct (IHla with "[$Hinterp $Hr $Hsts]") as "(Hr & Hsts & Hopen_res)"; eauto.
      iDestruct (read_allowed_inv _ _ a0 with "Hinterp")
        as (p' P) "(%Hperm_flow & %Hpers_P & Hrel_P & Hzcond_P & Hrcond_P & Hwcond_P & HmonoV)"
      ; auto.
      assert (writeAllowed p' = true) as ->.
      {eapply writeAllowed_flowsto; eauto. }
      iDestruct (readAllowed_valid_cap_implies with "Hinterp") as (ρ) "[%HWa %Hρ]"; auto.
      { by eapply withinBounds_true_iff. }
      iAssert (⌜ ρ = Temporary ⌝)%I as "%Hρ_eq" ;simplify_eq.
      {
        rewrite fixpoint_interp1_eq /=.
        destruct g; auto.
        iDestruct (big_sepL_elem_of with "Hinterp") as "Ha".
        {  rewrite elem_of_finz_seq_between; eauto. }
        iDestruct "Ha" as "(%pa & %Pa & _ & _ & _ & _ & _ & _ & _ & %Hstate)".
        by rewrite Hstate in HWa; simplify_eq.
      }
      assert (isWL p' = true) as Hwl_p'; simplify_eq.
      { destruct p' as [ [] [] ]; cbn in *; auto. }
      iDestruct (region_open_next_temp_pwl with "[$Hr $Hrel_P $Hsts]") as "Ha"; eauto.
      {
        intros Hcontra.
        apply elem_of_app in Hcontra. destruct Hcontra as [Hcontra|Hcontra]
        ; [set_solver+Hcontra Hnotin|set_solver+Hcontra Ha_notin_l'].
      }
      iDestruct "Ha" as (va) "(Hr & Hsts & Hsts_std_a & Hv_a & _ & #Hmono_a & Hφ_a)".
      pose proof (Hpers_P (W,C,va)); iDestruct "Hφ_a" as "#Hφ_a".
      cbn.
      iFrame "∗".
      iDestruct "Hopen_res" as (lv) "[Hlv Hopen_res]".
      iExists (va::lv); iFrame.
      iNext.
      cbn.
      iDestruct "Hopen_res" as "[??]"; iFrame.
      iExists P, p'; iFrame "∗#%".
      iSplit.
      + by rewrite mono_temporary_eq Hwl_p'.
      + by rewrite /monoReq HWa Hwl_p'.
  Qed.

  (* We can close the world using [StackOpenWorldResources] *)
  Lemma region_close_list_interp_gen (W : WORLD) (C : CmptName)
  (lv : list Word)
  (la la' : list Addr):

    NoDup la ->
    la ## la' ->
    length lv = length la ->

    open_region_many W C (la++la') ∗
    ([∗ list] a;v ∈ la;lv, a ↦ₐ v) ∗
    StackOpenWorldResources interp W C la lv
    -∗
    open_region_many W C la'
  .
  Proof.
    generalize dependent lv.
    induction la; intros lv Hnodup Hdis Hlen_lv
    ; iIntros "(Hr & Ha & Hclose_res)"; cbn in * |- *.
    - by iFrame.
    - destruct lv as [| v lv ]; simplify_eq.
      cbn.
      iDestruct "Hclose_res" as "[ [(%Pa & %pa & HPa & Hmono & Hrel_a & Hvalid & %Hp) Hclose_res] [Hstd_a Hstates] ]".
      iDestruct "Ha" as "[Ha Hlv]".
      apply NoDup_cons in Hnodup; destruct Hnodup as [Hnotin Hnodup].
      pose proof (disjoint_cons _ _ _ Hdis) as Ha_notin_l'.
      eapply disjoint_weak in Hdis.
      rewrite mono_temporary_eq.
      assert (isWL pa = true) as Hwl_pa.
      { destruct pa as [ [] [] ]; cbn in *; auto. }
      rewrite Hwl_pa.
      iAssert (⌜ persistent_cond Pa ⌝ )%I as "%Hpers_a".
      { by iDestruct "Hvalid" as "(?&?&?&?&%)". }
      iDestruct (region_close_next_temp_pwl with "[$Hstd_a $Hr $Ha $Hmono $HPa $Hrel_a]") as "Hr"; eauto.
      {
        intros Hcontra.
        apply elem_of_app in Hcontra. destruct Hcontra as [Hcontra|Hcontra]
        ; [set_solver+Hcontra Hnotin|set_solver+Hcontra Ha_notin_l'].
      }
      { by apply isWL_nonO in Hwl_pa. }
      iDestruct (IHla with "[$Hr $Hclose_res $Hstates $Hlv]") as "IH"; eauto.
  Qed.


  Local Lemma submseteq_dom (l : list Addr) (Wstd_sta : gmap Addr region_type) :
    Forall (λ i : Addr, Wstd_sta !! i = Some Temporary) l
    → NoDup l → l ⊆+ (map_to_list Wstd_sta).*1.
  Proof.
    generalize l.
    induction Wstd_sta using map_ind.
    + intros l' Htemps Hdup. destruct l'; auto. inversion Htemps. subst. discriminate.
    + intros l' Htemps Hdup. rewrite map_to_list_insert; auto.
      cbn.
      (* destruct on i being an element of l'! *)
      destruct (decide (i ∈ l')).
      ++ apply list_elem_of_split in e as [l1 [l2 Heq] ].
         rewrite Heq -Permutation_middle.
         apply submseteq_skip.
         rewrite Heq in Hdup.
         apply NoDup_app in Hdup as [Hdup1 [Hdisj Hdup2] ].
         apply NoDup_cons in Hdup2 as [Helem2 Hdup2].
         assert (i ∉ l1) as Helem1.
         { intros Hin. specialize (Hdisj i Hin). apply not_elem_of_cons in Hdisj as [Hcontr _]. done. }
         apply IHWstd_sta.
         +++ revert Htemps. repeat rewrite Forall_forall. intros Htemps.
             intros j Hin.
             assert (j ≠ i) as Hne.
             { intros Hcontr; subst. apply elem_of_app in Hin as [Hcontr | Hcontr]; congruence. }
             rewrite -(Htemps j);[rewrite lookup_insert_ne;auto|].
             subst. apply elem_of_app. apply elem_of_app in Hin as [Hin | Hin]; [left;auto|right].
             apply elem_of_cons;by right.
         +++ apply NoDup_app; repeat (split;auto).
             intros j Hj. specialize (Hdisj j Hj). apply not_elem_of_cons in Hdisj as [_ Hl2];auto.
      ++ apply submseteq_cons. apply IHWstd_sta; auto.
         revert Htemps. repeat rewrite Forall_forall. intros Htemps j Hin.
         specialize (Htemps j Hin).
         assert (i ≠ j) as Hneq; [intros Hcontr; subst; congruence|].
         rewrite lookup_insert_ne in Htemps;auto.
  Qed.

  (* NOTE
     The following defines predicates and lemmas that are prove with respect to the model.
     They are not meant to be understood or used by a Griotte user.

     It looks like we should be able to prove the final lemma [monotone_revoke_stack]
     using [monotone_revoke_keep],
     and then split [RevokedResources] in 2 parts:
     the one for unknown, and the one for known (stack) part.

     From the one for stack, because we have [interp] one would want to derive
     [StackRevokedResources], but it does not seem to work:
     there's seemingly some problem with the later modality.

     This is why the following is proven from the model.
   *)


  Local Lemma monotone_revoke_list_sts_full_world_keep_interp W C (l : list Addr) (l' l_unk : list Addr) :
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
     ∗ ([∗ list] a' ∈ l', ▷ (∃ v , StackWorldResource interp W C a' v ∗ a' ↦ₐ v))
     ∗ ▷ RevokedResources W C l_unk
    ).
  Proof.
   rewrite region_eq /region_def /= /RevokedResources.
    iInduction (l) as [|x l] "IH" forall (l' l_unk)
    ; iIntros (Hdup' Hdup Hsub Htmp) "(#Hrel' & Hfull & Hr)".
    {
      iFrame.
      apply submseteq_nil_r in Hsub as Heq.
      destruct (app_eq_nil _ _ Heq) as [-> ->].
      repeat rewrite big_sepL_nil. done.
    }
    destruct (decide (x ∈ l'));[|destruct (decide (x ∈ l_unk))].
   - apply list_elem_of_split in e as [l1 [l2 Heq] ].
     rewrite Heq in Hsub.
     iRevert (Hsub Hdup Hdup'). rewrite Heq -Permutation_middle. iIntros (Hsub Hdup Hdup').
     apply NoDup_cons in Hdup as [Hnin Hdup].
     setoid_rewrite <- Permutation_middle in Hdup'.
     apply NoDup_cons in Hdup' as [Hnin' Hdup'].
     assert (x ∈ l') as Ha.
     { rewrite Heq. apply elem_of_app. right. apply list_elem_of_here. }
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
     rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete_eq].
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
     ; [apply lookup_delete_eq|..]
     ; iClear "IH"
     ; iFrame "∗ #".
     { iSplitR;[iPureIntro; apply lookup_insert_eq|]. iExists _ ;iSplit;auto. }
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
        rewrite mono_temporary_eq.
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
   - apply list_elem_of_split in e as [l1 [l2 Heq] ].
     rewrite Heq in Hsub.
     iRevert (Hsub Hdup Hdup').
     setoid_rewrite <- Permutation_middle.
     iIntros (Hsub Hdup Hdup').
     apply NoDup_cons in Hdup as [Hnin Hdup].
     rewrite Heq in Hdup'.
     setoid_rewrite <- Permutation_middle in Hdup'.
     apply NoDup_cons in Hdup' as [Hnin' Hdup'].
     assert (x ∈ l_unk) as Ha.
     { rewrite Heq. apply elem_of_app. right. apply list_elem_of_here. }
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
     rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete_eq].
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
     ; [apply lookup_delete_eq|..]
     ; iClear "IH"
     ; iFrame "∗ #".
     { iSplitR;[iPureIntro; apply lookup_insert_eq|]. iExists _ ;iSplit;auto. }
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
     rewrite mono_temporary_eq.
     iSplitL "HmonoV";[by iNext; iApply "Hφeq'"|].
     all: destruct (isWL p0).
     +++ iApply future_pub_mono_eq_pred; auto.
     +++ destruct (isDL p0).
         ++++ iApply future_pub_mono_eq_pred; auto.
         ++++ iApply future_priv_mono_eq_pred; auto.
   - apply NoDup_cons in Hdup as [Hnin Hdup].
     assert ( x ∉ (l_unk ++ l')) as n1 by set_solver+n n0.
     apply submseteq_cons_r in Hsub as [Hsub | [l'' [Hcontr _] ] ].
     2: { exfalso. apply n1.
          rewrite Hcontr. apply list_elem_of_here. }
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

  Local Lemma monotone_revoke_sts_full_world_keep_interp W C (l : list Addr) :
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
    ∗ ([∗ list] a' ∈ l, ▷ (∃ v , StackWorldResource interp W C a' v ∗ a' ↦ₐ v))
    ∗ ▷ RevokedResources W C l_unk_temp.
  Proof.
    iIntros (Hdup) "(Hl & Hfull & Hr)".
    rewrite revoke_list_dom.
    iAssert ( ⌜ Forall (λ a : finz MemNum, W.1 !! a = Some Temporary) l⌝ )%I with "[Hl]" as "%Htmp".
    { iDestruct (big_sepL_sep with "Hl") as "[% _]".
      iPureIntro; apply Forall_forall; intros a [k Ha]%list_elem_of_lookup; eapply H; done.
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
  Local Lemma monotone_revoke_stack_pre W C b e a :
    let la := finz.seq_between b e in

    interp W C (WCap RWL Local b e a)
    ∗ sts_full_world W C
    ∗ region W C
    ==∗
    ∃ l_unk_temp,
      ⌜ NoDup (l_unk_temp ++ la) ∧ (forall (a : Addr), (std W) !! a = Some Temporary <-> a ∈ (l_unk_temp ++ la))⌝
    ∗ sts_full_world (revoke W) C
    ∗ region (revoke W) C
    ∗ ([∗ list] a ∈ la, ▷ (∃ v , StackWorldResource interp W C a v ∗ a ↦ₐ v))
    ∗ ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) la⌝
    ∗ ▷ RevokedResources W C l_unk_temp
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

  (* Revoke a stack region *)
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
      ∗ ▷ StackRevokedResources W C la
      ∗ ▷ ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) la⌝
      ∗ ▷ (∃ stk_mem, [[ b , e ]] ↦ₐ [[ stk_mem ]])
      ∗ ▷ RevokedResources W C l_unk_temp
      ∗ ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) l_unk_temp⌝.
  Proof.
    iIntros (la) "(#Hinterp & Hsts & Hr)".
    iMod (monotone_revoke_stack_pre with "[$Hinterp $Hsts $Hr]") as (l) "($ & $ & $ & Hstk & $ & $ & $)".
    iModIntro.
    rewrite -bi.later_sep.
    iNext.
    iClear "Hinterp".
    subst la.
    iStopProof.
    rewrite /region_pointsto.
    generalize (finz.seq_between b e) as la.
    induction la; iIntros "H"; cbn.
    { iFrame; iExists []; done. }
    iDestruct "H" as "[ (%v & Hres & Hv) IH]".
    iDestruct (IHla with "IH") as "(Hres' & [%stk Hstk])".
    iSplitR "Hv Hstk".
    - iDestruct (StackWorldResource_zero with "Hres") as "Hres"; iFrame.
    - iExists (v::stk); iFrame.
  Qed.

  (* Reinstate a stack region *)
  Lemma update_region_revoked_temp_pwl_multiple E W C la lv :
     NoDup la →
     Forall (eq (WInt 0)) lv ->
     Forall (fun a => (std W) !! a = Some Revoked) la ->

     sts_full_world W C -∗
     region W C -∗
     StackRevokedResources W C la -∗
     ([∗ list] a;v ∈ la;lv, a ↦ₐ v)

     ={E}=∗

     region (std_update_multiple W la Temporary) C
     ∗ sts_full_world (std_update_multiple W la Temporary) C.
   Proof.
     generalize dependent lv; induction la
     ; iIntros (lv HNoDup Hlv Hrev) "Hworld Hregion Hres Hl"; cbn.
     - by iFrame.
     - iDestruct (big_sepL2_length with "Hl") as "%Hlen_lv".
       destruct lv as [|v lv] ; first (by cbn in Hlen_lv).
       cbn in Hlen_lv; simplify_eq.
       apply NoDup_cons in HNoDup; destruct HNoDup as [Ha_la HNoDup].
       apply Forall_cons in Hlv; destruct Hlv as [<- Hlv].
       cbn.
       iDestruct "Hl" as "[Ha Hl]".
       iDestruct "Hres" as "[Hclose Hres]".
       apply Forall_cons in Hrev as [Hrev_a Hrevoked].
       pose proof (related_sts_pub_update_multiple_temp W la Hrevoked) as Hrelated.
       iDestruct "Hclose" as "[%P [%p (HP&#Hmono&#Hrel&(#Hmono'&#Hzcond&#Hwcond&#Hrcond&%Hpers)&%Hp) ] ]"
       ; pose proof (Hpers (W,C, WInt 0))
       ; iDestruct "HP" as "#HP".
       rewrite mono_temporary_eq.
       opose proof (isWL_flowsto _ _ Hp _) as Hp'; first done.
       rewrite Hp'.
       iDestruct ("Hmono" with "[] [$]") as "Hφ"; eauto.
       iMod (IHla with "Hworld Hregion Hres Hl") as "[Hregion Hworld]"; eauto.
       iMod (update_region_revoked_temp_pwl with "Hmono Hworld Hregion Ha Hφ Hrel")
         as "[Hregion Hworld]" ;auto.
       { rewrite std_sta_update_multiple_lookup_same_i; auto. }
       { eapply notisO_flowsfrom; eauto. }
       by iFrame.
   Qed.

End WorldInterpStack.
