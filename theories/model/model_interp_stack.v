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
    {stsg : STSG Addr region_type OType Word Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
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
     The following defines predicates and lemmas that are proved using the internal of the model.
     They are not meant to be understood or used by a Griotte user.
   *)

  Local Lemma revoked_stack_revoked W C l' :
    ([∗ list] a' ∈ l',
       ⌜ std W !! a' = Some Temporary ⌝ ∗
       (
         ∃ (p' : Perm) (P:V),
           ⌜ PermFlowsTo RWL p'⌝
           ∗ ⌜persistent_cond P⌝
           ∗ rel C a' p' (safeC P)
           ∗ ▷ zcond P C
           ∗ ▷ rcond P C p' interp
           ∗ (if writeAllowed p' then ▷ wcond P C interp else True)
           ∗ monoReq W C a' p' P
    )) -∗
    ([∗ list] y ∈ l', close_addr_resources C W y true)
    -∗
    ([∗ list] a' ∈ l', ▷ (∃ v , StackWorldResource interp W C a' v ∗ a' ↦ₐ v))
  .
    Proof.
      induction l'; iIntros "Hinterp Hrevoked"; first done.
      iDestruct "Hinterp" as "[Hinterp_a Hinterp]".
      iDestruct "Hrevoked" as "[Hrevoked_a Hrevoked]".
      iDestruct (IHl' with "Hinterp Hrevoked") as "$".
      iDestruct "Hinterp_a" as "(%Ha & %p1 & %P1 & %Hp1 & %Hpers_P1 & #Hrel_1 & #Hzcond & #Hrcond & #Hwcond & #HmonoReq)".
      rewrite /close_addr_resources /temp_resources /=.
      iDestruct "Hrevoked_a" as "(%p2 & %P2 & %Hpers_P2  & [ %va H ] & #Hrel_2 )".
      iDestruct (rel_agree C a (safeC P1) P2 with "[$Hrel_1 $Hrel_2]") as "[<- Heq]".
      iDestruct "H" as "(Hp2 & Ha & #HP2 & #Hmono)".
      iExists va; iFrame "Ha".
      rewrite /StackWorldResource.
      iExists P1, p1.

      assert (isWL p1 = true) as Hwl.
      { eapply isWL_flowsto; eauto. }
      assert (writeAllowed p1 = true) as ->.
      { eapply writeAllowed_flowsto; eauto. }
      iSplitR.
      { iNext; iSpecialize ("Heq" $! (W,C,va)); cbn ; iRewrite "Heq"; done. }
      iSplitR.
      { rewrite mono_temporary_eq.
        destruct (isWL p1); first by iApply future_pub_mono_eq_pred_rel.
        destruct (isDL p1); first by iApply future_pub_mono_eq_pred_rel.
        by iApply future_priv_mono_eq_pred_rel.
      }
      iNext.
      iSplit; first iFrame "#".
      iSplit; last iFrame "%".
      rewrite /valid_stk_interp.
      rewrite /monoReq Ha.
      rewrite Hwl; iFrame "∗#%".
    Qed.

  (* NOTE Although I would like to be able to use [world_interp_revoke] directly,
      unfortunately we *cannot* derive [StackRevokedResources]
      from [interp] and [RevokedResources],
      because there's a later modality that is not properly placed.

      The internal of the model, with [close_addr_resources] actually solve this problem. *)

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
    intros la.
     iIntros "(#Hinterp & Hsts & Hr)".
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
    iAssert (⌜Forall (λ a, std W !! a = Some Temporary) la⌝)%I as %Hla_tmp.
    { iDestruct (big_sepL_sep with "Hl") as "[Htemps Hrel]".
      iDestruct (big_sepL_forall with "Htemps") as %Htemps.
      iPureIntro. apply Forall_lookup. done. }

    assert (NoDup la) as Hla_nodup by apply finz_seq_between_NoDup.

     pose proof (extract_temps_split_world _ la Hla_nodup Hla_tmp) as (l_tmp_unk & Hnodup' & Hall_l).
     iExists (l_tmp_unk).

     iMod (monotone_revoke_keep _ _ (l_tmp_unk ++ la) with "[ $Hsts $Hr]")
       as "($ & $ & Hres & %)"; auto.
     {
       iPureIntro; intros k ka Hka; cbn.
       apply Hall_l.
       apply list_elem_of_lookup; eauto.
     }
     apply Forall_app in H as [? ?].
     iFrame "%".
     rewrite /close_list_resources.
     iDestruct (big_sepL_app with "Hres") as "[Hres Hres']".
     iAssert ( ▷ close_list_resources C W (l_tmp_unk) false )%I with "[Hres]" as "Hres" ; first (by iNext).
     rewrite -world_ghost_theory.RevokedResources_eq; iFrame.
     iModIntro.
     iSplit.
     { iPureIntro; split; auto. }
     iDestruct (revoked_stack_revoked _ _ la with "[$Hl] [$Hres']") as "H".
     rewrite -big_sepL_later.
     iAssert ( ∃ lv, ▷ ([∗ list] x;v ∈ la;lv, StackWorldResource interp W C x v ∗ x ↦ₐ v) )%I
               with "[H]" as "[% H]".
     { iClear "#".
       iStopProof.
       clear. subst la. generalize (finz.seq_between b e).
       induction l; iIntros "H"; cbn.
       { iExists []; done. }
       iDestruct "H" as "[ [%va Ha] H]".
       iDestruct (IHl with "H") as "[%lv IH]".
       iExists (va::lv); iFrame.
       }
     iDestruct (big_sepL2_sep with "H") as "[H $]"; iFrame.
     iNext. rewrite /StackRevokedResources.
     iApply StackWorldResources_zeros; eauto.
    - by rewrite length_replicate.
    - by apply Forall_replicate.
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
