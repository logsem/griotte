From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import sts_multiple_updates region_invariants_revocation.
From griotte Require Import memory_region proofmode map_simpl register_tactics.
From griotte Require Export world_ghost_theory stack_world_resources.

Section WorldInterpStack.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ} {relg : relGS Σ}
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

    interp W C (WCap true RWL g b e a) ∗
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
        iDestruct "Hinterp" as "[Hinterp _]".
        iDestruct (big_sepL_elem_of with "Hinterp") as "Ha".
        {  rewrite elem_of_finz_seq_between; eauto. }
        iDestruct "Ha" as "(%pa & %Pa & _ & _ & _ & _ & _ & _ & _ & %Hstate)".
        by rewrite Hstate in HWa; simplify_eq.
      }
      assert (isWL p' = true) as Hwl_p'; simplify_eq.
      { destruct p' as [ [] [] ]; cbn in *; auto. }
      iDestruct (sts_full_world_heap_wf with "Hsts") as %Hheap_wf.
      iDestruct (interp_cap_cell_live W C RWL g b e a a0 with "Hinterp") as %Hlive;
        [exact Hheap_wf|done|apply withinBounds_true_iff; solve_addr|].
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
    Forall (heap_cell_live (heap_std W)) la ->

    open_region_many W C (la++la') ∗
    ([∗ list] a;v ∈ la;lv, a ↦ₐ v) ∗
    StackOpenWorldResources interp W C la lv
    -∗
    open_region_many W C la'
  .
  Proof.
    generalize dependent lv.
    induction la; intros lv Hnodup Hdis Hlen_lv Hlive
    ; iIntros "(Hr & Ha & Hclose_res)"; cbn in * |- *.
    - by iFrame.
    - destruct lv as [| v lv ]; simplify_eq.
      cbn.
      iDestruct "Hclose_res" as "[ [(%Pa & %pa & HPa & Hmono & Hrel_a & Hvalid & %Hp) Hclose_res] [Hstd_a Hstates] ]".
      iDestruct "Ha" as "[Ha Hlv]".
      apply NoDup_cons in Hnodup; destruct Hnodup as [Hnotin Hnodup].
      apply Forall_cons in Hlive as [Hlive_a Hlive].
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

    interp W C (WCap true RWL Local b e a)
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

    iDestruct (sts_full_world_heap_wf with "Hsts") as %Hheap_wf.
    iDestruct (interp_cap_regions with "Hinterp") as %[_ Hcap_valid]; first done.
    assert (Forall (heap_cell_live (heap_std W)) la) as Hla_live.
    { apply Forall_forall. intros x Hx.
      eapply heap_cap_valid_cell_live; eauto.
      apply withinBounds_true_iff.
      apply elem_of_finz_seq_between in Hx. solve_addr. }

    pose proof (extract_temps_split_world _ la Hla_nodup Hla_tmp)
      as (l_tmp_unk & Hnodup' & Hall_l).
    assert (Forall (λ x, x ∈ dom (std W)) l_tmp_unk) as Hunk_dom.
    { apply Forall_forall. intros x Hx.
      rewrite elem_of_dom. exists Temporary.
      apply Hall_l. apply elem_of_app. left. exact Hx. }
    iDestruct (region_cells_status_some W C l_tmp_unk Hunk_dom with "Hr")
      as "[Hr %Hstatuses]".
    destruct (heap_status_partition (heap_std W) l_tmp_unk Hstatuses)
      as (l_live & l_q & Hperm & Hlive & Hqstatus).
    assert (Forall (λ x, std W !! x = Some Temporary) l_q) as Hqtemp.
    { apply Forall_forall. intros x Hx. apply Hall_l.
      apply elem_of_app. left. rewrite Hperm.
      apply elem_of_app. right. exact Hx. }
    assert (NoDup (l_live ++ la)) as Hnodup_rev.
    { apply NoDup_app. split.
      - apply NoDup_app in Hnodup' as [Hunk _].
        rewrite Hperm in Hunk.
        apply NoDup_app in Hunk as [Hlive_nodup _]. exact Hlive_nodup.
      - split.
        + intros x Hx Hxla.
          pose proof (proj1 (NoDup_app l_tmp_unk la) Hnodup') as Hsplit.
          destruct Hsplit as [Hunk Hrest]. destruct Hrest as [Hdisj Hla0].
          apply (Hdisj x);
            [rewrite Hperm; apply elem_of_app; left; exact Hx|exact Hxla].
        + exact Hla_nodup. }
    assert (Forall (heap_cell_live (heap_std W)) (l_live ++ la)) as Hlive_rev.
    { apply Forall_app. split; assumption. }
    assert (Forall (λ x, std W !! x = Some Temporary) (l_live ++ la)) as Htemp_rev.
    { apply Forall_app. split; last assumption.
      apply Forall_forall. intros x Hx. apply Hall_l.
      apply elem_of_app. left. rewrite Hperm.
      apply elem_of_app. left. exact Hx. }
    assert (Forall (λ x, std (revoke W) !! x = Some Revoked) (l_tmp_unk ++ la))
      as Hrev_all.
    { apply extract_temporaries_condition_revoke. split; assumption. }
    apply Forall_app in Hrev_all as [Hrev_unk Hrev_la].
    iMod (region_rels_get W C l_q Hqtemp with "[$Hr $Hsts]") as "(Hr & Hsts & Hq)".
    iMod (monotone_revoke_keep W C (l_live ++ la) Hlive_rev Hnodup_rev
      with "[$Hsts $Hr]") as "(Hsts & Hr & Hres & %Hrevoked_live)".
    { iPureIntro. rewrite Forall_lookup in Htemp_rev. exact Htemp_rev. }
    rewrite /close_list_resources.
    iDestruct (big_sepL_app with "Hres") as "[Hres_unk Hres_stk]".
    iAssert (▷ RevokedResources W C l_tmp_unk)%I with "[Hres_unk Hq]" as "Hunk".
    { iNext.
      rewrite (RevokedResources_partition W C l_tmp_unk l_live l_q Hperm Hlive Hqstatus).
      iFrame "Hq". iExact "Hres_unk". }
    iModIntro. iExists l_tmp_unk.
    iFrame "Hsts Hr Hunk". iFrame "%".
    iSplit.
    { iPureIntro; split; auto. }
    iDestruct (revoked_stack_revoked _ _ la with "[$Hl] [$Hres_stk]") as "H".
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
       assert (a ∈ dom (std W)) as Hdom_a.
       { rewrite elem_of_dom. eexists. exact Hrev_a. }
       iDestruct (region_cell_status_some W C a Hdom_a with "Hregion")
         as "[Hregion %Hstatus_some]".
       iMod (IHla with "Hworld Hregion Hres Hl") as "[Hregion Hworld]"; eauto.
       destruct Hstatus_some as [status Hstatus]. destruct status.
       + iDestruct (sts_full_world_heap_wf with "Hworld") as %Hheap_wf'.
         iDestruct ("Hmono" $! W (std_update_multiple W la Temporary) with "[] [] HP")
           as "Hφ".
         { iPureIntro. exact Hrelated. }
         { iPureIntro. exact Hheap_wf'. }
         iMod (update_region_revoked_temp_pwl with "Hmono Hworld Hregion Ha Hφ Hrel")
           as "[Hregion Hworld]".
         { exact Hpers. }
         { rewrite std_update_multiple_heap. exact Hstatus. }
         { rewrite std_sta_update_multiple_lookup_same_i; auto. }
         { eapply notisO_flowsfrom; eauto. }
         { exact Hp'. }
         by iFrame.
       + unfold heap_cell_status in Hstatus.
         destruct (is_heap_address a) eqn:Hheap; last discriminate.
         destruct (heap_lookup_addr (heap_std W) a) as [bo|] eqn:Hlookup;
           last discriminate.
         destruct bo as [base obj].
         simpl in Hstatus. injection Hstatus as Hobj.
         iMod (update_region_revoked_temp_quarantined_heap with "Hworld Hregion Hrel")
           as "[Hregion Hworld]".
         { exact Hheap. }
         { rewrite std_update_multiple_heap. exact Hlookup. }
         { exact Hobj. }
         { rewrite std_sta_update_multiple_lookup_same_i; auto. }
         by iFrame.
   Qed.

End WorldInterpStack.
