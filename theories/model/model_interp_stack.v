From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import sts_multiple_updates region_invariants_revocation.
From griotte Require Import memory_region proofmode map_simpl register_tactics.
From griotte Require Export world_ghost_theory stack_world_resources.

Section WorldInterpStack.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  #[local] Notation V := (interpO Σ).

  (*** World Interpretation for Safe Stack *)

  (** This file is part of the model.
      It proves some properties about the world in presence of a safe-to-share stack pointer.

     They are not meant to be understood or used by a Griotte user. *)

  (* Opening the world from a safe-to-share stack region gives [StackOpenWorldResources] *)
  Lemma region_open_list_interp_gen (W : WORLD) (C : CmptName)
    (la la' : list Addr) (g : Locality) (b e a : Addr) :
    NoDup la ->
    Forall (fun a' : Addr => (a' ∈ₐ [b, e)) ) la ->
    la ## la' ->

    interp W C (Cap RWL g b e a) ∗
    open_region_many W C (LNonHeap <$> la') ∗
    sts_full_world W C
    -∗
    open_region_many W C (LNonHeap <$> (la++la')) ∗
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
        rewrite interp_unfold /=.
        destruct g; auto.
        iDestruct "Hinterp" as "[Hinterp _]".
        iDestruct (big_sepL_elem_of with "Hinterp") as "Ha".
        {  rewrite elem_of_finz_seq_between; eauto. }
        iDestruct "Ha" as "(%pa & %Pa & _ & _ & _ & _ & _ & _ & _ & %Hstate)".
        by rewrite Hstate in HWa; simplify_eq.
      }
      assert (isWL p' = true) as Hwl_p'; simplify_eq.
      { destruct p' as [ [] [] ]; cbn in *; auto. }
      rewrite addr_key_None in HWa.
      iDestruct (region_open_next_temp_pwl with "[$Hr $Hrel_P $Hsts]") as "Ha"; eauto.
      {
        intros Hcontra.
        apply list_elem_of_fmap in Hcontra as (? & Heq & Hcontra).
        rewrite addr_key_None in Heq; simplify_eq.
        apply elem_of_app in Hcontra. destruct Hcontra as [Hcontra|Hcontra]
        ; [set_solver+Hcontra Hnotin|set_solver+Hcontra Ha_notin_l'].
      }
      iDestruct "Ha" as "(Hr & Hsts & Hsts_std_a & Hres_a)".
      iEval (rewrite addr_key_None heap_key_resource_nonheap) in "Hres_a".
      iDestruct "Hres_a" as (va) "(Hv_a & _ & #Hmono_a & Hφ_a)".
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
  (lv : list LWord)
  (la la' : list Addr):

    NoDup la ->
    la ## la' ->
    length lv = length la ->

    open_region_many W C (LNonHeap <$> (la++la')) ∗
    ([∗ list] a;v ∈ la;lv, a ↦ₐ v) ∗
    StackOpenWorldResources interp W C la lv
    -∗
    open_region_many W C (LNonHeap <$> la')
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
        apply list_elem_of_fmap in Hcontra as (? & Heq & Hcontra); simplify_eq.
        apply elem_of_app in Hcontra. destruct Hcontra as [Hcontra|Hcontra]
        ; [set_solver+Hcontra Hnotin|set_solver+Hcontra Ha_notin_l'].
      }
      { by apply isWL_nonO in Hwl_pa. }
      iDestruct (IHla with "[$Hr $Hclose_res $Hstates $Hlv]") as "IH"; eauto.
  Qed.


  #[local] Lemma submseteq_dom (l : list Addr) (Wstd_sta : gmap Addr region_type) :
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

  #[local] Lemma revoked_stack_revoked W C l' :
    ([∗ list] a' ∈ l',
       ⌜ std W !! LNonHeap a' = Some Temporary ⌝ ∗
       (
         ∃ (p' : Perm) (P:V),
           ⌜ PermFlowsTo RWL p'⌝
           ∗ ⌜persistent_cond P⌝
           ∗ rel C (LNonHeap a') p' (safeC P)
           ∗ ▷ zcond P C
           ∗ ▷ rcond P C p' interp
           ∗ (if writeAllowed p' then ▷ wcond P C interp else True)
           ∗ monoReq W C a' p' P
    )) -∗
    ([∗ list] y ∈ l', close_addr_resources C W (LNonHeap y) true)
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
      iDestruct (rel_agree C (LNonHeap a) (safeC P1) P2 with "[$Hrel_1 $Hrel_2]") as "[<- Heq]".
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

    interp W C (Cap RWL Local b e a)
    ∗ sts_full_world W C
    ∗ region W C
    ==∗
    ∃ l_unk_temp,
      ⌜ NoDup (l_unk_temp ++ (LNonHeap <$> la)) ∧
        (forall (a : LAddr), (std W) !! a = Some Temporary <->
           a ∈ (l_unk_temp ++ (LNonHeap <$> la)))⌝
      ∗ sts_full_world (revoke W) C
      ∗ region (revoke W) C
      ∗ ▷ StackRevokedResources W C la
      ∗ ▷ ⌜Forall (λ a, std (revoke W) !! LNonHeap a = Some Revoked) la⌝
      ∗ ▷ (∃ stk_mem, [[ b , e ]] ↦ₐ [[ stk_mem ]])
      ∗ ▷ RevokedResources W C l_unk_temp
      ∗ ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) l_unk_temp⌝.
  Proof.
    intros la.
     iIntros "(#Hinterp & Hsts & Hr)".
    iAssert (
       ([∗ list] a' ∈ la,
         ⌜(std W) !! LNonHeap a' = Some Temporary⌝ ∗
          (
            ∃ (p' : Perm) (P:V),
              ⌜ PermFlowsTo RWL p'⌝
              ∗ ⌜persistent_cond P⌝
              ∗ rel C (LNonHeap a') p' (safeC P)
              ∗ ▷ zcond P C
              ∗ ▷ rcond P C p' interp
              ∗ (if writeAllowed p' then ▷ wcond P C interp else True)
              ∗ monoReq W C a' p' P
          ))%I
      ) with "[Hinterp]" as "Hl".
    {
      iDestruct (interp_WL_addr_key with "Hinterp") as %Hkeys; first done.
      iDestruct (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp")
        as "Htemps"; first done.
      iDestruct (read_allowed_inv_full_cap with "Hinterp") as "Hrels"; first done.
      iApply big_sepL_sep. iSplitL "Htemps".
      - iApply (big_sepL_impl with "Htemps"). iIntros "!> %k %x %Hx".
        rewrite Forall_lookup in Hkeys. rewrite (Hkeys _ _ Hx). iIntros "$".
      - iApply (big_sepL_impl with "Hrels"). iIntros "!> %k %x %Hx".
        rewrite Forall_lookup in Hkeys. rewrite (Hkeys _ _ Hx). iIntros "$".
    }
    iAssert (⌜Forall (λ a, std W !! LNonHeap a = Some Temporary) la⌝)%I as %Hla_tmp.
    { iDestruct (big_sepL_sep with "Hl") as "[Htemps Hrel]".
      iDestruct (big_sepL_forall with "Htemps") as %Htemps.
      iPureIntro. apply Forall_lookup. done. }

    assert (NoDup la) as Hla_nodup by apply finz_seq_between_NoDup.

    pose proof (extract_temps_split_world _ (LNonHeap <$> la)
                  (proj2 (NoDup_LNonHeap_fmap la) Hla_nodup)
                  (proj2 (Forall_fmap _ _ _) Hla_tmp))
      as (l_tmp_unk & Hnodup' & Hall_l).
    assert (Forall (λ x, std W !! x = Some Temporary) (l_tmp_unk ++ (LNonHeap <$> la))) as Htemp_rev.
    { apply Forall_forall. intros x Hx. by apply Hall_l. }
    assert (Forall (λ x, std (revoke W) !! x = Some Revoked) (l_tmp_unk ++ (LNonHeap <$> la)))
      as Hrev_all.
    { apply extract_temporaries_condition_revoke. split; assumption. }
    apply Forall_app in Hrev_all as [Hrev_unk Hrev_la].
    apply Forall_fmap in Hrev_la.
    iMod (monotone_revoke_keep W C (l_tmp_unk ++ (LNonHeap <$> la)) Hnodup'
      with "[$Hsts $Hr]") as "(Hsts & Hr & Hres & %Hrevoked_all)".
    { iPureIntro. rewrite Forall_lookup in Htemp_rev. exact Htemp_rev. }
    rewrite /close_list_resources.
    iDestruct (big_sepL_app with "Hres") as "[Hres_unk Hres_stk]".
    rewrite big_sepL_fmap.
    iAssert (▷ RevokedResources W C l_tmp_unk)%I with "[Hres_unk]" as "Hunk".
    { rewrite RevokedResources_eq /close_list_resources big_sepL_later.
      iApply (big_sepL_impl with "Hres_unk").
      iIntros "!> %k %a' %Ha' Hres".
      rewrite /close_addr_resources /if_later_P.
      iDestruct "Hres" as (p φ Hpers) "(Htemp & #Hrel)".
      iExists p, φ. iFrame "Hrel". iSplitR; first done.
      destruct a' as [a'|a' ι]; cbn [heap_key_resource]; first done.
      iDestruct "Htemp" as "[Htemp|#Hq]"; [by iLeft|by iRight]. }
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

  (** [region_rels_get] for keys outside the open set. *)
  #[local] Lemma open_region_many_rels_get W C s l :
    Forall (λ a, std W !! a = Some Temporary ∧ a ∉ s) l ->
    open_region_many W C s ∗ sts_full_world W C
    ==∗
    open_region_many W C s ∗ sts_full_world W C ∗
    ([∗ list] a ∈ l,
      ∃ p Φ, ⌜∀ WCv, Persistent (Φ WCv)⌝ ∗ rel C a p Φ)%I.
  Proof.
    induction l as [|a l IH]; intros Hl.
    - iIntros "[$ $]". iModIntro. done.
    - apply Forall_cons in Hl as [ [Ha Hnin] Hl].
      iIntros "[Hr Hsts]".
      iMod (open_region_many_rel_get with "[$Hr $Hsts]") as "(Hr & Hsts & Hrel)"; [done|done|].
      iMod (IH Hl with "[$Hr $Hsts]") as "(Hr & Hsts & Hrels)".
      iModIntro. iFrame.
  Qed.

  #[local] Lemma pointsto_list_exists (l : list Addr) (ws : list LWord) :
    ([∗ list] a;w ∈ l;ws, a ↦ₐ w) -∗ [∗ list] a ∈ l, ∃ w, a ↦ₐ w.
  Proof.
    iIntros "Hl". iInduction l as [|a l] "IH" forall (ws); first done.
    destruct ws as [|w ws]; first done.
    iDestruct "Hl" as "[Ha Hl]". iSplitL "Ha"; first by iExists w.
    iApply ("IH" with "Hl").
  Qed.

  #[local] Lemma exists_pointsto_list (l : list Addr) :
    ([∗ list] a ∈ l, ∃ w, a ↦ₐ w) -∗ ∃ ws, [∗ list] a;w ∈ l;ws, a ↦ₐ w.
  Proof.
    iIntros "Hl". iInduction l as [|a l] "IH"; first by iExists [].
    iDestruct "Hl" as "[ [%w Ha] Hl]".
    iDestruct ("IH" with "Hl") as (ws) "Hl".
    iExists (w :: ws). iFrame.
  Qed.

  (* Revoke a stack region, part of which ([bs, es)) has been opened *)
  Lemma monotone_revoke_stack_open W C b e a bs es lv ws :
    let la := finz.seq_between b e in
    let ls := finz.seq_between bs es in
    (b <= bs)%a → (es <= e)%a →

    interp W C (Cap RWL Local b e a)
    ∗ sts_full_world W C
    ∗ open_region_many W C (LNonHeap <$> ls)
    ∗ ▷ StackWorldResources interp W C ls lv
    ∗ ([∗ list] a' ∈ ls, sts_state_std C (LNonHeap a') Temporary)
    ∗ [[ bs , es ]] ↦ₐ [[ ws ]]
    ==∗
    ∃ l_unk_temp,
      ⌜ NoDup (l_unk_temp ++ (LNonHeap <$> la)) ∧
        (forall (a : LAddr), (std W) !! a = Some Temporary <->
           a ∈ (l_unk_temp ++ (LNonHeap <$> la)))⌝
      ∗ sts_full_world (revoke W) C
      ∗ region (revoke W) C
      ∗ ▷ StackRevokedResources W C la
      ∗ ▷ ⌜Forall (λ a, std (revoke W) !! LNonHeap a = Some Revoked) la⌝
      ∗ ▷ (∃ stk_mem, [[ b , e ]] ↦ₐ [[ stk_mem ]])
      ∗ ▷ RevokedResources W C l_unk_temp
      ∗ ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) l_unk_temp⌝.
  Proof.
    intros la ls Hbs Hes.
    iIntros "(#Hinterp & Hsts & Hr & Hslot_res & Hslot_states & Hslot)".
    iAssert (
       ([∗ list] a' ∈ la,
         ⌜(std W) !! LNonHeap a' = Some Temporary⌝ ∗
          (
            ∃ (p' : Perm) (P:V),
              ⌜ PermFlowsTo RWL p'⌝
              ∗ ⌜persistent_cond P⌝
              ∗ rel C (LNonHeap a') p' (safeC P)
              ∗ ▷ zcond P C
              ∗ ▷ rcond P C p' interp
              ∗ (if writeAllowed p' then ▷ wcond P C interp else True)
              ∗ monoReq W C a' p' P
          ))%I
      ) with "[Hinterp]" as "Hl".
    {
      iDestruct (interp_WL_addr_key with "Hinterp") as %Hkeys; first done.
      iDestruct (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp")
        as "Htemps"; first done.
      iDestruct (read_allowed_inv_full_cap with "Hinterp") as "Hrels"; first done.
      iApply big_sepL_sep. iSplitL "Htemps".
      - iApply (big_sepL_impl with "Htemps"). iIntros "!> %k %x %Hx".
        rewrite Forall_lookup in Hkeys. rewrite (Hkeys _ _ Hx). iIntros "$".
      - iApply (big_sepL_impl with "Hrels"). iIntros "!> %k %x %Hx".
        rewrite Forall_lookup in Hkeys. rewrite (Hkeys _ _ Hx). iIntros "$".
    }
    iAssert (⌜Forall (λ a, std W !! LNonHeap a = Some Temporary) la⌝)%I as %Hla_tmp.
    { iDestruct (big_sepL_sep with "Hl") as "[Htemps Hrel]".
      iDestruct (big_sepL_forall with "Htemps") as %Htemps.
      iPureIntro. apply Forall_lookup. done. }

    assert (NoDup la) as Hla_nodup by apply finz_seq_between_NoDup.
    assert (NoDup ls) as Hls_nodup by apply finz_seq_between_NoDup.
    assert (∀ x, x ∈ ls → x ∈ la) as Hls_la.
    { intros x Hx. apply elem_of_finz_seq_between in Hx.
      apply elem_of_finz_seq_between. solve_addr. }
    (* The stack outside the open part *)
    set (lr := filter (λ x, x ∉ ls) la).
    assert (la ≡ₚ lr ++ ls) as Hperm_la.
    { rewrite -{1}(filter_app_complement (λ x, x ∉ ls) la).
      f_equiv; first done.
      apply NoDup_Permutation.
      - apply NoDup_filter, Hla_nodup.
      - exact Hls_nodup.
      - intros x. rewrite list_elem_of_filter. split.
        + intros [Hx _]. by apply dec_stable in Hx.
        + intros Hx. split; [by intros Hn|by apply Hls_la]. }

    pose proof (extract_temps_split_world _ (LNonHeap <$> la)
                  (proj2 (NoDup_LNonHeap_fmap la) Hla_nodup)
                  (proj2 (Forall_fmap _ _ _) Hla_tmp))
      as (l_tmp_unk & Hnodup' & Hall_l).
    assert ((l_tmp_unk ++ (LNonHeap <$> lr)) ++ (LNonHeap <$> ls)
              ≡ₚ l_tmp_unk ++ (LNonHeap <$> la)) as Hperm_keys.
    { by rewrite -app_assoc -fmap_app -Hperm_la. }
    assert (Forall (λ x, std W !! x = Some Temporary) (l_tmp_unk ++ (LNonHeap <$> la))) as Htemp_rev.
    { apply Forall_forall. intros x Hx. by apply Hall_l. }
    assert (Forall (λ x, std (revoke W) !! x = Some Revoked) (l_tmp_unk ++ (LNonHeap <$> la)))
      as Hrev_all.
    { apply extract_temporaries_condition_revoke. split; assumption. }
    apply Forall_app in Hrev_all as [Hrev_unk Hrev_la].
    apply Forall_fmap in Hrev_la.
    (* Split the stack facts into the rest and the open part *)
    iEval (rewrite Hperm_la) in "Hl".
    iDestruct (big_sepL_app with "Hl") as "[Hl_rest Hl_slot]".
    iAssert ([∗ list] k ∈ LNonHeap <$> ls,
               ∃ p φ, ⌜∀ WCv, Persistent (φ WCv)⌝ ∗
                      rel C k p φ ∗ sts_state_std C k Temporary)%I
      with "[Hl_slot Hslot_states]" as "Hslot_keys".
    { rewrite big_sepL_fmap.
      iDestruct (big_sepL_sep_2 with "Hl_slot Hslot_states") as "Hslot_pairs".
      iApply (big_sepL_mono with "Hslot_pairs").
      iIntros (i x Hx) "[ (_ & %p' & %P & _ & %Hpers & #Hrel & _) Hstate]".
      iExists p', (safeC P). iFrame "Hrel Hstate".
      iPureIntro. intros WCv. apply Hpers. }
    iMod (monotone_revoke_keep_open W C (l_tmp_unk ++ (LNonHeap <$> lr)) (LNonHeap <$> ls)
      with "[$Hsts $Hr $Hslot_keys]") as "(Hsts & Hr & Hres & _)".
    { by rewrite Hperm_keys. }
    { iPureIntro.
      rewrite -Hperm_keys in Htemp_rev.
      apply Forall_app in Htemp_rev as [Htemp_rev _].
      by apply Forall_lookup. }
    rewrite /close_list_resources.
    iDestruct (big_sepL_app with "Hres") as "[Hres_unk Hres_stk]".
    rewrite big_sepL_fmap.
    iAssert (▷ RevokedResources W C l_tmp_unk)%I with "[Hres_unk]" as "Hunk".
    { rewrite RevokedResources_eq /close_list_resources big_sepL_later.
      iApply (big_sepL_impl with "Hres_unk").
      iIntros "!> %k %a' %Ha' Hres".
      rewrite /close_addr_resources /if_later_P.
      iDestruct "Hres" as (p φ Hpers) "(Htemp & #Hrel)".
      iExists p, φ. iFrame "Hrel". iSplitR; first done.
      destruct a' as [a'|a' ι]; cbn [heap_key_resource]; first done.
      iDestruct "Htemp" as "[Htemp|#Hq]"; [by iLeft|by iRight]. }
    iModIntro. iExists l_tmp_unk.
    iFrame "Hsts Hr Hunk". iFrame "%".
    iSplit.
    { iPureIntro; split; auto. }
    (* Every cell of the stack, with its contents zeroed *)
    iDestruct (revoked_stack_revoked _ _ lr with "[$Hl_rest] [$Hres_stk]") as "Hrest".
    iAssert ([∗ list] a' ∈ lr ++ ls,
               ▷ StackWorldResource interp W C a' (WInt 0) ∗ ▷ (∃ w, a' ↦ₐ w))%I
      with "[Hrest Hslot_res Hslot]" as "Hstk".
    { iApply big_sepL_app. iSplitL "Hrest".
      - iApply (big_sepL_mono with "Hrest").
        iIntros (i x Hx) "(%w & Hres & Hcell)".
        iSplitL "Hres"; iNext; [by iApply StackWorldResource_zero|by iExists w].
      - iDestruct (pointsto_list_exists with "Hslot") as "Hslot".
        iAssert (▷ StackWorldResources interp W C ls
                   (replicate (length ls) (lword_of_word (WInt 0))))%I
          with "[Hslot_res]" as "Hslot_res".
        { iNext. iApply (StackWorldResources_zeros with "Hslot_res").
          - by rewrite length_replicate.
          - by apply Forall_replicate. }
        rewrite /StackWorldResources big_sepL2_replicate_r; last done.
        rewrite big_sepL_later.
        iApply (big_sepL_sep_2 with "Hslot_res").
        iApply (big_sepL_mono with "Hslot"). iIntros (i x Hx) "Hcell". by iNext. }
    iEval (rewrite -Hperm_la) in "Hstk".
    iDestruct (big_sepL_sep with "Hstk") as "[Hstk_res Hstk_mem]".
    rewrite -!big_sepL_later.
    iSplitL "Hstk_res".
    { iNext. rewrite /StackRevokedResources /StackWorldResources.
      rewrite big_sepL2_replicate_r; last done. iFrame. }
    iNext. iApply (exists_pointsto_list with "Hstk_mem").
  Qed.

  (* Reinstate a stack region *)
  Lemma update_region_revoked_temp_pwl_multiple E W C la lv :
     NoDup la →
     Forall (eq (lword_of_word (WInt 0))) lv ->
     Forall (fun a => (std W) !! LNonHeap a = Some Revoked) la ->

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
       ; pose proof (Hpers (W,C, lword_of_word (WInt 0)))
       ; iDestruct "HP" as "#HP".
       rewrite mono_temporary_eq.
       opose proof (isWL_flowsto _ _ Hp _) as Hp'; first done.
       rewrite Hp'.
       iMod (IHla with "Hworld Hregion Hres Hl") as "[Hregion Hworld]"; eauto.
       iDestruct ("Hmono" $! W (std_update_multiple W la Temporary) with "[] HP")
         as "Hφ".
       { iPureIntro. exact Hrelated. }
       iMod (update_region_revoked_temp_pwl _ _ _ (LNonHeap a) with "Hmono Hworld Hregion Ha Hφ Hrel")
         as "[Hregion Hworld]".
       { exact Hpers. }
       { rewrite std_sta_update_multiple_lookup_same_i; auto. }
       { eapply notisO_flowsfrom; eauto. }
       { exact Hp'. }
       by iFrame.
   Qed.

End WorldInterpStack.
