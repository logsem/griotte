From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import sts_multiple_updates world_interp_revocation.
From griotte Require Import memory_region proofmode map_simpl register_tactics.
From griotte Require Export world_ghost_theory stack_world_resources.

Section WorldInterpStack.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    {cthreads : CmptThreads}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  #[local] Notation V := (interpO Σ).

  (*** World Interpretation for Safe Stack *)

  (** This file is part of the model.
      It proves some properties about the world in presence of a safe-to-share stack pointer.

     They are not meant to be understood or used by a Griotte user. *)

  (** The regions of a safe-to-share stack: Temporary keys of the local
      world, with the conditions of a stack predicate. *)
  #[local] Lemma interp_stack_rels W C g b e a :
    interp W C (Cap RWL g b e a) -∗
    [∗ list] a' ∈ finz.seq_between b e,
      ∃ (p' : Perm) (P : V),
        ⌜PermFlowsTo RWL p'⌝ ∗ ⌜persistent_cond P⌝ ∗
        (LNonHeap a') ↪ˡ[C]{p'} (safeC P) ∗
        ⌜std W !! LNonHeap a' = Some Temporary⌝ ∗
        mono_pub C (safeC P) ∗
        ▷ zcond P C ∗ ▷ rcond_l P C p' interp ∗ ▷ wcond_wl P C interp.
  Proof.
    iIntros "#Hinterp".
    (* A write-local capability is Local: a Global one is not valid. *)
    destruct g.
    { iEval (rewrite interp_unfold /=) in "Hinterp". done. }
    iDestruct (interp_WL_addr_key with "Hinterp") as %Hkeys; first done.
    iDestruct (write_allowed_inv_full_cap with "Hinterp") as "Hrels"; first done.
    iApply (big_sepL_impl with "Hrels"). iIntros "!> %k %x %Hx".
    rewrite Forall_lookup in Hkeys. rewrite (Hkeys _ _ Hx).
    iIntros "(%p' & %P & %Hfl & %Hpers & Hrel & Hz & Hrc & Hwc)".
    assert (readAllowed p' = true) as ->.
    { eapply readAllowed_flowsto; eauto. }
    rewrite /region_rel /=.
    iDestruct "Hrel" as "(Hrel & %HT & Hmono)".
    iExists p', P. by iFrame "∗%".
  Qed.

  (** A revoked stack, cleared, keeps its safety resources. *)
  #[local] Lemma stack_revoked_resources W C g b e a :
    interp W C (Cap RWL g b e a) -∗
    ▷ StackRevokedResources W C (finz.seq_between b e).
  Proof.
    iIntros "#Hinterp".
    iDestruct (interp_stack_rels with "Hinterp") as "Hrels".
    rewrite /StackRevokedResources /StackWorldResources big_sepL2_replicate_r; last done.
    rewrite big_sepL_later.
    iApply (big_sepL_impl with "Hrels"). iIntros "!> %k %x %Hx".
    iIntros "(%p' & %P & %Hfl & %Hpers & #Hrel & %HT & #Hmono & #Hz & #Hrc & #Hwc)".
    iNext. iExists P, p'. iFrame "#%".
    iSplit; [iApply "Hwc"; iApply interp_int|].
    iApply "Hmono".
  Qed.

  (** The cells of revoked non-heap keys. *)
  #[local] Lemma revoked_cells W C (l : list Addr) :
    RevokedResources W C (LNonHeap <$> l) -∗ [∗ list] a ∈ l, ∃ w, a ↦ₐ w.
  Proof.
    rewrite /RevokedResources big_sepL_fmap.
    iIntros "HR". iApply (big_sepL_mono with "HR").
    iIntros (k x Hx) "(%p & %φ & _ & _ & %v & _ & Hv & _)". by iExists v.
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

  (* Opening the world from a safe-to-share stack region gives [StackOpenWorldResources] *)
  Lemma region_open_list_interp_gen (W : WORLD) (C : CmptName)
    (la la' : list Addr) (g : Locality) (b e a : Addr) :
    NoDup la ->
    Forall (fun a' : Addr => (a' ∈ₐ [b, e)) ) la ->
    la ## la' ->

    interp W C (Cap RWL g b e a) ∗
    world_interp_open W C (LNonHeap <$> la')
    -∗
    world_interp_open W C (LNonHeap <$> (la++la')) ∗
    (∃ lv, ([∗ list] a;v ∈ la;lv, a ↦ₐ v) ∗
           ▷ StackOpenWorldResources interp W C la lv).
  Proof.
    induction la as [|a0 la IH]; intros Hnodup Hin Hdis;
      iIntros "(#Hinterp & Hr)"; cbn in * |- *.
    - iFrame. iExists []. rewrite /StackOpenWorldResources /StackWorldResources /=. done.
    - apply Forall_cons in Hin as [Hin_a0 Hin].
      apply NoDup_cons in Hnodup as [Hnotin Hnodup].
      pose proof (disjoint_cons _ _ _ Hdis) as Ha_notin_l'.
      eapply disjoint_weak in Hdis.
      iDestruct (IH with "[$Hinterp $Hr]") as "(Hr & %lv & Hlv & Hopen_res)"; [done..|].
      iDestruct (interp_stack_rels with "Hinterp") as "Hrels".
      iDestruct (big_sepL_elem_of with "Hrels")
        as "(%p' & %P & %Hfl & %Hpers & #Hrel & %HT & #Hmono & #Hz & #Hrc & #Hwc)".
      { by apply elem_of_finz_seq_between. }
      iDestruct (open_world_interp_temporary with "Hr Hrel") as "[Hr Hres]"; [|done|].
      { intros (x & Heq & Hx)%list_elem_of_fmap. simplify_eq.
        apply elem_of_app in Hx as [Hx|Hx]; [done|set_solver+Hx Ha_notin_l']. }
      iDestruct "Hres" as (v) "(_ & Hv & HP & Hfmono)".
      iSplitL "Hr".
      { iApply (world_interp_open_permutation with "Hr"). intros k. set_solver. }
      iExists (v :: lv). iFrame "Hv Hlv".
      iNext. iDestruct "Hopen_res" as "[Hres Hstates]".
      rewrite /StackOpenWorldResources /StackWorldResources /=.
      iFrame "Hres Hstates %". by iFrame "∗#".
  Qed.

  (* We can close the world using [StackOpenWorldResources] *)
  Lemma region_close_list_interp_gen (W : WORLD) (C : CmptName)
  (lv : list LWord)
  (la la' : list Addr):

    NoDup la ->
    la ## la' ->
    length lv = length la ->

    world_interp_open W C (LNonHeap <$> (la++la')) ∗
    ([∗ list] a;v ∈ la;lv, a ↦ₐ v) ∗
    StackOpenWorldResources interp W C la lv
    -∗
    world_interp_open W C (LNonHeap <$> la').
  Proof.
    revert lv. induction la as [|a0 la IH]; intros lv Hnodup Hdis Hlen_lv;
      iIntros "(Hr & Ha & [Hres Hstates])"; cbn in * |- *.
    - done.
    - destruct lv as [|v lv]; simplify_eq/=.
      iDestruct "Hres" as
        "[(%φ & %p & Hφ & #Hfmono & #Hrel & (#Hmono & #Hz & #Hrc & #Hwc & %Hpers) & %Hp) Hres]".
      iDestruct "Hstates" as "[%HT Hstates]".
      iDestruct "Ha" as "[Ha Hlv]".
      apply NoDup_cons in Hnodup as [Hnotin Hnodup].
      pose proof (disjoint_cons _ _ _ Hdis) as Ha_notin_l'.
      eapply disjoint_weak in Hdis.
      assert (∀ x, Persistent (safeC φ x)) as HpersL by (intros x; apply Hpers).
      iDestruct (close_world_interp_temporary W C (LNonHeap <$> (la ++ la')) (LNonHeap a0) p
                  (safeC φ) v with "[Hr] Hrel [Hφ Ha]") as "[Hr _]".
      { intros (x & Heq & Hx)%list_elem_of_fmap. simplify_eq.
        apply elem_of_app in Hx as [Hx|Hx]; [done|set_solver+Hx Ha_notin_l']. }
      { done. }
      { iApply (world_interp_open_permutation with "Hr"). intros k. set_solver. }
      { rewrite /TmpRes /=. iFrame "∗#".
        iPureIntro. by eapply notisO_flowsfrom. }
      iApply (IH with "[$Hr $Hlv $Hres $Hstates]"); eauto.
  Qed.

  (** The keys Temporary in [W]: the unknown ones, then a stack split into a
      closed part and an open part [ls]. *)
  #[local] Lemma stack_split_keys (l_unk : list LAddr) (la ls : list Addr) k :
    NoDup (l_unk ++ (LNonHeap <$> la)) → (∀ x, x ∈ ls → x ∈ la) →
    k ∈ l_unk ++ (LNonHeap <$> filter (λ x, x ∉ ls) la) ↔
    k ∈ l_unk ++ (LNonHeap <$> la) ∧ k ∉ LNonHeap <$> ls.
  Proof.
    intros Hnd Hsub. apply NoDup_app in Hnd as (_ & Hdisj & _).
    rewrite !elem_of_app !list_elem_of_fmap.
    split.
    - intros [Hk | (x & -> & Hx)].
      + split; [by left|]. intros (y & -> & Hy).
        apply (Hdisj _ Hk). apply list_elem_of_fmap. eauto.
      + apply list_elem_of_filter in Hx as [Hxls Hxla].
        split; [right; eauto|]. intros (y & Heq & Hy). injection Heq as <-. done.
    - intros [ [Hk | (x & -> & Hx)] Hn]; [by left|]. right. exists x. split; [done|].
      apply list_elem_of_filter. split; [|done]. intros Hxs. apply Hn. eauto.
  Qed.

  (* Revoke a stack region *)
  Lemma monotone_revoke_stack W C b e a :
    let la := finz.seq_between b e in

    interp W C (Cap RWL Local b e a) ∗
    world_interp W C
    ==∗
    ∃ l_unk_temp,
      ⌜ extract_temporaries_condition W (l_unk_temp ++ (LNonHeap <$> la)) ⌝ ∗
      world_interp (revoke W) C ∗
      ▷ StackRevokedResources W C la ∗
      ▷ ⌜Forall (λ a, std (revoke W) !! LNonHeap a = Some Revoked) la⌝ ∗
      ▷ (∃ stk_mem, [[ b , e ]] ↦ₐ [[ stk_mem ]]) ∗
      ▷ RevokedResources W C l_unk_temp ∗
      ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) l_unk_temp⌝.
  Proof.
    intros la.
    iIntros "(#Hinterp & Hw)".
    iDestruct (writeLocalAllowed_valid_cap_implies_full_cap_nonheap with "Hinterp")
      as "Htemps"; first done.
    iDestruct (big_sepL_forall with "Htemps") as %Htemps.
    assert (Forall (λ a, std W !! LNonHeap a = Some Temporary) la) as Hla_tmp.
    { apply Forall_lookup. exact Htemps. }
    assert (NoDup la) as Hla_nodup by apply finz_seq_between_NoDup.
    pose proof (extract_temps_split_world _ (LNonHeap <$> la)
                  (proj2 (NoDup_LNonHeap_fmap la) Hla_nodup)
                  (proj2 (Forall_fmap _ _ _) Hla_tmp))
      as (l_unk & Hnodup' & Hall).
    iMod (world_interp_revoke W C (l_unk ++ (LNonHeap <$> la)) with "Hw")
      as "(Hw & HR & %Hrev)"; first by split.
    apply Forall_app in Hrev as [Hrev_unk Hrev_la].
    apply Forall_fmap in Hrev_la.
    rewrite RevokedResources_app.
    iDestruct "HR" as "[HR_unk HR_la]".
    iModIntro. iExists l_unk. iFrame "Hw HR_unk".
    iSplit; [iPureIntro; by split|].
    iSplit; [by iApply stack_revoked_resources|].
    iSplit; [done|].
    iSplitL "HR_la"; [|done].
    iNext. rewrite /region_pointsto.
    iApply exists_pointsto_list. by iApply revoked_cells.
  Qed.

  (* Revoke a stack region, part of which ([bs, es)) has been opened: the
     open keys are revoked with the others, and closed in the revoked world,
     where their body is empty. *)
  Lemma monotone_revoke_stack_open {E : coPset} W C b e a bs es lv ws :
    let la := finz.seq_between b e in
    let ls := finz.seq_between bs es in
    (b <= bs)%a → (es <= e)%a →

    interp W C (Cap RWL Local b e a) ∗
    world_interp_open W C (LNonHeap <$> ls) ∗
    ▷ StackOpenWorldResources interp W C ls lv ∗
    [[ bs , es ]] ↦ₐ [[ ws ]]
    ={E}=∗
    ∃ l_unk_temp,
      ⌜ extract_temporaries_condition W (l_unk_temp ++ (LNonHeap <$> la)) ⌝ ∗
      world_interp (revoke W) C ∗
      ▷ StackRevokedResources W C la ∗
      ▷ ⌜Forall (λ a, std (revoke W) !! LNonHeap a = Some Revoked) la⌝ ∗
      ▷ (∃ stk_mem, [[ b , e ]] ↦ₐ [[ stk_mem ]]) ∗
      ▷ RevokedResources W C l_unk_temp ∗
      ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) l_unk_temp⌝.
  Proof.
    intros la ls Hbs Hes.
    iIntros "(#Hinterp & Hr & _ & Hslot)".
    iDestruct (writeLocalAllowed_valid_cap_implies_full_cap_nonheap with "Hinterp")
      as "Htemps"; first done.
    iDestruct (big_sepL_forall with "Htemps") as %Htemps.
    assert (Forall (λ a, std W !! LNonHeap a = Some Temporary) la) as Hla_tmp.
    { apply Forall_lookup. exact Htemps. }
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
      as (l_unk & Hnodup' & Hall).
    assert (Forall (λ x, std (revoke W) !! x = Some Revoked) (l_unk ++ (LNonHeap <$> la)))
      as Hrev_all.
    { apply extract_temporaries_condition_revoke. split; assumption. }
    apply Forall_app in Hrev_all as [Hrev_unk Hrev_la].
    apply Forall_fmap in Hrev_la.
    (* The open keys, and the Temporary keys outside them *)
    set (O := list_to_set (LNonHeap <$> ls) : gset LAddr).
    set (S := list_to_set (l_unk ++ (LNonHeap <$> lr)) : gset LAddr).
    assert (NoDup (l_unk ++ (LNonHeap <$> lr))) as Hnodup_S.
    { apply NoDup_app in Hnodup' as (Hnd1 & Hdisj & Hnd2).
      apply NoDup_app. split; [done|]. split.
      - intros k Hk Hk'. apply (Hdisj _ Hk).
        apply list_elem_of_fmap in Hk' as (x & -> & Hx).
        apply list_elem_of_fmap. exists x. split; [done|].
        by apply list_elem_of_filter in Hx as [_ Hx].
      - apply NoDup_fmap_2; [apply _|]. apply NoDup_filter, Hla_nodup. }
    assert (extract_T W O S) as HS.
    { intros k. rewrite /S /O !elem_of_list_to_set Hall.
      by apply stack_split_keys. }
    assert (∀ k, k ∈ LNonHeap <$> ls → std W !! k = Some Temporary) as Hls_T.
    { intros k (x & -> & Hx)%list_elem_of_fmap.
      eapply Forall_forall in Hla_tmp; [exact Hla_tmp|]. by apply Hls_la. }
    iEval (rewrite world_interp_open_eq) in "Hr".
    assert (open_perm W (LNonHeap <$> ls) = ∅) as ->.
    { apply set_eq. intros k. rewrite elem_of_open_perm. split; [|set_solver].
      intros [Hk HnT]. by apply Hls_T in Hk. }
    assert (open_l W (LNonHeap <$> ls) = O) as ->.
    { apply set_eq. intros k. rewrite elem_of_open_l /O elem_of_list_to_set.
      split; [tauto|]. intros Hk. split; [done|]. by apply Hls_T. }
    iDestruct "Hr" as "[Hg Hl]".
    iDestruct (l_revoke th W C O S HS with "Hl") as "[Hl HR]".
    (* The open keys are Revoked in [revoke W]: they close with no body. *)
    iAssert (local_region_map th (revoke W) C ∅) with "[Hl]" as "Hl".
    { iDestruct "Hl" as (M) "Hw". iNamed "Hw". iExists M. rewrite /local_region_map_M. iFrame "Hloc %".
      rewrite -(union_empty_r_L O).
      iApply (rmap_close_all _ _ _ ∅ O with "[] [] Hm"); [set_solver| |].
      - iIntros "!>" (k p φ Hk). rewrite /body_l.
        pose proof (revoke_not_Temporary W k) as HnT.
        destruct (std (revoke W) !! k) as [ [] | ]; done.
      - rewrite /O big_sepS_list_to_set; [|by apply NoDup_LNonHeap_fmap].
        rewrite big_sepL_fmap.
        iDestruct (interp_stack_rels with "Hinterp") as "Hrels".
        iApply big_sepL_intro. iIntros "!>" (i x Hx).
        iDestruct (big_sepL_elem_of with "Hrels") as "(%p' & %P & _ & %Hpers & #Hrel & _)".
        { apply Hls_la. by eapply list_elem_of_lookup_2. }
        iExists p', (safeC P). iSplit; [iPureIntro; intros ?; apply Hpers|].
        by rewrite -rel_l_eq. }
    rewrite /S -RevokedRes_list //. rewrite big_sepL_app.
    iDestruct "HR" as "[HR_unk HR_lr]".
    iModIntro. iExists l_unk.
    iSplit; [iPureIntro; by split|].
    iSplitL "Hg Hl".
    { rewrite world_interp_eq. iFrame. }
    iSplit; [by iApply stack_revoked_resources|].
    iSplit; [done|].
    iSplitR "HR_unk"; [|by iFrame].
    (* Every cell of the stack *)
    iDestruct (revoked_cells with "HR_lr") as "Hrest".
    iDestruct (pointsto_list_exists with "Hslot") as "Hslot".
    iAssert ([∗ list] a' ∈ la, ∃ w, a' ↦ₐ w)%I with "[Hrest Hslot]" as "Hstk".
    { rewrite Hperm_la big_sepL_app. iFrame. }
    iNext. rewrite /region_pointsto. by iApply exists_pointsto_list.
  Qed.

  (* Reinstate a stack region *)
  Lemma update_region_revoked_temp_pwl_multiple E W C la lv :
     NoDup la →
     Forall (eq (lword_of_word (WInt 0))) lv ->
     Forall (fun a => (std W) !! LNonHeap a = Some Revoked) la ->

     world_interp W C -∗
     StackRevokedResources W C la -∗
     ([∗ list] a;v ∈ la;lv, a ↦ₐ v)

     ={E}=∗

     world_interp (std_update_multiple W la Temporary) C.
   Proof.
     iIntros (Hnodup Hlv Hrev) "Hw #Hres Hl".
     iDestruct (big_sepL2_length with "Hl") as %Hlen.
     rewrite -(replicate_as_Forall_2 (lword_of_word (WInt 0)) (length la) lv); [|by rewrite Hlen|exact Hlv].
     rewrite -close_list_std_update_multiple_revoked //.
     iMod (world_interp_restore W C (LNonHeap <$> la) with "[$Hw Hl]") as "Hw";
       [|by iModIntro].
     rewrite /RevokedResources big_sepL_fmap.
     rewrite /StackRevokedResources /StackWorldResources !big_sepL2_replicate_r //.
     iDestruct (big_sepL_sep_2 with "Hres Hl") as "H".
     iApply (big_sepL_mono with "H").
     iIntros (k x Hx) "[(%φ & %p & Hφ & #Hfmono & #Hrel & (#Hmono & #Hz & #Hrc & #Hwc & %Hpers) & %Hp) Ha]".
     iExists p, (safeC φ). iSplit; [iPureIntro; intros ?; apply Hpers|].
     iFrame "Hrel". rewrite /temp_res /TmpRes /=. iExists _. iFrame "Ha".
     iSplit; [iPureIntro; by eapply notisO_flowsfrom|].
     iSplitL "Hφ"; [iNext; iApply "Hz"; iExact "Hφ"|].
     iNext. iApply "Hmono".
   Qed.

End WorldInterpStack.

Section WorldInterpStack.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    {cthreads : CmptThreads}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  #[local] Notation V := (interpO Σ).

  (*** World interpretation for stack region *)

  (** This file defines an interface to revoke and reinstate a stack region,
      using the knowledge that the stack region is safe-to-share. *)

  Lemma open_world_interp_opening_resources (W : WORLD) (C : CmptName)
    (la la' : list Addr) (g : Locality) (b e a : Addr) :
    NoDup la ->
    Forall (fun a' : Addr => (a' ∈ₐ [b, e)) ) la ->
    la ## la' ->

    interp W C (Cap RWL g b e a) ∗
    world_interp_open W C (LNonHeap <$> la')
    -∗

    world_interp_open W C (LNonHeap <$> (la++la')) ∗
    (∃ lv, ([∗ list] a;v ∈ la;lv, a ↦ₐ v) ∗
           ▷ StackOpenWorldResources interp W C la lv)
  .
  Proof.
    iIntros (???) "[#Hinterp Hr]".
    iApply (region_open_list_interp_gen with "[$Hinterp $Hr]"); eauto.
  Qed.

  Lemma close_world_interp_opening_resources (W : WORLD) (C : CmptName)
  (lv : list LWord)
  (la la' : list Addr):

    NoDup la ->
    la ## la' ->
    length lv = length la ->

    world_interp_open W C (LNonHeap <$> (la++la')) ∗
    ([∗ list] a;v ∈ la;lv, a ↦ₐ v) ∗
    StackOpenWorldResources interp W C la lv
    -∗
   world_interp_open W C (LNonHeap <$> la').
  Proof.
    iIntros (???) "H".
    iApply (region_close_list_interp_gen with "H"); eauto.
  Qed.

  Lemma world_interp_revoke_stack (W : WORLD) (C : CmptName) (b e a : Addr) :
    let la := finz.seq_between b e in

    interp W C (Cap RWL Local b e a) ∗
    world_interp W C
    ==∗
    ∃ l_unk_temp,
      ⌜ extract_temporaries_condition W (l_unk_temp ++ (LNonHeap <$> la)) ⌝ ∗
      world_interp (revoke W) C ∗
      ▷ StackRevokedResources W C la ∗
      ▷ ⌜Forall (λ a, std (revoke W) !! LNonHeap a = Some Revoked) la⌝ ∗
      ▷ (∃ stk_mem, [[ b , e ]] ↦ₐ [[ stk_mem ]]) ∗
      ▷ RevokedResources W C l_unk_temp ∗
      ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) l_unk_temp⌝.
  Proof.
    apply monotone_revoke_stack.
  Qed.

  (** Revoke a stack region, part of which ([bs, es]) has been opened: the
      open cells are revoked whatever they hold. *)
  Lemma world_interp_revoke_stack_open {E : coPset} (W : WORLD) (C : CmptName)
    (b e a bs es : Addr) (lv ws : list LWord) :
    let la := finz.seq_between b e in
    let ls := finz.seq_between bs es in
    (b <= bs)%a → (es <= e)%a →

    interp W C (Cap RWL Local b e a) ∗
    world_interp_open W C (LNonHeap <$> ls) ∗
    ▷ StackOpenWorldResources interp W C ls lv ∗
    [[ bs , es ]] ↦ₐ [[ ws ]]
    ={E}=∗
    ∃ l_unk_temp,
      ⌜ extract_temporaries_condition W (l_unk_temp ++ (LNonHeap <$> la)) ⌝ ∗
      world_interp (revoke W) C ∗
      ▷ StackRevokedResources W C la ∗
      ▷ ⌜Forall (λ a, std (revoke W) !! LNonHeap a = Some Revoked) la⌝ ∗
      ▷ (∃ stk_mem, [[ b , e ]] ↦ₐ [[ stk_mem ]]) ∗
      ▷ RevokedResources W C l_unk_temp ∗
      ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) l_unk_temp⌝.
  Proof.
    intros la ls Hbs Hes.
    by iApply monotone_revoke_stack_open.
  Qed.

  Lemma world_interp_reinstate_stack
    { E : coPset } (W : WORLD) (C : CmptName) (la : list Addr) (lv : list LWord) :
    NoDup la →
    Forall (eq (lword_of_word (WInt 0))) lv ->
    Forall (λ a, std W !! LNonHeap a = Some Revoked) la ->

    world_interp W C -∗
    StackRevokedResources W C la -∗
    ([∗ list] a;v ∈ la;lv,  a ↦ₐ v)

    ={E}=∗

    world_interp (std_update_multiple W la Temporary) C.
  Proof.
    iIntros (???) "Hw Hres Hl".
    by iApply (update_region_revoked_temp_pwl_multiple with "Hw Hres Hl").
  Qed.

End WorldInterpStack.
