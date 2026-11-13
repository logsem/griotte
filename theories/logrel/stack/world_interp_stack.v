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
    {CL : ∀ t, CritLink Σ t}
    `{MP: MachineParameters}
    {CR : ∀ t, CritRoute Σ t (CL t)}
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
    iDestruct (interp_cap_disjoint_wl with "Hinterp") as %[Hmmio _]; first done.
    iDestruct (write_allowed_inv_full_cap with "Hinterp") as "Hrels";
      [done | by apply disjoint_from_mmio_exposed |].
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
    RevokedResources W C (LNonHeap <$> l) -∗ [∗ list] a ∈ l, ∃ w, stack_cell a w.
  Proof.
    rewrite /RevokedResources big_sepL_fmap.
    iIntros "HR". iApply (big_sepL_mono with "HR").
    iIntros (k x Hx) "(%p & %φ & _ & _ & %v & _ & Hv & _)".
    iExists v. by rewrite stack_cell_temp_cell.
  Qed.

  #[local] Lemma pointsto_list_exists (l : list Addr) (ws : list LWord) :
    ([∗ list] a;w ∈ l;ws, stack_cell a w) -∗ [∗ list] a ∈ l, ∃ w, stack_cell a w.
  Proof.
    iIntros "Hl". iInduction l as [|a l] "IH" forall (ws); first done.
    destruct ws as [|w ws]; first done.
    iDestruct "Hl" as "[Ha Hl]". iSplitL "Ha"; first by iExists w.
    iApply ("IH" with "Hl").
  Qed.

  #[local] Lemma exists_pointsto_list (l : list Addr) :
    ([∗ list] a ∈ l, ∃ w, stack_cell a w) -∗ ∃ ws, [∗ list] a;w ∈ l;ws, stack_cell a w.
  Proof.
    iIntros "Hl". iInduction l as [|a l] "IH"; first by iExists [].
    iDestruct "Hl" as "[ [%w Ha] Hl]".
    iDestruct ("IH" with "Hl") as (ws) "Hl".
    iExists (w :: ws). iFrame.
  Qed.

  (** The cells of a safe-to-share stack are Temporary keys. *)
  #[local] Lemma interp_stack_temporary_list W C g b e a (la : list Addr) :
    Forall (λ a', (a' ∈ₐ [b, e))) la →
    interp W C (Cap RWL g b e a) -∗
    ⌜Forall (λ a', std W !! LNonHeap a' = Some Temporary) la⌝.
  Proof.
    iIntros (Hin) "#Hinterp".
    iDestruct (writeLocalAllowed_valid_cap_implies_full_cap_nonheap with "Hinterp")
      as "Htemps"; first done.
    iDestruct (big_sepL_forall with "Htemps") as %Htemps.
    iPureIntro. eapply Forall_impl; [exact Hin|]. intros x Hx.
    apply elem_of_finz_seq_between, list_elem_of_lookup_1 in Hx as [i Hi].
    by eapply Htemps.
  Qed.

  (** Opening the local map on a safe-to-share stack region gives
      [StackOpenWorldResources]. *)
  Lemma local_open_stack (W : WORLD) (C : CmptName)
    (la la' : list Addr) (g : Locality) (b e a : Addr) :
    NoDup la ->
    Forall (fun a' : Addr => (a' ∈ₐ [b, e)) ) la ->
    la ## la' ->

    interp W C (Cap RWL g b e a) ∗
    local_region_map th W C (open_l W (LNonHeap <$> la'))
    -∗
    local_region_map th W C (open_l W (LNonHeap <$> (la++la'))) ∗
    (∃ lv, ([∗ list] a;v ∈ la;lv, temp_cell th (LNonHeap a) v) ∗
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
      rewrite open_l_cons_T //.
      iDestruct (l_open_transport with "Hr Hrel") as "[$ Hres]"; [|done|].
      { intros ((x & Heq & Hx)%list_elem_of_fmap & _)%elem_of_open_l. simplify_eq.
        apply elem_of_app in Hx as [Hx|Hx]; [done|set_solver+Hx Ha_notin_l']. }
      iDestruct "Hres" as (v) "(_ & Hv & HP & Hfmono)".
      iExists (v :: lv). iFrame "Hv Hlv".
      iNext. iDestruct "Hopen_res" as "[Hres Hstates]".
      rewrite /StackOpenWorldResources /StackWorldResources /=.
      iFrame "Hres Hstates %". by iFrame "∗#".
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
    (∃ lv, ([∗ list] a;v ∈ la;lv, temp_cell th (LNonHeap a) v) ∗
           ▷ StackOpenWorldResources interp W C la lv).
  Proof.
    iIntros (Hnodup Hin Hdis) "(#Hinterp & Hr)".
    iDestruct (interp_stack_temporary_list with "Hinterp") as %HT; [exact Hin|].
    rewrite !world_interp_open_eq open_perm_app_temporary //.
    iDestruct "Hr" as "[$ Hr]".
    iApply (local_open_stack with "[$Hinterp $Hr]"); done.
  Qed.

  (** Closing a stack opened in the local map. *)
  Lemma local_close_stack (W : WORLD) (C : CmptName)
    (lv : list LWord) (la la' : list Addr) :
    NoDup la ->
    la ## la' ->
    length lv = length la ->

    local_region_map th W C (open_l W (LNonHeap <$> (la++la'))) ∗
    ([∗ list] a;v ∈ la;lv, temp_cell th (LNonHeap a) v) ∗
    StackOpenWorldResources interp W C la lv
    -∗
    local_region_map th W C (open_l W (LNonHeap <$> la')).
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
      rewrite open_l_cons_T //.
      iDestruct (l_close th W C _ (LNonHeap a0) p (safeC φ) with "Hr Hrel [Hφ Ha]") as "Hr".
      { intros ((x & Heq & Hx)%list_elem_of_fmap & _)%elem_of_open_l. simplify_eq.
        apply elem_of_app in Hx as [Hx|Hx]; [done|set_solver+Hx Ha_notin_l']. }
      { done. }
      { intros x. apply Hpers. }
      { iApply heap_key_resource_intro. iExists v. rewrite /TmpRes /=. iFrame "∗#".
        iPureIntro. by eapply notisO_flowsfrom. }
      iApply (IH with "[$Hr $Hlv $Hres $Hstates]"); eauto.
  Qed.

  (* We can close the world using [StackOpenWorldResources] *)
  Lemma region_close_list_interp_gen (W : WORLD) (C : CmptName)
  (lv : list LWord)
  (la la' : list Addr):

    NoDup la ->
    la ## la' ->
    length lv = length la ->

    world_interp_open W C (LNonHeap <$> (la++la')) ∗
    ([∗ list] a;v ∈ la;lv, temp_cell th (LNonHeap a) v) ∗
    StackOpenWorldResources interp W C la lv
    -∗
    world_interp_open W C (LNonHeap <$> la').
  Proof.
    iIntros (Hnodup Hdis Hlen_lv) "(Hr & Ha & [Hres #Hstates])".
    iDestruct (big_sepL_forall with "Hstates") as %HT.
    rewrite !world_interp_open_eq open_perm_app_temporary; last by apply Forall_lookup.
    iDestruct "Hr" as "[$ Hr]".
    iApply (local_close_stack with "[$Hr $Ha $Hres $Hstates]"); done.
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

  (* Revoke a stack region in the local map *)
  Lemma local_revoke_stack W C b e a :
    let la := finz.seq_between b e in

    interp W C (Cap RWL Local b e a) ∗
    local_region_map th W C ∅
    ==∗
    ∃ l_unk_temp,
      ⌜ extract_temporaries_condition W (l_unk_temp ++ (LNonHeap <$> la)) ⌝ ∗
      local_region_map th (revoke W) C ∅ ∗
      ▷ StackRevokedResources W C la ∗
      ▷ ⌜Forall (λ a, std (revoke W) !! LNonHeap a = Some Revoked) la⌝ ∗
      ▷ (∃ stk_mem, stack_region b e stk_mem) ∗
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
    iMod (local_revoke W C (l_unk ++ (LNonHeap <$> la)) with "Hw")
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
    iNext. rewrite /stack_region.
    iApply exists_pointsto_list. by iApply revoked_cells.
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
      ▷ (∃ stk_mem, stack_region b e stk_mem) ∗
      ▷ RevokedResources W C l_unk_temp ∗
      ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) l_unk_temp⌝.
  Proof.
    intros la.
    iIntros "(#Hinterp & Hw)".
    rewrite world_interp_eq. iDestruct "Hw" as "[Hg Hl]".
    iMod (local_revoke_stack with "[$Hinterp $Hl]") as (l_unk) "(%Hext & Hl & Hrest)".
    iModIntro. iExists l_unk. rewrite world_interp_eq. by iFrame "∗%".
  Qed.

  (** Revoke a stack region in the local map, part of which ($[bs, es)$) has
      been opened: the open keys are revoked with the others, and closed in
      the revoked world, where their body is empty. *)
  Lemma local_revoke_stack_open {E : coPset} W C b e a bs es lv ws :
    let la := finz.seq_between b e in
    let ls := finz.seq_between bs es in
    (b <= bs)%a → (es <= e)%a →

    interp W C (Cap RWL Local b e a) ∗
    local_region_map th W C (open_l W (LNonHeap <$> ls)) ∗
    ▷ StackOpenWorldResources interp W C ls lv ∗
    stack_region bs es ws
    ={E}=∗
    ∃ l_unk_temp,
      ⌜ extract_temporaries_condition W (l_unk_temp ++ (LNonHeap <$> la)) ⌝ ∗
      local_region_map th (revoke W) C ∅ ∗
      ▷ StackRevokedResources W C la ∗
      ▷ ⌜Forall (λ a, std (revoke W) !! LNonHeap a = Some Revoked) la⌝ ∗
      ▷ (∃ stk_mem, stack_region b e stk_mem) ∗
      ▷ RevokedResources W C l_unk_temp ∗
      ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) l_unk_temp⌝.
  Proof.
    intros la ls Hbs Hes.
    iIntros "(#Hinterp & Hl & _ & Hslot)".
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
    assert (open_l W (LNonHeap <$> ls) = O) as ->.
    { apply set_eq. intros k. rewrite elem_of_open_l /O elem_of_list_to_set.
      split; [tauto|]. intros Hk. split; [done|]. by apply Hls_T. }
    iDestruct (l_revoke th W C O S HS with "Hl") as "[Hl HR]".
    (* The open keys are Revoked in [revoke W]: they close with no body. *)
    iAssert (local_region_map th (revoke W) C ∅) with "[Hl]" as "Hl".
    { iDestruct "Hl" as (M) "Hw". iNamed "Hw". iExists M. rewrite /local_region_map_M.
      iFrame "Hloc %".
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
    iFrame "Hl".
    iSplit; [by iApply stack_revoked_resources|].
    iSplit; [done|].
    iSplitR "HR_unk"; [|by iFrame].
    (* Every cell of the stack *)
    iDestruct (revoked_cells with "HR_lr") as "Hrest".
    iDestruct (pointsto_list_exists with "Hslot") as "Hslot".
    iAssert ([∗ list] a' ∈ la, ∃ w, stack_cell a' w)%I with "[Hrest Hslot]" as "Hstk".
    { rewrite Hperm_la big_sepL_app. iFrame. }
    iNext. rewrite /stack_region. by iApply exists_pointsto_list.
  Qed.

  (* Revoke a stack region, part of which ($[bs, es)$) has been opened: the
     open keys are revoked with the others, and closed in the revoked world,
     where their body is empty. *)
  Lemma monotone_revoke_stack_open {E : coPset} W C b e a bs es lv ws :
    let la := finz.seq_between b e in
    let ls := finz.seq_between bs es in
    (b <= bs)%a → (es <= e)%a →

    interp W C (Cap RWL Local b e a) ∗
    world_interp_open W C (LNonHeap <$> ls) ∗
    ▷ StackOpenWorldResources interp W C ls lv ∗
    stack_region bs es ws
    ={E}=∗
    ∃ l_unk_temp,
      ⌜ extract_temporaries_condition W (l_unk_temp ++ (LNonHeap <$> la)) ⌝ ∗
      world_interp (revoke W) C ∗
      ▷ StackRevokedResources W C la ∗
      ▷ ⌜Forall (λ a, std (revoke W) !! LNonHeap a = Some Revoked) la⌝ ∗
      ▷ (∃ stk_mem, stack_region b e stk_mem) ∗
      ▷ RevokedResources W C l_unk_temp ∗
      ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) l_unk_temp⌝.
  Proof.
    intros la ls Hbs Hes.
    iIntros "(#Hinterp & Hr & Hres & Hslot)".
    iDestruct (interp_stack_temporary_list _ _ _ _ _ _ ls with "Hinterp") as %HT.
    { apply Forall_forall. intros x Hx%elem_of_finz_seq_between. solve_addr. }
    rewrite world_interp_open_temporary_split; last by apply Forall_fmap.
    iDestruct "Hr" as "[Hg Hl]".
    iMod (local_revoke_stack_open with "[$Hinterp $Hl $Hres $Hslot]")
      as (l_unk) "(%Hext & Hl & Hrest)"; [done..|].
    iModIntro. iExists l_unk. rewrite world_interp_eq. by iFrame "∗%".
  Qed.

  (** Reinstate a stack region in the local map. *)
  Lemma local_reinstate_stack {E : coPset} W C la lv :
     NoDup la →
     Forall lword_int lv ->
     Forall (fun a => (std W) !! LNonHeap a = Some Revoked) la ->

     local_region_map th W C ∅ -∗
     StackRevokedResources W C la -∗
     ([∗ list] a;v ∈ la;lv, temp_cell th (LNonHeap a) v)

     ={E}=∗

     local_region_map th (std_update_multiple W la Temporary) C ∅.
   Proof.
     iIntros (Hnodup Hlv Hrev) "Hw #Hres Hl".
     iDestruct (big_sepL2_length with "Hl") as %Hlen.
     iDestruct (StackWorldResources_zeros W C la _ lv with "Hres") as "#Hres_lv";
       [done | exact Hlv |].
     rewrite -close_list_std_update_multiple_revoked //.
     iMod (local_restore W C (LNonHeap <$> la) with "[$Hw Hl]") as "Hw";
       [|by iModIntro].
     rewrite /RevokedResources big_sepL_fmap.
     rewrite /StackWorldResources.
     iDestruct (big_sepL2_sep_2 with "Hres_lv Hl") as "H".
     iAssert ([∗ list] y;_ ∈ la;lv, RevokedRes1 th (close_list (LNonHeap <$> la) W) C (LNonHeap y))%I
       with "[H]" as "H".
     { iApply (big_sepL2_mono with "H").
       iIntros (k x v Hx Hv) "[(%φ & %p & Hφ & #Hfmono & #Hrel & (#Hmono & #Hz & #Hrc & #Hwc & %Hpers) & %Hp) Ha]".
       destruct (Forall_lookup_1 _ _ _ _ Hlv Hv) as [z ->].
       iExists p, (safeC φ). iSplit; [iPureIntro; intros ?; apply Hpers|].
       iFrame "Hrel". rewrite /temp_res /TmpRes /=. iExists _. iFrame "Ha".
       iSplit; [iPureIntro; by eapply notisO_flowsfrom|].
       iSplitL "Hφ"; [iNext; iApply "Hz"; iExact "Hφ"|].
       iNext. iApply "Hmono". }
     rewrite big_sepL2_const_sepL_l. iDestruct "H" as "[_ $]".
   Qed.

  (** Owning the cells of a stack region forces its keys Revoked in the
      local map. *)
  Lemma local_revoked_by_stack_region (W : WORLD) (C : CmptName)
    (b e : Addr) (ws : list LWord) :
    Forall (λ a, LNonHeap a ∈ dom (std W)) (finz.seq_between b e) →
    local_region_map th W C ∅ ∗ stack_region b e ws
    ==∗
    local_region_map th W C ∅ ∗ stack_region b e ws ∗
    ⌜ Forall (λ a, std W !! LNonHeap a = Some Revoked) (finz.seq_between b e) ⌝.
  Proof.
    rewrite /stack_region. generalize (finz.seq_between b e) as la. intros la.
    revert ws. induction la as [|a la IH]; iIntros (ws Hdom) "[Hw Hl]".
    - iFrame. iPureIntro. constructor.
    - iDestruct (big_sepL2_cons_inv_l with "Hl") as (w ws' ->) "[Ha Hl]".
      apply Forall_cons in Hdom as [Ha Hdom].
      iMod (IH with "[$Hw $Hl]") as "(Hw & $ & %Hrevs)"; [done|].
      iDestruct "Ha" as "[Ha | (%z & Hc & %Hw0) ]".
      + iMod (local_revoked_by_separation W C (LNonHeap a) w 1%Qp with "[$Hw $Ha]")
          as "(_ & $ & Ha & %Hrev)"; [done|].
        iModIntro. iSplitL "Ha"; first by iLeft. iPureIntro. by constructor.
      + iMod (local_revoked_by_zone_cell with "[$Hw $Hc]") as "($ & Hc & %Hrev)"; [done|].
        iModIntro. iSplitL "Hc"; first (iRight; iExists z; by iFrame). iPureIntro. by constructor.
  Qed.

End WorldInterpStack.

Section WorldInterpStack.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    {cthreads : CmptThreads}
    {CL : ∀ t, CritLink Σ t}
    `{MP: MachineParameters}
    {CR : ∀ t, CritRoute Σ t (CL t)}
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
    (∃ lv, ([∗ list] a;v ∈ la;lv, temp_cell th (LNonHeap a) v) ∗
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
    ([∗ list] a;v ∈ la;lv, temp_cell th (LNonHeap a) v) ∗
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
      ▷ (∃ stk_mem, stack_region b e stk_mem) ∗
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
    stack_region bs es ws
    ={E}=∗
    ∃ l_unk_temp,
      ⌜ extract_temporaries_condition W (l_unk_temp ++ (LNonHeap <$> la)) ⌝ ∗
      world_interp (revoke W) C ∗
      ▷ StackRevokedResources W C la ∗
      ▷ ⌜Forall (λ a, std (revoke W) !! LNonHeap a = Some Revoked) la⌝ ∗
      ▷ (∃ stk_mem, stack_region b e stk_mem) ∗
      ▷ RevokedResources W C l_unk_temp ∗
      ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) l_unk_temp⌝.
  Proof.
    intros la ls Hbs Hes.
    by iApply monotone_revoke_stack_open.
  Qed.

  (** The cells of a stack region force their addresses Revoked in a world
      that holds them: a Temporary address would own its cell. *)
  Lemma world_interp_revoked_by_separation_stack (W : WORLD) (C : CmptName)
      (b e : Addr) (ws : list LWord) :
    Forall (λ a, LNonHeap a ∈ dom (std W)) (finz.seq_between b e) →
    world_interp W C ∗ stack_region b e ws
    ==∗
    world_interp W C ∗ stack_region b e ws ∗
    ⌜Forall (λ a, std W !! LNonHeap a = Some Revoked) (finz.seq_between b e)⌝.
  Proof.
    rewrite /stack_region. generalize (finz.seq_between b e) as la. intros la.
    revert ws. induction la as [|a la IH]; iIntros (ws Hdom) "[Hw Hl]".
    - iFrame. iPureIntro. constructor.
    - iDestruct (big_sepL2_cons_inv_l with "Hl") as (w ws' ->) "[Ha Hl]".
      apply Forall_cons_1 in Hdom as [Ha Hdom].
      iAssert (|==> world_interp W C ∗ stack_cell a w ∗
                 ⌜std W !! LNonHeap a = Some Revoked⌝)%I
        with "[Hw Ha]" as ">(Hw & Ha & %Hrev)".
      { iDestruct "Ha" as "[Ha | (%z & Hcell & %Hw) ]".
        - iMod (world_interp_revoked_by_separation W C (LNonHeap a) w 1%Qp
                 with "[$Hw $Ha]") as "(_ & $ & Ha & $)"; first done.
          iModIntro. by iLeft.
        - iMod (world_interp_revoked_by_zone_cell with "[$Hw $Hcell]")
            as "($ & Hcell & $)"; first done.
          iModIntro. iRight. iExists z. by iFrame. }
      iMod (IH with "[$Hw $Hl]") as "($ & Hl & %Hrevs)"; first done.
      iFrame. iPureIntro. by constructor.
  Qed.

End WorldInterpStack.
