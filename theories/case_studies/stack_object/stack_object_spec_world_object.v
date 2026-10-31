From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region proofmode.
From griotte Require Import world_interp_revocation world_interp_allocation.
From griotte Require Import interp_weakening monotone world_std_revocation.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import stack_object_spec_states.

(** * Opening and closing the world around [checkints]

    The lemmas of this file do not execute code. They are used around the
    block group [stack_object_spec_checkints_blocks_2] in the proof of
    [stack_object_f_spec]: [so_world_open_object] revokes the world of the
    call and gives the points-to predicates of the stack object [in], and
    the closing part of its postcondition puts them back in the world, once
    [checkints] has shown that they only contain integers. *)

Section SO_World_List.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ} {CNames : gset CmptName}
    {stsg : STSG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
  .
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Lemma addr_key_pointsto_list π (la : list Addr) (lv : list LWord) :
    ([∗ list] k;v ∈ addr_key π <$> la;lv, k ↦ₖ v) ⊣⊢
    ([∗ list] a;v ∈ la;lv, a ↦ₐ v) ∗ ([∗ list] a ∈ la, key_share (addr_key π a)).
  Proof.
    rewrite big_sepL2_fmap_l.
    setoid_rewrite addr_key_pointsto.
    rewrite big_sepL2_sep big_sepL2_const_sepL_l.
    iSplit.
    - iIntros "[$ [_ $] ]".
    - iIntros "[Hv $]". iDestruct (big_sepL2_length with "Hv") as %Hlen. by iFrame.
  Qed.

  Lemma so_invs_pointsto
      (l : list (LAddr * Perm * (CmptName * LWord → iProp Σ)))
      (lk : list LAddr) (lv : list LWord) :
    (λ '(k,_,_), k) <$> l = lk ->
    ([∗ list] '(k,_,_);v ∈ l;lv, k ↦ₖ v) ⊣⊢ [∗ list] k;v ∈ lk;lv, k ↦ₖ v.
  Proof.
    intros <-. rewrite big_sepL2_fmap_l.
    apply big_sepL2_proper. by intros ? [ [k p] phi] v _ _.
  Qed.

  (** Open a list of keys of the map of Global regions. *)
  Lemma open_world_interp_list (W : WORLD) (C' : CmptName)
    (l : list (LAddr * Perm * (CmptName * LWord → iProp Σ)))
    (l' : list LAddr) :
    let la := (fun '(a,p,φ) => a) <$> l in
    NoDup la →
    la ## l' →
    Forall (fun '(a,p,φ) => std W !! a ≠ Some Temporary) l →
    ([∗ list] '(a,p,φ) ∈ l, a ↪ᵍ[C']{p} φ) ∗
    world_interp_open W C' l' -∗
    world_interp_open W C' (la ++ l') ∗
    ([∗ list] '(a,p,φ) ∈ l, heap_key_resource a (∃ v, ⌜isO p = false⌝ ∗ a ↦ₖ v ∗ ▷ φ (C', v))).
  Proof.
    cbv zeta.
    iInduction l as [|[ [a p] φ] l] "IH"; cbn;
      iIntros (Hnodup Hdis HT) "[Hrels Hw]"; first by iFrame.
    apply NoDup_cons in Hnodup as [Hnotin Hnodup].
    apply Forall_cons in HT as [HTa HT].
    iDestruct "Hrels" as "[Hrel Hrels]".
    iDestruct ("IH" with "[%] [%] [%] [$Hrels $Hw]") as "[Hw $]"; [done| |done|].
    { set_solver. }
    rewrite world_interp_open_eq /world_interp_open_def.
    iDestruct (region_open_perm with "Hw Hrel") as "[Hw Hb]"; [|done|].
    { set_solver. }
    rewrite /body_g. iFrame "Hb".
    iApply (open_region_many_permutation with "Hw"). set_solver.
  Qed.

  (** The cells of a list of opened keys, as lists of values. *)
  Lemma open_cells_list (C' : CmptName)
    (l : list (LAddr * Perm * (CmptName * LWord → iProp Σ))) :
    ([∗ list] '(a,p,φ) ∈ l, ∃ v, ⌜isO p = false⌝ ∗ a ↦ₖ v ∗ ▷ φ (C', v)) -∗
    ∃ lv,
      ([∗ list] '(a,p,φ);v ∈ l;lv, a ↦ₖ v) ∗
      ▷ ([∗ list] '(a,p,φ);v ∈ l;lv, φ (C', v)) ∗
      ⌜length lv = length ((fun '(a,p,φ) => a) <$> l)⌝ ∗
      ([∗ list] '(a,p,φ) ∈ l, ⌜isO p = false⌝).
  Proof.
    iInduction l as [|[ [a p] φ] l] "IH"; cbn.
    { iIntros "_". iExists []. by cbn. }
    iIntros "[(%v & %HpO & Hv & Hφ) Hl]".
    iDestruct ("IH" with "Hl") as (lv) "(Hlv & Hφs & %Hlen & HpOs)".
    iExists (v :: lv). cbn. iFrame. iFrame "%".
    iPureIntro. by rewrite Hlen.
  Qed.

  Lemma heap_key_resource_list_cases {A : Type} (π : option AId)
    (l : list A) (k : A → LAddr) (P : A → iProp Σ) :
    Forall (λ x, ∃ a, k x = addr_key π a) l ->
    ([∗ list] x ∈ l, heap_key_resource (k x) (P x)) -∗
    ([∗ list] x ∈ l, P x) ∨ (∃ ι, ⌜π = Some ι⌝ ∗ ⌜l ≠ []⌝ ∗ ι ⊒ AQuar).
  Proof.
    iIntros (Hkeys) "Hl".
    iInduction l as [|x l] "IH"; first by iLeft.
    apply Forall_cons in Hkeys as [ [a Hka] Hkeys].
    iDestruct "Hl" as "[Hx Hl]".
    iDestruct (heap_key_open_cases with "Hx") as "[Hx | (%a' & %ι & %Hk & #Hq)]".
    - iDestruct ("IH" with "[//] Hl") as "[Hl | (%ι & %Hι & _ & Hq)]";
        [iLeft; iFrame | iRight; iExists ι; by iFrame "Hq"].
    - iRight. iExists ι. iFrame "Hq". iPureIntro. split; last done.
      rewrite Hk in Hka. destruct π as [ι'|]; cbn in Hka; [|discriminate].
      by injection Hka as _ ->.
  Qed.

  (** Close a list of opened keys of a freed object [ι] with their
      tombstones. *)

  (** Close a list of opened Global keys of a freed object [ι] with their
      tombstones. *)
  Lemma close_world_interp_list_tomb (W : WORLD) (C' : CmptName) (ι : AId)
    (l : list (LAddr * Perm * (CmptName * LWord → iProp Σ)))
    (l' : list LAddr) :
    let la := (fun '(a,p,φ) => a) <$> l in
    NoDup la →
    la ## l' →
    Forall (fun '(a,p,φ) => ∃ x, a = LHeap x ι) l →
    Forall (fun '(a,p,φ) => std W !! a ≠ Some Temporary) l →
    Forall (fun '(a,p,φ) => ∀ Cv : CmptName * LWord, Persistent (φ Cv)) l →
    ι ⊒ AQuar -∗
    world_interp_open W C' (la ++ l') -∗
    ([∗ list] '(a,p,φ) ∈ l, a ↪ᵍ[C']{p} φ) -∗
    world_interp_open W C' l'.
  Proof.
    cbv zeta.
    iInduction l as [|[ [a p] φ] l] "IH"; cbn;
      iIntros (Hnodup Hdis Hheap HT Hpers) "#Hq Hw #Hrels"; first done.
    apply NoDup_cons in Hnodup as [Hnotin Hnodup].
    apply Forall_cons in Hheap as [ [x ->] Hheap].
    apply Forall_cons in HT as [HTa HT].
    apply Forall_cons in Hpers as [Hpers_a Hpers].
    iDestruct "Hrels" as "[Hrel Hrels]".
    iDestruct (close_world_interp_next_quarantined_heap_g W C'
                 (((λ '(a, _, _), a) <$> l) ++ l') with "Hq [Hw] Hrel") as "Hw".
    { set_solver. }
    { done. }
    { iApply (world_interp_open_permutation with "Hw"). set_solver. }
    iApply ("IH" with "[%] [%] [%] [%] [%] Hq Hw Hrels"); try done.
    set_solver.
  Qed.

  (** Close a list of opened Global keys with their cells. *)
  Lemma close_world_interp_list (W : WORLD) (C' : CmptName)
    (l : list (LAddr * Perm * (CmptName * LWord → iProp Σ)))
    (l' : list LAddr) (lv : list LWord) :
    let la := (fun '(a,p,φ) => a) <$> l in
    length l = length lv →
    NoDup la →
    la ## l' →
    Forall (fun '(a,p,φ) => std W !! a ≠ Some Temporary) l →
    Forall (fun '(a,p,φ) => ∀ Cv : CmptName * LWord, Persistent (φ Cv)) l →
    world_interp_open W C' (la ++ l') ∗
    ([∗ list] '(a,p,φ);v ∈ l;lv, a ↦ₖ v) ∗
    ▷ ([∗ list] '(a,p,φ);v ∈ l;lv, φ (C', v)) ∗
    ([∗ list] '(a,p,φ) ∈ l, a ↪ᵍ[C']{p} φ) ∗
    ([∗ list] '(a,p,φ) ∈ l, ⌜isO p = false⌝) -∗
    world_interp_open W C' l'.
  Proof.
    cbv zeta.
    iInduction l as [|[ [a p] φ] l] "IH" forall (lv); cbn;
      iIntros (Hlen Hnodup Hdis HT Hpers) "(Hw & Hv & Hφ & Hrels & Hp)".
    { done. }
    destruct lv as [|v lv]; first done.
    cbn in Hlen |- *.
    apply NoDup_cons in Hnodup as [Hnotin Hnodup].
    apply Forall_cons in HT as [HTa HT].
    apply Forall_cons in Hpers as [Hpers_a Hpers].
    iDestruct "Hv" as "[Hva Hv]".
    iDestruct "Hφ" as "[Hφa Hφ]".
    iDestruct "Hrels" as "[Hrel Hrels]".
    iDestruct "Hp" as "[%HpO Hp]".
    iAssert (world_interp_open W C' (((λ '(a, _, _), a) <$> l) ++ l'))%I with "[Hw Hva Hφa Hrel]" as "Hw".
    { rewrite world_interp_open_eq /world_interp_open_def.
      iApply (region_close_perm with "[Hw] Hrel"); [first [done|set_solver] .. | |].
      - iApply (open_region_many_permutation with "Hw"). set_solver.
      - rewrite /body_g. iApply heap_key_resource_intro. iExists v. by iFrame. }
    iApply ("IH" $! lv with "[%] [%] [%] [%] [%] [$Hw $Hv $Hφ $Hrels $Hp]"); try done.
    - lia.
    - set_solver.
  Qed.

End SO_World_List.

Section SO_World_Object.
  Context
    {Σ : gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg : sealStoreG Σ} {CNames : gset CmptName}
    {stsg : STSG Σ}
    {relg : relGS Σ} {cstackg : CSTACKG Σ}
    `{MP : MachineParameters}.

  (** The revoked Temporary keys whose cells are held, outside the open
      keys [s] of [W1]: the capability reaches them through their local
      regions, so their predicates hold for integers in every world. *)
  Lemma so_temps_zcond (W W1 : WORLD) (C : CmptName) (s : list LAddr) (π : option AId)
      (p : Perm) (g : Locality) (l : list Addr) :
    Forall (λ a, addr_key π a ∉ s) l →
    world_interp_open W1 C s -∗
    ([∗ list] a ∈ l, ∃ p' P, region_rel W C (addr_key π a) p' P p g ∗ ▷ zcond P C) -∗
    ([∗ list] a ∈ l,
       ∃ pa Φa, ⌜∀ WCv, Persistent (Φa WCv)⌝ ∗ addr_key π a ↪ˡ[C]{pa} Φa ∗
         ∃ wa, ⌜isO pa = false⌝ ∗ addr_key π a ↦ₖ wa ∗
               future_pub_mono C Φa wa ∗ ▷ Φa (W, C, wa)) -∗
    world_interp_open W1 C s ∗
    ([∗ list] a ∈ l,
       ∃ pa Φa, ⌜∀ WCv, Persistent (Φa WCv)⌝ ∗ addr_key π a ↪ˡ[C]{pa} Φa ∗
         ▷ zcond (safeUC Φa) C ∗
         ∃ wa, ⌜isO pa = false⌝ ∗ addr_key π a ↦ₖ wa ∗
               future_pub_mono C Φa wa ∗ ▷ Φa (W, C, wa)).
  Proof.
    iInduction l as [|a l] "IH"; cbn; iIntros (Hs) "Hw #Hinterp Hl"; first by iFrame.
    apply Forall_cons in Hs as [Ha Hs].
    iDestruct "Hinterp" as "[(%p' & %P & #Hrel' & #Hzcond) Hinterp]".
    iDestruct "Hl" as "[(%pa & %Φa & %Hpers & #Hrel & %wa & HpO & Hv & Hmono & HΦ) Hl]".
    iDestruct ("IH" with "[//] Hw Hinterp Hl") as "[Hw $]".
    iDestruct (region_rel_parts with "Hrel'") as (ρ) "Hpart".
    destruct ρ; cbn.
    - iExFalso. rewrite /region_rel_g.
      iApply (world_interp_open_rel_g_cell_false with "Hw Hpart Hv"). done.
    - iDestruct "Hpart" as "(Hrel'' & _ & _)".
      iDestruct (rel_l_agree with "Hrel Hrel''") as "[_ #Heq]".
      iFrame "Hw". iExists pa, Φa. iFrame "Hrel %".
      iSplitR "HpO Hv Hmono HΦ"; last (iExists wa; iFrame).
      iNext. iIntros (W1' W2' z π0) "!> H"; cbn.
      iDestruct ("Heq" $! (W1', C, WInt z @@? π0)) as "-#Heq0".
      iDestruct ("Heq" $! (W2', C, WInt z @@? π0)) as "-#Heq1".
      iDestruct (internal_eq_iff with "Heq1") as "[_ Heq1]".
      iDestruct (internal_eq_iff with "Heq0") as "[Heq0 _]".
      iApply "Heq1".
      iDestruct ("Heq0" with "H") as "H".
      iApply "Hzcond"; eauto.
  Qed.

  Lemma stack_object_open_region_for_checkints
      (W0 : WORLD) (C : CmptName)
      (t : bool) (p : Perm) (g : Locality) (b e cur : Addr) (π : option AId)
      (csp_b csp_e : Addr)
      (l_revoked : list LAddr) (stk_mem : list LWord) :
    let W1 := revoke W0 in
    let object := so_object_addresses b e in
    let temps := so_object_temporaries W0 π b e in
    let perms := so_object_permanents W0 π b e in
    let rest := so_revoked_without_object W0 π b e l_revoked in
    extract_temporaries_condition
      W0 (l_revoked ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) ->
    object ## finz.seq_between csp_b csp_e ->
    readAllowed p = true ->
    (t = true ∨ (e <= b)%a) ->
    thread_in th C
    ∗ interp W0 C (WCap t p g b e cur @@? π)
    ∗ world_interp W1 C
    ∗ ▷ RevokedResources W0 C l_revoked
    ∗ [[csp_b, csp_e]] ↦ₐ [[stk_mem]]
    ∗ £ 1
    ={⊤}=∗
    (∃ object_mem,
      ⌜length object_mem = length object⌝
      ∗ ⌜object ≡ₚ perms ++ temps⌝
      ∗ ([∗ list] a;v ∈ perms ++ temps;object_mem, a ↦ₐ v)
      ∗ ▷ (
          (⌜Forall (fun w => exists z : Z, w.(lw) = WInt z) object_mem⌝
           ∗ ([∗ list] a;v ∈ perms ++ temps;object_mem, a ↦ₐ v)
           ={⊤}=∗
           world_interp (close_list (addr_key π <$> temps) W1) C
           ∗ RevokedResources W0 C rest
           ∗ [[csp_b, csp_e]] ↦ₐ [[stk_mem]]
           ∗ interp
               (close_list (addr_key π <$> temps) W1) C
               (WCap t p g b e (finz.max b e) @@? π))
          ∧
          (([∗ list] a;v ∈ perms ++ temps;object_mem, a ↦ₐ v)
           ={⊤}=∗
           world_interp W1 C
           ∗ RevokedResources W0 C l_revoked
           ∗ [[csp_b, csp_e]] ↦ₐ [[stk_mem]])))
    ∨ (∃ ι,
        ⌜t = true⌝ ∗ ⌜π = Some ι⌝ ∗ ⌜(b < e)%a⌝ ∗ ι ⊒ AQuar
        ∗ world_interp W1 C
        ∗ RevokedResources W0 C l_revoked
        ∗ [[csp_b, csp_e]] ↦ₐ [[stk_mem]]).
  Proof.
    intros W1 object temps perms rest.
    iIntros (Hextract Hobject_stack Hread Htag_or_empty)
      "(#Hthread & #Hinterp_wca0_W0 & Hworld_interp_C & Hl_revoked & Hstk & Hlc)".
    destruct t; cycle 1.
    { destruct Htag_or_empty as [Htag | Hempty]; first discriminate.
      assert (finz.seq_between b e = []) as Hrange by
        (apply finz_seq_between_empty; exact Hempty).
      assert (object = []) as -> by (subst object; exact Hrange).
      assert (temps = []) as -> by
        (subst temps; rewrite /so_object_temporaries /so_object_addresses Hrange; done).
      assert (perms = []) as -> by
        (subst perms; rewrite /so_object_permanents /so_object_addresses Hrange; done).
      assert (rest = l_revoked) as ->.
      { subst rest. rewrite /so_revoked_without_object /so_object_temporaries
          /so_object_addresses Hrange /=.
        change (filter (fun a : LAddr => a ∉ []) l_revoked = l_revoked).
        clear -l_revoked. induction l_revoked as [|x xs IH]; first done.
        rewrite filter_cons_True; last set_solver. by rewrite IH. }
      rewrite fmap_nil close_list_empty /=.
      iDestruct (lc_fupd_elim_later with "Hlc Hl_revoked") as ">Hl_revoked".
      iModIntro. iLeft. iExists []. iSplit; first done. iSplit; first done.
      iSplit; first done. iNext.
      iSplit.
      - iIntros "_".
        iModIntro. iFrame. iApply interp_untagged; done.
      - iIntros "_".
        iModIntro. iFrame.
    }
    destruct Hextract as [Hrevoked_nodup Hrevoked_temps].

    (* Partition the object region into the addresses that are not
       Temporary in [W0] and the Temporary ones, revoked with the current
       frame. *)
    pose proof (so_object_addresses_partition W0 π b e) as Hobject_partition.
    change (finz.seq_between b e ≡ₚ perms ++ temps) in Hobject_partition.

    assert (addr_key π <$> temps ⊆ l_revoked) as Htemps_subset.
    { intros k Hk.
      apply list_elem_of_fmap in Hk as [a' [-> Ha] ].
      subst temps object.
      apply list_elem_of_filter in Ha as [Ha Ha_object].
      apply Hrevoked_temps in Ha.
      apply elem_of_app in Ha as [Ha|Ha]; first done.
      apply list_elem_of_fmap in Ha as [a'' [Heq Ha''] ].
      assert (a' = a'') as <-.
      { by apply addr_key_LNonHeap_eq in Heq. }
      rewrite elem_of_disjoint in Hobject_stack.
      exfalso. eapply Hobject_stack; eauto.
    }
    apply NoDup_app in Hrevoked_nodup as (Hl_revoked_nodup & _ & _).
    assert (addr_key π <$> temps ≡ₚ filter (fun a => a ∈ addr_key π <$> temps) l_revoked)
      as Htemps_filter.
    { apply NoDup_subset_filter_membership; auto.
      apply NoDup_addr_key_fmap, so_object_temporaries_NoDup.
    }
    assert (l_revoked ≡ₚ (addr_key π <$> temps) ++ rest) as Hl_revoked_partition.
    { subst rest.
      rewrite {1}Htemps_filter.
      apply filter_complement_list.
    }
    iDestruct (lc_fupd_elim_later with "Hlc Hl_revoked") as ">Hl_revoked".
    iEval (setoid_rewrite Hl_revoked_partition) in "Hl_revoked".
    iDestruct (RevokedResources_app with "Hl_revoked") as
      "[Hrevoked_temps Hrevoked_rest]".
    iEval (rewrite /RevokedResources big_sepL_fmap) in "Hrevoked_temps".
    iAssert (([∗ list] a ∈ temps,
               ∃ pa Φa, ⌜∀ WCv, Persistent (Φa WCv)⌝ ∗ addr_key π a ↪ˡ[C]{pa} Φa) ∗
             ([∗ list] a ∈ temps,
               heap_key_resource (addr_key π a)
                 (∃ pa Φa, ⌜∀ WCv, Persistent (Φa WCv)⌝ ∗ addr_key π a ↪ˡ[C]{pa} Φa ∗
                    ∃ wa, ⌜isO pa = false⌝ ∗ addr_key π a ↦ₖ wa ∗
                          future_pub_mono C Φa wa ∗ ▷ Φa (W0, C, wa))))%I
      with "[Hrevoked_temps]" as "[#Htemps_rels Hrevoked_temps]".
    { rewrite -big_sepL_sep. iApply (big_sepL_impl with "Hrevoked_temps").
      iIntros "!>" (i a _) "(%pa & %Φa & %Hpers & #Hrel & Hres)".
      iSplit; first (iExists pa, Φa; by iFrame "Hrel").
      rewrite /temp_res.
      iApply (heap_key_resource_mono with "[] Hres").
      iIntros "(%wa & %HpO & Hv & Hmono & HΦ)". iExists pa, Φa. iFrame "Hrel".
      iSplit; first done.
      iExists wa. rewrite /temp_body. by iFrame. }

    (* The addresses of the object that are not Temporary in [W0] are
       Global regions: open them through the world interpretation. *)
    iDestruct (read_allowed_inv_full_cap with "Hthread Hinterp_wca0_W0")
      as "Hinterp_wca0_invs"; auto.
    iAssert (
        ∃ (wca0_invs : list (LAddr * Perm * (CmptName * LWord -> iProp Σ))),
          ⌜(fun '(a, _, _) => a) <$> wca0_invs = addr_key π <$> perms⌝ ∗
          ([∗ list] '(a, p0, φ) ∈ wca0_invs, a ↪ᵍ[C]{p0} φ) ∗
          ⌜Forall
              (fun '(_, _, φ) => ∀ Cv : CmptName * LWord, Persistent (φ Cv))
              wca0_invs⌝)%I
      with "[]" as (wca0_invs) "(%Hwca0_invs_perma & #Hrels_wca0 & %Hpers_wca0_invs)".
    { iDestruct "Hinterp_wca0_invs" as "-#Hinterp_wca0_invs".
      iClear "#".
      setoid_rewrite Hobject_partition.
      iDestruct (big_sepL_app with "Hinterp_wca0_invs") as "[H _]".
      iDestruct "H" as "#H".
      assert (Forall (fun a => std W0 !! addr_key π a ≠ Some Temporary) perms)
        as Hperms.
      { subst perms. apply Forall_forall. intros a Ha.
        by apply list_elem_of_filter in Ha as [Ha _]. }
      generalize perms, Hperms.
      clear; intros l Hl.
      iInduction (l) as [|a l] "IH".
      - iExists []; cbn.
        repeat (iSplit; iPureIntro; done).
      - apply Forall_cons in Hl as [Ha Hl].
        cbn.
        iDestruct "H" as "[(%p' & %P' & %Hpermflow & %HpersP & #HrelP & _) H]".
        iDestruct (region_rel_parts with "HrelP") as (ρ) "Hpart".
        destruct ρ; cbn; last first.
        { iDestruct "Hpart" as "(_ & %HT & _)". done. }
        iDestruct ("IH" with "[%] [$]") as (invs) "(%Hl_ & #Hrels & %Hpers)"; auto.
        iExists ((addr_key π a, p', safeGC P') :: invs).
        iSplit; first (iPureIntro; cbn; by rewrite Hl_).
        iSplit; first (cbn; iFrame "#").
        iPureIntro. apply Forall_cons; split; auto.
        intros Cv. apply (HpersP (∅, Cv.1, Cv.2)).
    }
    assert (Forall (fun '(k, _, _) => std W1 !! k ≠ Some Temporary) wca0_invs)
      as Hwca0_W1.
    { apply Forall_forall. intros [ [k p0] φ0] _; cbn. intros Hk.
      by apply revoke_lookup_non_temp in Hk. }

    iEval (rewrite open_world_interp_empty) in "Hworld_interp_C".
    iDestruct (open_world_interp_list with
      "[$Hrels_wca0 $Hworld_interp_C]") as
      "(Hworld_interp_C & Hperms_res)".
    { rewrite Hwca0_invs_perma. apply NoDup_addr_key_fmap, so_object_permanents_NoDup. }
    { rewrite Hwca0_invs_perma. set_solver+. }
    { exact Hwca0_W1. }
    (* The object holds its cells, or it was freed: its keys are
       tombstones, and the world closes back. *)
    assert (Forall
      (λ x : LAddr * Perm * (CmptName * LWord → iProp Σ),
         ∃ a, x.1.1 = addr_key π a) wca0_invs) as Hwca0_keys.
    { rewrite Forall_forall. intros [ [k p0] φ0] Hx. cbn.
      assert (k ∈ addr_key π <$> perms) as Hk.
      { rewrite -Hwca0_invs_perma. eapply list_elem_of_fmap_2'; [exact Hx|done]. }
      apply list_elem_of_fmap in Hk as [a' [-> _] ]. by exists a'. }
    assert (Forall (λ a, ∃ a', addr_key π a = addr_key π a') temps) as Htemps_keys.
    { apply Forall_forall. intros a' _. by exists a'. }
    iAssert (
        (([∗ list] '(a,p0,φ) ∈ wca0_invs, ∃ v, ⌜isO p0 = false⌝ ∗ a ↦ₖ v ∗ ▷ φ (C, v))
         ∗ ([∗ list] a ∈ temps,
              ∃ pa Φa, ⌜∀ WCv, Persistent (Φa WCv)⌝ ∗ addr_key π a ↪ˡ[C]{pa} Φa ∗
                ∃ wa, ⌜isO pa = false⌝ ∗ addr_key π a ↦ₖ wa ∗
                      future_pub_mono C Φa wa ∗ ▷ Φa (W0, C, wa)))
        ∨ (∃ ι, ⌜π = Some ι⌝ ∗ ⌜wca0_invs ≠ [] ∨ temps ≠ []⌝ ∗ ι ⊒ AQuar))%I
      with "[Hperms_res Hrevoked_temps]"
      as "[ [Hperms_cells Hrevoked_temps] | (%ι & -> & %Hobject_ne & #Hq)]".
    { iDestruct (heap_key_resource_list_cases π wca0_invs (λ x, x.1.1)
        (λ '(a,p0,φ), ∃ v, ⌜isO p0 = false⌝ ∗ a ↦ₖ v ∗ ▷ φ (C, v))%I Hwca0_keys
        with "[Hperms_res]") as "[Hperms_cells | (%ι & -> & %Hne & #Hq)]".
      { iApply (big_sepL_mono with "Hperms_res"). by intros ? [ [ ] ] _. }
      2: { iRight. iExists ι. iFrame "Hq". iPureIntro. split; [done | by left]. }
      iDestruct (heap_key_resource_list_cases π temps (addr_key π) _ Htemps_keys
        with "Hrevoked_temps") as "[Hrevoked_temps | (%ι & -> & %Hne & #Hq)]".
      2: { iRight. iExists ι. iFrame "Hq". iPureIntro. split; [done | by right]. }
      iLeft. iFrame. }
    2: { (* The object was freed *)
      iDestruct (close_world_interp_list_tomb W1 C ι wca0_invs []
        with "Hq Hworld_interp_C Hrels_wca0") as "Hworld_interp_C".
      { rewrite Hwca0_invs_perma. apply NoDup_addr_key_fmap, so_object_permanents_NoDup. }
      { set_solver+. }
      { eapply Forall_impl; first exact Hwca0_keys.
        intros [ [k p0] φ0] [a' Ha']. cbn in Ha'. by exists a'. }
      { exact Hwca0_W1. }
      { exact Hpers_wca0_invs. }
      rewrite -open_world_interp_empty.
      iModIntro. iRight. iExists ι. iFrame "Hq Hworld_interp_C Hstk".
      iSplit; first done. iSplit; first done.
      iSplit.
      { iPureIntro. destruct (decide (b < e)%a) as [|Hbe]; first done. exfalso.
        assert (finz.seq_between b e = []) as Hnil by (apply finz_seq_between_empty; solve_addr).
        rewrite Hnil in Hobject_partition.
        apply Permutation_nil, app_eq_nil in Hobject_partition as [Hperms_nil Htemps_nil].
        destruct Hobject_ne as [Hne | Hne]; apply Hne; last done.
        rewrite Hperms_nil /= in Hwca0_invs_perma. by apply fmap_nil_inv in Hwca0_invs_perma. }
      iEval (setoid_rewrite Hl_revoked_partition).
      rewrite RevokedResources_app. iFrame "Hrevoked_rest".
      rewrite /RevokedResources big_sepL_fmap.
      iApply (big_sepL_impl with "Htemps_rels").
      iIntros "!>" (i a' _) "(%pa & %Φa & %Hpers & Hrel)".
      iExists pa, Φa. iFrame "Hrel". iSplit; first done.
      rewrite /temp_res. by iApply heap_key_close_tomb. }
    iDestruct (open_cells_list with "Hperms_cells") as (wca0_lv_perma)
      "(Hperms_lv & Hwca0_φs & %Hlength_wca0_lv & Hwca0_pO)".
    iAssert (([∗ list] a;v ∈ perms;wca0_lv_perma, a ↦ₐ v) ∗
      ([∗ list] a ∈ perms, key_share (addr_key π a)))%I
      with "[Hperms_lv]" as "[Hperms_lv Hperms_shares]".
    { by rewrite (so_invs_pointsto _ _ _ Hwca0_invs_perma) addr_key_pointsto_list. }
    assert (Forall
      (fun a => std (revoke W0) !! addr_key π a = Some Revoked) temps)
      as Hrevoked_temps_pure.
    { apply Forall_forall. intros a Ha.
      apply revoke_lookup_Monotemp.
      apply Hrevoked_temps.
      apply elem_of_app; left.
      apply Htemps_subset. by apply list_elem_of_fmap_2.
    }

    (* The predicates of the Temporary addresses of the object hold for
       integers (used by the first closing): the capability reaches them
       through their local regions. *)
    iAssert ([∗ list] a ∈ temps,
               ∃ p' P, region_rel W0 C (addr_key π a) p' P p g ∗ ▷ zcond P C)%I
      with "[]" as "#Hinterp_temps".
    { iDestruct "Hinterp_wca0_invs" as "-#Hinterp".
      iClear "#".
      setoid_rewrite Hobject_partition.
      iDestruct (big_sepL_app with "Hinterp") as "[_ Hinterp]".
      iApply (big_sepL_mono with "Hinterp").
      iIntros (k a _) "(%p' & %P & _ & _ & Hrel & Hz & _)". iExists p', P. iFrame. }
    iDestruct (so_temps_zcond W0 W1 C _ π p g temps
                with "Hworld_interp_C Hinterp_temps Hrevoked_temps")
      as "[Hworld_interp_C Hrevoked_temps]".
    { apply Forall_forall. intros a Ha Hin.
      rewrite app_nil_r Hwca0_invs_perma in Hin.
      apply elem_of_addr_key_fmap in Hin.
      subst temps perms.
      apply list_elem_of_filter in Ha as [HaT _].
      apply list_elem_of_filter in Hin as [HaP _].
      done. }

    iAssert (
        ∃ (lp : list Perm)
          (lφ : list (WORLD * CmptName * LWord -> iPropI Σ))
          (lv : list LWord),
          ⌜length lp = length temps⌝
          ∗ ⌜length lφ = length temps⌝
          ∗ ⌜length lv = length temps⌝
          ∗ ([∗ list] φ ∈ lφ,
               ⌜forall Wv : WORLD * CmptName * LWord, Persistent (φ Wv)⌝)
          ∗ ([∗ list] a;pφ ∈ temps;(zip lp lφ), addr_key π a ↪ˡ[C]{pφ.1} pφ.2)
          ∗ ([∗ list] φ ∈ lφ, ▷ zcond (safeUC φ) C)
          ∗ ([∗ list] p0 ∈ lp, ⌜isO p0 = false⌝)
          ∗ ([∗ list] a;v ∈ temps;lv, a ↦ₐ v)
          ∗ ([∗ list] a ∈ temps, key_share (addr_key π a))
          ∗ ([∗ list] lpφ;v ∈ (zip lp lφ);lv, future_pub_mono C lpφ.2 v)
          ∗ ([∗ list] φ;v ∈ lφ;lv, ▷ φ (W0, C, v)))%I
      with "[Hrevoked_temps]" as
      (lp lφ wca0_lv_temps)
      "(%Hlen_lp & %Hlen_lφ & %Hlen_lv & Hlφ_pers
       & #Hlpφ_rels & #Hzcond_lφ & HlpO & Htemps_lv & Htemps_shares & Hlpφ_mono & Hlφ_lv)".
    { iClear "#".
      generalize temps. clear; intros l.
      iInduction (l) as [|a l] "IH".
      - iExists [], [], []; cbn; done.
      - iDestruct "Hrevoked_temps" as "[Ha Hl]".
        iDestruct ("IH" with "Hl") as "Hl".
        iDestruct "Ha" as (p0 P HpersP) "(Hrel_a & Hz_a & Ha)".
        iDestruct "Ha" as (v) "(HpO & Hv & HmonoP & HP)".
        iDestruct (addr_key_pointsto with "Hv") as "[Hv Hsh]".
        iDestruct "Hl" as (lp0 lP lv)
          "(% & % & % & %Hpers_lP & Hrels & Hzs & HpOs & Hvs & Hshs & Hmonos & HPs)".
        iExists (p0 :: lp0), (P :: lP), (v :: lv).
        iFrame. iFrame "%".
        iPureIntro. cbn; lia.
    }
    iDestruct (big_sepL_later_2 with "Hzcond_lφ") as "#Hzcond_lφ_later".
    iClear "Hzcond_lφ".
    (* Present [checkints] with one points-to list.  Its address order may be
       permuted, but the object contents and length remain unchanged. *)
    iDestruct (big_sepL2_app with "Hperms_lv Htemps_lv") as "Hobject_mem".

    iModIntro. iLeft.
    iExists (wca0_lv_perma ++ wca0_lv_temps).
    iSplit; first iPureIntro.
    { rewrite length_app Hlength_wca0_lv Hlen_lv Hwca0_invs_perma length_fmap.
      change
        (length perms + length temps = length (finz.seq_between b e)).
      rewrite -length_app.
      symmetry. by apply Permutation_length.
    }
    iSplit; first done.
    iFrame "Hobject_mem".
    iNext.
    iSplit; cycle 1.
    { (* Second closing: the object is put back with its contents *)
      iIntros "Hobject_mem".
      iDestruct (big_sepL2_app' with "Hobject_mem") as
        "[Hperms_lv Htemps_lv]".
      { by rewrite Hlength_wca0_lv Hwca0_invs_perma length_fmap. }
      iAssert
        ([∗ list] '(k0, _, _);v ∈ wca0_invs;wca0_lv_perma, k0 ↦ₖ v)%I
        with "[Hperms_lv Hperms_shares]" as "Hperms_lv".
      { rewrite (so_invs_pointsto _ _ _ Hwca0_invs_perma) addr_key_pointsto_list.
        iFrame. }
      iDestruct (close_world_interp_list W1 C wca0_invs [] with
        "[$Hworld_interp_C $Hperms_lv $Hwca0_φs $Hrels_wca0 $Hwca0_pO]") as "Hworld_interp_C".
      { by rewrite Hlength_wca0_lv length_fmap. }
      { rewrite Hwca0_invs_perma. apply NoDup_addr_key_fmap, so_object_permanents_NoDup. }
      { set_solver+. }
      { exact Hwca0_W1. }
      { exact Hpers_wca0_invs. }
      rewrite -open_world_interp_empty.
      iAssert (RevokedResources W0 C (addr_key π <$> temps))%I
        with "[Hlφ_pers HlpO Hlpφ_mono Htemps_lv Htemps_shares Hlφ_lv]"
        as "Hrevoked_temps".
      { iDestruct "Hlpφ_rels" as "-#Hlpφ_rels".
        iClear "#".
        rewrite /RevokedResources big_sepL_fmap.
        clear -Hlen_lp Hlen_lφ Hlen_lv.
        generalize dependent temps; intros l Hlen_lp Hlen_lφ Hlen_lv.
        generalize wca0_lv_temps Hlen_lv; intros lv.
        clear Hlen_lv wca0_lv_temps; intros Hlen_lv.
        iRename "Htemps_lv" into "Hlv".
        iInduction (l) as [|a l] "IH"
          forall (lφ lp lv Hlen_lp Hlen_lφ Hlen_lv); first done.
        destruct lv as [|v lv]; cbn in Hlen_lv; simplify_eq.
        destruct lφ as [|φ lφ]; cbn in Hlen_lφ; simplify_eq.
        destruct lp as [|p0 lp]; cbn in Hlen_lp; simplify_eq.
        cbn in *.
        iDestruct "Hlφ_pers" as "[%Hpers_a Hlφ_pers]".
        iDestruct "HlpO" as "[%HpO_a HlpO]".
        iDestruct "Hlpφ_mono" as "[Hmono_a Hlpφ_mono]".
        iDestruct "Hlv" as "[Hlv_a Hlv]".
        iDestruct "Hlφ_lv" as "[Hφ_a Hlφ_lv]".
        iDestruct "Hlpφ_rels" as "[Hrel_a Hlpφ_rels]".
        iDestruct "Htemps_shares" as "[Hsh_a Htemps_shares]".
        iDestruct (addr_key_pointsto with "[$Hlv_a $Hsh_a]") as "Hlv_a".
        iSplitL "Hmono_a Hlv_a Hφ_a Hrel_a".
        { iExists p0, φ. iFrame "Hrel_a". iSplit; first done.
          iApply heap_key_resource_intro. iExists v. rewrite /temp_body. by iFrame. }
        iApply ("IH" $! lφ lp lv with
          "[%] [%] [%] [$] [$] [$] [$] [$] [$] [$]"); eauto.
      }
      iModIntro.
      iFrame "Hworld_interp_C Hstk".
      iEval (setoid_rewrite Hl_revoked_partition).
      rewrite RevokedResources_app.
      iFrame.
    }
    iIntros "(%Hobject_ints & Hobject_mem)".

    iDestruct (big_sepL2_app' with "Hobject_mem") as
      "[Hperms_lv Htemps_lv]".
    { by rewrite Hlength_wca0_lv Hwca0_invs_perma length_fmap. }
    iAssert
      ([∗ list] '(k0, _, _);v ∈ wca0_invs;wca0_lv_perma, k0 ↦ₖ v)%I
      with "[Hperms_lv Hperms_shares]" as "Hperms_lv".
    { rewrite (so_invs_pointsto _ _ _ Hwca0_invs_perma) addr_key_pointsto_list.
      iFrame. }

    (* The continuation first closes the Global regions back into [W1],
       then uses the integer-valued Temporary addresses to reinstate the
       object. *)
    iDestruct (close_world_interp_list W1 C wca0_invs [] with
      "[$Hworld_interp_C $Hperms_lv $Hwca0_φs $Hrels_wca0 $Hwca0_pO]") as "Hworld_interp_C".
    { by rewrite Hlength_wca0_lv length_fmap. }
    { rewrite Hwca0_invs_perma. apply NoDup_addr_key_fmap, so_object_permanents_NoDup. }
    { set_solver+. }
    { exact Hwca0_W1. }
    { exact Hpers_wca0_invs. }
    rewrite -open_world_interp_empty.

    iDestruct "Hzcond_lφ_later" as "-#Hzcond_lφ'".
    iAssert ([∗ list] φ;v ∈ lφ;wca0_lv_temps, φ (W1, C, v))%I
      with "[Hlφ_lv Hzcond_lφ']" as "Hlφ_lv".
    { iClear "#".
      apply Forall_app in Hobject_ints as [_ Htemps_ints].
      generalize wca0_lv_temps, Htemps_ints, Hlen_lv.
      generalize temps, Hlen_lp, Hlen_lφ. clear.
      intros la Hlen_lp Hlen_lφ lv Hl_ints Hlen_lv.
      iInduction (la) as [|a la] "IH"
        forall (lp lφ lv Hlen_lp Hlen_lφ Hlen_lv Hl_ints).
      all: destruct lφ; simplify_eq.
      all: destruct lp; simplify_eq.
      all: destruct lv; simplify_eq.
      - done.
      - cbn.
        iDestruct "Hlφ_lv" as "[Hb Hlb]".
        iDestruct "Hzcond_lφ'" as "[#Hz Hzl]".
        apply Forall_cons in Hl_ints as [ [z Hz] Hl_ints].
        iSplitL "Hb Hz";
          last (iApply ("IH" with "[] [] [] [] [$] [$]"); eauto).
        rewrite /zcond.
        destruct l as [w0 π0]; cbn in Hz; subst w0.
        iSpecialize ("Hz" $! W0 W1 z π0). cbn.
        iApply "Hz"; auto.
    }
    iDestruct (big_sepL2_disjoint with "[$Hstk $Htemps_lv]") as %Htemps_stack.
    iAssert (RevokedResources W1 C (addr_key π <$> temps))%I
      with "[Hlφ_pers HlpO Hlpφ_mono Htemps_lv Htemps_shares Hlφ_lv]"
      as "Htemps_closing_resources".
    { iDestruct "Hlpφ_rels" as "-#Hlpφ_rels".
      iClear "#".
      rewrite /RevokedResources big_sepL_fmap.
      clear -Hlen_lp Hlen_lφ Hlen_lv.
      generalize dependent temps; intros l Hlen_lp Hlen_lφ Hlen_lv.
      generalize wca0_lv_temps Hlen_lv; intros lv.
      clear Hlen_lv wca0_lv_temps; intros Hlen_lv.
      iRename "Htemps_lv" into "Hlv".
      iInduction (l) as [|a l] "IH"
        forall (lφ lp lv Hlen_lp Hlen_lφ Hlen_lv); first done.
      destruct lv as [|v lv]; cbn in Hlen_lv; simplify_eq.
      destruct lφ as [|φ lφ]; cbn in Hlen_lφ; simplify_eq.
      destruct lp as [|p0 lp]; cbn in Hlen_lp; simplify_eq.
      cbn in *.
      iDestruct "Hlφ_pers" as "[%Hpers_a Hlφ_pers]".
      iDestruct "HlpO" as "[%HpO_a HlpO]".
      iDestruct "Hlpφ_mono" as "[Hmono_a Hlpφ_mono]".
      iDestruct "Hlv" as "[Hlv_a Hlv]".
      iDestruct "Hlφ_lv" as "[Hφ_a Hlφ_lv]".
      iDestruct "Hlpφ_rels" as "[Hrel_a Hlpφ_rels]".
      iDestruct "Htemps_shares" as "[Hsh_a Htemps_shares]".
      iDestruct (addr_key_pointsto with "[$Hlv_a $Hsh_a]") as "Hlv_a".
      iSplitL "Hmono_a Hlv_a Hφ_a Hrel_a".
      { iExists p0, φ. iFrame "Hrel_a". iSplit; first done.
        iApply heap_key_resource_intro. iExists v. rewrite /temp_body. by iFrame. }
      iApply ("IH" $! lφ lp lv with
        "[%] [%] [%] [$] [$] [$] [$] [$] [$] [$]"); eauto.
    }
    iMod (world_interp_restore_world W1 W1 C (addr_key π <$> temps) with
      "[$Hworld_interp_C] [Htemps_closing_resources]")
      as "Hworld_interp_C".
    { apply close_list_related_sts_pub. }
    { iExact "Htemps_closing_resources". }
    set (W2 := close_list (addr_key π <$> temps) W1).

    (* The object's Temporary keys are Temporary again in [W2] *)
    assert (∀ x, x ∈ finz.seq_between b e →
              std W0 !! addr_key π x = Some Temporary →
              std W2 !! addr_key π x = Some Temporary) as HT_W2.
    { intros x Hx HTx.
      apply close_list_lookup_in.
      + cbn; apply revoke_lookup_Monotemp; auto.
      + apply elem_of_addr_key_fmap, list_elem_of_filter; split; done. }
    iAssert (interp W2 C (Cap p g b e (finz.max b e) @@? π))%I
      as "#Hinterp_wca0_W2".
    { iEval (rewrite interp_unfold interp1_eq).
      iEval (rewrite interp_unfold interp1_eq) in "Hinterp_wca0_W0".
      destruct (isO p) eqn:HpO.
      { iDestruct "Hinterp_wca0_W0" as "[#Hok #Hcoverage]".
        iFrame "Hok". iApply (big_sepL_impl with "Hcoverage").
        iIntros "!>" (n x Hx) "Hx %Hheap".
        iApply heap_cap_O_key_temp_transfer; last by iApply "Hx".
        apply HT_W2. by eapply list_elem_of_lookup_2. }
      destruct (has_sreg_access p); first done.
      iDestruct "Hinterp_wca0_W0" as "[Hinterp $]".
      iClear "∗".
      iApply (big_sepL_impl with "Hinterp").
      iModIntro.
      iIntros (k x Hx)
        "(%px & %Px & %Hpx_flow & %Hpers_Px & Hrelx & Hzcondx & Hrcondx & Hwcondx)".
      iExists px, Px. iFrame "Hzcondx Hrcondx Hwcondx %".
      iApply (region_rel_temp_transfer with "Hrelx").
      apply HT_W2. by eapply list_elem_of_lookup_2.
    }
    iEval (rewrite /reinstate) in "Hworld_interp_C".
    iModIntro. iFrame.
    iExact "Hinterp_wca0_W2".
  Qed.


  (** Revoke the world [W0] of the call to [f], and open the region of the
      readable stack object [(t, p, g, b, e, a)], tagged or empty, which
      does not overlap with the stack frame [[csp_b, csp_e)]. The first closing puts the cells of
      the object back in the world, provided that they contain integers,
      and gives back the stack frame. The second closing, used when
      [checkints] faults, puts the object back unchanged in the revoked
      world, and gives back the revoked resources and the stack frame. If
      the object was freed, the world is revoked and nothing is opened. *)
  Lemma so_world_open_object
      (W0 : WORLD) (C : CmptName)
      (t : bool) (p : Perm) (g : Locality) (b e a : Addr) (π : option AId)
      (csp_b csp_e : Addr) :
    readAllowed p = true ->
    (t = true ∨ (e <= b)%a) ->
    finz.seq_between b e ## finz.seq_between csp_b csp_e ->
    thread_in th C -∗
    interp W0 C (Cap RWL Local csp_b csp_e (stk_start_a csp_b csp_e)) -∗
    interp W0 C (WCap t p g b e a @@? π) -∗
    world_interp W0 C -∗
    £ 1
    ={⊤}=∗
    ∃ l_revoked stk_mem,
      ⌜extract_temporaries_condition W0
         (l_revoked ++ (LNonHeap <$> finz.seq_between csp_b csp_e))⌝ ∗
      ▷ StackRevokedResources W0 C (finz.seq_between csp_b csp_e) ∗
      ((∃ la object_mem,
      ⌜la ≡ₚ finz.seq_between b e⌝ ∗
      ([∗ list] a;v ∈ la;object_mem, a ↦ₐ v) ∗
      ▷ ((⌜Forall (fun w => exists z : Z, w.(lw) = WInt z) object_mem⌝ ∗
           ([∗ list] a;v ∈ la;object_mem, a ↦ₐ v)
           ={⊤}=∗
           world_interp
             (close_list (addr_key π <$> so_object_temporaries W0 π b e) (revoke W0)) C ∗
           RevokedResources W0 C (so_revoked_without_object W0 π b e l_revoked) ∗
           [[csp_b, csp_e]] ↦ₐ [[stk_mem]] ∗
           interp (close_list (addr_key π <$> so_object_temporaries W0 π b e) (revoke W0)) C
             (WCap t p g b e (finz.max b e) @@? π)) ∧
         (([∗ list] a;v ∈ la;object_mem, a ↦ₐ v)
           ={⊤}=∗
           world_interp (revoke W0) C ∗
           RevokedResources W0 C l_revoked ∗
           [[csp_b, csp_e]] ↦ₐ [[stk_mem]])))
       ∨ (∃ ι,
           ⌜t = true⌝ ∗ ⌜π = Some ι⌝ ∗ ⌜(b < e)%a⌝ ∗ ι ⊒ AQuar ∗
           world_interp (revoke W0) C ∗
           RevokedResources W0 C l_revoked ∗
           [[csp_b, csp_e]] ↦ₐ [[stk_mem]])).
  Proof.
    iIntros (Hp Htag_or_empty Hno_overlap) "#Hthread #Hinterp_csp #Hinterp_object Hworld_interp_C Hlc".
    iMod (world_interp_revoke_stack with "[$Hinterp_csp $Hworld_interp_C]")
      as (l_revoked) "(%Hextract & Hworld_interp_C & Hstack_revoked & _
                       & >[%stk_mem Hstk] & Hl_revoked & _)".
    iMod (stack_object_open_region_for_checkints
            W0 C t p g b e a π csp_b csp_e l_revoked stk_mem
           with "[$Hthread $Hinterp_object $Hworld_interp_C $Hl_revoked $Hstk $Hlc]")
      as "[(%object_mem & _ & %Hobject & Hobject & Hclose) | Htomb]";
      [done|done|done|done| |].
    - iModIntro.
      iExists l_revoked, stk_mem.
      iFrame "∗%".
      iLeft. iExists _, object_mem. iFrame.
      iPureIntro; by symmetry.
    - iModIntro.
      iExists l_revoked, stk_mem.
      iFrame "∗%".
  Qed.

End SO_World_Object.
