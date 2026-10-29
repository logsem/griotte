From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region proofmode.
From griotte Require Import region_invariants_revocation region_invariants_allocation.
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
    - iIntros "[$ [_ $]]".
    - iIntros "[Hv $]". iDestruct (big_sepL2_length with "Hv") as %Hlen. by iFrame.
  Qed.

  Lemma so_invs_pointsto
      (l : list (LAddr * Perm * (WORLD * CmptName * LWord → iProp Σ) * region_type))
      (lk : list LAddr) (lv : list LWord) :
    (λ '(k,_,_,_), k) <$> l = lk ->
    ([∗ list] '(k,_,_,_);v ∈ l;lv, k ↦ₖ v) ⊣⊢ [∗ list] k;v ∈ lk;lv, k ↦ₖ v.
  Proof.
    intros <-. rewrite big_sepL2_fmap_l.
    apply big_sepL2_proper. by intros ? [ [ [k p] phi] rho] v _ _.
  Qed.

  Lemma open_world_interp_list (W : WORLD) (C' : CmptName)
    (l : list (LAddr * Perm * (WORLD * CmptName * LWord → iProp Σ) * region_type))
    (l' : list LAddr)
    :

    let la  := (fmap (fun '(a,p,φ,ρ) => a) l) in
    NoDup la ->
    la ## l' ->
    Forall (fun '(a,p,φ,ρ) => ρ ≠ Revoked) l ->
    Forall (fun '(a,p,φ,ρ) => (std W) !! a = Some ρ) l ->

    ([∗ list] '(a,p,φ,ρ) ∈ l, rel C' a p φ)
    ∗ world_interp_open W C' l' -∗

    world_interp_open W C' (la++l')
    ∗ ([∗ list] '(a,p,φ,ρ) ∈ l, sts_state_std C' a ρ)
    ∗ ([∗ list] '(a,p,φ,ρ) ∈ l,
         heap_key_resource a
           (∃ v, a ↦ₖ v
                 ∗ ▷ monotonicity_guarantees_region C' φ p v ρ
                 ∗ ▷ φ (W,C',v)
                 ∗ ⌜ isO p = false ⌝))
  .
  Proof.
    intros la.
    rewrite world_interp_open_eq /world_interp_open_def.
    iIntros (????) "(Hrels & @)".
    iDestruct (region_open_list W C' l l' with "[$Hrels $Hr $Hsts]") as
      "($ & $ & $ & $)"; auto.
  Qed.

  (** The cells of a list of opened keys, as lists of values. *)
  Lemma open_cells_list (W : WORLD) (C' : CmptName)
    (l : list (LAddr * Perm * (WORLD * CmptName * LWord → iProp Σ) * region_type)) :
    ([∗ list] '(a,p,φ,ρ) ∈ l,
       ∃ v, a ↦ₖ v
            ∗ ▷ monotonicity_guarantees_region C' φ p v ρ
            ∗ ▷ φ (W,C',v)
            ∗ ⌜ isO p = false ⌝) -∗
    ∃ lv,
      ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, a ↦ₖ v)
      ∗ ▷ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, monotonicity_guarantees_region C' φ p v ρ)
      ∗ ▷ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, φ (W,C',v))
      ∗ ⌜ length lv = length (fmap (fun '(a,p,φ,ρ) => a) l) ⌝
      ∗ ([∗ list] '(a,p,φ,ρ) ∈ l , ⌜ isO p = false ⌝).
  Proof.
    iInduction l as [|[ [ [a p] φ] ρ] l] "IH"; cbn.
    { iIntros "_". iExists []. by cbn. }
    iIntros "[(%v & Hv & Hmono & Hφ & %HpO) Hl]".
    iDestruct ("IH" with "Hl") as (lv) "(Hlv & Hmonos & Hφs & %Hlen & HpOs)".
    iExists (v :: lv). cbn. iFrame.
    iPureIntro. by rewrite Hlen.
  Qed.

  (** Opened keys of one object hold their resources, or a tombstone of
      the object. *)
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
  Lemma close_world_interp_list_tomb (W : WORLD) (C' : CmptName) (ι : AId)
    (l : list (LAddr * Perm * (WORLD * CmptName * LWord → iProp Σ) * region_type))
    (l' : list LAddr) :
    let la  := (fmap (fun '(a,p,φ,ρ) => a) l) in
    NoDup la ->
    la ## l' ->
    Forall (fun '(a,p,φ,ρ) => ∃ x, a = LHeap x ι) l ->
    Forall (fun '(a,p,φ,ρ) => ∀ Wv : WORLD * CmptName * LWord, Persistent (φ Wv)) l ->
    ι ⊒ AQuar -∗
    world_interp_open W C' (la++l') -∗
    ([∗ list] '(a,p,φ,ρ) ∈ l, sts_state_std C' a ρ) -∗
    ([∗ list] '(a,p,φ,ρ) ∈ l, rel C' a p φ) -∗
    world_interp_open W C' l'.
  Proof.
    cbv zeta.
    iInduction l as [|[ [ [a p] φ] ρ] l] "IH"; cbn;
      iIntros (Hnodup Hdis Hheap Hpers) "#Hq Hw Hsts #Hrels"; first done.
    apply NoDup_cons in Hnodup as [Hnotin Hnodup].
    apply Forall_cons in Hheap as [ [x ->] Hheap].
    apply Forall_cons in Hpers as [Hpers_a Hpers].
    iDestruct "Hsts" as "[Hst Hsts]".
    iDestruct "Hrels" as "[Hrel Hrels]".
    iDestruct (close_world_interp_next_quarantined_heap with "Hq Hw Hrel Hst") as "Hw".
    { apply not_elem_of_app; split; first done.
      intros Hin. apply (Hdis (LHeap x ι)); [by left|done]. }
    iApply ("IH" with "[%] [%] [%] [%] Hq Hw Hsts Hrels"); try done.
    by eapply disjoint_weak.
  Qed.

  Lemma close_world_interp_list (W : WORLD) (C' : CmptName)
    (l : list (LAddr * Perm * (WORLD * CmptName * LWord → iProp Σ) * region_type))
    (l' : list LAddr)
    (lv : list LWord)
    :

    let la  := (fmap (fun '(a,p,φ,ρ) => a) l) in
    length l = length lv ->
    NoDup la ->
    la ## l' ->
    Forall (fun '(a,p,φ,ρ) => ρ ≠ Revoked) l ->
    Forall (fun '(a,p,φ,ρ) => ∀ Wv : WORLD * CmptName * LWord, Persistent (φ Wv)) l ->

    world_interp_open W C' (la++l')
    ∗ ([∗ list] '(a,p,φ,ρ) ∈ l, sts_state_std C' a ρ)
    ∗ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, a ↦ₖ v)
    ∗ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, monotonicity_guarantees_region C' φ p v ρ)
    ∗ ▷ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, φ (W,C',v))
    ∗ ([∗ list] '(a,p,φ,ρ) ∈ l, rel C' a p φ)
    ∗ ([∗ list] '(a,p,φ,ρ) ∈ l , ⌜ isO p = false ⌝)
      -∗ world_interp_open W C' l'.
  Proof.
    intros la.
    rewrite world_interp_open_eq /world_interp_open_def.
    iIntros (?????) "([Hr $ ] & Hstd & Hv & Hmono & Hφ & Hrel & Hp)".
    iDestruct (region_close_list with "[$Hr $Hstd $Hv $Hmono $Hφ $Hrel $Hp]") as "$"; auto.
  Qed.

End SO_World_List.

Section SO_World_Object.
  Context
    {Σ : gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg : sealStoreG Σ} {CNames : gset CmptName}
    {stsg : STSG Σ}
    {relg : relGS Σ} {cstackg : CSTACKG Σ}
    `{MP : MachineParameters}.

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
    interp W0 C (WCap t p g b e cur @@? π)
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
      "(#Hinterp_wca0_W0 & Hworld_interp_C & Hl_revoked & Hstk & Hlc)".
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

    (* Classify the readable object region, then partition it into permanent
       addresses and temporary addresses that were revoked with the current frame. *)
    iAssert (⌜Forall
      (fun a => std W0 !! addr_key π a = Some Permanent \/
                std W0 !! addr_key π a = Some Temporary) object⌝)%I
      as %Hobject_states.
    { iDestruct (readAllowed_valid_cap with "Hinterp_wca0_W0") as %Hvalid; auto.
      iPureIntro.
      eapply Forall_impl; eauto; cbn.
      intros a (ρ & Ha & Hρ).
      destruct ρ; [right|left|]; done.
    }
    assert (object ≡ₚ perms ++ temps) as Hobject_partition.
    { apply so_object_addresses_partition. exact Hobject_states. }
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
               ∃ pa Φa, ⌜∀ WCv, Persistent (Φa WCv)⌝ ∗ rel C (addr_key π a) pa Φa) ∗
             ([∗ list] a ∈ temps,
               heap_key_resource (addr_key π a)
                 (∃ pa Φa, ⌜∀ WCv, Persistent (Φa WCv)⌝ ∗ rel C (addr_key π a) pa Φa ∗
                    ∃ wa, TmpRes W0 C (addr_key π a) pa Φa wa)))%I
      with "[Hrevoked_temps]" as "[#Htemps_rels Hrevoked_temps]".
    { rewrite -big_sepL_sep. iApply (big_sepL_impl with "Hrevoked_temps").
      iIntros "!>" (i a _) "(%pa & %Φa & %Hpers & #Hrel & Hres)".
      iSplit; first (iExists pa, Φa; by iFrame "Hrel").
      iApply (heap_key_resource_mono with "[] Hres").
      iIntros "Hres". iExists pa, Φa. by iFrame "Hrel Hres". }

    (* Open only the permanent part through the world interpretation.  The
       permission, predicate, and STS witnesses stay local to this helper. *)
    iDestruct (read_allowed_inv_full_cap with "Hinterp_wca0_W0")
      as "Hinterp_wca0_invs"; auto.
    iAssert (
        ∃ (wca0_invs : list
             (LAddr * Perm * (WORLD * CmptName * LWord -> iProp Σ) * region_type)),
          ⌜(fun '(a, _, _, _) => a) <$> wca0_invs = addr_key π <$> perms⌝ ∗
          ⌜Forall
              (fun '(a, _, _, ρ) =>
                 std W0 !! a = Some ρ /\ ρ = Permanent)
              wca0_invs⌝ ∗
          ([∗ list] '(a, p0, φ, _) ∈ wca0_invs, rel C a p0 φ) ∗
          ⌜Forall
              (fun '(_, _, φ, _) =>
                 forall Wv : WORLD * CmptName * LWord, Persistent (φ Wv))
              wca0_invs⌝)%I
      as (wca0_invs)
        "(%Hwca0_invs_perma & %Hwca0_invs_std_perma
         & Hrels_wca0 & %Hpers_wca0_invs)".
    { iDestruct "Hinterp_wca0_invs" as "-#Hinterp_wca0_invs".
      iClear "#".
      setoid_rewrite Hobject_partition.
      iDestruct (big_sepL_app with "Hinterp_wca0_invs") as "[H _]".
      iDestruct "H" as "#H".
      assert (Forall (fun a => std W0 !! addr_key π a = Some Permanent) perms)
        as Hperms.
      { subst perms.
        rewrite /so_object_permanents /so_object_addresses.
        clear.
        induction (finz.seq_between b e); first done.
        cbn.
        destruct (decide (std W0 !! addr_key π a = Some Permanent)); last done.
        apply Forall_cons; split; auto.
      }
      generalize perms, Hperms.
      clear; intros l Hl.
      iInduction (l) as [|a l] "IH".
      - iExists []; cbn.
        repeat (iSplit; iPureIntro; done).
      - apply Forall_cons in Hl as [Ha Hl].
        cbn.
        iDestruct "H" as
          "[(%p' & %P' & %Hpermflow & %HpersP & HrelP
             & Hzcond & Hrcond & Hwcond & Hmono) H]".
        iDestruct ("IH" with "[%] [$]") as
          (invs) "(%Hl_ & %Hperma & #Hrels & %Hpers)"; auto.
        iExists (((addr_key π a, p', safeC P'), Permanent) :: invs).
        iSplit; first (iPureIntro; cbn; by rewrite Hl_).
        iSplit; first (iPureIntro; apply Forall_cons; split; auto).
        iSplit; first (cbn; iFrame "#").
        iPureIntro. apply Forall_cons; split; auto.
    }

    iEval (rewrite open_world_interp_empty) in "Hworld_interp_C".
    iDestruct (open_world_interp_list with
      "[$Hrels_wca0 $Hworld_interp_C]") as
      "(Hworld_interp_C & Hsts_std_wca0 & Hperms_res)".
    { rewrite Hwca0_invs_perma. apply NoDup_addr_key_fmap, so_object_permanents_NoDup. }
    { rewrite Hwca0_invs_perma. set_solver+. }
    { rewrite !Forall_forall in Hwca0_invs_std_perma |- *.
      intros [ [ [ ] ] ] Hx; cbn in *; simplify_eq.
      apply Hwca0_invs_std_perma in Hx.
      destruct Hx as [_ ->]; done.
    }
    { cbn in *.
      rewrite !Forall_forall in Hwca0_invs_std_perma |- *.
      intros [ [ [ ] ] ] Hx; cbn in *; simplify_eq.
      apply Hwca0_invs_std_perma in Hx.
      destruct Hx as [Hx ->].
      by apply revoke_lookup_Perm.
    }
    (* The object holds its cells, or it was freed: its keys are
       tombstones, and the world closes back. *)
    assert (Forall
      (λ x : LAddr * Perm * (WORLD * CmptName * LWord → iProp Σ) * region_type,
         ∃ a, x.1.1.1 = addr_key π a) wca0_invs) as Hwca0_keys.
    { rewrite Forall_forall. intros [ [ [k p0] φ0] ρ0] Hx. cbn.
      assert (k ∈ addr_key π <$> perms) as Hk.
      { rewrite -Hwca0_invs_perma. eapply list_elem_of_fmap_2'; [exact Hx|done]. }
      apply list_elem_of_fmap in Hk as [a' [-> _] ]. by exists a'. }
    assert (Forall (λ a, ∃ a', addr_key π a = addr_key π a') temps) as Htemps_keys.
    { apply Forall_forall. intros a' _. by exists a'. }
    iAssert (
        (([∗ list] '(a,p0,φ,ρ) ∈ wca0_invs,
            ∃ v, a ↦ₖ v
                 ∗ ▷ monotonicity_guarantees_region C φ p0 v ρ
                 ∗ ▷ φ (W1,C,v)
                 ∗ ⌜ isO p0 = false ⌝)
         ∗ ([∗ list] a ∈ temps,
              ∃ pa Φa, ⌜∀ WCv, Persistent (Φa WCv)⌝ ∗ rel C (addr_key π a) pa Φa ∗
                ∃ wa, TmpRes W0 C (addr_key π a) pa Φa wa))
        ∨ (∃ ι, ⌜π = Some ι⌝ ∗ ⌜wca0_invs ≠ [] ∨ temps ≠ []⌝ ∗ ι ⊒ AQuar))%I
      with "[Hperms_res Hrevoked_temps]"
      as "[ [Hperms_cells Hrevoked_temps] | (%ι & -> & %Hobject_ne & #Hq)]".
    { iDestruct (heap_key_resource_list_cases π wca0_invs (λ x, x.1.1.1)
        (λ '(a,p0,φ,ρ), ∃ v, a ↦ₖ v
             ∗ ▷ monotonicity_guarantees_region C φ p0 v ρ
             ∗ ▷ φ (W1,C,v)
             ∗ ⌜ isO p0 = false ⌝)%I Hwca0_keys
        with "[Hperms_res]") as "[Hperms_cells | (%ι & -> & %Hne & #Hq)]".
      { iApply (big_sepL_mono with "Hperms_res"). by intros ? [ [ [ ] ] ] _. }
      2: { iRight. iExists ι. iFrame "Hq". iPureIntro. split; [done | by left]. }
      iDestruct (heap_key_resource_list_cases π temps (addr_key π) _ Htemps_keys
        with "Hrevoked_temps") as "[Hrevoked_temps | (%ι & -> & %Hne & #Hq)]".
      2: { iRight. iExists ι. iFrame "Hq". iPureIntro. split; [done | by right]. }
      iLeft. iFrame. }
    2: { (* The object was freed *)
      iDestruct (close_world_interp_list_tomb W1 C ι wca0_invs []
        with "Hq Hworld_interp_C Hsts_std_wca0 Hrels_wca0") as "Hworld_interp_C".
      { rewrite Hwca0_invs_perma. apply NoDup_addr_key_fmap, so_object_permanents_NoDup. }
      { set_solver+. }
      { eapply Forall_impl; first exact Hwca0_keys.
        intros [ [ [k p0] φ0] ρ0] [a' Ha']. cbn in Ha'. by exists a'. }
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
      by iApply heap_key_close_tomb. }
    iDestruct (open_cells_list with "Hperms_cells") as (wca0_lv_perma)
      "(Hperms_lv & Hwca0_mono & Hwca0_φs & %Hlength_wca0_lv & Hwca0_pO)".
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

    iAssert (
        ∃ (lp : list Perm)
          (lφ : list (WORLD * CmptName * LWord -> iPropI Σ))
          (lv : list LWord),
          ⌜length lp = length temps⌝
          ∗ ⌜length lφ = length temps⌝
          ∗ ⌜length lv = length temps⌝
          ∗ ([∗ list] φ ∈ lφ,
               ⌜forall Wv : WORLD * CmptName * LWord, Persistent (φ Wv)⌝)
          ∗ ([∗ list] a;pφ ∈ temps;(zip lp lφ), rel C (addr_key π a) pφ.1 pφ.2)
          ∗ ([∗ list] p0 ∈ lp, ⌜isO p0 = false⌝)
          ∗ ([∗ list] a;v ∈ temps;lv, a ↦ₐ v)
          ∗ ([∗ list] a ∈ temps, key_share (addr_key π a))
          ∗ ([∗ list] lpφ;v ∈ (zip lp lφ);lv,
               if isWL lpφ.1 then future_pub_mono C lpφ.2 v
               else if isDL lpφ.1 then future_pub_mono C lpφ.2 v
                    else future_priv_mono C lpφ.2 v)
          ∗ ([∗ list] φ;v ∈ lφ;lv, φ (W0, C, v)))%I
      with "[Hrevoked_temps]" as
      (lp lφ wca0_lv_temps)
      "(%Hlen_lp & %Hlen_lφ & %Hlen_lv & Hlφ_pers
       & #Hlpφ_rels & HlpO & Htemps_lv & Htemps_shares & Hlpφ_mono & Hlφ_lv)".
    { iClear "#".
      generalize temps. clear; intros l.
      iInduction (l) as [|a l] "IH".
      - iExists [], [], []; cbn; done.
      - iDestruct "Hrevoked_temps" as "[Ha Hl]".
        iDestruct ("IH" with "Hl") as "Hl".
        iDestruct "Ha" as (p0 P HpersP) "[Hrel_a Ha]".
        iDestruct "Ha" as (v) "(HpO & Hv & HP & HmonoP)".
        iDestruct (addr_key_pointsto with "Hv") as "[Hv Hsh]".
        iDestruct "Hl" as (lp0 lP lv)
          "(% & % & % & %Hpers_lP & Hrels & HpOs & Hvs & Hshs & Hmonos & HPs)".
        iExists (p0 :: lp0), (P :: lP), (v :: lv).
        rewrite mono_temporary_eq.
        iFrame. iFrame "%".
        iPureIntro. cbn; lia.
    }
    (* Present [checkints] with one points-to list.  Its address order may be
       permuted, but the object contents and length remain unchanged. *)
    iDestruct (big_sepL2_app with "Hperms_lv Htemps_lv") as "Hobject_mem".

    (* The predicates of the temporary addresses of the object hold for
       integers (used by the first closing). *)
    iAssert (▷ [∗ list] φ ∈ lφ, zcond (safeUC φ) C)%I as "#Hzcond_lφ".
    { iClear "∗".
      iDestruct "Hlpφ_rels" as "-#Hrels".
      iDestruct "Hinterp_wca0_invs" as "-#Hinterp".
      iClear "#".
      setoid_rewrite Hobject_partition.
      iDestruct (big_sepL_app with "Hinterp") as "[_ #Hinterp]".
      generalize temps, Hlen_lp, Hlen_lφ. clear.
      intros l Hlen_lp Hlen_lφ.
      iInduction (l) as [|a l] "IH" forall (lp lφ Hlen_lp Hlen_lφ).
      all: destruct lφ; simplify_eq.
      all: destruct lp; simplify_eq.
      - done.
      - cbn.
        iDestruct "Hinterp" as
          "[(%p' & %P' & _ & _ & Hrel' & Hzcond & _) Hinterp]".
        iDestruct "Hrels" as "[Hrel #Hrels]".
        iDestruct (rel_agree with "[$Hrel $Hrel']") as "[_ #Heq]".
        iSplitL "Heq"; last (iApply "IH"; eauto).
        iNext. iIntros (????) "!> H"; cbn.
        iDestruct ("Heq" $! (W1, C, WInt z @@? π0)) as "-#Heq0".
        iDestruct ("Heq" $! (W2, C, WInt z @@? π0)) as "-#Heq1".
        iDestruct (internal_eq_iff with "Heq1") as "[_ Heq1]".
        iDestruct (internal_eq_iff with "Heq0") as "[Heq0 _]".
        iApply "Heq1".
        iDestruct ("Heq0" with "H") as "H".
        iApply "Hzcond"; eauto.
    }
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
        ([∗ list] '(k0, _, _, _);v ∈ wca0_invs;wca0_lv_perma,
           k0 ↦ₖ v)%I
        with "[Hperms_lv Hperms_shares]" as "Hperms_lv".
      { rewrite (so_invs_pointsto _ _ _ Hwca0_invs_perma) addr_key_pointsto_list.
        iFrame. }
      iDestruct (close_world_interp_list W1 C wca0_invs [] with
        "[$Hworld_interp_C $Hsts_std_wca0 $Hperms_lv $Hwca0_mono
          $Hwca0_φs $Hrels_wca0 $Hwca0_pO]") as "Hworld_interp_C".
      { by rewrite Hlength_wca0_lv length_fmap. }
      { rewrite Hwca0_invs_perma. apply NoDup_addr_key_fmap, so_object_permanents_NoDup. }
      { set_solver+. }
      { rewrite !Forall_forall in Hwca0_invs_std_perma |- *.
        intros [ [ [ ] ] ] Hx; cbn in *; simplify_eq.
        apply Hwca0_invs_std_perma in Hx.
        destruct Hx as [_ ->]; done.
      }
      { exact Hpers_wca0_invs. }
      rewrite -open_world_interp_empty.
      iAssert
        ([∗ list] a ∈ temps,
           ∃ p0 φ,
             ⌜forall Wv, Persistent (φ Wv)⌝ ∗
             temp_resources W0 C φ (addr_key π a) p0 ∗ rel C (addr_key π a) p0 φ)%I
        with "[Hlφ_pers HlpO Hlpφ_mono Htemps_lv Htemps_shares Hlφ_lv]"
        as "Htemps_res".
      { iDestruct "Hlpφ_rels" as "-#Hlpφ_rels".
        iClear "#".
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
        iDestruct "Hlφ_pers" as "[Hlφ_pers_a Hlφ_pers]".
        iDestruct "HlpO" as "[HlpO_a HlpO]".
        iDestruct "Hlpφ_mono" as "[Hlpφ_mono_a Hlpφ_mono]".
        iDestruct "Hlv" as "[Hlv_a Hlv]".
        iDestruct "Hlφ_lv" as "[Hlφ_lv_a Hlφ_lv]".
        iDestruct "Hlpφ_rels" as "[Hlpφ_rels_a Hlpφ_rels]".
        iDestruct "Htemps_shares" as "[Hsh_a Htemps_shares]".
        iDestruct (addr_key_pointsto with "[$Hlv_a $Hsh_a]") as "Hlv_a".
        iFrame.
        iApply ("IH" $! lφ lp lv with
          "[%] [%] [%] [$] [$] [$] [$] [$] [$] [$]"); eauto.
      }
      iAssert (RevokedResources W0 C (addr_key π <$> temps))%I
        with "[Htemps_res]" as "Hrevoked_temps".
      { iClear "#".
        rewrite /RevokedResources big_sepL_fmap.
        iApply (big_sepL_impl with "Htemps_res").
        iModIntro; iIntros (k ka Hka) "H".
        iDestruct "H" as (p0 phi Hpers) "(Htemp & Hrel)".
        iExists p0, phi.
        iFrame "Hrel".
        iSplit; first (iPureIntro; exact Hpers).
        iApply heap_key_resource_intro.
        iDestruct "Htemp" as (v) "(HpO & Ha & Hmono & Hphi)".
        iExists v.
        rewrite /TmpRes mono_temporary_eq.
        iFrame.
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
      ([∗ list] '(k0, _, _, _);v ∈ wca0_invs;wca0_lv_perma,
         k0 ↦ₖ v)%I
      with "[Hperms_lv Hperms_shares]" as "Hperms_lv".
    { rewrite (so_invs_pointsto _ _ _ Hwca0_invs_perma) addr_key_pointsto_list.
      iFrame. }

    (* The continuation first closes permanent resources back into [W1], then
       uses the integer-valued temporary addresses to reinstate the object. *)
    iDestruct (close_world_interp_list W1 C wca0_invs [] with
      "[$Hworld_interp_C $Hsts_std_wca0 $Hperms_lv $Hwca0_mono
        $Hwca0_φs $Hrels_wca0 $Hwca0_pO]") as "Hworld_interp_C".
    { by rewrite Hlength_wca0_lv length_fmap. }
    { rewrite Hwca0_invs_perma. apply NoDup_addr_key_fmap, so_object_permanents_NoDup. }
    { set_solver+. }
    { rewrite !Forall_forall in Hwca0_invs_std_perma |- *.
      intros [ [ [ ] ] ] Hx; cbn in *; simplify_eq.
      apply Hwca0_invs_std_perma in Hx.
      destruct Hx as [_ ->]; done.
    }
    { auto. }
    rewrite -open_world_interp_empty.

    iDestruct "Hzcond_lφ" as "-#Hzcond_lφ'".
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
    iAssert
      ([∗ list] a ∈ temps,
         ∃ p0 φ,
           ⌜forall Wv, Persistent (φ Wv)⌝ ∗
           temp_resources W1 C φ (addr_key π a) p0 ∗ rel C (addr_key π a) p0 φ)%I
      with "[Hlφ_pers HlpO Hlpφ_mono Htemps_lv Htemps_shares Hlφ_lv]"
      as "Htemps_closing_resources".
    { iDestruct "Hlpφ_rels" as "-#Hlpφ_rels".
      iClear "#".
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
      iDestruct "Hlφ_pers" as "[Hlφ_pers_a Hlφ_pers]".
      iDestruct "HlpO" as "[HlpO_a HlpO]".
      iDestruct "Hlpφ_mono" as "[Hlpφ_mono_a Hlpφ_mono]".
      iDestruct "Hlv" as "[Hlv_a Hlv]".
      iDestruct "Hlφ_lv" as "[Hlφ_lv_a Hlφ_lv]".
      iDestruct "Hlpφ_rels" as "[Hlpφ_rels_a Hlpφ_rels]".
      iDestruct "Htemps_shares" as "[Hsh_a Htemps_shares]".
      iDestruct (addr_key_pointsto with "[$Hlv_a $Hsh_a]") as "Hlv_a".
      iFrame.
      iApply ("IH" $! lφ lp lv with
        "[%] [%] [%] [$] [$] [$] [$] [$] [$] [$]"); eauto.
    }
    iMod (world_interp_restore_world W1 W1 C (addr_key π <$> temps) with
      "[$Hworld_interp_C] [Htemps_closing_resources]")
      as "Hworld_interp_C".
    { apply close_list_related_sts_pub. }
    { iClear "#".
      rewrite /RevokedResources big_sepL_fmap.
      iApply (big_sepL_impl with "Htemps_closing_resources").
      iModIntro; iIntros (k ka Hka) "H".
      iDestruct "H" as (p0 phi Hpers) "(Htemp & Hrel)".
      iExists p0, phi.
      iFrame "Hrel".
      iSplit; first (iPureIntro; exact Hpers).
      iApply heap_key_resource_intro.
      iDestruct "Htemp" as (v) "(HpO & Ha & Hmono & Hphi)".
      iExists v.
      rewrite /TmpRes mono_temporary_eq.
      iFrame.
    }
    set (W2 := close_list (addr_key π <$> temps) W1).

    iAssert (interp W2 C (Cap p g b e (finz.max b e) @@? π))%I
      as "#Hinterp_wca0_W2".
    { iEval (rewrite interp_unfold interp1_eq).
      iEval (rewrite interp_unfold interp1_eq) in "Hinterp_wca0_W0".
      destruct (isO p) eqn:HpO.
      { iDestruct "Hinterp_wca0_W0" as "[#Hok %Hcoverage]".
        iSplit; first iExact "Hok".
        iPureIntro.
        intros x Hx Hheap.
          specialize (Hcoverage x Hx Hheap).
          rewrite /region_state_nwl in Hcoverage |- *.
          assert (Hxeq : std W0 !! addr_key π x = std W2 !! addr_key π x).
          { rewrite Forall_forall in Hobject_states.
            assert (Hobj : x ∈ object)
              by (unfold object, so_object_addresses; exact Hx).
            destruct (Hobject_states x Hobj) as [Hx'|Hx']; rewrite Hx'; symmetry.
            - rewrite close_list_lookup_not_in.
              { cbn. by apply revoke_lookup_Perm. }
              intro Hcontra.
              apply elem_of_addr_key_fmap in Hcontra.
              apply list_elem_of_filter in Hcontra as [Hcontra _].
              by rewrite Hcontra in Hx'.
            - apply close_list_lookup_in; auto.
              + cbn; apply revoke_lookup_Monotemp; auto.
              + apply elem_of_addr_key_fmap, list_elem_of_filter; split; done. }
          rewrite -Hxeq. exact Hcoverage. }
      destruct (has_sreg_access p); first done.
      iDestruct "Hinterp_wca0_W0" as "[Hinterp $]".
      iClear "∗".
      iApply (big_sepL_impl with "Hinterp").
      iModIntro.
      iIntros (k x Hx)
        "(%px & %Px & %Hpx_flow & %Hpers_Px & Hrelx
         & Hzcondx & Hrcondx & Hwcondx & Hmonox & %Hstatex)".
      iFrame "∗%".
      apply list_elem_of_lookup_2 in Hx.
      rewrite Forall_forall in Hobject_states.
      assert (std W0 !! addr_key π x = std W2 !! addr_key π x) as Hxeq.
      { destruct (Hobject_states x Hx) as [Hx'|Hx']; rewrite Hx'; symmetry.
        - rewrite close_list_lookup_not_in.
          { cbn. by apply revoke_lookup_Perm. }
          intro Hcontra.
          apply elem_of_addr_key_fmap in Hcontra.
          apply list_elem_of_filter in Hcontra as [Hcontra _].
          by rewrite Hcontra in Hx'.
        - apply close_list_lookup_in; auto.
          + cbn; apply revoke_lookup_Monotemp; auto.
          + apply elem_of_addr_key_fmap, list_elem_of_filter; split; done.
      }
      iSplitL "Hmonox".
      - rewrite /monoReq. by rewrite Hxeq.
      - iPureIntro.
        destruct (isWL p);
          rewrite !/region_state_nwl !/region_state_pwl in Hstatex |- *;
          rewrite -Hxeq; done.
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
    iIntros (Hp Htag_or_empty Hno_overlap) "#Hinterp_csp #Hinterp_object Hworld_interp_C Hlc".
    iMod (world_interp_revoke_stack with "[$Hinterp_csp $Hworld_interp_C]")
      as (l_revoked) "(%Hextract & Hworld_interp_C & Hstack_revoked & _
                       & >[%stk_mem Hstk] & Hl_revoked & _)".
    iMod (stack_object_open_region_for_checkints
            W0 C t p g b e a π csp_b csp_e l_revoked stk_mem
           with "[$Hinterp_object $Hworld_interp_C $Hl_revoked $Hstk $Hlc]")
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
