From iris.proofmode Require Import proofmode.
From griotte Require Export region_invariants sts_multiple_updates.
From griotte Require Import logrel monotone interp_weakening.
From griotte Require Import compartment_layout mkregion_helpers disjoint_regions_tactics.
From griotte Require Import switcher.
From griotte Require Import world_ghost_theory region_invariants_allocation.
From griotte Require Import stdpp_extra.

Section region_alloc_cmpt.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Definition exported_entries_sealable (C_cmpt : cmpt) : list Sealable :=
    let export_tbl_addrs := finz.seq_between (cmpt_exp_tbl_entries_start C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt) in
    let exported_word g a := (SCap true RO g (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt) a) in
    ((exported_word Global) <$> export_tbl_addrs) ++ ((exported_word Local) <$> export_tbl_addrs).

  Definition exported_entries_words (C_cmpt : cmpt) : gset LWord :=
    list_to_set ((λ sb, lword_of_word (WSealable sb)) <$> (exported_entries_sealable C_cmpt)).
  Definition exported_entries_sealed (C_cmpt : cmpt) : gset LWord :=
    list_to_set ((λ sb, lword_of_word (WSealed ot_switcher sb)) <$> (exported_entries_sealable C_cmpt)).

  (** The Global regions of a compartment are not in the local world, which
      the compartment's allocation leaves unchanged. *)
  Definition std_update_compartment (W : WORLD) (C_cmpt : cmpt) := W.

  Lemma std_update_compartment_pub (W : WORLD) (C_cmpt : cmpt) :
    let imports_addrs := finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_a_code C_cmpt) in
    let code_addrs := finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt) in
    let data_addrs := finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) in
    Forall (λ k, std W !! LNonHeap k = None) imports_addrs →
    Forall (λ k, std W !! LNonHeap k = None) code_addrs →
    Forall (λ k, std W !! LNonHeap k = None) data_addrs →
    related_sts_pub_world W (std_update_compartment W C_cmpt).
  Proof. intros * _ _ _. apply related_sts_pub_refl_world. Qed.

  Lemma switcher_cmpt_disjoint_std_update_compartment
    (W : WORLD) (C_cmpt : cmpt) (switcher_cmpt : cmptSwitcher) (a : Addr) :
    a ∈ finz.seq_between (b_stack switcher_cmpt) (e_stack switcher_cmpt) ->
    switcher_cmpt_disjoint C_cmpt switcher_cmpt ->
    std W !! LNonHeap a = None ->
    std (std_update_compartment W C_cmpt) !! LNonHeap a = None.
  Proof. by intros _ _ Ha_W. Qed.

  (** Global regions whose predicates need the region predicates, with a
      frame: the keys enter the map open, then close with their bodies. *)
  (* TODO: move to model/world_ghost_theory.v *)
  Lemma world_interp_extend_perm_sepL2_open_frame
    {E : coPset}
    (W : WORLD) (C : CmptName) (la : list Addr) (lw : list LWord) (p : Perm) (φ : CmptName * LWord → iProp Σ)
    (R : iProp Σ) `{∀ Cv, Persistent (φ Cv)} :
    NoDup la ->
    isO p = false ->
    world_interp W C -∗
    ([∗ list] k;v ∈ la;lw, k ↦ₐ v) -∗
    (
      ([∗ list] k ∈ la, LNonHeap k ↪ᵍ[C]{p} φ)
      -∗
      ([∗ list] v ∈ lw, φ (C, v)) ∗ R
    )

    ={E}=∗

    world_interp W C ∗
    ([∗ list] k ∈ la, LNonHeap k ↪ᵍ[C]{p} φ) ∗
    ([∗ list] v ∈ lw, φ (C, v)) ∗
    R.
  Proof.
    iIntros (Hnd HpO) "Hw Hcells Hφ".
    rewrite !world_interp_gl /world_interp_open_gl.
    iDestruct "Hw" as "[(%M & Hm) $]".
    assert (NoDup (LNonHeap <$> la)) as Hnd'.
    { apply NoDup_fmap; [intros ?? [= ->]; done|done]. }
    iMod (g_insert_open_list C M ∅ (LNonHeap <$> la) lw p φ with "Hm [Hcells]")
      as (M') "(Hm & #Hrels & Hcells)"; [done|set_solver|by rewrite big_sepL2_fmap_l|].
    iDestruct ("Hφ" with "[]") as "[#Hφs HR]"; [by rewrite big_sepL_fmap|].
    iModIntro. rewrite big_sepL_fmap. iFrame "Hrels Hφs HR".
    iExists M'. iApply (g_close_list with "Hm [Hcells]"); [done|set_solver|done|done|].
    iDestruct (big_sepL2_length with "Hcells") as %Hlen.
    iApply (big_sepL2_impl with "Hcells"). iIntros "!>" (i k v Hk Hv) "Hc".
    iFrame "Hc". apply list_lookup_fmap_Some in Hk as (a & -> & Ha). iSplitR.
    - iNext. by iApply (big_sepL_lookup with "Hφs").
    - by iApply (big_sepL_lookup with "Hrels").
  Qed.

  (** The PCC and CGP of a compartment are valid in every world, from the
      Global regions of their addresses. *)
  Lemma cmpt_caps_interp (W : WORLD) (C_cmpt : cmpt) (C : CmptName) :
    let imports_addrs := finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_a_code C_cmpt) in
    let code_addrs := finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt) in
    let data_addrs := finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) in
    let pcc_cap := (Cap RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_b_pcc C_cmpt)%a) in
    let cgp_cap := (Cap RW Global (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) (cmpt_b_cgp C_cmpt)%a) in
    ([∗ list] k ∈ (imports_addrs++code_addrs), LNonHeap k ↪ᵍ[C]{RX} interp_in_mem_gC) -∗
    ([∗ list] k ∈ data_addrs, LNonHeap k ↪ᵍ[C]{RW} interp_in_mem_gC) -∗
    interp W C pcc_cap ∗ interp W C cgp_cap.
  Proof.
    intros *.
    pose proof (cmpt_pcc_disjoint_from_mmio C_cmpt) as Hpcc_shadow.
    pose proof (cmpt_pcc_disjoint_from_heap C_cmpt) as Hpcc_heap.
    pose proof (cmpt_cgp_disjoint_from_mmio C_cmpt) as Hcgp_shadow.
    pose proof (cmpt_cgp_disjoint_from_heap C_cmpt) as Hcgp_heap.
    iIntros "#Hrel_pcc #Hrel_data".
    iSplit.
    - iEval (rewrite interp_unfold /=).
      iSplitR; last (iSplit; [iPureIntro; exact Hpcc_shadow|iApply heap_cap_ok_disjoint; exact Hpcc_heap]).
      iApply big_sepL_intro; iModIntro.
      iIntros (ka a Ha).
      rewrite /addr_key.
      iExists RX, (interp_in_mem RWL).
      iEval (cbn).
      iSplit; first done.
      iSplit; first (iPureIntro ; by apply persistent_cond_interp_in_mem).
      iSplit.
      { apply list_elem_of_lookup_2 in Ha.
        iApply (big_sepL_elem_of with "Hrel_pcc"); eauto.
        rewrite -finz_seq_between_split;auto.
        pose proof (cmpt_import_size C_cmpt) as HC.
        pose proof (cmpt_code_size C_cmpt) as HC'.
        solve_addr.
      }
      iSplit; first (iNext ; by iApply zcond_interp_in_mem).
      iSplit; first (iNext ; by iApply rcond_interp_in_mem).
      done.
    - iEval (rewrite interp_unfold /=).
      iSplitR; last (iSplit; [iPureIntro; exact Hcgp_shadow|iApply heap_cap_ok_disjoint; exact Hcgp_heap]).
      iApply big_sepL_intro; iModIntro.
      iIntros (ka a Ha).
      rewrite /addr_key.
      iExists RW, (interp_in_mem RWL).
      iEval (cbn).
      iSplit; first done.
      iSplit; first (iPureIntro ; by apply persistent_cond_interp_in_mem).
      iDestruct (big_sepL_lookup _ _ ka a Ha with "Hrel_data") as "Hrel_a".
      iSplit; first iExact "Hrel_a".
      iSplit; first (iNext ; by iApply zcond_interp_in_mem).
      iSplit; first (iNext ; by iApply rcond_interp_in_mem).
      iNext ; by iApply wcond_interp_in_mem.
  Qed.

  Lemma alloc_compartment_interp_rel {E : coPset} (W : WORLD) ( C_cmpt : cmpt ) (C : CmptName) :
    let imports_addrs := finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_a_code C_cmpt) in
    let code_addrs := finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt) in
    let data_addrs := finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) in
    let pcc_cap := (Cap RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_b_pcc C_cmpt)%a) in
    let cgp_cap := (Cap RW Global (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) (cmpt_b_cgp C_cmpt)%a) in
    let Wfinal := std_update_compartment W C_cmpt in

    Forall (λ k, std W !! LNonHeap k = None) imports_addrs →
    Forall (λ k, std W !! LNonHeap k = None) code_addrs →
    Forall (λ k, std W !! LNonHeap k = None) data_addrs →

    Forall (λ w : Word, is_z w) (cmpt_code C_cmpt) ->
    Forall (is_initial_data_word C_cmpt) (cmpt_data C_cmpt) ->

    ([∗ list] k;v ∈ imports_addrs ; lword_of_word <$> cmpt_imports C_cmpt, k ↦ₐ v) -∗
    ([∗ list] k;v ∈ code_addrs ; lword_of_word <$> cmpt_code C_cmpt, k ↦ₐ v) -∗
    ([∗ list] k;v ∈ data_addrs ; lword_of_word <$> cmpt_data C_cmpt, k ↦ₐ v) -∗

    (
      (
        ([∗ list] k ∈ (imports_addrs++code_addrs), LNonHeap k ↪ᵍ[C]{RX} interp_in_mem_gC) ∗
        ([∗ list] k ∈ (data_addrs), LNonHeap k ↪ᵍ[C]{RW} interp_in_mem_gC)
      )
      -∗
      ([∗ list] v ∈ lword_of_word <$> cmpt_imports C_cmpt, interp_in_mem_gC (C, v)) ∗
      ([∗ set] v ∈ exported_entries_sealed C_cmpt, interp_in_mem RWL Wfinal C v)
    ) -∗

    world_interp W C

    ={E}=∗

    world_interp Wfinal C ∗
    interp Wfinal C pcc_cap ∗
    interp Wfinal C cgp_cap ∗
    ([∗ list] v ∈ lword_of_word <$> cmpt_imports C_cmpt, interp_in_mem RWL Wfinal C v) ∗
    ([∗ set] v ∈ exported_entries_sealed C_cmpt, interp_in_mem RWL Wfinal C v)
  .
  Proof.
    intros * Himports Hcode Hdata C_code C_data.
    pose proof (cmpt_pcc_disjoint_from_mmio C_cmpt) as Hpcc_shadow.
    pose proof (cmpt_pcc_disjoint_from_heap C_cmpt) as Hpcc_heap.
    pose proof (cmpt_cgp_disjoint_from_mmio C_cmpt) as Hcgp_shadow.
    pose proof (cmpt_cgp_disjoint_from_heap C_cmpt) as Hcgp_heap.
    iIntros "HC_imports HC_code HC_data Himport_interp Hworld_C".

    iMod (world_interp_extend_perm_sepL2 W C
            code_addrs (lword_of_word <$> cmpt_code C_cmpt)
            RX interp_in_mem_gC
           with "Hworld_C [HC_code]") as "(Hworld_C & #HC_code)".
    {
      rewrite !big_sepL2_fmap_r.
      iApply (big_sepL2_mono with "HC_code").
      intros k v1 v2 Hv1 Hv2. cbn. iIntros "Hv".
      pose proof (Forall_lookup_1 _ _ _ _ C_code Hv2) as Hncap.
      destruct v2; [| by inversion Hncap..].
      rewrite /PermRes key_pointsto_nonheap.
      iFrame "Hv".
      iSplit; first done.
      iApply interp_int.
    }

    iMod (world_interp_extend_perm_sepL2_open W C
            data_addrs
            (lword_of_word <$> cmpt_data C_cmpt)
            RW interp_in_mem_gC
           with "Hworld_C HC_data []") as "(Hworld_C & #HC_data & _)".
    { apply finz_seq_between_NoDup. }
    { done. }
    {
      iClear "#".
      rewrite big_sepL_fmap.
      clear -C_data Hcgp_shadow Hcgp_heap.
      generalize dependent (cmpt_data C_cmpt); iIntros (l Hl).
      iIntros "#Hrels".
      iInduction (l) as [| w l] "IH"; first done.
      cbn.
      apply Forall_cons in Hl; destruct Hl as [Hw Hl].
      iSplitL; last (iApply "IH"; eauto).
      destruct w as [| [|] | |] ; cbn in Hw; destruct Hw as [Hw|Hw]; cbn in Hw; try done
      ; [|destruct g ; last done].
      - iApply interp_int.
      - iApply interp_to_in_mem.
        destruct tag; last (iApply interp_untagged; done).
        rewrite interp_unfold interp1_eq.
        destruct Hw as (Hp & Hb & He).
        destruct (isO p) eqn:HpO.
        { assert (Hsub : finz.seq_between b e ⊆
              finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt)).
          { intros x Hx. apply elem_of_finz_seq_between in Hx.
            apply elem_of_finz_seq_between. solve_addr. }
          assert (Hdisjoint : disjoint_from_heap b e).
          { rewrite /disjoint_from_heap in Hcgp_heap |- *.
            set_solver+Hsub Hcgp_heap. }
          iSplit; first by iApply heap_cap_ok_disjoint.
          iApply big_sepL_intro. iIntros "!>" (i x Hx%list_elem_of_lookup_2 Hheap).
          rewrite /disjoint_from_heap elem_of_disjoint in Hdisjoint.
          exfalso. eapply Hdisjoint; first exact Hx.
          apply withinBounds_true_iff in Hheap.
          apply elem_of_finz_seq_between. solve_addr. }
        destruct (has_sreg_access p) eqn:HpXSR.
        { destruct p as [ [] w dl dro ]; cbn in *; done. }
        assert (isWL p = false) as Hwl.
        { destruct p as [ rx [] dl dro ]; cbn in *; auto.
          rewrite !andb_True in Hp.
          destruct Hp as [ [ [] ] ]; done.
        }
        rewrite Hwl.
        iSplitR; cycle 1.
        { assert (finz.seq_between b e ⊆
            finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt)) as Hbounds.
          { intros a' Ha'. apply elem_of_finz_seq_between in Ha'.
            apply elem_of_finz_seq_between; solve_addr. }
          iSplit.
          - iPureIntro. split; first done.
            pose proof Hcgp_shadow as [Hcgp_sh Hcgp_rev]. split.
            + rewrite /disjoint_from_shadow in Hcgp_sh |- *.
              set_solver+Hbounds Hcgp_sh.
            + set_solver+Hbounds Hcgp_rev.
          - iApply heap_cap_ok_disjoint.
            rewrite /disjoint_from_heap in Hcgp_heap |- *.
            set_solver+Hbounds Hcgp_heap.
        }
        iApply big_sepL_intro; iModIntro.
        iIntros (k a' Ha').
        apply list_elem_of_lookup_2, elem_of_finz_seq_between in Ha'.
        assert (a' ∈ₐ [(cmpt_b_cgp C_cmpt), (cmpt_e_cgp C_cmpt))) as Ha'' by solve_addr.
        apply elem_of_finz_seq_between in Ha''.
        rewrite /addr_key.
        iDestruct (big_sepL_elem_of with "Hrels") as "Hrel_a'"; eauto.
        iExists RW, (interp_in_mem RWL); cbn.
        iSplit; first done.
        iSplit; first (iPureIntro; apply persistent_cond_interp_in_mem).
        iSplit; first by rewrite /region_rel Hwl.
        iSplit; first iApply zcond_interp_in_mem.
        iSplit; first iApply rcond_interp_in_mem.
        iApply wcond_interp_in_mem.
    }

    iMod (world_interp_extend_perm_sepL2_open_frame W C
            imports_addrs
            (lword_of_word <$> cmpt_imports C_cmpt)
            RX interp_in_mem_gC
            ([∗ set] v ∈ exported_entries_sealed C_cmpt, interp_in_mem RWL Wfinal C v)
           with "Hworld_C HC_imports [Himport_interp]")
      as "(Hworld_C & #HC_imports & #Hinterp_imports & Hinterp_exports)".
    { apply finz_seq_between_NoDup. }
    { done. }
    {
      iIntros "#HC_imports".
      iApply "Himport_interp".
      iFrame "HC_data".
      rewrite big_sepL_app. iFrame "HC_imports HC_code".
    }
    iDestruct (big_sepL_app _ imports_addrs code_addrs with "[$HC_imports $HC_code]") as "HC_PCC".
    iDestruct (cmpt_caps_interp Wfinal C_cmpt C with "HC_PCC HC_data") as "[#Hpcc #Hcgp]".
    iModIntro. iFrame "Hworld_C Hpcc Hcgp Hinterp_exports".
    iApply (big_sepL_impl with "Hinterp_imports").
    iIntros "!>" (k v Hv) "Hv". iApply (interp_in_mem_monotone with "Hv").
    apply related_sts_pub_world_empty.
  Qed.

  Lemma alloc_compartment_interp (E : coPset) (W : WORLD) ( C_cmpt : cmpt ) (C : CmptName) :
    let imports_addrs := finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_a_code C_cmpt) in
    let code_addrs := finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt) in
    let data_addrs := finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) in
    let pcc_cap := (Cap RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_b_pcc C_cmpt)%a) in
    let cgp_cap := (Cap RW Global (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) (cmpt_b_cgp C_cmpt)%a) in
    let Wfinal := std_update_compartment W C_cmpt in

    Forall (λ k, std W !! LNonHeap k = None) imports_addrs →
    Forall (λ k, std W !! LNonHeap k = None) code_addrs →
    Forall (λ k, std W !! LNonHeap k = None) data_addrs →

    Forall (λ w : Word, is_z w) (cmpt_code C_cmpt) ->
    Forall (is_initial_data_word C_cmpt) (cmpt_data C_cmpt) ->

    ([∗ list] k;v ∈ imports_addrs ; lword_of_word <$> cmpt_imports C_cmpt, k ↦ₐ v) -∗
    ([∗ list] k;v ∈ code_addrs ; lword_of_word <$> cmpt_code C_cmpt, k ↦ₐ v) -∗
    ([∗ list] k;v ∈ data_addrs ; lword_of_word <$> cmpt_data C_cmpt, k ↦ₐ v) -∗
    (
      (
        interp Wfinal C pcc_cap ∗
        interp Wfinal C cgp_cap
      )
      -∗
      ([∗ list] v ∈ lword_of_word <$> cmpt_imports C_cmpt, interp_in_mem_gC (C, v)) ∗
      ([∗ set] v ∈ exported_entries_sealed C_cmpt, interp_in_mem RWL Wfinal C v)
    )
    -∗

    world_interp W C

    ={E}=∗

    world_interp Wfinal C ∗
    interp Wfinal C pcc_cap ∗
    interp Wfinal C cgp_cap ∗
    ([∗ list] v ∈ lword_of_word <$> cmpt_imports C_cmpt, interp_in_mem RWL Wfinal C v) ∗
    ([∗ set] v ∈ exported_entries_sealed C_cmpt, interp_in_mem RWL Wfinal C v)
  .
  Proof.
    intros * Himports Hcode Hdata C_code C_data.
    iIntros "HC_imports HC_code HC_data Himport_interp Hworld_C".
    iApply (alloc_compartment_interp_rel W C_cmpt C Himports Hcode Hdata C_code C_data
      with "HC_imports HC_code HC_data [Himport_interp] Hworld_C").
    iIntros "(#Hrel_pcc & #Hrel_data)".
    iApply "Himport_interp".
    iApply (cmpt_caps_interp with "Hrel_pcc Hrel_data").
  Qed.

End region_alloc_cmpt.
