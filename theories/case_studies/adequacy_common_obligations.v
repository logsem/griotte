From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From griotte Require Import logrel monotone interp_weakening.
From griotte Require Import assert_spec.
From griotte Require Import
  world_interp_revocation world_interp_allocation world_interp_allocation_compartments.
From griotte Require Import switcher_base_interp.
From griotte Require Import stack_world_resources.
From griotte Require Import compartment_layout switcher_adequacy adequacy_helpers.
From griotte Require Import allocator_resources heap_region.
From griotte Require Import context_switch_layout_instance.

(** * Shared building blocks for the case-study adequacy proofs.

    The lemmas below compose: each adequacy proof calls them in turn
    (Iris adequacy wrapper, world initialisation, compartment
    initialisation, adversary world, register split, size obligations),
    and can insert its own initialisation steps in between. *)

(** ** Concrete capabilities of the initial configuration *)
Section initial_capabilities.
  Context `{MP: MachineParameters}.

  (** PCC and CGP of a compartment, as stored in its export table. *)
  Definition cmpt_pcc_cap (C_cmpt : cmpt) : Word :=
    Cap RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_b_pcc C_cmpt).
  Definition cmpt_cgp_cap (C_cmpt : cmpt) : Word :=
    Cap RW Global (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) (cmpt_b_cgp C_cmpt).

  (** Stack and trusted-stack capabilities of the switcher. *)
  Definition stack_cap (sw : cmptSwitcher) : Word :=
    Cap RWL Local (b_stack sw) (e_stack sw) (stk_start_a (b_stack sw) (e_stack sw)).

  (** The (unsealed) export-table capability for the entry at address [a]. *)
  Definition cmpt_export (C_cmpt : cmpt) (a : Addr) : Sealable :=
    SCap true RO Global (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt) a.

  Definition stack_addrs (sw : cmptSwitcher) : list Addr :=
    finz.seq_between (b_stack sw) (e_stack sw).

  (** The addresses of the entries of the export table of a compartment. *)
  Definition cmpt_exp_tbl_addrs (C_cmpt : cmpt) : list Addr :=
    finz.seq_between (cmpt_exp_tbl_entries_start C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt).

  Lemma cmpt_exp_tbl_addrs_lookup (C_cmpt : cmpt) (i : nat) (a : Addr) :
    cmpt_exp_tbl_addrs C_cmpt !! i = Some a →
    a = (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_entry i) ∧
    i < length (cmpt_exp_tbl_entries C_cmpt).
  Proof.
    intros Ha.
    pose proof (cmpt_exp_tbl_entries_size C_cmpt) as Hsize.
    pose proof (cmpt_exp_tbl_header_size C_cmpt) as Hheader.
    assert (i < length (cmpt_exp_tbl_entries C_cmpt)) as Hi.
    { apply lookup_lt_Some in Ha.
      rewrite /cmpt_exp_tbl_addrs finz_seq_between_length /finz.dist in Ha.
      solve_addr. }
    rewrite /cmpt_exp_tbl_addrs (finz_seq_between_lookup _ _ _ (length (cmpt_exp_tbl_entries C_cmpt)))
      in Ha; [|done|done].
    simplify_eq. split; [solve_addr | done].
  Qed.

  Lemma cmpt_exp_tbl_addrs_elem_of (C_cmpt : cmpt) (i : nat) :
    i < length (cmpt_exp_tbl_entries C_cmpt) →
    (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_entry i) ∈ cmpt_exp_tbl_addrs C_cmpt.
  Proof.
    intros Hi.
    pose proof (cmpt_exp_tbl_entries_size C_cmpt) as Hsize.
    pose proof (cmpt_exp_tbl_header_size C_cmpt) as Hheader.
    apply list_elem_of_lookup_2 with i.
    rewrite /cmpt_exp_tbl_addrs (finz_seq_between_lookup _ _ _ (length (cmpt_exp_tbl_entries C_cmpt)));
      [| done | done].
    f_equal; solve_addr.
  Qed.

End initial_capabilities.

(** ** Rootedness of the initial configuration

    The [ghost_init_cond] side condition of [cerise_flag_adequacy], with a
    set [R] of heap roots held by the compartments (an allocator holds the
    root of the heap; without an allocator, [R] is empty). *)
Section initial_rootedness.
  Context `{MP: MachineParameters} {TV : trapVector}.

  (** The initial condition, with heap roots [R]. *)
  Lemma ghost_init_cond_roots (R : gset Addr) (σ : ExecConf) :
    shadowtbl σ = initial_heap_shadow →
    (∀ a, a ∈ R → is_heap_address a = true) →
    mem_rooted R (mem σ) →
    word_rooted R (pcc σ) →
    (∀ r w, reg σ !! r = Some w → word_rooted R w) →
    (∀ sr w, sreg σ !! sr = Some w → word_rooted R w) →
    mem_avoids_mmio (mem σ) →
    heap_mapped (mem σ) →
    reg σ !! cnull = Some (WInt 0) →
    mem_exec_ok (mem σ) →
    word_exec_ok (pcc σ) →
    (∀ r w, reg σ !! r = Some w → word_exec_ok w) →
    (∀ sr w, sreg σ !! sr = Some w → word_exec_ok w) →
    pc_ok (pcc σ) →
    (∀ sr w, is_pc_sreg sr = true → sreg σ !! sr = Some w → pc_ok w) →
    (∀ sr, sr ∈ reserved_sregs → is_Some (sreg σ !! sr)) →
    sreg σ !! mtcc = Some mtcc_vec →
    (∃ z, sreg σ !! mtval = Some (WInt z)) →
    (∃ mie mpie, sreg σ !! mstatus = Some (WInt (mstatus_enc mie mpie))) →
    ghost_init_cond σ R.
  Proof.
    intros Hσsh HR Hm Hpc Hreg Hsreg Hmmio Hheap Hnull Hmx Hpcx Hregx Hsregx Hpcok Hsregok
      Hreserved Hmtcc Hmtval Hmstatus.
    assert (∀ a, is_heap_address a = true →
      initial_heap_shadow !! a = Some ShadowLive) as Hsh.
    { intros a Ha. rewrite /initial_heap_shadow lookup_fmap /initial_heap_memory
        lookup_gset_to_gmap option_guard_True //.
      by apply elem_of_heap_addresses. }
    constructor; cbn.
    - exact HR.
    - intros a Ha. rewrite Hσsh. by apply Hsh, HR.
    - intros a Ha. eexists. rewrite Hσsh. by apply Hsh.
    - intros a w b Ha. by eapply Hm.
    - intros b. by eapply Hpc.
    - intros r w b _ Hw. by eapply Hreg.
    - intros sr w b Hw. by eapply Hsreg.
    - exact Hmmio.
    - exact Hheap.
    - intros w Hw. rewrite Hnull in Hw. by injection Hw as <-.
    - exact Hmx.
    - exact Hpcx.
    - exact Hregx.
    - exact Hsregx.
    - exact Hpcok.
    - exact Hsregok.
    - exact Hreserved.
    - exact Hmtcc.
    - exact Hmtval.
    - exact Hmstatus.
  Qed.

End initial_rootedness.

(** ** Lists of pools and of thread resources *)
Section thread_ghost_lists.
  Context {Σ : gFunctors}.

  (** A non-atomic pool for each element of a list. *)
  Lemma na_pools_alloc {na_invg : na_invariants.na_invG Σ} {A} (l : list A) :
    ⊢ |==> ∃ ps : list na_inv_pool_name, [∗ list] p; _ ∈ ps; l, na_own p ⊤.
  Proof.
    iInduction l as [|x l] "IH".
    - iModIntro. by iExists [].
    - iMod na_alloc as (p) "Hna".
      iMod "IH" as (ps) "Hnas".
      iModIntro. iExists (p :: ps).
      rewrite big_sepL2_cons. iFrame.
  Qed.

  Lemma big_sepL2_nth_l {A B} (Φ : A → B → iProp Σ) (xs : list A) (ys : list B) (d : A) :
    ([∗ list] x; y ∈ xs; ys, Φ x y) ⊢ [∗ list] k ↦ y ∈ ys, Φ (nth k xs d) y.
  Proof.
    revert ys. induction xs as [|x xs IH]; intros [|y ys]; cbn.
    - by iIntros.
    - by iIntros "[]".
    - by iIntros "[]".
    - iIntros "[$ H]". by iApply IH.
  Qed.
End thread_ghost_lists.

(** ** The worlds of the compartments under their regimes *)
Section world_resources_init_all.
  (* Threads [0] and [t] meet here: every form names its thread. *)
  #[local] Remove Hints ceriseG_of : typeclass_instances.
  Context
    {Σ : gFunctors}
    {ceriseb : ceriseBaseG Σ} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg : sealStoreG Σ} {stsg : STSG Σ} {relg : relGS Σ}
    `{MP : MachineParameters}.

  (** The compartments of [Cs] in shared mode. *)
  Definition shared_of (Cs : gset CmptName) : gset CmptName :=
    filter (λ C, cmpt_shared C = true) Cs.

  (** The first thread turns the world of each compartment into the world
      premise of its regime. The map of Permanent regions of each shared
      compartment goes into its invariant, which the other threads then
      share. *)
  Lemma world_resources_init_all (E : coPset) (Wf : CmptName → WORLD) (Cs : gset CmptName) :
    ([∗ set] C ∈ Cs,
       world_interp (ceriseg := ceriseG_of (UserThread 0)) (th := UserThread 0) (Wf C) C)
    ={E}=∗
    ([∗ set] C ∈ Cs, world_resources (th := UserThread 0) (Wf C) C) ∗
    ([∗ set] C ∈ shared_of Cs, wg_inv C).
  Proof.
    iIntros "Hworlds".
    rewrite /shared_of big_sepS_filter' -big_sepS_sep.
    iApply big_sepS_fupd.
    iApply (big_sepS_impl with "Hworlds").
    iIntros "!>" (C _) "Hworld".
    case_decide as Hshared.
    - by iApply (world_resources_init_shared (th := UserThread 0) with "Hworld").
    - apply not_true_is_false in Hshared.
      rewrite (world_resources_exclusive (th := UserThread 0) _ _ Hshared).
      by iFrame.
  Qed.

  (** Another thread joins the shared compartments with its local maps; it
      keeps those of the other compartments. *)
  Lemma world_resources_join_all (t : Thread) (W : WORLD) (Cs : gset CmptName) :
    ([∗ set] C ∈ shared_of Cs, wg_inv C) -∗
    ([∗ set] C ∈ Cs, local_region_map t W C ∅) -∗
    ([∗ set] C ∈ shared_of Cs, world_resources (th := t) W C) ∗
    ([∗ set] C ∈ filter (λ C, cmpt_shared C = false) Cs, local_region_map t W C ∅).
  Proof.
    iIntros "Hinvs Hlocals".
    rewrite /shared_of !big_sepS_filter' -big_sepS_sep.
    iCombine "Hinvs Hlocals" as "Hboth".
    rewrite -big_sepS_sep.
    iApply (big_sepS_impl with "Hboth").
    iIntros "!>" (C _) "[Hinv Hlocal]".
    case_decide as Hshared; case_decide as Hexcl.
    - by rewrite Hshared in Hexcl.
    - iSplitL; last done.
      by iApply (world_resources_join (th := t) with "Hinv Hlocal").
    - by iFrame.
    - by apply not_true_is_false in Hshared.
  Qed.
End world_resources_init_all.

(** ** Worlds of the adversaries *)
Section adversary_world.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}.

  (** The world of an adversary compartment after the allocation of the
      switcher stack with state [ρ]. *)
  Definition adv_world_with (ρ : region_type) (W : WORLD) (sw : cmptSwitcher) : WORLD :=
    std_update_multiple W (stack_addrs sw) ρ.

  (** The data of the main compartment is not in the world of an adversary. *)
  Lemma main_cgp_not_in_adv_world (ρ : region_type) (W : WORLD)
    (sw : cmptSwitcher) (main : cmpt) (a : Addr) :
    switcher_cmpt_disjoint main sw →
    LNonHeap a ∉ dom (std W) →
    a ∈ finz.seq_between (cmpt_b_cgp main) (cmpt_e_cgp main) →
    LNonHeap a ∉ dom (std (adv_world_with ρ W sw)).
  Proof.
    intros Hsw HaW Ha Hcontra.
    rewrite /adv_world_with in Hcontra.
    apply elem_of_dom_std_multiple_update in Hcontra as [Hcontra|Hcontra].
    { rewrite /switcher_cmpt_disjoint /cmpt_switcher_region /cmpt_switcher_stack_region
        /cmpt_region /cmpt_cgp_region in Hsw.
      rewrite /stack_addrs in Hcontra.
      set_solver. }
    done.
  Qed.

  (** A stack outside of the mmio and heap regions, whose addresses are
      temporary in the world, with [interp_in_mem] safety invariants, is safe
      to share. *)
  Lemma interp_stack_temporary (W : WORLD) (C : CmptName) (b e : Addr) :
    disjoint_from_mmio b e →
    disjoint_from_heap b e →
    Forall (λ a, std W !! LNonHeap a = Some Temporary) (finz.seq_between b e) →
    ([∗ list] a ∈ finz.seq_between b e, (LNonHeap a) ↪ˡ[C]{RWL} interp_in_memC) -∗
    interp W C (Cap RWL Local b e (stk_start_a b e)).
  Proof.
    iIntros (Hmmio Hheap Htemp) "#Hrel".
    rewrite /stk_start_a.
    iEval (rewrite interp_unfold /=). iLeft.
    iSplit.
    { iApply big_sepL_intro; iModIntro.
      iIntros (k a Ha).
      rewrite /addr_key.
      iExists RWL, (interp_in_mem RWL).
      iEval (cbn).
      iSplit; first done.
      iSplit; first (iPureIntro ; by apply persistent_cond_interp_in_mem).
      assert (std W !! LNonHeap a = Some Temporary) by (rewrite Forall_lookup in Htemp; eauto).
      iSplit.
      { rewrite /region_rel /= /region_rel_l.
        iDestruct (big_sepL_lookup with "Hrel") as "$"; first done.
        iSplit; first done. iApply mono_pub_interp_in_mem. }
      iSplit; first (iNext ; by iApply zcond_interp_in_mem).
      iSplit; first (iNext ; by iApply rcond_l_interp_in_mem_nodl).
      iNext ; by iApply wcond_wl_interp_in_mem. }
    iSplit; first done.
    by iApply heap_cap_ok_disjoint.
  Qed.

  (** ** Sealed entries exported by an adversary *)

  Lemma exported_entries_sealed_words (C_cmpt : cmpt) (v : LWord) :
    v ∈ exported_entries_sealed C_cmpt →
    ∃ sb, v = lword_of_word (WSealed switcher.ot_switcher sb) ∧
          heap_authority_base (WSealed switcher.ot_switcher sb) = None ∧
          (∃ g a, sb = SCap true RO g (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt) a) ∧
          {[lword_of_word (WSealable sb); lword_of_word (borrow (WSealable sb))]}
            ⊆ exported_entries_words C_cmpt.
  Proof.
    rewrite /exported_entries_sealed /exported_entries_words elem_of_list_to_set.
    intros (sb & -> & Hsb)%list_elem_of_fmap.
    exists sb; split; first done.
    split.
    { rewrite /exported_entries_sealable in Hsb.
      destruct (heap_authority_base _) as [b|] eqn:Hauth; last done.
      apply heap_authority_base_heap_cap_base in Hauth.
      apply elem_of_app in Hsb as [Hsb|Hsb]; apply list_elem_of_fmap in Hsb as (a & -> & Ha);
        match type of Hauth with
        | heap_cap_base (WSealed ?o (SCap ?t ?p ?g ?b ?e ?a)) = _ =>
            pose proof (sealed_cap_nonheap o t p g b e a (cmpt_exp_tbl_base_not_heap C_cmpt))
              as Hnonheap
        end;
        unfold is_heap_cap in Hnonheap; rewrite Hauth in Hnonheap; discriminate. }
    split.
    { rewrite /exported_entries_sealable in Hsb.
      apply elem_of_app in Hsb as [Hsb|Hsb]; apply list_elem_of_fmap in Hsb as (a & -> & Ha);
        by eexists _, a. }
    apply union_subseteq; split; apply singleton_subseteq_l, elem_of_list_to_set,
      list_elem_of_fmap.
    - by exists sb.
    - rewrite /exported_entries_sealable in Hsb |- *.
      apply elem_of_app in Hsb as [Hsb|Hsb]; apply list_elem_of_fmap in Hsb as (a & -> & Ha);
        (eexists; split; [done|]); apply elem_of_app; right; apply list_elem_of_fmap; by exists a.
  Qed.

  (** The sealed exported entries are safe, once the switcher's seal
      predicate holds of the exported entries. *)
  Lemma exported_entries_sealed_interp (W : WORLD) (C : CmptName) (C_cmpt : cmpt) :
    switcher.ot_switcher ↪ₒ{SealGlobal} ot_switcher_propC -∗
    □ ([∗ list] a ∈ cmpt_exp_tbl_addrs C_cmpt,
         ot_switcher_prop W C (WSealable (cmpt_export C_cmpt a))) -∗
    [∗ set] v ∈ exported_entries_sealed C_cmpt, interp W C v.
  Proof.
    iIntros "#Hseal_pred #Hprops".
    iApply big_sepS_intro; iIntros "!>" (v Hv).
    rewrite /exported_entries_sealed /exported_entries_sealable elem_of_list_to_set in Hv.
    apply list_elem_of_fmap in Hv as (sb & -> & Hsb).
    assert (∃ g a, sb = SCap true RO g (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt) a
                   ∧ a ∈ cmpt_exp_tbl_addrs C_cmpt) as (g & a & -> & Ha).
    { apply elem_of_app in Hsb as [Hsb|Hsb]; apply list_elem_of_fmap in Hsb as (a & -> & Ha);
        by eexists _, a. }
    iApply (interp_sb_intro_global W C switcher.ot_switcher ot_switcher_propC
              (SCap true RO g (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt) a) None
              with "[] Hseal_pred"); first iApply ot_switcher_kind_ok.
    - iDestruct (big_sepL_elem_of _ _ _ Ha with "Hprops") as "Hprop".
      assert (lforce_global (Cap RO g (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt) a @@? None)
              = lword_of_word (WSealable (cmpt_export C_cmpt a))) as Heq
        by (destruct g; reflexivity).
      (* [iNext] would search the unfolded switcher predicate for laters *)
      rewrite Heq /ot_switcher_propC. cbn [fst snd].
      iApply bi.later_intro. iExact "Hprop".
    - iApply heap_cap_ok_disjoint. apply cmpt_exp_tbl_disjoint_from_heap.
  Qed.

  (** Allocate an adversary compartment [C_cmpt] in the world: its imports,
      code and data become permanent, and its exported entries are sealed with
      [ot_switcher] in the world. The caller proves that the exported entries
      satisfy the sealing predicate of the switcher ([Hexports]) and that the
      imports are safe ([Himports]). *)
  Lemma alloc_adversary_compartment {E : coPset} (W : WORLD) (C_cmpt : cmpt) (C : CmptName) :
    Forall is_z (cmpt_code C_cmpt) →
    Forall (is_initial_data_word C_cmpt) (cmpt_data C_cmpt) →
    switcher.ot_switcher ↪ₒ{SealGlobal} ot_switcher_propC -∗
    [[ cmpt_b_pcc C_cmpt, cmpt_a_code C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_imports C_cmpt ]] -∗
    [[ cmpt_a_code C_cmpt, cmpt_e_pcc C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_code C_cmpt ]] -∗
    [[ cmpt_b_cgp C_cmpt, cmpt_e_cgp C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_data C_cmpt ]] -∗
    □ (∀ i a, ⌜cmpt_exp_tbl_addrs C_cmpt !! i = Some a⌝ -∗
        interp W C (cmpt_pcc_cap C_cmpt) -∗
        interp W C (cmpt_cgp_cap C_cmpt) -∗
        ot_switcher_prop W C (WSealable (cmpt_export C_cmpt a))) -∗
    ((interp W C (cmpt_pcc_cap C_cmpt) ∗ interp W C (cmpt_cgp_cap C_cmpt) ∗
      [∗ set] v ∈ exported_entries_sealed C_cmpt, interp W C v) -∗
     [∗ list] v ∈ lword_of_word <$> cmpt_imports C_cmpt, safeGC interp_cmpt_threads (C, v)) -∗
    thread_in th C -∗
    world_interp W C
    ={E}=∗
    world_interp W C ∗
    interp W C (cmpt_pcc_cap C_cmpt) ∗
    interp W C (cmpt_cgp_cap C_cmpt) ∗
    [∗ set] v ∈ exported_entries_sealed C_cmpt, interp W C v.
  Proof.
    intros Hcode Hdata.
    iIntros "#Hseal_pred HC_imports HC_code HC_data #Hexports Himports #Hthread Hworld".
    iAssert (□ ([∗ set] v ∈ exported_entries_sealed C_cmpt, interp_in_mem RWL W C v) -∗
               [∗ set] v ∈ exported_entries_sealed C_cmpt, interp W C v)%I as "Hto_interp".
    { iIntros "#Hexp".
      iApply (big_sepS_impl with "Hexp"); iIntros "!>" (v Hv) "Hv".
      destruct (exported_entries_sealed_words C_cmpt v Hv) as (sb & -> & Hbase & _).
      iApply (interp_in_mem_load_result with "Hv").
      by right. }
    iMod (alloc_compartment_interp with "HC_imports HC_code HC_data [Himports] Hthread Hworld")
      as "($ & $ & $ & _ & #Hexp)"; [done..| |].
    { iIntros "(#Hpcc & #Hcgp)".
      iDestruct (exported_entries_sealed_interp W with "Hseal_pred []") as "#Hexp".
      { iModIntro. iApply big_sepL_intro; iIntros "!>" (i a Ha).
        iApply ("Hexports" with "[//] Hpcc Hcgp"). }
      iSplitL "Himports"; first (iApply "Himports"; iFrame "#").
      iApply (big_sepS_impl with "Hexp"); iIntros "!>" (v Hv) "Hv".
      by iApply interp_to_in_mem. }
    iModIntro. by iApply "Hto_interp".
  Qed.

  (** Initialise the world of an adversary compartment [C_cmpt]:
      - its imports, code and data become permanent;
      - its exported entries are sealed with [ot_switcher] in the world;
      - the switcher stack becomes temporary.
      The caller proves that the exported entries satisfy the sealing
      predicate of the switcher ([Hexports]) and that the imports are safe
      ([Himports]). *)
  Lemma initialise_adversary_world {E : coPset}
    (W : WORLD) (sw : cmptSwitcher) (C_cmpt : cmpt) (C : CmptName) :
    let Wadv := adv_world_with Temporary W sw in
    switcher_cmpt_disjoint C_cmpt sw →
    (∀ a, a ∈ cmpt_region C_cmpt ∨ a ∈ stack_addrs sw → std W !! LNonHeap a = None) →
    Forall is_z (cmpt_code C_cmpt) →
    Forall (is_initial_data_word C_cmpt) (cmpt_data C_cmpt) →
    Forall is_z (stack_content sw) →
    switcher.ot_switcher ↪ₒ{SealGlobal} ot_switcher_propC -∗
    [[ cmpt_b_pcc C_cmpt, cmpt_a_code C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_imports C_cmpt ]] -∗
    [[ cmpt_a_code C_cmpt, cmpt_e_pcc C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_code C_cmpt ]] -∗
    [[ cmpt_b_cgp C_cmpt, cmpt_e_cgp C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_data C_cmpt ]] -∗
    [[ b_stack sw, e_stack sw ]] ↦ₐ [[ lword_of_word <$> stack_content sw ]] -∗
    □ (∀ i a, ⌜cmpt_exp_tbl_addrs C_cmpt !! i = Some a⌝ -∗
        interp W C (cmpt_pcc_cap C_cmpt) -∗
        interp W C (cmpt_cgp_cap C_cmpt) -∗
        ot_switcher_prop W C (WSealable (cmpt_export C_cmpt a))) -∗
    ((interp W C (cmpt_pcc_cap C_cmpt) ∗ interp W C (cmpt_cgp_cap C_cmpt) ∗
      [∗ set] v ∈ exported_entries_sealed C_cmpt, interp W C v) -∗
     [∗ list] v ∈ lword_of_word <$> cmpt_imports C_cmpt, safeGC interp_cmpt_threads (C, v)) -∗
    thread_in th C -∗
    world_interp W C
    ={E}=∗
    world_interp Wadv C ∗
    interp Wadv C (cmpt_pcc_cap C_cmpt) ∗
    interp Wadv C (cmpt_cgp_cap C_cmpt) ∗
    interp Wadv C (stack_cap sw) ∗
    [∗ set] v ∈ exported_entries_sealed C_cmpt, interp Wadv C v.
  Proof.
    intros Wadv Hsw Hfree Hcode Hdata Hstack.
    assert (Forall (λ k, std W !! LNonHeap k = None) (stack_addrs sw)) as Hfree_stack.
    { apply Forall_forall; intros a Ha; apply Hfree; by right. }
    iIntros "#Hseal_pred HC_imports HC_code HC_data Hstack #Hexports Himports #Hthread Hworld".
    iMod (alloc_adversary_compartment with
           "Hseal_pred HC_imports HC_code HC_data Hexports Himports Hthread Hworld")
      as "(Hworld & #Hpcc & #Hcgp & #Hexp)"; eauto.
    iMod (world_interp_extend_temp_sepL2 _ _ (stack_addrs sw)
            (lword_of_word <$> stack_content sw) RWL interp_in_memC
           with "Hworld [Hstack]") as "(Hworld & #Hrel_stk)".
    { done. }
    { exact Hfree_stack. }
    { rewrite big_sepL2_fmap_r.
      iEval (rewrite /region_pointsto big_sepL2_fmap_r) in "Hstack".
      iApply (big_sepL2_mono ((fun (_ : nat) (k : finz.finz MemNum) (v : Word) =>
        pointsto k (DfracOwn (pos_to_Qp 1)) (lword_of_word v))) with "Hstack").
      intros k v1 v2 Hv1 Hv2. cbn. iIntros "Hv". rewrite /TmpRes key_pointsto_nonheap.
      iFrame "Hv".
      pose proof (Forall_lookup_1 _ _ _ _ Hstack Hv2) as Hncap.
      destruct v2; [| by inversion Hncap..].
      iSplit; first done.
      iSplit.
      { iApply bi.later_intro. iEval (rewrite /interp_in_mem_pre /=).
        iApply interp_int. }
      iApply bi.later_intro. iApply future_pub_mono_interp_in_mem_z.
    }
    iModIntro; iFrame "Hworld".
    assert (related_sts_priv_world W Wadv) as Hrelated.
    { apply related_sts_pub_priv_world, related_sts_pub_update_multiple.
      eapply Forall_impl; first exact Hfree_stack.
      intros a Ha; cbn in *; by rewrite not_elem_of_dom.
    }
    iSplit; first (iApply (interp_monotone_nl with "[] [] Hpcc"); eauto).
    iSplit; first (iApply (interp_monotone_nl with "[] [] Hcgp"); eauto).
    iSplit.
    { iApply interp_stack_temporary; last done.
      - apply stack_disjoint_from_mmio.
      - apply stack_disjoint_from_heap.
      - apply Forall_forall; intros a Ha.
        by apply std_sta_update_multiple_lookup_in_i. }
    iApply (big_sepS_impl with "Hexp"); iIntros "!>" (v Hv) "Hv".
    destruct (exported_entries_sealed_words C_cmpt v Hv) as (sb & -> & _).
    by iApply (interp_sealed_global_kind_world_free with "Hseal_pred Hv").
  Qed.

  (** Same as [initialise_adversary_world], but the switcher stack is
      allocated as revoked: the caller keeps its points-to predicates. *)
  Lemma initialise_adversary_world_revoked {E : coPset}
    (W : WORLD) (sw : cmptSwitcher) (C_cmpt : cmpt) (C : CmptName) :
    let Wadv := adv_world_with Revoked W sw in
    switcher_cmpt_disjoint C_cmpt sw →
    (∀ a, a ∈ cmpt_region C_cmpt ∨ a ∈ stack_addrs sw → std W !! LNonHeap a = None) →
    Forall is_z (cmpt_code C_cmpt) →
    Forall (is_initial_data_word C_cmpt) (cmpt_data C_cmpt) →
    switcher.ot_switcher ↪ₒ{SealGlobal} ot_switcher_propC -∗
    [[ cmpt_b_pcc C_cmpt, cmpt_a_code C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_imports C_cmpt ]] -∗
    [[ cmpt_a_code C_cmpt, cmpt_e_pcc C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_code C_cmpt ]] -∗
    [[ cmpt_b_cgp C_cmpt, cmpt_e_cgp C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_data C_cmpt ]] -∗
    □ (∀ i a, ⌜cmpt_exp_tbl_addrs C_cmpt !! i = Some a⌝ -∗
        interp W C (cmpt_pcc_cap C_cmpt) -∗
        interp W C (cmpt_cgp_cap C_cmpt) -∗
        ot_switcher_prop W C (WSealable (cmpt_export C_cmpt a))) -∗
    ((interp W C (cmpt_pcc_cap C_cmpt) ∗ interp W C (cmpt_cgp_cap C_cmpt) ∗
      [∗ set] v ∈ exported_entries_sealed C_cmpt, interp W C v) -∗
     [∗ list] v ∈ lword_of_word <$> cmpt_imports C_cmpt, safeGC interp_cmpt_threads (C, v)) -∗
    thread_in th C -∗
    world_interp W C
    ={E}=∗
    world_interp Wadv C ∗
    interp Wadv C (cmpt_pcc_cap C_cmpt) ∗
    interp Wadv C (cmpt_cgp_cap C_cmpt) ∗
    StackRevokedResources Wadv C (stack_addrs sw) ∗
    [∗ set] v ∈ exported_entries_sealed C_cmpt, interp Wadv C v.
  Proof.
    intros Wadv Hsw Hfree Hcode Hdata.
    assert (Forall (λ k, std W !! LNonHeap k = None) (stack_addrs sw)) as Hfree_stack.
    { apply Forall_forall; intros a Ha; apply Hfree; by right. }
    iIntros "#Hseal_pred HC_imports HC_code HC_data #Hexports Himports #Hthread Hworld".
    iMod (alloc_adversary_compartment with
           "Hseal_pred HC_imports HC_code HC_data Hexports Himports Hthread Hworld")
      as "(Hworld & #Hpcc & #Hcgp & #Hexp)"; eauto.
    iMod (world_interp_extend_revoked_sepL2 _ _ (stack_addrs sw) RWL interp_in_memC
           with "Hworld")
      as "(Hworld & Hrel_stk)".
    { exact Hfree_stack. }
    iModIntro; iFrame "Hworld".
    assert (related_sts_priv_world W Wadv) as Hrelated.
    { apply related_sts_pub_priv_world, related_sts_pub_update_multiple.
      eapply Forall_impl; first exact Hfree_stack.
      intros a Ha; cbn in *; by rewrite not_elem_of_dom.
    }
    iSplit; first (iApply (interp_monotone_nl with "[] [] Hpcc"); eauto).
    iSplit; first (iApply (interp_monotone_nl with "[] [] Hcgp"); eauto).
    iSplitL "Hrel_stk"; first by iApply StackWorldResources_from_rel_stack.
    iApply (big_sepS_impl with "Hexp"); iIntros "!>" (v Hv) "Hv".
    destruct (exported_entries_sealed_words C_cmpt v Hv) as (sb & -> & _).
    by iApply (interp_sealed_global_kind_world_free with "Hseal_pred Hv").
  Qed.

End adversary_world.

(** ** Exported entry points of an adversary *)
Section adversary_exports.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}.

  (** The [i]-th entry of the export table of an adversary [C_cmpt],
      at address [a], satisfies the sealing predicate of the switcher. *)
  Lemma adversary_export_prop
    (W : WORLD) (C : CmptName) (C_cmpt : cmpt)
    (posture : InterruptStatus) (i args minstk off : nat) (a : Addr) (eh ehs : Z) :
    cmpt_exp_tbl_entries C_cmpt !! i = Some (WInt (encode_entry_point posture args minstk off)) →
    (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_entry i) = a →
    args < 7 →
    is_Some (cmpt_b_pcc C_cmpt + off%nat)%a →
    switcher_threads C ⊢
    cmpt_exp_tbl_pcc C_cmpt ↦ₐ□ cmpt_pcc_cap C_cmpt -∗
    cmpt_exp_tbl_cgp C_cmpt ↦ₐ□ cmpt_cgp_cap C_cmpt -∗
    cmpt_exp_tbl_pcc C_cmpt ↦ₑ□{stackful} eh -∗
    cmpt_exp_tbl_pcc C_cmpt ↦ₑ□{stackless} ehs -∗
    ([∗ list] k ↦ v ∈ cmpt_exp_tbl_entries C_cmpt,
       (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_entry k) ↦ₐ□ lword_of_word v) -∗
    interp W C (cmpt_pcc_cap C_cmpt) -∗
    interp W C (cmpt_cgp_cap C_cmpt) -∗
    ot_switcher_prop W C (WSealable (cmpt_export C_cmpt a)).
  Proof.
    intros Hi Ha Hargs Hentry_some.
    iIntros "#Hswitcher #Hpcc #Hcgp #Heh #Hehs #Hentries #Hinterp_pcc #Hinterp_cgp".
    pose proof (cmpt_exp_tbl_entries_size C_cmpt) as Hsize.
    pose proof (cmpt_exp_tbl_header_size C_cmpt) as Hheader.
    assert (i < length (cmpt_exp_tbl_entries C_cmpt)) as Hi_lt
        by (by apply lookup_lt_Some in Hi).
    iDestruct (big_sepL_lookup with "Hentries") as "Hentry_inv"; first done.
    rewrite Ha.
    iApply (ot_switcher_interp _ _ _ Global _ posture args minstk off eh ehs with
              "Hswitcher Hpcc Hcgp Heh Hehs Hentry_inv Hinterp_pcc Hinterp_cgp");
      [solve_addr|lia|done].
  Qed.

  (** The [i]-th sealed entry of the export table of an adversary [C_cmpt]
      is safe to share. *)
  Lemma adversary_export_interp (W : WORLD) (C : CmptName) (C_cmpt : cmpt) (i : nat) (a : Addr) :
    cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_entry i = a →
    i < length (cmpt_exp_tbl_entries C_cmpt) →
    ([∗ set] v ∈ exported_entries_sealed C_cmpt, interp W C v) -∗
    interp W C (WSealed switcher.ot_switcher (cmpt_export C_cmpt a)).
  Proof.
    intros <- Hi.
    iIntros "#Hexp".
    iApply (big_sepS_elem_of with "Hexp").
    rewrite /exported_entries_sealed /exported_entries_sealable elem_of_list_to_set.
    apply list_elem_of_fmap; eexists; split; first done.
    apply elem_of_app; left.
    apply list_elem_of_fmap; eexists; split; first done.
    by apply cmpt_exp_tbl_addrs_elem_of.
  Qed.

  (** All the entries of the export table of an adversary [C_cmpt] satisfy
      the sealing predicate of the switcher, given its export table as a list
      of quadruples (interrupt posture, number of arguments, minimum stack
      size, offset). This is the premise of [initialise_adversary_world]. *)
  Lemma adversary_exports_prop
    (W : WORLD) (C : CmptName) (C_cmpt : cmpt)
    (exports : list (InterruptStatus * nat * nat * nat)) (eh ehs : Z) :
    cmpt_exp_tbl_entries C_cmpt =
      (λ e : InterruptStatus * nat * nat * nat,
         WInt (encode_entry_point e.1.1.1 e.1.1.2 e.1.2 e.2)) <$> exports →
    Forall (λ e, e.1.1.2 < 7) exports →
    Forall (λ e : InterruptStatus * nat * nat * nat, is_Some (cmpt_b_pcc C_cmpt + e.2%nat)%a) exports →
    switcher_threads C ⊢
    cmpt_exp_tbl_pcc C_cmpt ↦ₐ□ cmpt_pcc_cap C_cmpt -∗
    cmpt_exp_tbl_cgp C_cmpt ↦ₐ□ cmpt_cgp_cap C_cmpt -∗
    cmpt_exp_tbl_pcc C_cmpt ↦ₑ□{stackful} eh -∗
    cmpt_exp_tbl_pcc C_cmpt ↦ₑ□{stackless} ehs -∗
    ([∗ list] k ↦ v ∈ cmpt_exp_tbl_entries C_cmpt,
       (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_entry k) ↦ₐ□ lword_of_word v) -∗
    □ (∀ i a, ⌜cmpt_exp_tbl_addrs C_cmpt !! i = Some a⌝ -∗
        interp W C (cmpt_pcc_cap C_cmpt) -∗
        interp W C (cmpt_cgp_cap C_cmpt) -∗
        ot_switcher_prop W C (WSealable (cmpt_export C_cmpt a))).
  Proof.
    intros Htbl Hargs Hentries_some.
    iIntros "#Hswitcher #Hpcc #Hcgp #Heh #Hehs #Hentries !>"
      (i a Ha) "#Hinterp_pcc #Hinterp_cgp".
    destruct (cmpt_exp_tbl_addrs_lookup _ _ _ Ha) as [-> Hi].
    rewrite Htbl length_fmap in Hi.
    destruct (lookup_lt_is_Some_2 _ _ Hi) as [ [ [ [posture args] minstk] offset] He].
    iApply (adversary_export_prop _ _ _ posture i args minstk offset _ eh ehs
             with "Hswitcher Hpcc Hcgp Heh Hehs Hentries Hinterp_pcc Hinterp_cgp").
    - by rewrite Htbl list_lookup_fmap He.
    - done.
    - by apply (Forall_lookup_1 _ _ _ _ Hargs He).
    - by apply (Forall_lookup_1 _ _ _ _ Hentries_some He).
  Qed.

End adversary_exports.

(** ** Imports of an adversary

    The imports of an adversary are safe to store in its memory: the
    switcher call sentry, and words sealed in the world (for instance, the
    entries exported by a service compartment). *)
Section adversary_imports.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}.

  (** A word sealed with [o] is safe once the Global-kind predicate of [o]
      holds of its sealable. *)
  Lemma interp_sealed_of_seals (W : WORLD) (C : CmptName) (o : OType)
    (Pc : Thread * WORLD * CmptName * LWord → iProp Σ) (sb : Sealable) :
    (∀ p g b e a, sb = SCap true p g b e a → disjoint_from_heap b e) →
    o ↪ₒ{SealGlobal} Pc -∗
    seal_kind_ok SealGlobal C Pc -∗
    ▷ Pc (th, W, C, lforce_global (lword_of_word (WSealable sb))) -∗
    interp W C (WSealed o sb).
  Proof.
    iIntros (Hheap) "#Hseal #Hok HP".
    iApply (interp_sb_intro_global with "Hok Hseal HP").
    destruct sb as [ [] p g b e a | [] ? ? ? ]; cbn; try done.
    iApply heap_cap_ok_disjoint; by eapply Hheap.
  Qed.

  (** A global word sealed with a Global-kind otype is a safe import. *)
  Lemma sealed_import_safe (C : CmptName) (o : OType)
    (Pc : Thread * WORLD * CmptName * LWord → iProp Σ) (sb : Sealable) :
    let w := lword_of_word (WSealed o sb) in
    isGlobalSealable sb = true →
    (∀ p g b e a, sb = SCap true p g b e a → disjoint_from_heap b e) →
    o ↪ₒ{SealGlobal} Pc -∗
    seal_kind_ok SealGlobal C Pc -∗
    □ ▷ Pc (th, ∅, C, lword_of_word (WSealable sb)) -∗
    safeGC interp_cmpt_threads (C, w).
  Proof.
    intros w Hglobal Hheap; subst w.
    iIntros "#Hseal #Hok #HP".
    iEval (cbn; rewrite /interp_cmpt_threads /=).
    iIntros "!>" (t') "_".
    (* A Global sealed word is valid at every thread *)
    assert (isLocalWord (lword_of_word (WSealed o sb)).(lw) = false) as Hnl
      by (destruct sb as [ [] ? [] | [] ? [] ]; by cbn in * ).
    rewrite -(interp_global_thread_world_free th t' ∅ ∅ C _ Hnl).
    iApply (interp_sealed_of_seals ∅ C o Pc sb Hheap with "Hseal Hok").
    assert (lforce_global (lword_of_word (WSealable sb)) = lword_of_word (WSealable sb)) as Heq
      by (destruct sb as [ [] ? [] | [] ? [] ]; by cbn in * ).
    rewrite Heq. iExact "HP".
  Qed.

End adversary_imports.

(** ** Entry points exported by a service compartment *)
Section service_exports.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}.

  (** The (global) exported entries [sbs] of a service compartment, sealed
      with [ot_switcher], are safe in the world [W] of a compartment [C],
      given that they satisfy the sealing predicate of the switcher. *)
  Lemma seal_service_exports (W : WORLD) (C : CmptName) (sbs : list Sealable) :
    Forall (λ sb, isGlobalSealable sb = true) sbs →
    Forall (λ sb, ∀ p g b e a, sb = SCap true p g b e a → disjoint_from_heap b e) sbs →
    switcher.ot_switcher ↪ₒ{SealGlobal} ot_switcher_propC -∗
    □ ([∗ list] sb ∈ sbs, ot_switcher_prop W C (WSealable sb)) -∗
    [∗ list] sb ∈ sbs, interp W C (WSealed switcher.ot_switcher sb).
  Proof.
    intros Hglobal Hheap.
    iIntros "#Hseal_pred #Hprops".
    iApply big_sepL_intro; iIntros "!>" (i sb Hsb).
    pose proof (Forall_lookup_1 _ _ _ _ Hglobal Hsb) as Hg.
    pose proof (Forall_lookup_1 _ _ _ _ Hheap Hsb) as Hh.
    iApply (interp_sealed_of_seals W C switcher.ot_switcher ot_switcher_propC sb Hh
              with "Hseal_pred []").
    { iApply ot_switcher_kind_ok. }
    iDestruct (big_sepL_lookup _ _ _ _ Hsb with "Hprops") as "Hprop".
    assert (lforce_global (lword_of_word (WSealable sb)) = lword_of_word (WSealable sb)) as Heq
      by (destruct sb as [ [] ? [] | [] ? [] ]; by cbn in * ).
    rewrite Heq /ot_switcher_propC. cbn [fst snd].
    iApply bi.later_intro. iExact "Hprop".
  Qed.

End service_exports.

(** ** Initial heap *)
Section initial_heap.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} `{MP: MachineParameters}.

  (** The resources of the initial heap: its memory and its unpainted
      shadow entries, in the form taken by an allocator initialisation. *)
  Lemma initial_heap_resources :
    ([∗ map] a↦w ∈ initial_heap_memory, a ↦ₐ lword_of_word w) -∗
    ([∗ map] a↦s ∈ initial_heap_shadow, a ↦ₛ s) -∗
    [∗ map] a↦v ∈ lword_of_word <$> initial_heap_memory, a ↦ₐ v ∗ a ↦ₛ ShadowLive.
  Proof.
    iIntros "Hheap Hshadow".
    iEval (rewrite /initial_heap_shadow big_sepM_fmap) in "Hshadow".
    rewrite big_sepM_fmap.
    iApply big_sepM_sep; iFrame.
  Qed.

End initial_heap.

(** ** Exported entry points of the main compartment *)
Section main_exports.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}.

  (** An exported entry [sb] of the main compartment, sealed with
      [ot_switcher], is safe in the world [W], given that it satisfies the
      sealing predicate of the switcher. *)
  Lemma seal_main_export (W : WORLD) (C : CmptName) (sb : Sealable) :
    isGlobalSealable sb = true →
    (∀ p g b e a, sb = SCap true p g b e a → disjoint_from_heap b e) →
    switcher.ot_switcher ↪ₒ{SealGlobal} ot_switcher_propC -∗
    ot_switcher_prop W C (WSealable sb) -∗
    interp W C (WSealed switcher.ot_switcher sb).
  Proof.
    intros Hglobal Hheap.
    iIntros "#Hseal_pred #Hprop".
    iApply (interp_sealed_of_seals W C switcher.ot_switcher ot_switcher_propC sb Hheap
              with "Hseal_pred []").
    { iApply ot_switcher_kind_ok. }
    assert (lforce_global (lword_of_word (WSealable sb)) = lword_of_word (WSealable sb)) as Heq
      by (destruct sb as [ [] ? [] | [] ? [] ]; by cbn in * ).
    rewrite Heq /ot_switcher_propC. cbn [fst snd].
    iApply bi.later_intro. iExact "Hprop".
  Qed.

End main_exports.

(** ** Size obligations of the main compartment *)
Section main_sizes.
  Context `{MP: MachineParameters}.


(** ** The words of a save area, by computation *)

Lemma save_area_lookup_mstatus a b c d h m :
  (lword_of_word <$> save_area_content a b c d h m) !! Z.to_nat TrustedStack_offset_mstatus =
  Some (lword_of_word m).
Proof. reflexivity. Qed.

Lemma save_area_word_mstatus a b c d h m :
  save_area_word (lword_of_word <$> save_area_content a b c d h m) TrustedStack_offset_mstatus =
  lword_of_word m.
Proof. reflexivity. Qed.

Lemma save_area_word_mepcc a b c d h m :
  save_area_word (lword_of_word <$> save_area_content a b c d h m) TrustedStack_offset_mepcc =
  lword_of_word a.
Proof. reflexivity. Qed.

Lemma save_area_word_mcause a b c d h m :
  save_area_word (lword_of_word <$> save_area_content a b c d h m) TrustedStack_offset_mcause =
  lnull.
Proof. reflexivity. Qed.

(** A lookup in [resume_regs_of]. *)
Lemma resume_regs_of_lookup ws r :
  resume_regs_of ws !! r =
  Some (if decide (r = cnull) then lnull else save_area_word ws (TrustedStack_offset_reg r)).
Proof.
  apply elem_of_list_to_map_1.
  - rewrite -list_fmap_compose. apply all_registers_NoDup.
  - apply list_elem_of_fmap. exists r. split; [done | apply all_registers_correct].
Qed.
  Lemma main_spec_size_obligations (main : cmpt) (imports code data : list Word) :
    cmpt_imports main = imports →
    cmpt_code main = code →
    cmpt_data main = data →
    SubBounds (cmpt_b_pcc main) (cmpt_e_pcc main)
      (cmpt_a_code main) (cmpt_a_code main ^+ length code)
    ∧ (cmpt_b_cgp main + length data)%a = Some (cmpt_e_cgp main)
    ∧ (cmpt_b_pcc main + length imports)%a = Some (cmpt_a_code main).
  Proof.
    intros <- <- <-.
    pose proof (cmpt_import_size main).
    pose proof (cmpt_code_size main).
    pose proof (cmpt_data_size main).
    rewrite /SubBounds.
    split; [solve_addr|split; done].
  Qed.

  Lemma cmpt_exp_tbl_cgp_eq (C_cmpt : cmpt) :
    cmpt_exp_tbl_cgp C_cmpt = (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_cgp).
  Proof. pose proof (cmpt_exp_tbl_pcc_size C_cmpt); solve_addr. Qed.

  (** The main compartment's code region, as a [codefrag]. *)
  Lemma cmpt_code_codefrag `{Σ : gFunctors} {ceriseg : ceriseG Σ} (main : cmpt) :
    [[ cmpt_a_code main, cmpt_e_pcc main ]] ↦ₐ [[ lword_of_word <$> cmpt_code main ]] ⊣⊢
    codefrag (cmpt_a_code main) (cmpt_code main).
  Proof.
    rewrite /codefrag.
    replace (cmpt_a_code main ^+ length (cmpt_code main)) with (cmpt_e_pcc main); first done.
    pose proof (cmpt_code_size main); solve_addr.
  Qed.

End main_sizes.
