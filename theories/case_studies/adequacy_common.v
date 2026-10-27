From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import adequacy.
From iris.base_logic Require Import invariants.
From griotte Require Import logrel monotone interp_weakening.
From griotte Require Import assert_spec.
From griotte Require Import
  region_invariants_revocation region_invariants_allocation world_interp_allocation_compartments.
From griotte Require Import switcher_base_interp.
From griotte Require Import stack_world_resources.
From griotte Require Import compartment_layout switcher_adequacy adequacy_helpers.
From griotte Require Import allocator_resources heap_region.

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
    WCap true RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_b_pcc C_cmpt).
  Definition cmpt_cgp_cap (C_cmpt : cmpt) : Word :=
    WCap true RW Global (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) (cmpt_b_cgp C_cmpt).

  (** Stack and trusted-stack capabilities of the switcher. *)
  Definition stack_cap (sw : cmptSwitcher) : Word :=
    WCap true RWL Local (b_stack sw) (e_stack sw) (stk_start_a (b_stack sw) (e_stack sw)).

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
    a = (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_entry i)%a ∧
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
    (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_entry i)%a ∈ cmpt_exp_tbl_addrs C_cmpt.
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
  Lemma ghost_init_cond_roots (R : gset Addr) (pc : Word) (reg : Reg) (sreg : SReg) (m : Mem) :
    (∀ a, a ∈ R → is_heap_address a = true) →
    mem_rooted R m →
    word_rooted R pc →
    (∀ r w, reg !! r = Some w → word_rooted R w) →
    (∀ sr w, sreg !! sr = Some w → word_rooted R w) →
    mem_avoids_mmio m →
    heap_mapped m →
    reg !! cnull = Some (WInt 0) →
    mem_exec_ok m →
    word_exec_ok pc →
    (∀ r w, reg !! r = Some w → word_exec_ok w) →
    (∀ sr w, sreg !! sr = Some w → word_exec_ok w) →
    pc_ok pc →
    (∀ sr w, is_pc_sreg sr = true → sreg !! sr = Some w → pc_ok w) →
    (∀ sr, sr ∈ reserved_sregs → is_Some (sreg !! sr)) →
    sreg !! MTCC = Some mtcc_vec →
    (∃ z, sreg !! MTVAL = Some (WInt z)) →
    (∃ mie mpie, sreg !! MSTATUS = Some (WInt (mstatus_enc mie mpie))) →
    ghost_init_cond (pc, reg, sreg, m, initial_heap_shadow) R.
  Proof.
    intros HR Hm Hpc Hreg Hsreg Hmmio Hheap Hnull Hmx Hpcx Hregx Hsregx Hpcok Hsregok
      Hreserved Hmtcc Hmtval Hmstatus.
    assert (∀ a, is_heap_address a = true →
      initial_heap_shadow !! a = Some ShadowLive) as Hsh.
    { intros a Ha. rewrite /initial_heap_shadow lookup_fmap /initial_heap_memory
        lookup_gset_to_gmap option_guard_True //.
      by apply elem_of_heap_addresses. }
    constructor; cbn.
    - exact HR.
    - intros a Ha. by apply Hsh, HR.
    - intros a Ha. eexists. by apply Hsh.
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

(** ** Iris adequacy for the assert flag

    The premise receives the program-logic resources of the initial state
    (registers, mtdc, memory, shadow table, address claims, the
    non-atomic invariant token) and must produce a WP for the machine together with
    the invariant of the assert flag. The machine runs as the user thread [0]:
    its PC, registers and pool are those of [UserThread 0] in the base; the
    shared heaps are stated at the base. *)
Lemma cerise_flag_adequacy (Σ : gFunctors)
  {inv_preg : invGpreS Σ}
  {cerise_preg : ceriseGpreS Σ}
  {na_invg : na_invariants.na_invG Σ}
  `{MP: MachineParameters} {TV : trapVector}
  (flagN : namespace) (flag : Addr) (H : gset Addr)
  (pc pc' : Word) (reg reg' : Reg) (sreg sreg' : SReg) (m m' : Mem) (sh sh' : ShadowTbl)
  (wmtdc : Word) (es : list griotte_lang.expr) :
  ghost_init_cond (pc, reg, sreg, m, sh) H →
  reg !! cnull = Some (WInt 0) →
  sreg !! MTDC = Some wmtdc →
  (∀ (ceriseb : ceriseBaseG Σ),
     (* the trap vector of [ceriseb] is the one of the initial state *)
     @mtcc_vec (@cb_trapVector Σ ceriseb) = @mtcc_vec TV →
     PC ↦ₚ[u 0] lword_of_word pc -∗
     ([∗ map] r↦w ∈ lword_of_word <$> reg, r ↦ᵣ[u 0] w) -∗
     mtdc ↦ₜ[u 0] TStack (lword_of_word wmtdc) -∗
     ([∗ map] a↦w ∈ m, a ↦ₐ lword_of_word w) -∗
     ([∗ map] a↦s ∈ sh, a ↦ₛ s) -∗
     ([∗ map] a↦c ∈ init_claims H, addr_alloc a c) -∗
     (* the pool of thread [0] in [ceriseb], not the [na_invg] parameter *)
     @na_own Σ (@cb_na_invG Σ ceriseb) (tpool (UserThread 0)) ⊤
     ={⊤}=∗
     WP Seq (Instr Executable) @[u 0] {{ _, True }} ∗
     inv flagN (flag ↦ₐ WInt 0)) →
  rtc erased_step ([Seq (Instr Executable)], (pc, reg, sreg, m, sh)) (es, (pc', reg', sreg', m', sh')) →
  m' !! flag = Some (WInt 0).
Proof.
  intros Hinit Hnull Hmtdc Hwp Hstep.
  pose proof (@wp_invariance Σ griotte_lang _ NotStuck) as WPI. cbn in WPI.
  pose (fun (c: ExecConf) => mem c !! flag = Some (WInt 0%Z)) as state_is_good.
  specialize (WPI (Seq (Instr Executable)) (pc, reg, sreg, m, sh) es (pc', reg', sreg', m', sh')
                (state_is_good (pc', reg', sreg', m', sh'))).
  eapply WPI. 2: assumption. intros Hinv κs. clear WPI.
  iMod (@na_alloc Σ na_invg) as (pool) "Hna".
  pose cerise_na_invs := Build_cerise_na_invs _ na_invg pool.
  iMod (cerise_ghost_init (pc, reg, sreg, m, sh) H (TStack (lword_of_word wmtdc)) wmtdc
          Hinit Hmtdc (mtdc_match_TStack _))
    as (mem_heapg shadow_heapg pc_g reg_heapg sreg_heapg registryg addr_allocg mtdcg mieg mpieg)
       "(Hσ & HPC & Hreg & Hmtdc & Hmem & Hshadow & Hclaims)".
  iEval (rewrite init_lmem_pointsto) in "Hmem".
  rewrite (init_lregs_cnull reg Hnull).
  (* Every thread has the PC, the registers, mtdc, MIE and the pool of the
     machine. *)
  pose ceriseb := {|
    cb_invG := Hinv;
    cb_na_invG := na_invg;
    cb_mem := mem_heapg;
    cb_shadow := shadow_heapg;
    cb_sreg := sreg_heapg;
    cb_registry := registryg;
    cb_addr_alloc := addr_allocg;
    cb_trapVector := TV;
    cb_mpie := mpieg;
    cb_pc_of := λ _, pc_g;
    cb_regs_of := λ _, reg_heapg;
    cb_mtdc_of := λ _, mtdcg;
    cb_mie_of := λ _, mieg;
    tpool := λ _, pool |}.
  pose ceriseg := ceriseG_of (base := ceriseb) (UserThread 0).
  iMod (Hwp ceriseb eq_refl with "HPC Hreg Hmtdc Hmem Hshadow Hclaims Hna") as "[Hwp #Hflag]".
  iModIntro.
  iExists (fun σ _ _ => cerise_state_interp σ ∗ crit_link σ)%I.
  iExists (fun _ => True)%I. cbn. iFrame "Hσ".
  iSplitL "Hwp".
  { iApply (wp_mono with "Hwp"); iIntros (?) "?"; done. }
  iIntros "[Hσ _]".
  iDestruct (SI_open with "Hσ") as "Hσ". iNamed "Hσ".
  iExists (⊤ ∖ ↑flagN).
  iInv flagN as ">Hflag'" "Hclose".
  iDestruct (gen_heap_valid with "Hm Hflag'") as %Hm'_flag.
  iModIntro. iPureIntro.
  destruct (erasure_lookup_mem _ _ _ _ _ _ _ _ _ Her Hm'_flag)
    as (pw & Hpw & _ & _ & Hnonheap & _).
  destruct (Hnonheap eq_refl) as [Heq | (_ & Hb)]; last by destruct Hb.
  rewrite /state_is_good Hpw Heq //.
Qed.

(** ** Initial world, seal store and call stack *)
Section world_init.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {Cname : CmptNameG}
    {seal_store_preg : sealStorePreG Σ}
    {sts_preg : STS_preG LAddr region_type OType LWord Σ} {relpreg : relGpreS Σ}
    {cstack_preg : CSTACK_preG Σ}
    `{MP: MachineParameters}.

  (** The call stack starts with the entry frame [ef] of the thread only. *)
  Lemma initialise_world (Cs : list CmptName) (ots : gset OType) (ef : trusted_frame) :
    CNames = list_to_set Cs →
    NoDup Cs →
    ⊢ |==> ∃ (seal_storeg : sealStoreG Σ) (relg : relGS Σ)
            (stsg : STSG LAddr region_type OType LWord Σ) (cstackg : CSTACKG Σ),
      ([∗ set] o ∈ ots, can_alloc_pred o) ∗
      cstack_full (entry_cstack ef) ∗
      cstack_frag (entry_cstack ef) ∗
      [∗ list] C ∈ Cs, world_interp (∅, (∅, ∅), ∅, ∅) C.
  Proof.
    intros HCNames HNoDup.
    iMod (gen_cstack_init (entry_cstack ef)) as (cstackg) "[Hcstk_full Hcstk_frag]".
    iMod (world_interp_init ots) as (relg stsg seal_storeg) "(Hworld_interp & Hseal_store)".
    rewrite HCNames big_sepS_list_to_set //.
    iModIntro; iExists seal_storeg, relg, stsg, cstackg; iFrame.
  Qed.

End world_init.

(** ** Worlds of the adversaries *)
Section adversary_world.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}.

  (** The world of an adversary compartment [C_cmpt] after the allocation of its
      imports, code and data (permanent), and of the switcher stack with state [ρ]. *)
  Definition adv_world_with (ρ : region_type) (W : WORLD) (sw : cmptSwitcher) (C_cmpt : cmpt)
    : WORLD :=
    std_update_multiple (std_update_compartment W C_cmpt) (stack_addrs sw) ρ.

  Lemma adv_world_with_heap ρ W sw C_cmpt :
    heap_std (adv_world_with ρ W sw C_cmpt) = heap_std W.
  Proof. by rewrite /adv_world_with std_update_multiple_heap std_update_compartment_heap. Qed.

  Lemma elem_of_dom_std_update_compartment (W : WORLD) (C_cmpt : cmpt) (a : Addr) :
    LNonHeap a ∈ dom (std (std_update_compartment W C_cmpt)) →
    a ∈ finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt)
    ∨ a ∈ finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt)
    ∨ LNonHeap a ∈ dom (std W).
  Proof.
    intros Ha.
    pose proof (cmpt_import_size C_cmpt).
    pose proof (cmpt_code_size C_cmpt).
    rewrite /std_update_compartment in Ha.
    apply elem_of_dom_std_multiple_update in Ha as [Ha|Ha].
    { left; rewrite !elem_of_finz_seq_between in Ha |- *; solve_addr. }
    apply elem_of_dom_std_multiple_update in Ha as [Ha|Ha]; first by right; left.
    apply elem_of_dom_std_multiple_update in Ha as [Ha|Ha]; last by right; right.
    left; rewrite !elem_of_finz_seq_between in Ha |- *; solve_addr.
  Qed.

  (** The data of the main compartment is not in the world of an adversary. *)
  Lemma main_cgp_not_in_adv_world (ρ : region_type) (W : WORLD)
    (sw : cmptSwitcher) (main C_cmpt : cmpt) (a : Addr) :
    main ## C_cmpt →
    switcher_cmpt_disjoint main sw →
    LNonHeap a ∉ dom (std W) →
    a ∈ finz.seq_between (cmpt_b_cgp main) (cmpt_e_cgp main) →
    LNonHeap a ∉ dom (std (adv_world_with ρ W sw C_cmpt)).
  Proof.
    intros HmainC Hsw HaW Ha Hcontra.
    rewrite /adv_world_with in Hcontra.
    apply elem_of_dom_std_multiple_update in Hcontra as [Hcontra|Hcontra].
    { rewrite /switcher_cmpt_disjoint /cmpt_switcher_region /cmpt_switcher_stack_region
        /cmpt_region /cmpt_cgp_region in Hsw.
      rewrite /stack_addrs in Hcontra.
      set_solver. }
    apply elem_of_dom_std_update_compartment in Hcontra as [Hcontra | [Hcontra | Hcontra] ].
    - rewrite /disjoint /Cmpt_Disjoint /disjoint_cmpt /cmpt_region
        /cmpt_cgp_region /cmpt_pcc_region in HmainC.
      set_solver.
    - rewrite /disjoint /Cmpt_Disjoint /disjoint_cmpt /cmpt_region
        /cmpt_cgp_region in HmainC.
      set_solver.
    - done.
  Qed.

  (** A stack outside of the mmio and heap regions, whose addresses are
      temporary in the world, with [interp_in_mem] safety invariants, is safe
      to share. *)
  Lemma interp_stack_temporary (W : WORLD) (C : CmptName) (b e : Addr) :
    disjoint_from_mmio b e →
    disjoint_from_heap b e →
    Forall (λ a, std W !! LNonHeap a = Some Temporary) (finz.seq_between b e) →
    ([∗ list] a ∈ finz.seq_between b e, rel C (LNonHeap a) RWL interp_in_memC) -∗
    interp W C (WCap true RWL Local b e (stk_start_a b e)).
  Proof.
    iIntros (Hmmio Hheap Htemp) "#Hrel".
    rewrite /stk_start_a.
    iEval (rewrite interp_unfold /=).
    iSplit.
    { iApply big_sepL_intro; iModIntro.
      iIntros (k a Ha).
      rewrite /addr_key.
      iExists RWL, (interp_in_mem RWL).
      iEval (cbn).
      iSplit; first done.
      iSplit; first (iPureIntro ; by apply persistent_cond_interp_in_mem).
      iDestruct (big_sepL_lookup with "Hrel") as "$"; first done.
      iSplit; first (iNext ; by iApply zcond_interp_in_mem).
      iSplit; first (iNext ; by iApply rcond_interp_in_mem).
      iSplit; first (iNext ; by iApply wcond_interp_in_mem).
      assert (std W !! LNonHeap a = Some Temporary) by (rewrite Forall_lookup in Htemp; eauto).
      iSplit; last done.
      iApply (monoReq_interp_in_mem _ _ _ _ Temporary); done. }
    iPureIntro; split; first done.
    by apply heap_cap_valid_disjoint.
  Qed.

  Lemma adv_world_free_cmpt (W : WORLD) (C_cmpt : cmpt) :
    (∀ a, a ∈ cmpt_region C_cmpt → std W !! LNonHeap a = None) →
    Forall (λ k, std W !! LNonHeap k = None) (finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_a_code C_cmpt))
    ∧ Forall (λ k, std W !! LNonHeap k = None) (finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt))
    ∧ Forall (λ k, std W !! LNonHeap k = None) (finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt)).
  Proof.
    intros Hfree.
    pose proof (cmpt_import_size C_cmpt).
    pose proof (cmpt_code_size C_cmpt).
    rewrite !Forall_forall.
    split; [|split]; intros a Ha; apply Hfree;
      rewrite /cmpt_region /cmpt_pcc_region /cmpt_cgp_region.
    - assert (a ∈ finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt)); last set_solver.
      rewrite !elem_of_finz_seq_between in Ha |- *; solve_addr.
    - assert (a ∈ finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt)); last set_solver.
      rewrite !elem_of_finz_seq_between in Ha |- *; solve_addr.
    - set_solver.
  Qed.

  Lemma adv_world_free_stack (W : WORLD) (sw : cmptSwitcher) (C_cmpt : cmpt) :
    switcher_cmpt_disjoint C_cmpt sw →
    (∀ a, a ∈ stack_addrs sw → std W !! LNonHeap a = None) →
    Forall (λ k, std (std_update_compartment W C_cmpt) !! LNonHeap k = None) (stack_addrs sw).
  Proof.
    intros Hsw Hfree.
    apply Forall_forall; intros a Ha.
    eapply switcher_cmpt_disjoint_std_update_compartment; eauto.
  Qed.

  Lemma stack_addrs_nonheap (sw : cmptSwitcher) :
    Forall (λ a, is_heap_address a = false) (stack_addrs sw).
  Proof.
    apply Forall_forall; intros a Ha.
    eapply disjoint_from_heap_not_in; first apply stack_disjoint_from_heap.
    apply withinBounds_true_iff. by apply elem_of_finz_seq_between.
  Qed.

  (** ** Sealed entries exported by an adversary *)

  Lemma exported_entries_words_normalise (C_cmpt : cmpt) :
    normalise_sealed_words (exported_entries_words C_cmpt) =
    list_to_set ((λ a, lword_of_word (WSealable (cmpt_export C_cmpt a))) <$> cmpt_exp_tbl_addrs C_cmpt).
  Proof.
    rewrite /normalise_sealed_words /exported_entries_words /exported_entries_sealable
      /cmpt_exp_tbl_addrs /cmpt_export.
    apply set_eq; intros w.
    rewrite elem_of_map elem_of_list_to_set.
    setoid_rewrite elem_of_list_to_set.
    split.
    - intros (w' & -> & Hw').
      apply list_elem_of_fmap in Hw' as (sb & -> & Hsb).
      apply list_elem_of_fmap.
      apply elem_of_app in Hsb as [Hsb|Hsb];
        apply list_elem_of_fmap in Hsb as (a & -> & Ha); by exists a.
    - intros (a & -> & Ha)%list_elem_of_fmap.
      eexists; split; last first.
      { apply list_elem_of_fmap; eexists; split; first done.
        apply elem_of_app; left; apply list_elem_of_fmap; by exists a. }
      done.
  Qed.

  Lemma cmpt_exp_tbl_addrs_exports_NoDup (C_cmpt : cmpt) :
    NoDup ((λ a, lword_of_word (WSealable (cmpt_export C_cmpt a))) <$> cmpt_exp_tbl_addrs C_cmpt).
  Proof.
    apply NoDup_fmap_2_strong; last apply finz_seq_between_NoDup.
    intros a a' _ _ Heq; by simplify_eq.
  Qed.

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

  (** The sealed exported entries are safe, once their sealed words are in the
      sealing part of the world. *)
  Lemma exported_entries_sealed_interp (W : WORLD) (C : CmptName) (C_cmpt : cmpt) :
    sts_seals_std C switcher.ot_switcher (exported_entries_words C_cmpt) -∗
    [∗ set] v ∈ exported_entries_sealed C_cmpt, interp W C v.
  Proof.
    iIntros "#Hseal".
    iApply big_sepS_intro; iIntros "!>" (v Hv).
    destruct (exported_entries_sealed_words C_cmpt v Hv) as (sb & -> & _ & (g & a & ->) & Hsub).
    iEval (rewrite interp_unfold /= /interp_sb).
    iSplit; first (iApply sts_seals_std_weaken; done).
    iPureIntro; cbn.
    apply heap_cap_valid_disjoint, cmpt_exp_tbl_disjoint_from_heap.
  Qed.

  (** Allocate an adversary compartment [C_cmpt] in the world: its imports,
      code and data become permanent, and its exported entries are sealed with
      [ot_switcher] in the world. The caller proves that the exported entries
      satisfy the sealing predicate of the switcher ([Hexports]) and that the
      imports are safe ([Himports]). *)
  Lemma alloc_adversary_compartment {E : coPset} (W : WORLD) (C_cmpt : cmpt) (C : CmptName) :
    let W' := std_update_compartment W C_cmpt in
    (∀ a, a ∈ cmpt_region C_cmpt → std W !! LNonHeap a = None) →
    Forall is_z (cmpt_code C_cmpt) →
    Forall (is_initial_data_word C_cmpt) (cmpt_data C_cmpt) →
    seal_pred switcher.ot_switcher ot_switcher_propC -∗
    [[ cmpt_b_pcc C_cmpt, cmpt_a_code C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_imports C_cmpt ]] -∗
    [[ cmpt_a_code C_cmpt, cmpt_e_pcc C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_code C_cmpt ]] -∗
    [[ cmpt_b_cgp C_cmpt, cmpt_e_cgp C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_data C_cmpt ]] -∗
    □ (∀ i a, ⌜cmpt_exp_tbl_addrs C_cmpt !! i = Some a⌝ -∗
        interp W' C (cmpt_pcc_cap C_cmpt) -∗
        interp W' C (cmpt_cgp_cap C_cmpt) -∗
        ot_switcher_prop W' C (WSealable (cmpt_export C_cmpt a))) -∗
    ((interp W' C (cmpt_pcc_cap C_cmpt) ∗ interp W' C (cmpt_cgp_cap C_cmpt) ∗
      [∗ set] v ∈ exported_entries_sealed C_cmpt, interp W' C v) -∗
     [∗ list] v ∈ lword_of_word <$> cmpt_imports C_cmpt,
       interp_in_memC (W', C, v) ∗ future_priv_mono C interp_in_memC v) -∗
    world_interp W C
    ={E}=∗
    world_interp W' C ∗
    interp W' C (cmpt_pcc_cap C_cmpt) ∗
    interp W' C (cmpt_cgp_cap C_cmpt) ∗
    [∗ set] v ∈ exported_entries_sealed C_cmpt, interp W' C v.
  Proof.
    intros W' Hfree Hcode Hdata.
    iIntros "#Hseal_pred HC_imports HC_code HC_data #Hexports Himports Hworld".
    destruct (adv_world_free_cmpt W C_cmpt Hfree) as (Hfree_imports & Hfree_code & Hfree_data).
    iAssert (□ ([∗ set] v ∈ exported_entries_sealed C_cmpt, interp_in_mem RWL W' C v) -∗
               [∗ set] v ∈ exported_entries_sealed C_cmpt, interp W' C v)%I as "Hto_interp".
    { iIntros "#Hexp".
      iApply (big_sepS_impl with "Hexp"); iIntros "!>" (v Hv) "Hv".
      destruct (exported_entries_sealed_words C_cmpt v Hv) as (sb & -> & Hbase & _).
      iApply (interp_in_mem_load_result with "Hv").
      right; split; [reflexivity|].
      apply filter_heap_nonheap; exact Hbase. }
    iMod (alloc_compartment_interp with "HC_imports HC_code HC_data [Himports] Hworld")
      as "($ & $ & $ & _ & #Hexp)"; [done..| |].
    { iIntros "(#Hpcc & #Hcgp & Hworld)".
      iMod (world_interp_open_sealing_update' _ C _ ot_switcher_propC switcher.ot_switcher
              (exported_entries_words C_cmpt) with "Hseal_pred [] [] Hworld")
        as "(Hworld & #Hseal)".
      { iIntros (w); iApply mono_priv_ot_switcher. }
      { rewrite exported_entries_words_normalise big_sepS_list_to_set;
          last apply cmpt_exp_tbl_addrs_exports_NoDup.
        rewrite big_sepL_fmap.
        iApply big_sepL_intro; iIntros "!>" (i a Ha); iNext.
        iApply ("Hexports" with "[//] Hpcc Hcgp"). }
      iDestruct (exported_entries_sealed_interp W' with "Hseal") as "#Hexp".
      iModIntro; iFrame "Hworld".
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
    let W' := std_update_compartment W C_cmpt in
    let Wadv := adv_world_with Temporary W sw C_cmpt in
    switcher_cmpt_disjoint C_cmpt sw →
    (∀ a, a ∈ cmpt_region C_cmpt ∨ a ∈ stack_addrs sw → std W !! LNonHeap a = None) →
    Forall is_z (cmpt_code C_cmpt) →
    Forall (is_initial_data_word C_cmpt) (cmpt_data C_cmpt) →
    Forall is_z (stack_content sw) →
    seal_pred switcher.ot_switcher ot_switcher_propC -∗
    [[ cmpt_b_pcc C_cmpt, cmpt_a_code C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_imports C_cmpt ]] -∗
    [[ cmpt_a_code C_cmpt, cmpt_e_pcc C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_code C_cmpt ]] -∗
    [[ cmpt_b_cgp C_cmpt, cmpt_e_cgp C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_data C_cmpt ]] -∗
    [[ b_stack sw, e_stack sw ]] ↦ₐ [[ lword_of_word <$> stack_content sw ]] -∗
    □ (∀ i a, ⌜cmpt_exp_tbl_addrs C_cmpt !! i = Some a⌝ -∗
        interp W' C (cmpt_pcc_cap C_cmpt) -∗
        interp W' C (cmpt_cgp_cap C_cmpt) -∗
        ot_switcher_prop W' C (WSealable (cmpt_export C_cmpt a))) -∗
    ((interp W' C (cmpt_pcc_cap C_cmpt) ∗ interp W' C (cmpt_cgp_cap C_cmpt) ∗
      [∗ set] v ∈ exported_entries_sealed C_cmpt, interp W' C v) -∗
     [∗ list] v ∈ lword_of_word <$> cmpt_imports C_cmpt,
       interp_in_memC (W', C, v) ∗ future_priv_mono C interp_in_memC v) -∗
    world_interp W C
    ={E}=∗
    world_interp Wadv C ∗
    interp Wadv C (cmpt_pcc_cap C_cmpt) ∗
    interp Wadv C (cmpt_cgp_cap C_cmpt) ∗
    interp Wadv C (stack_cap sw) ∗
    [∗ set] v ∈ exported_entries_sealed C_cmpt, interp Wadv C v.
  Proof.
    intros W' Wadv Hsw Hfree Hcode Hdata Hstack.
    iIntros "#Hseal_pred HC_imports HC_code HC_data Hstack #Hexports Himports Hworld".
    iMod (alloc_adversary_compartment with
           "Hseal_pred HC_imports HC_code HC_data Hexports Himports Hworld")
      as "(Hworld & #Hpcc & #Hcgp & #Hexp)"; eauto.
    iMod (world_interp_extend_temp_sepL2_nonheap _ _ (stack_addrs sw)
            (lword_of_word <$> stack_content sw) RWL interp_in_memC
           with "Hworld [Hstack]") as "(Hworld & #Hrel_stk)".
    { apply stack_addrs_nonheap. }
    { done. }
    { apply adv_world_free_stack; first done.
      intros a Ha; apply Hfree; by right. }
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
      { iEval (rewrite /interp_in_mem_pre /=).
        iApply interp_int. }
      rewrite mono_temporary_eq; cbn; iApply future_pub_mono_interp_in_mem_z.
    }
    iModIntro; iFrame "Hworld".
    assert (related_sts_priv_world W' Wadv) as Hrelated.
    { apply related_sts_pub_priv_world, related_sts_pub_update_multiple.
      eapply Forall_impl; first (apply adv_world_free_stack; first done).
      - intros a Ha; apply Hfree; by right.
      - intros a Ha; cbn in *; by rewrite not_elem_of_dom.
    }
    assert (heap_std W' = heap_std Wadv) as Hheap.
    { by rewrite /Wadv adv_world_with_heap /W' std_update_compartment_heap. }
    iSplit; first (iApply (interp_monotone_nl_same_heap with "[] [] Hpcc"); eauto).
    iSplit; first (iApply (interp_monotone_nl_same_heap with "[] [] Hcgp"); eauto).
    iSplit.
    { iApply interp_stack_temporary; last done.
      - apply stack_disjoint_from_mmio.
      - apply stack_disjoint_from_heap.
      - apply Forall_forall; intros a Ha.
        by apply std_sta_update_multiple_lookup_in_i. }
    iApply (big_sepS_impl with "Hexp"); iIntros "!>" (v Hv) "Hv".
    destruct (exported_entries_sealed_words C_cmpt v Hv) as (sb & -> & _).
    by iApply (interp_monotone_sd_same_heap with "[] Hv").
  Qed.

  (** Same as [initialise_adversary_world], but the switcher stack is
      allocated as revoked: the caller keeps its points-to predicates. *)
  Lemma initialise_adversary_world_revoked {E : coPset}
    (W : WORLD) (sw : cmptSwitcher) (C_cmpt : cmpt) (C : CmptName) :
    let W' := std_update_compartment W C_cmpt in
    let Wadv := adv_world_with Revoked W sw C_cmpt in
    switcher_cmpt_disjoint C_cmpt sw →
    (∀ a, a ∈ cmpt_region C_cmpt ∨ a ∈ stack_addrs sw → std W !! LNonHeap a = None) →
    Forall is_z (cmpt_code C_cmpt) →
    Forall (is_initial_data_word C_cmpt) (cmpt_data C_cmpt) →
    seal_pred switcher.ot_switcher ot_switcher_propC -∗
    [[ cmpt_b_pcc C_cmpt, cmpt_a_code C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_imports C_cmpt ]] -∗
    [[ cmpt_a_code C_cmpt, cmpt_e_pcc C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_code C_cmpt ]] -∗
    [[ cmpt_b_cgp C_cmpt, cmpt_e_cgp C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_data C_cmpt ]] -∗
    □ (∀ i a, ⌜cmpt_exp_tbl_addrs C_cmpt !! i = Some a⌝ -∗
        interp W' C (cmpt_pcc_cap C_cmpt) -∗
        interp W' C (cmpt_cgp_cap C_cmpt) -∗
        ot_switcher_prop W' C (WSealable (cmpt_export C_cmpt a))) -∗
    ((interp W' C (cmpt_pcc_cap C_cmpt) ∗ interp W' C (cmpt_cgp_cap C_cmpt) ∗
      [∗ set] v ∈ exported_entries_sealed C_cmpt, interp W' C v) -∗
     [∗ list] v ∈ lword_of_word <$> cmpt_imports C_cmpt,
       interp_in_memC (W', C, v) ∗ future_priv_mono C interp_in_memC v) -∗
    world_interp W C
    ={E}=∗
    world_interp Wadv C ∗
    interp Wadv C (cmpt_pcc_cap C_cmpt) ∗
    interp Wadv C (cmpt_cgp_cap C_cmpt) ∗
    StackRevokedResources Wadv C (stack_addrs sw) ∗
    [∗ set] v ∈ exported_entries_sealed C_cmpt, interp Wadv C v.
  Proof.
    intros W' Wadv Hsw Hfree Hcode Hdata.
    iIntros "#Hseal_pred HC_imports HC_code HC_data #Hexports Himports Hworld".
    iMod (alloc_adversary_compartment with
           "Hseal_pred HC_imports HC_code HC_data Hexports Himports Hworld")
      as "(Hworld & #Hpcc & #Hcgp & #Hexp)"; eauto.
    iMod (world_interp_extend_revoked_sepL2_nonheap _ _ (stack_addrs sw) RWL interp_in_memC
           with "Hworld")
      as "(Hworld & Hrel_stk)".
    { apply stack_addrs_nonheap. }
    { apply adv_world_free_stack; first done.
      intros a Ha; apply Hfree; by right. }
    iModIntro; iFrame "Hworld".
    assert (related_sts_priv_world W' Wadv) as Hrelated.
    { apply related_sts_pub_priv_world, related_sts_pub_update_multiple.
      eapply Forall_impl; first (apply adv_world_free_stack; first done).
      - intros a Ha; apply Hfree; by right.
      - intros a Ha; cbn in *; by rewrite not_elem_of_dom.
    }
    assert (heap_std W' = heap_std Wadv) as Hheap.
    { by rewrite /Wadv adv_world_with_heap /W' std_update_compartment_heap. }
    iSplit; first (iApply (interp_monotone_nl_same_heap with "[] [] Hpcc"); eauto).
    iSplit; first (iApply (interp_monotone_nl_same_heap with "[] [] Hcgp"); eauto).
    iSplitL "Hrel_stk"; first by iApply StackWorldResources_from_rel_stack.
    iApply (big_sepS_impl with "Hexp"); iIntros "!>" (v Hv) "Hv".
    destruct (exported_entries_sealed_words C_cmpt v Hv) as (sb & -> & _).
    by iApply (interp_monotone_sd_same_heap with "[] Hv").
  Qed.

End adversary_world.

Notation adv_world := (adv_world_with Temporary).
Notation adv_world_revoked := (adv_world_with Revoked).

(** ** Exported entry points of an adversary *)
Section adversary_exports.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}.

  (** The [i]-th entry of the export table of an adversary [C_cmpt],
      at address [a], satisfies the sealing predicate of the switcher. *)
  Lemma adversary_export_prop
    (W : WORLD) (C : CmptName) (C_cmpt : cmpt)
    (posture : InterruptStatus) (i args minstk off : nat) (a : Addr) (eh ehs : Z) :
    cmpt_exp_tbl_entries C_cmpt !! i = Some (WInt (encode_entry_point posture args minstk off)) →
    (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_entry i)%a = a →
    args < 7 →
    is_Some (cmpt_b_pcc C_cmpt + off%nat)%a →
    na_inv (tpool th) Nswitcher switcher_inv ⊢
    switcher_static -∗
    cmpt_exp_tbl_pcc C_cmpt ↦ₐ□ cmpt_pcc_cap C_cmpt -∗
    cmpt_exp_tbl_cgp C_cmpt ↦ₐ□ cmpt_cgp_cap C_cmpt -∗
    cmpt_exp_tbl_pcc C_cmpt ↦ₕ□{stackful} eh -∗
    cmpt_exp_tbl_pcc C_cmpt ↦ₕ□{stackless} ehs -∗
    ([∗ list] k ↦ v ∈ cmpt_exp_tbl_entries C_cmpt,
       (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_entry k)%a ↦ₐ□ lword_of_word v) -∗
    interp W C (cmpt_pcc_cap C_cmpt) -∗
    interp W C (cmpt_cgp_cap C_cmpt) -∗
    ot_switcher_prop W C (WSealable (cmpt_export C_cmpt a)).
  Proof.
    intros Hi Ha Hargs Hentry_some.
    iIntros "#Hswitcher #Hswitcher_static #Hpcc #Hcgp #Heh #Hehs #Hentries #Hinterp_pcc #Hinterp_cgp".
    pose proof (cmpt_exp_tbl_entries_size C_cmpt) as Hsize.
    pose proof (cmpt_exp_tbl_header_size C_cmpt) as Hheader.
    assert (i < length (cmpt_exp_tbl_entries C_cmpt)) as Hi_lt
        by (by apply lookup_lt_Some in Hi).
    iDestruct (big_sepL_lookup with "Hentries") as "Hentry_inv"; first done.
    rewrite Ha.
    iApply (ot_switcher_interp _ _ _ Global _ posture args minstk off eh ehs with
              "Hswitcher Hswitcher_static Hpcc Hcgp Heh Hehs Hentry_inv Hinterp_pcc Hinterp_cgp");
      [solve_addr|lia|done].
  Qed.

  (** The [i]-th sealed entry of the export table of an adversary [C_cmpt]
      is safe to share. *)
  Lemma adversary_export_interp (W : WORLD) (C : CmptName) (C_cmpt : cmpt) (i : nat) (a : Addr) :
    (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_entry i)%a = a →
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
    na_inv (tpool th) Nswitcher switcher_inv ⊢
    switcher_static -∗
    cmpt_exp_tbl_pcc C_cmpt ↦ₐ□ cmpt_pcc_cap C_cmpt -∗
    cmpt_exp_tbl_cgp C_cmpt ↦ₐ□ cmpt_cgp_cap C_cmpt -∗
    cmpt_exp_tbl_pcc C_cmpt ↦ₕ□{stackful} eh -∗
    cmpt_exp_tbl_pcc C_cmpt ↦ₕ□{stackless} ehs -∗
    ([∗ list] k ↦ v ∈ cmpt_exp_tbl_entries C_cmpt,
       (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_entry k)%a ↦ₐ□ lword_of_word v) -∗
    □ (∀ i a, ⌜cmpt_exp_tbl_addrs C_cmpt !! i = Some a⌝ -∗
        interp W C (cmpt_pcc_cap C_cmpt) -∗
        interp W C (cmpt_cgp_cap C_cmpt) -∗
        ot_switcher_prop W C (WSealable (cmpt_export C_cmpt a))).
  Proof.
    intros Htbl Hargs Hentries_some.
    iIntros "#Hswitcher #Hswitcher_static #Hpcc #Hcgp #Heh #Hehs #Hentries !>"
      (i a Ha) "#Hinterp_pcc #Hinterp_cgp".
    destruct (cmpt_exp_tbl_addrs_lookup _ _ _ Ha) as [-> Hi].
    rewrite Htbl length_fmap in Hi.
    destruct (lookup_lt_is_Some_2 _ _ Hi) as [ [ [ [posture args] minstk] offset] He].
    iApply (adversary_export_prop _ _ _ posture i args minstk offset _ eh ehs
             with "Hswitcher Hswitcher_static Hpcc Hcgp Heh Hehs Hentries Hinterp_pcc Hinterp_cgp").
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
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}.

  Lemma switcher_call_import_safe (W : WORLD) (C : CmptName) :
    let w := lword_of_word (WSentry FwdDisable true XSRW_ Local
               switcher.b_switcher switcher.e_switcher switcher.a_switcher_call) in
    na_inv (tpool th) Nswitcher switcher_inv ⊢
    switcher_static -∗
    interp_in_memC (W, C, w) ∗ future_priv_mono C interp_in_memC w.
  Proof.
    intros w; subst w.
    iIntros "#Hswitcher #Hswitcher_static".
    assert (heap_authority_base
              (WSentry FwdDisable true XSRW_ Local
                 switcher.b_switcher switcher.e_switcher switcher.a_switcher_call) = None)
      as Hcall_nonheap.
    { destruct (heap_authority_base _) as [b|] eqn:Hauth; last done.
      apply heap_authority_base_heap_cap_base in Hauth.
      pose proof switcher_call_sentry_not_heap as Hnonheap.
      unfold is_heap_cap in Hnonheap; rewrite Hauth in Hnonheap; discriminate. }
    iEval (cbn); iSplit.
    - iEval (rewrite /interp_in_mem_pre /=).
      rewrite filter_heap_nonheap; last exact Hcall_nonheap.
      by iApply (interp_switcher_call with "[$Hswitcher $Hswitcher_static]").
    - iIntros "!>" (W' W'' Hrel) "_".
      iEval (rewrite /interp_in_mem_pre /=).
      rewrite filter_heap_nonheap; last exact Hcall_nonheap.
      by iApply (interp_switcher_call with "[$Hswitcher $Hswitcher_static]").
  Qed.

  (** A word sealed with [o] is safe, in any world, once the sealable and
      its borrowed version are in the sealing part of the world. *)
  Lemma interp_sealed_of_seals (W : WORLD) (C : CmptName) (o : OType)
    (ws : gset LWord) (sb : Sealable) :
    {[ lword_of_word (WSealable sb); lword_of_word (borrow (WSealable sb)) ]} ⊆ ws →
    (∀ p g b e a, sb = SCap true p g b e a → disjoint_from_heap b e) →
    sts_seals_std C o ws -∗
    interp W C (WSealed o sb).
  Proof.
    iIntros (Hsub Hheap) "#Hseal".
    iEval (rewrite interp_unfold /= /interp_sb).
    destruct (get_tag_sealable sb); last done.
    iSplit; first (iApply (sts_seals_std_weaken with "Hseal"); by destruct sb).
    iPureIntro.
    destruct sb as [ [] p g b e a | [] ? ? ? ]; cbn; try done.
    apply heap_cap_valid_disjoint; by eapply Hheap.
  Qed.

  (** A global word sealed in the world is a safe import. *)
  Lemma sealed_import_safe (W : WORLD) (C : CmptName) (o : OType)
    (ws : gset LWord) (sb : Sealable) :
    let w := lword_of_word (WSealed o sb) in
    isGlobalSealable sb = true →
    {[ lword_of_word (WSealable sb); lword_of_word (borrow (WSealable sb)) ]} ⊆ ws →
    (∀ p g b e a, sb = SCap true p g b e a → disjoint_from_heap b e) →
    sts_seals_std C o ws -∗
    interp_in_memC (W, C, w) ∗ future_priv_mono C interp_in_memC w.
  Proof.
    intros w Hglobal Hsub Hheap; subst w.
    iIntros "#Hseal".
    iSplit.
    - iApply interp_to_in_mem. by iApply interp_sealed_of_seals.
    - iIntros (W' W'') "!> %Hrelated Hinterp".
      iEval (cbn) in "Hinterp".
      iApply (interp_in_mem_monotone_nl with "Hinterp"); first done.
      by destruct sb as [ [] ? [] | [] ? [] ].
  Qed.

End adversary_imports.

(** ** Entry points exported by a service compartment *)
Section service_exports.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}.

  (** The sealed words of a list of exported entries: each entry and its
      borrowed version. *)
  Definition exports_words (sbs : list Sealable) : gset LWord :=
    ⋃ ((λ sb, {[ lword_of_word (WSealable sb); lword_of_word (borrow (WSealable sb)) ]}) <$> sbs).

  Lemma exports_words_elem_of (sbs : list Sealable) (sb : Sealable) :
    sb ∈ sbs →
    {[ lword_of_word (WSealable sb); lword_of_word (borrow (WSealable sb)) ]} ⊆ exports_words sbs.
  Proof.
    intros Hsb w Hw. rewrite /exports_words elem_of_union_list.
    eexists; split; last done.
    apply list_elem_of_fmap. by exists sb.
  Qed.

  (** Seal the (global) exported entries [sbs] of a service compartment with
      [ot_switcher] in the world [W] of a compartment [C], given that they
      satisfy the sealing predicate of the switcher in the updated world. *)
  Lemma seal_service_exports (W : WORLD) (C : CmptName) (sbs : list Sealable) :
    let W' := <o[ switcher.ot_switcher := exports_words sbs ]o> W in
    Forall (λ sb, isGlobalSealable sb = true) sbs →
    switcher.ot_switcher ∉ dom (seal_std W) →
    seal_pred switcher.ot_switcher ot_switcher_propC -∗
    □ ([∗ list] sb ∈ sbs, ot_switcher_prop W' C (WSealable sb)) -∗
    world_interp W C
    ==∗
    world_interp W' C ∗ sts_seals_std C switcher.ot_switcher (exports_words sbs).
  Proof.
    intros W' Hglobal Hfresh.
    iIntros "#Hseal_pred #Hprops Hworld".
    iMod (world_interp_salloc W C ot_switcher_propC switcher.ot_switcher (exports_words sbs)
           with "Hseal_pred [] [] Hworld") as "($ & $)"; first done.
    { iIntros (w); iApply mono_priv_ot_switcher. }
    { iApply big_sepS_intro; iIntros "!>" (w Hw).
      rewrite /normalise_sealed_words elem_of_map in Hw.
      destruct Hw as (w' & -> & Hw').
      rewrite /exports_words elem_of_union_list in Hw'.
      destruct Hw' as (X & HX & Hw').
      apply list_elem_of_fmap in HX as (sb & -> & Hsb).
      assert (lforce_global w' = lword_of_word (WSealable sb)) as ->.
      { rewrite Forall_forall in Hglobal. specialize (Hglobal _ Hsb).
        apply elem_of_union in Hw' as [->%elem_of_singleton | ->%elem_of_singleton];
          destruct sb as [ [] ? [] | [] ? [] ]; by cbn in *. }
      iNext. iDestruct (big_sepL_elem_of with "Hprops") as "$"; done. }
    done.
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
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}.

  (** Seal an exported entry [sb] of the main compartment with [ot_switcher]
      in the world [W], given that it satisfies the sealing predicate of the
      switcher in the updated world. *)
  Lemma seal_main_export (W : WORLD) (C : CmptName) (sb : Sealable) :
    let W' := <o[ switcher.ot_switcher :=
                 {[ lword_of_word (WSealable sb); lword_of_word (borrow (WSealable sb)) ]} ]o> W in
    isGlobalSealable sb = true →
    (∀ p g b e a, sb = SCap true p g b e a → disjoint_from_heap b e) →
    switcher.ot_switcher ∉ dom (seal_std W) →
    seal_pred switcher.ot_switcher ot_switcher_propC -∗
    ot_switcher_prop W' C (WSealable sb) -∗
    world_interp W C
    ==∗
    world_interp W' C ∗
    interp W' C (WSealed switcher.ot_switcher sb).
  Proof.
    intros W' Hglobal Hheap Hfresh.
    iIntros "#Hseal_pred #Hprop Hworld".
    iMod (world_interp_salloc W C ot_switcher_propC switcher.ot_switcher
            {[ lword_of_word (WSealable sb); lword_of_word (borrow (WSealable sb)) ]}
           with "Hseal_pred [] [] Hworld")
      as "($ & #Hseal)"; first done.
    { iIntros (w); iApply mono_priv_ot_switcher. }
    { rewrite (normalise_sealed_words_borrow (lword_of_word (WSealable sb))) big_sepS_singleton.
      replace (lforce_global (lword_of_word (WSealable sb))) with (lword_of_word (WSealable sb))
        by (destruct sb as [ [] ? [] | [] ? [] ]; by cbn in * ).
      iFrame "Hprop". }
    iModIntro.
    iEval (rewrite interp_unfold /= /interp_sb).
    replace (get_tag_sealable sb) with true
      by (destruct sb as [ [] ? [] | [] ? [] ]; by cbn in * ).
    iSplit; first done.
    iPureIntro.
    destruct sb as [ [] p g b e a | [] ? ? ? ]; cbn; try done.
    apply heap_cap_valid_disjoint; by eapply Hheap.
  Qed.

End main_exports.

(** ** Size obligations of the main compartment *)
Section main_sizes.
  Context `{MP: MachineParameters}.

  Lemma main_spec_size_obligations (main : cmpt) (imports code data : list Word) :
    cmpt_imports main = imports →
    cmpt_code main = code →
    cmpt_data main = data →
    SubBounds (cmpt_b_pcc main) (cmpt_e_pcc main)
      (cmpt_a_code main) (cmpt_a_code main ^+ length code)%a
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
    cmpt_exp_tbl_cgp C_cmpt = (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_cgp)%a.
  Proof. pose proof (cmpt_exp_tbl_pcc_size C_cmpt); solve_addr. Qed.

  Lemma cmpt_exp_tbl_entries_start_eq (C_cmpt : cmpt) :
    cmpt_exp_tbl_entries_start C_cmpt = (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_entries)%a.
  Proof.
    pose proof (cmpt_exp_tbl_pcc_size C_cmpt).
    pose proof (cmpt_exp_tbl_header_size C_cmpt).
    solve_addr.
  Qed.

  (** The main compartment's code region, as a [codefrag]. *)
  Lemma cmpt_code_codefrag `{Σ : gFunctors} {ceriseg : ceriseG Σ} (main : cmpt) :
    [[ cmpt_a_code main, cmpt_e_pcc main ]] ↦ₐ [[ lword_of_word <$> cmpt_code main ]] ⊣⊢
    codefrag (cmpt_a_code main) (cmpt_code main).
  Proof.
    rewrite /codefrag.
    replace (cmpt_a_code main ^+ length (cmpt_code main))%a with (cmpt_e_pcc main); first done.
    pose proof (cmpt_code_size main); solve_addr.
  Qed.

End main_sizes.
