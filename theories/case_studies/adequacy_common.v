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
    sreg !! mtcc = Some mtcc_vec →
    (∃ z, sreg !! mtval = Some (WInt z)) →
    (∃ mie mpie, sreg !! mstatus = Some (WInt (mstatus_enc mie mpie))) →
    (∃ z, sreg !! mshwmb = Some (WInt z) ∧ sreg !! mshwm = Some (WInt z)) →
    ghost_init_cond (pc, reg, sreg, m, initial_heap_shadow) R.
  Proof.
    intros HR Hm Hpc Hreg Hsreg Hmmio Hheap Hnull Hmx Hpcx Hregx Hsregx Hpcok Hsregok
      Hreserved Hmtcc Hmtval Hmstatus Hhwm.
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
    - exact Hhwm.
  Qed.

End initial_rootedness.

(** ** The ghost state of the other threads *)
Section thread_ghost_init.
  Context {Σ : gFunctors}.

  (** The ghost state of a thread that does not run first: its PC, its
      registers, its mtdc, its MIE, and its MSHWMB, MSHWM and zone. Their
      authorities are dropped until the threads are scheduled; only the
      fragment of mtdc is kept. *)
  Lemma thread_ghost_init {cerise_preg : ceriseGpreS Σ} (m : mtdc_val) :
    ⊢ |==> ∃ (pg : pcG Σ) (rg : gen_heapGS RegName LWord Σ) (mtg : mtdcG Σ) (mieg : mieG Σ)
             (hwmg : hwmG Σ),
      @mtdc_frag Σ mtg m.
  Proof.
    iMod (PC_init (lword_of_word (WInt 0))) as (pg) "_".
    iMod (gen_heap_init (∅ : gmap RegName LWord)) as (rg) "_".
    iMod (mtdc_init m) as (mtg) "[_ Hmtdc]".
    iMod (MIE_init InterruptDisabled) as (mieg) "_".
    iMod (hwm_init 0) as (hwmg) "_".
    iModIntro. by iExists pg, rg, mtg, mieg, hwmg.
  Qed.

  (** [thread_ghost_init] for a list of mtdc values. *)
  Lemma threads_ghost_init {cerise_preg : ceriseGpreS Σ} (ms : list mtdc_val) :
    ⊢ |==> ∃ gs : list (pcG Σ * gen_heapGS RegName LWord Σ * mtdcG Σ * mieG Σ * hwmG Σ),
      [∗ list] g; m ∈ gs; ms, @mtdc_frag Σ g.1.1.2 m.
  Proof.
    iInduction ms as [|m ms] "IH".
    - iModIntro. by iExists [].
    - iMod (thread_ghost_init m) as (pg rg mtg mieg hwmg) "Hmtdc".
      iMod "IH" as (gs) "Hgs".
      iModIntro. iExists ((pg, rg, mtg, mieg, hwmg) :: gs).
      rewrite big_sepL2_cons /=. iFrame.
  Qed.

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
End thread_ghost_init.

(** ** Iris adequacy for the assert flag

    The premise receives the program-logic resources of the initial state
    (registers, mtdc, memory, shadow table, address claims, the
    non-atomic invariant token) and must produce a WP for the machine together with
    the invariant of the assert flag. The machine runs as the user thread [0]:
    its PC, registers and pool are those of [UserThread 0] in the base; the
    shared heaps are stated at the base. The user thread [S k] receives the
    mtdc value [ms !! k] and the token of its pool; its PC and registers are
    placeholders, unused until the threads are scheduled. *)
Section flag_adequacy.
  (* Threads [0] and [S k] meet here: every form names its thread. *)
  #[local] Remove Hints ceriseG_of : typeclass_instances.

Lemma cerise_flag_adequacy (Σ : gFunctors)
  {inv_preg : invGpreS Σ}
  {cerise_preg : ceriseGpreS Σ}
  {na_invg : na_invariants.na_invG Σ}
  `{MP: MachineParameters} {TV : trapVector}
  (flagN : namespace) (flag : Addr) (H : gset Addr)
  (pc pc' : Word) (reg reg' : Reg) (sreg sreg' : SReg) (m m' : Mem) (sh sh' : ShadowTbl)
  (wmtdc : Word) (m0 : mtdc_val) (ms : list mtdc_val) (es : list griotte_lang.expr) :
  ghost_init_cond (pc, reg, sreg, m, sh) H →
  reg !! cnull = Some (WInt 0) →
  sreg !! mtdc = Some wmtdc →
  mtdc_match m0 (lword_of_word wmtdc) →
  (∀ (ceriseb : ceriseBaseG Σ),
     (* the trap vector of [ceriseb] is the one of the initial state *)
     @mtcc_vec (@cb_trapVector Σ ceriseb) = @mtcc_vec TV →
     PC ↦ₚ[u 0] lword_of_word pc -∗
     regs[u 0] (lword_of_word <$> reg) -∗
     mtdc ↦ₜ[u 0] m0 -∗
     ([∗ map] a↦w ∈ m, a ↦ₐ lword_of_word w) -∗
     ([∗ map] a↦s ∈ sh, a ↦ₛ s) -∗
     ([∗ map] a↦c ∈ init_claims H, addr_alloc a c) -∗
     (* the pool of thread [0] in [ceriseb], not the [na_invg] parameter *)
     @na_own Σ (@cb_na_invG Σ ceriseb) (tpool (UserThread 0)) ⊤ -∗
     (* the user threads [S k]: their mtdc and the tokens of their pools *)
     ([∗ list] k ↦ m ∈ ms,
        mtdc ↦ₜ[u (S k)] m ∗
        @na_own Σ (@cb_na_invG Σ ceriseb) (tpool (UserThread (S k))) ⊤)
     ={⊤}=∗
     WP Exec @[u 0] {{ _, True }} ∗
     inv flagN (flag ↦ₐ WInt 0)) →
  rtc erased_step ([Exec], (pc, reg, sreg, m, sh)) (es, (pc', reg', sreg', m', sh')) →
  m' !! flag = Some (WInt 0).
Proof.
  intros Hinit Hnull Hmtdc Hm0 Hwp Hstep.
  pose proof (@wp_invariance Σ griotte_lang _ NotStuck) as WPI. cbn in WPI.
  pose (fun (c: ExecConf) => mem c !! flag = Some (WInt 0%Z)) as state_is_good.
  specialize (WPI Exec (pc, reg, sreg, m, sh) es (pc', reg', sreg', m', sh')
                (state_is_good (pc', reg', sreg', m', sh'))).
  eapply WPI. 2: assumption. intros Hinv κs. clear WPI.
  iMod (@na_alloc Σ na_invg) as (pool) "Hna".
  (* The pools of the user threads [S k], of the context-switch thread and
     of the other threads. *)
  iMod (na_pools_alloc ms) as (pools) "Hnas".
  iMod (@na_alloc Σ na_invg) as (pool_c) "_".
  iMod (@na_alloc Σ na_invg) as (pool_d) "_".
  pose cerise_na_invs := Build_cerise_na_invs _ na_invg pool.
  (* The ghost state of the user threads [S k], of the context-switch thread
     and of the other threads; before thread [0]'s, which typeclass search
     must find. *)
  iMod (threads_ghost_init ms) as (gs) "Hgs".
  iMod (thread_ghost_init (ExceptionScratch (lword_of_word (WInt 0))))
    as (pg_c rg_c mtg_c mieg_c hwmg_c) "_".
  iMod (thread_ghost_init (ExceptionScratch (lword_of_word (WInt 0))))
    as (pg_d rg_d mtg_d mieg_d hwmg_d) "_".
  iMod (cerise_ghost_init (pc, reg, sreg, m, sh) H m0 wmtdc Hinit Hmtdc Hm0)
    as (mem_heapg shadow_heapg pc_g reg_heapg sreg_heapg registryg addr_allocg mtdcg mieg mpieg
        hwmg)
       "(Hσ & HPC & Hreg & Hmtdc & Hmem & Hshadow & Hclaims)".
  iEval (rewrite init_lmem_pointsto) in "Hmem".
  rewrite (init_lregs_cnull reg Hnull).
  iDestruct (big_sepL2_nth_l _ _ _ (pg_d, rg_d, mtg_d, mieg_d, hwmg_d) with "Hgs") as "Hgs".
  iDestruct (big_sepL2_nth_l _ _ _ pool_d with "Hnas") as "Hnas".
  (* Thread [0] has the PC, the registers, mtdc, MIE, MSHWMB, MSHWM and the
     pool of the machine; every other thread its own. *)
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
    cb_pc_of := λ th,
      (thread_map (pc_g, reg_heapg, mtdcg, mieg, hwmg) gs (pg_c, rg_c, mtg_c, mieg_c, hwmg_c)
         (pg_d, rg_d, mtg_d, mieg_d, hwmg_d) th).1.1.1.1;
    cb_regs_of := λ th,
      (thread_map (pc_g, reg_heapg, mtdcg, mieg, hwmg) gs (pg_c, rg_c, mtg_c, mieg_c, hwmg_c)
         (pg_d, rg_d, mtg_d, mieg_d, hwmg_d) th).1.1.1.2;
    cb_mtdc_of := λ th,
      (thread_map (pc_g, reg_heapg, mtdcg, mieg, hwmg) gs (pg_c, rg_c, mtg_c, mieg_c, hwmg_c)
         (pg_d, rg_d, mtg_d, mieg_d, hwmg_d) th).1.1.2;
    cb_mie_of := λ th,
      (thread_map (pc_g, reg_heapg, mtdcg, mieg, hwmg) gs (pg_c, rg_c, mtg_c, mieg_c, hwmg_c)
         (pg_d, rg_d, mtg_d, mieg_d, hwmg_d) th).1.2;
    cb_hwm_of := λ th,
      (thread_map (pc_g, reg_heapg, mtdcg, mieg, hwmg) gs (pg_c, rg_c, mtg_c, mieg_c, hwmg_c)
         (pg_d, rg_d, mtg_d, mieg_d, hwmg_d) th).2;
    tpool := thread_map pool pools pool_c pool_d |}.
  pose ceriseg := ceriseG_of (base := ceriseb) (UserThread 0).
  iMod (Hwp ceriseb eq_refl with "HPC Hreg Hmtdc Hmem Hshadow Hclaims Hna [Hgs Hnas]")
    as "[Hwp #Hflag]".
  { iApply (big_sepL_sep_2 with "Hgs Hnas"). }
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
End flag_adequacy.

(** ** Initial world, seal store and call stack *)
Section world_init.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {Cname : CmptNameG}
    {seal_store_preg : sealStorePreG Σ}
    {sts_preg : STS_preG Σ} {relpreg : relGpreS Σ}
    {cstack_preg : CSTACK_preG Σ}
    `{MP: MachineParameters}.

  (** The call stack of the user thread [0] starts with its entry frame
      [ef] only, that of the user thread [S k] with the entry frame
      [efs !! k] only. The worlds are those of the user thread [0]; the
      local maps of the other threads are empty. *)
  Lemma initialise_world (Cs : list CmptName) (ots : gset OType) (ef : trusted_frame)
      (efs : list trusted_frame) :
    CNames = list_to_set Cs →
    NoDup Cs →
    ⊢ |==> ∃ (seal_storeg : sealStoreG Σ) (relg : relGS Σ)
            (stsg : STSG Σ) (cstackg : CSTACKG Σ),
      ([∗ set] o ∈ ots, can_alloc_pred o) ∗
      ●(CSTK)[u 0] (entry_cstack ef) ∗
      ◯(CSTK)[u 0] (entry_cstack ef) ∗
      ([∗ list] k ↦ ef' ∈ efs,
         ●(CSTK)[u (S k)] (entry_cstack ef') ∗ ◯(CSTK)[u (S k)] (entry_cstack ef')) ∗
      [∗ list] C ∈ Cs, world_interp (th := UserThread 0) (MkWorld ∅ (∅,∅)) C.
  Proof.
    intros HCNames HNoDup.
    iMod (gen_cstack_init (entry_cstack ef) ((λ ef', entry_cstack ef') <$> efs))
      as (cstackg) "(Hcstk_full & Hcstk_frag & Hcstks)".
    iEval (rewrite big_sepL_fmap) in "Hcstks".
    iMod (world_interp_init ots (S (length efs))) as (relg stsg seal_storeg)
      "(Hworld_interp & _ & Hseal_store)"; first lia.
    rewrite HCNames big_sepS_list_to_set //.
    iModIntro; iExists seal_storeg, relg, stsg, cstackg; iFrame.
  Qed.

End world_init.

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

  (** The world of an adversary compartment [C_cmpt] after the allocation of its
      imports, code and data (permanent), and of the switcher stack with state [ρ]. *)
  Definition adv_world_with (ρ : region_type) (W : WORLD) (sw : cmptSwitcher) (C_cmpt : cmpt)
    : WORLD :=
    std_update_multiple (std_update_compartment W C_cmpt) (stack_addrs sw) ρ.

  Lemma elem_of_dom_std_update_compartment (W : WORLD) (C_cmpt : cmpt) (a : Addr) :
    LNonHeap a ∈ dom (std (std_update_compartment W C_cmpt)) →
    a ∈ finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt)
    ∨ a ∈ finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt)
    ∨ LNonHeap a ∈ dom (std W).
  Proof. intros Ha. by right; right. Qed.

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
    ([∗ list] a ∈ finz.seq_between b e, (LNonHeap a) ↪ˡ[C]{RWL} interp_in_memC) -∗
    interp W C (Cap RWL Local b e (stk_start_a b e)).
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
      assert (std W !! LNonHeap a = Some Temporary) by (rewrite Forall_lookup in Htemp; eauto).
      iSplit.
      { rewrite /region_rel /= /region_rel_l.
        iDestruct (big_sepL_lookup with "Hrel") as "$"; first done.
        iSplit; first done. iApply mono_pub_interp_in_mem. }
      iSplit; first (iNext ; by iApply zcond_interp_in_mem).
      iSplit; first (iNext ; by iApply rcond_interp_in_mem_nodl).
      iNext ; by iApply wcond_interp_in_mem. }
    iSplit; first done.
    by iApply heap_cap_ok_disjoint.
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
    let W' := std_update_compartment W C_cmpt in
    (∀ a, a ∈ cmpt_region C_cmpt → std W !! LNonHeap a = None) →
    Forall is_z (cmpt_code C_cmpt) →
    Forall (is_initial_data_word C_cmpt) (cmpt_data C_cmpt) →
    switcher.ot_switcher ↪ₒ{SealGlobal} ot_switcher_propC -∗
    [[ cmpt_b_pcc C_cmpt, cmpt_a_code C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_imports C_cmpt ]] -∗
    [[ cmpt_a_code C_cmpt, cmpt_e_pcc C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_code C_cmpt ]] -∗
    [[ cmpt_b_cgp C_cmpt, cmpt_e_cgp C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_data C_cmpt ]] -∗
    □ (∀ i a, ⌜cmpt_exp_tbl_addrs C_cmpt !! i = Some a⌝ -∗
        interp W' C (cmpt_pcc_cap C_cmpt) -∗
        interp W' C (cmpt_cgp_cap C_cmpt) -∗
        ot_switcher_prop W' C (WSealable (cmpt_export C_cmpt a))) -∗
    ((interp W' C (cmpt_pcc_cap C_cmpt) ∗ interp W' C (cmpt_cgp_cap C_cmpt) ∗
      [∗ set] v ∈ exported_entries_sealed C_cmpt, interp W' C v) -∗
     [∗ list] v ∈ lword_of_word <$> cmpt_imports C_cmpt, safeGC interp_cmpt_threads (C, v)) -∗
    thread_in th C -∗
    world_interp W C
    ={E}=∗
    world_interp W' C ∗
    interp W' C (cmpt_pcc_cap C_cmpt) ∗
    interp W' C (cmpt_cgp_cap C_cmpt) ∗
    [∗ set] v ∈ exported_entries_sealed C_cmpt, interp W' C v.
  Proof.
    intros W' Hfree Hcode Hdata.
    iIntros "#Hseal_pred HC_imports HC_code HC_data #Hexports Himports #Hthread Hworld".
    destruct (adv_world_free_cmpt W C_cmpt Hfree) as (Hfree_imports & Hfree_code & Hfree_data).
    iAssert (□ ([∗ set] v ∈ exported_entries_sealed C_cmpt, interp_in_mem RWL W' C v) -∗
               [∗ set] v ∈ exported_entries_sealed C_cmpt, interp W' C v)%I as "Hto_interp".
    { iIntros "#Hexp".
      iApply (big_sepS_impl with "Hexp"); iIntros "!>" (v Hv) "Hv".
      destruct (exported_entries_sealed_words C_cmpt v Hv) as (sb & -> & Hbase & _).
      iApply (interp_in_mem_load_result with "Hv").
      by right. }
    iMod (alloc_compartment_interp with "HC_imports HC_code HC_data [Himports] Hthread Hworld")
      as "($ & $ & $ & _ & #Hexp)"; [done..| |].
    { iIntros "(#Hpcc & #Hcgp)".
      iDestruct (exported_entries_sealed_interp W' with "Hseal_pred []") as "#Hexp".
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
    let W' := std_update_compartment W C_cmpt in
    let Wadv := adv_world_with Temporary W sw C_cmpt in
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
        interp W' C (cmpt_pcc_cap C_cmpt) -∗
        interp W' C (cmpt_cgp_cap C_cmpt) -∗
        ot_switcher_prop W' C (WSealable (cmpt_export C_cmpt a))) -∗
    ((interp W' C (cmpt_pcc_cap C_cmpt) ∗ interp W' C (cmpt_cgp_cap C_cmpt) ∗
      [∗ set] v ∈ exported_entries_sealed C_cmpt, interp W' C v) -∗
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
    intros W' Wadv Hsw Hfree Hcode Hdata Hstack.
    iIntros "#Hseal_pred HC_imports HC_code HC_data Hstack #Hexports Himports #Hthread Hworld".
    iMod (alloc_adversary_compartment with
           "Hseal_pred HC_imports HC_code HC_data Hexports Himports Hthread Hworld")
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
      iApply future_pub_mono_interp_in_mem_z.
    }
    iModIntro; iFrame "Hworld".
    assert (related_sts_priv_world W' Wadv) as Hrelated.
    { apply related_sts_pub_priv_world, related_sts_pub_update_multiple.
      eapply Forall_impl; first (apply adv_world_free_stack; first done).
      - intros a Ha; apply Hfree; by right.
      - intros a Ha; cbn in *; by rewrite not_elem_of_dom.
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
    by iApply (interp_monotone_sd with "[] Hseal_pred Hv").
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
    switcher.ot_switcher ↪ₒ{SealGlobal} ot_switcher_propC -∗
    [[ cmpt_b_pcc C_cmpt, cmpt_a_code C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_imports C_cmpt ]] -∗
    [[ cmpt_a_code C_cmpt, cmpt_e_pcc C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_code C_cmpt ]] -∗
    [[ cmpt_b_cgp C_cmpt, cmpt_e_cgp C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_data C_cmpt ]] -∗
    □ (∀ i a, ⌜cmpt_exp_tbl_addrs C_cmpt !! i = Some a⌝ -∗
        interp W' C (cmpt_pcc_cap C_cmpt) -∗
        interp W' C (cmpt_cgp_cap C_cmpt) -∗
        ot_switcher_prop W' C (WSealable (cmpt_export C_cmpt a))) -∗
    ((interp W' C (cmpt_pcc_cap C_cmpt) ∗ interp W' C (cmpt_cgp_cap C_cmpt) ∗
      [∗ set] v ∈ exported_entries_sealed C_cmpt, interp W' C v) -∗
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
    intros W' Wadv Hsw Hfree Hcode Hdata.
    iIntros "#Hseal_pred HC_imports HC_code HC_data #Hexports Himports #Hthread Hworld".
    iMod (alloc_adversary_compartment with
           "Hseal_pred HC_imports HC_code HC_data Hexports Himports Hthread Hworld")
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
    iSplit; first (iApply (interp_monotone_nl with "[] [] Hpcc"); eauto).
    iSplit; first (iApply (interp_monotone_nl with "[] [] Hcgp"); eauto).
    iSplitL "Hrel_stk"; first by iApply StackWorldResources_from_rel_stack.
    iApply (big_sepS_impl with "Hexp"); iIntros "!>" (v Hv) "Hv".
    destruct (exported_entries_sealed_words C_cmpt v Hv) as (sb & -> & _).
    by iApply (interp_monotone_sd with "[] Hseal_pred Hv").
  Qed.

End adversary_world.

Notation adv_world := (adv_world_with Temporary).
Notation adv_world_revoked := (adv_world_with Revoked).

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
    switcher_family C ⊢
    switcher_static -∗
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
    switcher_family C ⊢
    switcher_static -∗
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
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}.

  Lemma switcher_call_import_safe (C : CmptName) :
    let w := lword_of_word (Sentry FwdDisable XSRW_ Local
               switcher.b_switcher switcher.e_switcher switcher.a_switcher_call) in
    switcher_family C ⊢
    switcher_static -∗
    safeGC interp_cmpt_threads (C, w).
  Proof.
    intros w; subst w.
    iIntros "#Hfamily #_".
    iEval (cbn; rewrite /interp_cmpt_threads /=).
    iIntros "!>" (t') "#Ht'".
    iDestruct ("Hfamily" $! t' with "Ht'") as "[Hswitcher Hswitcher_static]".
    by iApply (interp_switcher_call (th := t') with "[$Hswitcher $Hswitcher_static]").
  Qed.

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

  Lemma cmpt_exp_tbl_entries_start_eq (C_cmpt : cmpt) :
    cmpt_exp_tbl_entries_start C_cmpt = (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_entries).
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
    replace (cmpt_a_code main ^+ length (cmpt_code main)) with (cmpt_e_pcc main); first done.
    pose proof (cmpt_code_size main); solve_addr.
  Qed.

End main_sizes.
