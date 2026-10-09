From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import adequacy.
From iris.base_logic Require Import invariants.
From griotte Require Import logrel monotone interp_weakening.
From griotte Require Import switcher assert_spec.
From griotte Require Import
  region_invariants_revocation region_invariants_allocation world_interp_allocation_compartments.
From griotte Require Import switcher_preamble interp_switcher_call interp_switcher_return.
From griotte Require Import stack_world_resources.
From griotte Require Import compartment_layout switcher_adequacy adequacy_helpers.

(** * Shared building blocks for the case-study adequacy proofs.

    The lemmas below compose: each adequacy proof calls them in turn
    (Iris adequacy wrapper, world initialisation, compartment
    initialisation, adversary world, register split, size obligations),
    and can insert its own initialisation steps in between. *)

(** ** Concrete capabilities of the initial configuration *)
Section initial_capabilities.
  Context `{MP: MachineParameters}.

  (** Initial PC of a compartment: its PCC, pointing to the start of the code. *)
  Definition cmpt_entry_pc (C_cmpt : cmpt) : Word :=
    WCap RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_a_code C_cmpt).

  (** PCC and CGP of a compartment, as stored in its export table. *)
  Definition cmpt_pcc_cap (C_cmpt : cmpt) : Word :=
    WCap RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_b_pcc C_cmpt).
  Definition cmpt_cgp_cap (C_cmpt : cmpt) : Word :=
    WCap RW Global (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) (cmpt_b_cgp C_cmpt).

  (** Stack and trusted-stack capabilities of the switcher. *)
  Definition stack_cap (sw : cmptSwitcher) : Word :=
    WCap RWL Local (b_stack sw) (e_stack sw) (b_stack sw).
  Definition trusted_stack_cap (sw : cmptSwitcher) : Word :=
    WCap RWL Local (b_trusted_stack sw) (e_trusted_stack sw) (b_trusted_stack sw).

  (** The (unsealed) export-table capability for the entry at address [a]. *)
  Definition cmpt_export (C_cmpt : cmpt) (a : Addr) : Sealable :=
    SCap RO Global (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt) a.

  Definition stack_addrs (sw : cmptSwitcher) : list Addr :=
    finz.seq_between (b_stack sw) (e_stack sw).

End initial_capabilities.

(** ** Initial register files *)
Definition is_initial_registers_of `{MP: MachineParameters}
  (sw : cmptSwitcher) (main : cmpt) (reg : Reg) :=
  reg !! PC = Some (cmpt_entry_pc main) ∧
  reg !! cgp = Some (cmpt_cgp_cap main) ∧
  reg !! csp = Some (stack_cap sw) ∧
  (∀ (r : RegName), r ∉ ({[ PC; cgp; csp ]} : gset RegName) → reg !! r = Some (WInt 0)).

Definition is_initial_sregisters_of `{MP: MachineParameters}
  (sw : cmptSwitcher) (sreg : SReg) :=
  sreg !! MTDC = Some (trusted_stack_cap sw).

Section registers.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} `{MP: MachineParameters}.

  Lemma initial_registers_split (sw : cmptSwitcher) (main : cmpt) (reg : Reg) :
    is_initial_registers_of sw main reg →
    ([∗ map] r↦w ∈ reg, r ↦ᵣ w) ⊢
    ∃ rmap,
      PC ↦ᵣ cmpt_entry_pc main ∗
      cgp ↦ᵣ cmpt_cgp_cap main ∗
      csp ↦ᵣ stack_cap sw ∗
      ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) ∗
      ⌜dom rmap = all_registers_s ∖ {[ PC; cgp; csp ]}⌝ ∗
      ⌜∀ r, r ∈ dom rmap → rmap !! r = Some (WInt 0)⌝.
  Proof.
    intros (HPC & Hcgp & Hcsp & Hzero).
    iIntros "Hreg".
    iDestruct (big_sepM_delete _ _ PC with "Hreg") as "[HPC Hreg]"; first done.
    iDestruct (big_sepM_delete _ _ cgp with "Hreg") as "[Hcgp Hreg]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ csp with "Hreg") as "[Hcsp Hreg]"; first by simplify_map_eq.
    iExists _; iFrame.
    iPureIntro; split.
    - rewrite !dom_delete_L regmap_full_dom; first done.
      intros r.
      destruct (decide (r ∈ ({[ PC; cgp; csp ]} : gset RegName))) as [Hr|Hr].
      + rewrite !elem_of_union !elem_of_singleton in Hr.
        destruct Hr as [ [ -> | -> ] | -> ]; eauto.
      + eexists; eapply Hzero; done.
    - intros r Hr.
      rewrite !dom_delete_L !elem_of_difference !elem_of_singleton in Hr.
      destruct Hr as [ [ [_ HrPC] Hrcgp] Hrcsp].
      rewrite !lookup_delete_ne //.
      apply Hzero; set_solver.
  Qed.

End registers.

(** ** Entry-point resources *)

(** The entry-point map for a list of exported (unsealed) entries and their
    number of arguments: each entry is registered both as is and borrowed. *)
Definition exported_entries (ot : OType) (entries : list (Sealable * nat)) : gmap Word nat :=
  list_to_map
    (concat ((λ e, [(WSealed ot e.1, e.2); (WSealed ot (borrow_sb e.1), e.2)]) <$> entries)).

Lemma global_ne_borrow_sb (sb sb' : Sealable) :
  isGlobalSealable sb = true → sb ≠ borrow_sb sb'.
Proof. destruct sb as [? [] | ? [] ], sb'; cbn; intros Hg Heq; simplify_eq. Qed.

Lemma borrow_sb_inj_global (sb sb' : Sealable) :
  isGlobalSealable sb = true → isGlobalSealable sb' = true →
  borrow_sb sb = borrow_sb sb' → sb = sb'.
Proof.
  destruct sb as [? [] | ? [] ], sb' as [? [] | ? [] ]; cbn; intros; simplify_eq; done.
Qed.

Lemma exported_entries_keys_NoDup (ot : OType) (entries : list (Sealable * nat)) :
  NoDup entries.*1 →
  Forall (λ sb, isGlobalSealable sb = true) entries.*1 →
  NoDup (concat ((λ e, [(WSealed ot e.1, e.2); (WSealed ot (borrow_sb e.1), e.2)]) <$> entries)).*1.
Proof.
  induction entries as [|[sb n] entries IH]; cbn; intros Hnodup Hglobal; first constructor.
  apply NoDup_cons in Hnodup as [Hsb Hnodup].
  apply Forall_cons in Hglobal as [Hg Hglobal].
  assert (∀ w, w ∈ (concat ((λ e, [(WSealed ot e.1, e.2); (WSealed ot (borrow_sb e.1), e.2)])
                              <$> entries)).*1 →
               ∃ sb', sb' ∈ entries.*1 ∧ (w = WSealed ot sb' ∨ w = WSealed ot (borrow_sb sb')))
    as Hkeys.
  { clear. induction entries as [|[sb' n'] entries IH]; cbn; intros w Hw;
      first by apply elem_of_nil in Hw.
    rewrite !elem_of_cons in Hw.
    destruct Hw as [ -> | [ -> | Hw ] ].
    - exists sb'; split; [left|left]; done.
    - exists sb'; split; [left|right]; done.
    - destruct (IH w Hw) as (sb'' & Hin & Hw'); exists sb''; split; [right|]; done.
  }
  rewrite Forall_forall in Hglobal.
  constructor; [|constructor]; last by apply IH; [|apply Forall_forall].
  - intros Hin; rewrite elem_of_cons in Hin.
    destruct Hin as [Heq | Hin].
    + simplify_eq; by eapply global_ne_borrow_sb.
    + destruct (Hkeys _ Hin) as (sb' & Hsb' & [Heq | Heq]); simplify_eq.
      * done.
      * by eapply global_ne_borrow_sb.
  - intros Hin.
    destruct (Hkeys _ Hin) as (sb' & Hsb' & [Heq | Heq]); simplify_eq.
    + pose proof (Hglobal _ Hsb') as Hg'; by destruct sb as [? [] | ? [] ].
    + apply borrow_sb_inj_global in Heq; [simplify_eq; done | done | by apply Hglobal].
Qed.

Section entries.
  Context {Σ : gFunctors} {entryg : entryGS Σ}.

  Lemma entries_split (ot : OType) (entries : list (Sealable * nat)) :
    NoDup entries.*1 →
    Forall (λ sb, isGlobalSealable sb = true) entries.*1 →
    ([∗ map] w↦n ∈ exported_entries ot entries, w ↦□ₑ n) ⊢
    [∗ list] e ∈ entries, WSealed ot e.1 ↦□ₑ e.2 ∗ WSealed ot (borrow_sb e.1) ↦□ₑ e.2.
  Proof.
    intros Hnodup Hglobal.
    rewrite /exported_entries big_sepM_list_to_map;
      last by apply exported_entries_keys_NoDup.
    clear.
    iIntros "H".
    iInduction entries as [|[sb n] entries] "IH"; cbn; first done.
    iDestruct "H" as "($ & $ & H)".
    by iApply "IH".
  Qed.

End entries.

(** ** Iris adequacy for the assert flag

    The premise receives the program-logic resources of the initial state
    (registers, system registers, memory, the non-atomic invariant token and
    the entry-point resources of [entries], sealed with [ot]) and must produce
    a WP for the machine together with the invariant of the assert flag. *)
Lemma cerise_flag_adequacy (Σ : gFunctors)
  {inv_preg : invGpreS Σ}
  {mem_preg : gen_heapGpreS Addr Word Σ}
  {reg_preg : gen_heapGpreS RegName Word Σ}
  {sreg_preg : gen_heapGpreS SRegName Word Σ}
  {entry_preg : entryGpreS Σ}
  {na_invg : na_invG Σ}
  `{MP: MachineParameters}
  (ot : OType) (entries : list (Sealable * nat))
  (flagN : namespace) (flag : Addr)
  (reg reg' : Reg) (sreg sreg' : SReg) (m m' : Mem)
  (es : list griotte_lang.expr) :
  NoDup entries.*1 →
  Forall (λ sb, isGlobalSealable sb = true) entries.*1 →
  (∀ (ceriseg : ceriseG Σ),
     ([∗ map] r↦w ∈ reg, r ↦ᵣ w) -∗
     ([∗ map] r↦w ∈ sreg, r ↦ₛᵣ w) -∗
     ([∗ map] a↦w ∈ m, a ↦ₐ w) -∗
     (* the pool of [ceriseg], not the [na_invg] parameter *)
     @na_own Σ (@cerise_instance.na_invG Σ (@cerise_nainvG Σ ceriseg)) cerise_nais ⊤ -∗
     ([∗ list] e ∈ entries, WSealed ot e.1 ↦□ₑ e.2 ∗ WSealed ot (borrow_sb e.1) ↦□ₑ e.2)
     ={⊤}=∗
     WP Seq (Instr Executable) {{ _, True }} ∗
     inv flagN (flag ↦ₐ WInt 0)) →
  rtc erased_step ([Seq (Instr Executable)], (reg, sreg, m)) (es, (reg', sreg', m')) →
  m' !! flag = Some (WInt 0).
Proof.
  intros Hnodup Hglobal Hinit Hstep.
  eapply (@wp_invariance Σ griotte_lang _ NotStuck); last exact Hstep.
  intros Hinv κs.
  iMod (gen_heap_init (reg:Reg)) as (reg_heapg) "(Hreg_ctx & Hreg & _)".
  iMod (gen_heap_init (sreg:SReg)) as (sreg_heapg) "(Hsreg_ctx & Hsreg & _)".
  iMod (gen_heap_init (m:Mem)) as (mem_heapg) "(Hmem_ctx & Hmem & _)".
  iMod (entry_init (exported_entries ot entries)) as (entry_g) "Hentries".
  iMod (@na_alloc Σ na_invg) as (cerise_nais) "Hna".
  pose cerise_na_invs := Build_cerise_na_invs _ na_invg cerise_nais.
  pose ceriseg := CeriseG Σ Hinv cerise_na_invs mem_heapg reg_heapg sreg_heapg entry_g.
  iDestruct (entries_split with "Hentries") as "Hentries"; [done..|].
  iMod (Hinit ceriseg with "Hreg Hsreg Hmem Hna Hentries") as "[Hwp #Hflag]".
  iModIntro.
  iExists (fun σ _ _ => ((gen_heap_interp σ.1.1 ∗ gen_heap_interp σ.1.2) ∗ gen_heap_interp σ.2))%I.
  iExists (fun _ => True)%I. cbn. iFrame.
  iIntros "[[Hreg' Hsreg'] Hmem']". iExists (⊤ ∖ ↑flagN).
  iInv flagN as ">Hflag'" "Hclose".
  iDestruct (gen_heap_valid with "Hmem' Hflag'") as %Hm'_flag.
  by iModIntro.
Qed.

(** ** Initial world, seal store and call stack *)
Section world_init.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {Cname : CmptNameG}
    {seal_store_preg : sealStorePreG Σ}
    {sts_preg : STS_preG Addr region_type Σ} {relpreg : relGpreS Σ}
    {cstack_preg : CSTACK_preG Σ}
    `{MP: MachineParameters}.

  Lemma initialise_world (Cs : list CmptName) (ots : gset OType) :
    CNames = list_to_set Cs →
    NoDup Cs →
    ⊢ |==> ∃ (seal_storeg : sealStoreG Σ) (relg : relGS Σ)
            (stsg : STSG Addr region_type Σ) (cstackg : CSTACKG Σ),
      ([∗ set] o ∈ ots, can_alloc_pred o) ∗
      cstack_full [] ∗
      cstack_frag [] ∗
      [∗ list] C ∈ Cs, world_interp (∅, (∅, ∅)) C.
  Proof.
    intros HCNames HNoDup.
    iMod (seal_store_init ots) as (seal_storeg) "Hseal_store".
    iMod (gen_cstack_init []) as (cstackg) "[Hcstk_full Hcstk_frag]".
    iMod world_interp_init as (relg stsg) "Hworld_interp".
    rewrite HCNames big_sepS_list_to_set //.
    iModIntro; iExists seal_storeg, relg, stsg, cstackg; iFrame.
  Qed.

End world_init.

(** ** Worlds of the adversaries *)
Section adversary_world.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}.

  (** The world of an adversary compartment [C_cmpt] after the allocation of its
      imports, code and data (permanent), and of the switcher stack with state [ρ]. *)
  Definition adv_world_with (ρ : region_type) (W : WORLD) (sw : cmptSwitcher) (C_cmpt : cmpt)
    : WORLD :=
    std_update_multiple (std_update_compartment W C_cmpt) (stack_addrs sw) ρ.

  Lemma elem_of_dom_std_update_compartment (W : WORLD) (C_cmpt : cmpt) (a : Addr) :
    a ∈ dom (std (std_update_compartment W C_cmpt)) →
    a ∈ finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt)
    ∨ a ∈ finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt)
    ∨ a ∈ dom (std W).
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
    a ∉ dom (std W) →
    a ∈ finz.seq_between (cmpt_b_cgp main) (cmpt_e_cgp main) →
    a ∉ dom (std (adv_world_with ρ W sw C_cmpt)).
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

  (** A stack whose addresses are temporary in the world, with [interp]
      safety invariants, is safe to share. *)
  Lemma interp_stack_temporary (W : WORLD) (C : CmptName) (b e : Addr) :
    Forall (λ a, std W !! a = Some Temporary) (finz.seq_between b e) →
    ([∗ list] a ∈ finz.seq_between b e, rel C a RWL interpC) -∗
    interp W C (WCap RWL Local b e b).
  Proof.
    iIntros (Htemp) "#Hrel".
    iEval (rewrite fixpoint_interp1_eq /=).
    iApply big_sepL_intro; iModIntro.
    iIntros (k a Ha).
    iExists RWL, interp.
    iEval (cbn).
    iSplit; first done.
    iSplit; first (iPureIntro ; by apply persistent_cond_interp).
    iDestruct (big_sepL_lookup with "Hrel") as "$"; first done.
    iSplit; first (iNext ; by iApply zcond_interp).
    iSplit; first (iNext ; by iApply rcond_interp).
    iSplit; first (iNext ; by iApply wcond_interp).
    assert (std W !! a = Some Temporary) by (rewrite Forall_lookup in Htemp; eauto).
    iSplit; last done.
    iApply (monoReq_interp _ _ _ _ Temporary); done.
  Qed.

  Lemma adv_world_free_cmpt (W : WORLD) (C_cmpt : cmpt) :
    (∀ a, a ∈ cmpt_region C_cmpt → std W !! a = None) →
    Forall (λ k, std W !! k = None) (finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_a_code C_cmpt))
    ∧ Forall (λ k, std W !! k = None) (finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt))
    ∧ Forall (λ k, std W !! k = None) (finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt)).
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
    (∀ a, a ∈ stack_addrs sw → std W !! a = None) →
    Forall (λ k, std (std_update_compartment W C_cmpt) !! k = None) (stack_addrs sw).
  Proof.
    intros Hsw Hfree.
    apply Forall_forall; intros a Ha.
    eapply switcher_cmpt_disjoint_std_update_compartment; eauto.
  Qed.

  (** Initialise the world of an adversary compartment [C_cmpt]:
      - its imports, code and data become permanent;
      - the switcher stack becomes temporary.
      The caller proves that the imports are safe ([Himports]). *)
  Lemma initialise_adversary_world {E : coPset}
    (W : WORLD) (sw : cmptSwitcher) (C_cmpt : cmpt) (C : CmptName) :
    let W' := std_update_compartment W C_cmpt in
    let Wadv := adv_world_with Temporary W sw C_cmpt in
    switcher_cmpt_disjoint C_cmpt sw →
    (∀ a, a ∈ cmpt_region C_cmpt ∨ a ∈ stack_addrs sw → std W !! a = None) →
    Forall is_z (cmpt_code C_cmpt) →
    Forall (is_initial_data_word C_cmpt) (cmpt_data C_cmpt) →
    Forall is_z (stack_content sw) →
    [[ cmpt_b_pcc C_cmpt, cmpt_a_code C_cmpt ]] ↦ₐ [[ cmpt_imports C_cmpt ]] -∗
    [[ cmpt_a_code C_cmpt, cmpt_e_pcc C_cmpt ]] ↦ₐ [[ cmpt_code C_cmpt ]] -∗
    [[ cmpt_b_cgp C_cmpt, cmpt_e_cgp C_cmpt ]] ↦ₐ [[ cmpt_data C_cmpt ]] -∗
    [[ b_stack sw, e_stack sw ]] ↦ₐ [[ stack_content sw ]] -∗
    ((interp W' C (cmpt_pcc_cap C_cmpt) ∗ interp W' C (cmpt_cgp_cap C_cmpt)) -∗
     [∗ list] v ∈ cmpt_imports C_cmpt, interpC (W', C, v) ∗ future_priv_mono C interpC v) -∗
    world_interp W C
    ={E}=∗
    world_interp Wadv C ∗
    interp Wadv C (cmpt_pcc_cap C_cmpt) ∗
    interp Wadv C (cmpt_cgp_cap C_cmpt) ∗
    interp Wadv C (stack_cap sw).
  Proof.
    intros W' Wadv Hsw Hfree Hcode Hdata Hstack.
    iIntros "HC_imports HC_code HC_data Hstack Himports Hworld".
    destruct (adv_world_free_cmpt W C_cmpt) as (Hfree_imports & Hfree_code & Hfree_data).
    { intros a Ha; apply Hfree; by left. }
    iMod (alloc_compartment_interp with "HC_imports HC_code HC_data Himports Hworld")
      as "(Hworld & #Hpcc & #Hcgp & _)"; eauto.
    iMod (world_interp_extend_temp_sepL2 _ _ (stack_addrs sw) (stack_content sw) RWL interpC
           with "Hworld [Hstack]") as "(Hworld & #Hrel_stk)".
    { done. }
    { apply adv_world_free_stack; first done.
      intros a Ha; apply Hfree; by right. }
    { iApply (big_sepL2_mono ((fun (_ : nat) (k : finz.finz MemNum) (v : Word) =>
                                 pointsto k (DfracOwn (pos_to_Qp 1)) v)) with "Hstack").
      intros k v1 v2 Hv1 Hv2. cbn. iIntros; iFrame.
      pose proof (Forall_lookup_1 _ _ _ _ Hstack Hv2) as Hncap.
      destruct v2; [| by inversion Hncap..].
      rewrite fixpoint_interp1_eq /=.
      iSplit; eauto.
      iSplit; eauto.
      rewrite mono_temporary_eq; cbn; iApply future_pub_mono_interp_z.
    }
    iModIntro; iFrame "Hworld".
    assert (related_sts_priv_world W' Wadv) as Hrelated.
    { apply related_sts_pub_priv_world, related_sts_pub_update_multiple.
      eapply Forall_impl; first (apply adv_world_free_stack; first done).
      - intros a Ha; apply Hfree; by right.
      - intros a Ha; cbn in *; by rewrite not_elem_of_dom.
    }
    iSplit; first (iApply interp_monotone_nl; eauto).
    iSplit; first (iApply interp_monotone_nl; eauto).
    iApply interp_stack_temporary; last done.
    apply Forall_forall; intros a Ha.
    by apply std_sta_update_multiple_lookup_in_i.
  Qed.

  (** Same as [initialise_adversary_world], but the switcher stack is
      allocated as revoked: the caller keeps its points-to predicates. *)
  Lemma initialise_adversary_world_revoked {E : coPset}
    (W : WORLD) (sw : cmptSwitcher) (C_cmpt : cmpt) (C : CmptName) :
    let W' := std_update_compartment W C_cmpt in
    let Wadv := adv_world_with Revoked W sw C_cmpt in
    switcher_cmpt_disjoint C_cmpt sw →
    (∀ a, a ∈ cmpt_region C_cmpt ∨ a ∈ stack_addrs sw → std W !! a = None) →
    Forall is_z (cmpt_code C_cmpt) →
    Forall (is_initial_data_word C_cmpt) (cmpt_data C_cmpt) →
    [[ cmpt_b_pcc C_cmpt, cmpt_a_code C_cmpt ]] ↦ₐ [[ cmpt_imports C_cmpt ]] -∗
    [[ cmpt_a_code C_cmpt, cmpt_e_pcc C_cmpt ]] ↦ₐ [[ cmpt_code C_cmpt ]] -∗
    [[ cmpt_b_cgp C_cmpt, cmpt_e_cgp C_cmpt ]] ↦ₐ [[ cmpt_data C_cmpt ]] -∗
    ((interp W' C (cmpt_pcc_cap C_cmpt) ∗ interp W' C (cmpt_cgp_cap C_cmpt)) -∗
     [∗ list] v ∈ cmpt_imports C_cmpt, interpC (W', C, v) ∗ future_priv_mono C interpC v) -∗
    world_interp W C
    ={E}=∗
    world_interp Wadv C ∗
    interp Wadv C (cmpt_pcc_cap C_cmpt) ∗
    interp Wadv C (cmpt_cgp_cap C_cmpt) ∗
    StackRevokedResources Wadv C (stack_addrs sw).
  Proof.
    intros W' Wadv Hsw Hfree Hcode Hdata.
    iIntros "HC_imports HC_code HC_data Himports Hworld".
    destruct (adv_world_free_cmpt W C_cmpt) as (Hfree_imports & Hfree_code & Hfree_data).
    { intros a Ha; apply Hfree; by left. }
    iMod (alloc_compartment_interp with "HC_imports HC_code HC_data Himports Hworld")
      as "(Hworld & #Hpcc & #Hcgp & _)"; eauto.
    iMod (world_interp_extend_revoked_sepL2 _ _ (stack_addrs sw) RWL interpC with "Hworld")
      as "(Hworld & Hrel_stk)".
    { apply adv_world_free_stack; first done.
      intros a Ha; apply Hfree; by right. }
    iModIntro; iFrame "Hworld".
    assert (related_sts_priv_world W' Wadv) as Hrelated.
    { apply related_sts_pub_priv_world, related_sts_pub_update_multiple.
      eapply Forall_impl; first (apply adv_world_free_stack; first done).
      - intros a Ha; apply Hfree; by right.
      - intros a Ha; cbn in *; by rewrite not_elem_of_dom.
    }
    iSplit; first (iApply interp_monotone_nl; eauto).
    iSplit; first (iApply interp_monotone_nl; eauto).
    by iApply StackWorldResources_from_rel_stack.
  Qed.

End adversary_world.

Notation adv_world := (adv_world_with Temporary).
Notation adv_world_revoked := (adv_world_with Revoked).

(** ** Exported entry points of an adversary *)
Section adversary_exports.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}.

  (** The [i]-th entry of the export table of an adversary [C_cmpt],
      at address [a], is safe to share once sealed. *)
  Lemma adversary_export_interp
    (W : WORLD) (C : CmptName) (C_cmpt : cmpt) (ot : OType) (Nswitcher : namespace)
    (i args off : nat) (a : Addr) :
    let exp_tbl_addrs :=
      finz.seq_between (cmpt_exp_tbl_entries_start C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt) in
    cmpt_exp_tbl_entries C_cmpt !! i = Some (WInt (encode_entry_point args off)) →
    (cmpt_exp_tbl_entries_start C_cmpt ^+ i)%a = a →
    args < 7 →
    na_inv cerise_nais Nswitcher switcher_inv ⊢
    seal_pred ot ot_switcher_propC -∗
    inv (export_table_PCCN (nroot.@C)) (cmpt_exp_tbl_pcc C_cmpt ↦ₐ cmpt_pcc_cap C_cmpt) -∗
    inv (export_table_CGPN (nroot.@C)) (cmpt_exp_tbl_cgp C_cmpt ↦ₐ cmpt_cgp_cap C_cmpt) -∗
    ([∗ list] a;v ∈ exp_tbl_addrs ; cmpt_exp_tbl_entries C_cmpt,
       inv (export_table_entryN (nroot .@ C) a) (a ↦ₐ v)) -∗
    interp W C (cmpt_pcc_cap C_cmpt) -∗
    interp W C (cmpt_cgp_cap C_cmpt) -∗
    WSealed switcher.ot_switcher (cmpt_export C_cmpt a) ↦□ₑ args -∗
    WSealed switcher.ot_switcher (borrow_sb (cmpt_export C_cmpt a)) ↦□ₑ args -∗
    interp W C (WSealed ot (cmpt_export C_cmpt a)).
  Proof.
    intros exp_tbl_addrs Hi Ha Hargs.
    iIntros "#Hswitcher #Hseal #Hpcc #Hcgp #Hentries #Hinterp_pcc #Hinterp_cgp #Hentry #Hentry'".
    pose proof (cmpt_exp_tbl_entries_size C_cmpt) as Hsize.
    assert (i < length (cmpt_exp_tbl_entries C_cmpt)) as Hi_lt
        by (by apply lookup_lt_Some in Hi).
    assert (exp_tbl_addrs !! i = Some a) as Ha_lookup.
    { subst exp_tbl_addrs.
      rewrite (finz_seq_between_lookup _ _ _ (length (cmpt_exp_tbl_entries C_cmpt))) //.
      f_equal; solve_addr. }
    iDestruct (big_sepL2_lookup with "Hentries") as "Hentry_inv"; [done..|].
    iApply (ot_switcher_interp_entry _ _ _ _ args off with "[$] [$] [$] [$] [$] [$] [$] [$] [$]");
      last lia.
    solve_addr.
  Qed.

End adversary_exports.

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

  (** Exported entries of disjoint compartments are distinct
      (for the [NoDup] premise of [cerise_flag_adequacy]). *)
  Lemma cmpt_export_disjoint (C1 C2 : cmpt) (a1 a2 : Addr) :
    C1 ## C2 → cmpt_export C1 a1 ≠ cmpt_export C2 a2.
  Proof.
    intros Hdis Heq.
    apply (exported_entry_point_disjoint C1 C2 RO RO Global Global a1 a2 Hdis).
    rewrite /cmpt_export in Heq; by rewrite Heq.
  Qed.

  Lemma cmpt_exp_tbl_cgp_eq (C_cmpt : cmpt) :
    cmpt_exp_tbl_cgp C_cmpt = (cmpt_exp_tbl_pcc C_cmpt ^+ 1)%a.
  Proof. pose proof (cmpt_exp_tbl_pcc_size C_cmpt); solve_addr. Qed.

  Lemma cmpt_exp_tbl_entries_start_eq (C_cmpt : cmpt) :
    cmpt_exp_tbl_entries_start C_cmpt = (cmpt_exp_tbl_pcc C_cmpt ^+ 2)%a.
  Proof.
    pose proof (cmpt_exp_tbl_pcc_size C_cmpt).
    pose proof (cmpt_exp_tbl_cgp_size C_cmpt).
    solve_addr.
  Qed.

  (** The main compartment's code region, as a [codefrag]. *)
  Lemma cmpt_code_codefrag `{Σ : gFunctors} {ceriseg : ceriseG Σ} (main : cmpt) :
    [[ cmpt_a_code main, cmpt_e_pcc main ]] ↦ₐ [[ cmpt_code main ]] ⊣⊢
    codefrag (cmpt_a_code main) (cmpt_code main).
  Proof.
    rewrite /codefrag.
    replace (cmpt_a_code main ^+ length (cmpt_code main))%a with (cmpt_e_pcc main); first done.
    pose proof (cmpt_code_size main); solve_addr.
  Qed.

End main_sizes.
