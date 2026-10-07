From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import adequacy.
From griotte Require Import sts_multiple_updates.
From griotte Require Import logrel_binary.
From griotte Require Import region_invariants_revocation_binary.
From griotte Require Import switcher_preamble_binary.
From griotte Require Import mkregion_helpers memory_region memory_region_binary disjoint_regions_tactics.
From griotte Require Import compartment_layout machine_run.

(** * Helpers for the adequacy theorems of the binary model

    The adequacy theorems of the binary model state that two runs of the
    machine, from two initial memories that only differ in the private data
    of a trusted compartment, either both halt or both do not halt.

    Each direction is obtained from the binary logical relation, with one run
    as implementation and the other run as specification:
    [binary_adequacy] turns a proof of the binary configuration relation into
    "the implementation halts implies the specification halts". The lemma
    [halts_equiv] combines both directions.

    The remaining lemmas allocate the resources of the initial state: the
    compartments shared by both runs (switcher, adversaries, code of the
    trusted compartments) own the points-to of both runs, the private data of
    the trusted compartments are given separately for each run. *)

(** ** Halting *)

(** The machine halts from the initial state [σ]. *)
Definition halts `{MP: MachineParameters} (σ : ExecConf) : Prop :=
  ∃ es c, rtc erased_step ([Seq (Instr Executable)], σ) (Seq (Instr Halted) :: es, c).

Lemma halts_equiv `{MP: MachineParameters} (σ1 σ2 : ExecConf) :
  (halts σ1 → halts σ2) →
  (halts σ2 → halts σ1) →
  (halts σ1 ↔ halts σ2).
Proof. tauto. Qed.

(** A halting thread reduces to the value [HaltedV]. *)
Lemma rtc_erased_step_seq_halted `{MP: MachineParameters}
  (ρ : cfg griotte_lang) (es : list griotte_lang.expr) (c : ExecConf) :
  rtc erased_step ρ (Seq (Instr Halted) :: es, c) →
  rtc erased_step ρ (Instr Halted :: es, c).
Proof.
  intros Hsteps.
  eapply rtc_r; first exact Hsteps.
  assert (pure_step (Seq (Instr Halted)) (Instr Halted)) as Hps.
  { apply nsteps_once_inv, (pure_seq_halted I). }
  destruct (pure_step_safe _ _ Hps c) as (e2' & σ2 & efs & Hprim).
  destruct (pure_step_det _ _ Hps _ _ _ _ _ Hprim) as (_ & -> & -> & ->).
  exists []. eapply (step_atomic _ _ _ _ _ [] es); [done| |exact Hprim].
  by rewrite /= app_nil_r.
Qed.

(** A run of the interpreter [machine_run] that halts gives a halting
    execution of the operational semantics. *)
Lemma machine_run_halts `{MP: MachineParameters} fuel cf (φ : ExecConf) :
  machine_run fuel (cf, φ) = Some Halted →
  ∃ φ', rtc erased_step ([Seq (Instr cf)], φ) ([Seq (Instr Halted)], φ').
Proof.
  revert cf φ. induction fuel; first (cbn; done).
  cbn. intros ? [ [r sr] m ] Hc.
  destruct cf; simplify_eq.
  - destruct (r !! PC) as [wpc | ] eqn:HePC; last done.
    destruct (isCorrectPCb wpc) eqn:HPC; last done.
    apply isCorrectPCb_isCorrectPC in HPC.
    destruct wpc eqn:Hr; [by inversion HPC| | by inversion HPC | by inversion HPC].
    destruct sb as [p g b e a | ]; last by inversion HPC.
    destruct (m !! a) as [wa | ] eqn:HeMem; last done.
    eapply IHfuel in Hc as [φ' Hc]. eexists.
    eapply rtc_l; last eapply Hc.
    exists [].
    eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
    eapply ectx_language.Ectx_step with (K:=[SeqCtx]). 1,2: reflexivity.
    constructor. eapply step_exec_instr; eauto.
  - eexists. apply rtc_refl.
  - apply IHfuel in Hc as [φ' Hc]. eexists.
    eapply rtc_l.
    + exists [].
      eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
      eapply ectx_language.Ectx_step with (K:=[]). 1,2: reflexivity. cbn.
      econstructor.
    + cbn. apply Hc.
Qed.

(** ** Adequacy of the binary configuration relation *)

(** Pre-condition for allocating non-atomic invariants. Its field is not an
    instance: inside an adequacy proof, the only instance of [na_invG] is the
    one of [ceriseG], so that [na_own] and [na_inv] resolve to it. *)
Class na_invGpreS (Σ : gFunctors) := {
    na_invGpreS_na_invG : na_invariants.na_invG Σ;
  }.

Global Instance subG_na_invGpreS {Σ} : subG na_invariants.na_invΣ Σ → na_invGpreS Σ.
Proof. intros. constructor. apply _. Qed.

Section binary_adequacy.
  Context `{MP: MachineParameters}.
  Context (Σ : gFunctors).
  Context {inv_preg : invGpreS Σ}.
  Context {mem_preg : gen_heapGpreS Addr Word Σ}.
  Context {reg_preg : gen_heapGpreS RegName Word Σ}.
  Context {sreg_preg : gen_heapGpreS SRegName Word Σ}.
  Context {entry_preg : entryGpreS Σ}.
  Context {na_inv_preg : na_invGpreS Σ}.
  Context {spec_preg : specGpreS Σ}.

  (** If, for all instances of the program logic, the initial resources of
      the implementation run (configuration [(regs1, sregs1, m1)]) and of the
      specification run (configuration [(regs2, sregs2, m2)]) give the
      postcondition of the binary configuration relation, then the
      specification run halts whenever the implementation run halts.

      The entry points of [ents] are allocated beforehand. *)
  Lemma binary_adequacy
    (ents : gmap Word nat)
    (regs1 regs2 : Reg) (sregs1 sregs2 : SReg) (m1 m2 : Mem) :
    (∀ (ceriseg : ceriseG Σ) (specg : specG Σ),
       ⊢ spec_ctx -∗
         ⤇ Seq (Instr Executable) -∗
         @na_own Σ cerise_instance.na_invG cerise_nais ⊤ -∗
         ([∗ map] r↦w ∈ regs1, r ↦ᵣ w) -∗
         ([∗ map] sr↦w ∈ sregs1, sr ↦ₛᵣ w) -∗
         ([∗ map] a↦w ∈ m1, a ↦ₐ w) -∗
         ([∗ map] r↦w ∈ regs2, r ↣ᵣ w) -∗
         ([∗ map] sr↦w ∈ sregs2, sr ↣ₛᵣ w) -∗
         ([∗ map] a↦w ∈ m2, a ↣ₐ w) -∗
         ([∗ map] w↦n ∈ ents, w ↦□ₑ n)
         ={⊤}=∗
         WP Seq (Instr Executable)
           {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ @na_own Σ cerise_instance.na_invG cerise_nais ⊤ }}) →
    halts (regs1, sregs1, m1) →
    halts (regs2, sregs2, m2).
  Proof.
    intros Hwp (es & c & Hsteps).
    apply rtc_erased_step_seq_halted in Hsteps.
    apply erased_steps_nsteps in Hsteps as (n & κs & Hsteps).
    eapply (wp_strong_adequacy Σ griotte_lang NotStuck [Seq (Instr Executable)] (regs1, sregs1, m1)
              n κs (Instr Halted :: es) c _ (λ _, 0)); last exact Hsteps.
    intros Hinv.

    (* Resources of the implementation run *)
    iMod (gen_heap_init (regs1:Reg)) as (reg_heapg) "(Hreg_ctx & Hreg & _)".
    iMod (gen_heap_init (sregs1:SReg)) as (sreg_heapg) "(Hsreg_ctx & Hsreg & _)".
    iMod (gen_heap_init (m1:Mem)) as (mem_heapg) "(Hmem_ctx & Hmem & _)".
    iMod (entry_init ents) as (entry_g) "Hentries".
    iMod (@na_alloc Σ (@na_invGpreS_na_invG Σ na_inv_preg)) as (cerise_nais) "Hna".
    pose cerise_na_invs := Build_cerise_na_invs _ (@na_invGpreS_na_invG Σ na_inv_preg) cerise_nais.
    pose ceriseg := CeriseG Σ Hinv cerise_na_invs mem_heapg reg_heapg sreg_heapg entry_g.

    (* Resources of the specification run *)
    iMod (spec_init ⊤ (Seq (Instr Executable)) (regs2, sregs2, m2))
      as (specg) "(#Hinv_spec & #Hspec & Hj & Hreg_s & Hsreg_s & Hmem_s)".

    iMod (Hwp ceriseg specg with "Hspec Hj Hna Hreg Hsreg Hmem Hreg_s Hsreg_s Hmem_s Hentries")
      as "Hwp".
    iModIntro.
    iExists (λ σ _ _ _, ((gen_heap_interp (reg σ) ∗ gen_heap_interp (sreg σ)) ∗ gen_heap_interp (mem σ))%I).
    iExists [(λ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤)%I].
    iExists (λ _, True)%I, (λ _ _ _ _, fupd_intro _ _).
    cbn.
    iFrame "Hreg_ctx Hsreg_ctx Hmem_ctx".
    iSplitL "Hwp".
    { rewrite ?big_sepL2_singleton. by iFrame. }

    (* The implementation thread reached [HaltedV] *)
    iIntros (es' t2' Ht2 Hlen _) "_ HΦ _".
    destruct es' as [|e' [|e'' es''] ]; cbn in Ht2, Hlen; simplify_eq.
    iEval (rewrite ?big_sepL2_singleton /=) in "HΦ".
    iDestruct ("HΦ" with "[//]") as "[Hj _]".

    (* Hence, the specification thread reached [Seq (Instr Halted)] *)
    iMod (spec_inv_reachable with "Hinv_spec Hj") as "[_ %Hreach]"; try solve_ndisj.
    iApply fupd_mask_intro_discard; first set_solver.
    iPureIntro.
    destruct Hreach as [σ Hσ].
    by exists [], σ.
  Qed.

End binary_adequacy.

(** ** Compartments with different private data *)

(** [cmpt_with_data C data] is the compartment [C] whose data region
    contains [data] instead of [cmpt_data C]. The two compartments have the
    same layout, hence the same disjointness properties. *)
Definition cmpt_with_data (C : cmpt) (data : list Word)
  (Hdata : (cmpt_b_cgp C + length data)%a = Some (cmpt_e_cgp C)) : cmpt :=
  {|
    cmpt_b_pcc := cmpt_b_pcc C;
    cmpt_a_code := cmpt_a_code C;
    cmpt_e_pcc := cmpt_e_pcc C;
    cmpt_b_cgp := cmpt_b_cgp C;
    cmpt_e_cgp := cmpt_e_cgp C;
    cmpt_exp_tbl_pcc := cmpt_exp_tbl_pcc C;
    cmpt_exp_tbl_cgp := cmpt_exp_tbl_cgp C;
    cmpt_exp_tbl_entries_start := cmpt_exp_tbl_entries_start C;
    cmpt_exp_tbl_entries_end := cmpt_exp_tbl_entries_end C;
    cmpt_imports := cmpt_imports C;
    cmpt_code := cmpt_code C;
    cmpt_data := data;
    cmpt_exp_tbl_entries := cmpt_exp_tbl_entries C;
    cmpt_import_size := cmpt_import_size C;
    cmpt_code_size := cmpt_code_size C;
    cmpt_data_size := Hdata;
    cmpt_exp_tbl_pcc_size := cmpt_exp_tbl_pcc_size C;
    cmpt_exp_tbl_cgp_size := cmpt_exp_tbl_cgp_size C;
    cmpt_exp_tbl_entries_size := cmpt_exp_tbl_entries_size C;
    cmpt_disjointness := cmpt_disjointness C;
  |}.

(** ** Initial resources *)

Section initial_resources_generic.
  Context {Σ : gFunctors} `{MP: MachineParameters}.

  (** Splits the initial memory of a compartment, for any points-to
      predicate [φ]. *)
  Lemma initialise_compartment_gen (φ : Addr → Word → iProp Σ) (C_cmpt : cmpt) :
    let PCC := WCap RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_b_pcc C_cmpt) in
    let CGP := WCap RW Global (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) (cmpt_b_cgp C_cmpt) in
    ([∗ map] k↦y ∈ mk_initial_cmpt C_cmpt, φ k y)
    -∗
    ([∗ list] k;v ∈ finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_a_code C_cmpt); cmpt_imports C_cmpt, φ k v) ∗
    ([∗ list] k;v ∈ finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt); cmpt_code C_cmpt, φ k v) ∗
    ([∗ list] k;v ∈ finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt); cmpt_data C_cmpt, φ k v) ∗
    φ (cmpt_exp_tbl_pcc C_cmpt) PCC ∗
    φ (cmpt_exp_tbl_cgp C_cmpt) CGP ∗
    ([∗ list] k;v ∈ finz.seq_between (cmpt_exp_tbl_entries_start C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt);
                    cmpt_exp_tbl_entries C_cmpt, φ k v).
  Proof.
    intros PCC CGP.
    iIntros "Hcmpt_C".
    iEval (rewrite /mk_initial_cmpt) in "Hcmpt_C".
    iDestruct (big_sepM_union with "Hcmpt_C") as "[HC HC_etbl]".
    { eapply cmpt_exp_tbl_disjoint ; eauto. }
    iDestruct (big_sepM_union with "HC") as "[HC_code HC_data]".
    { eapply cmpt_cgp_disjoint ; eauto. }
    rewrite /cmpt_pcc_mregion.
    iDestruct (big_sepM_union with "HC_code") as "[HC_imports HC_code]".
    { eapply cmpt_code_disjoint ; eauto. }
    rewrite /cmpt_cgp_mregion.
    iDestruct (mkregion_sepM_to_sepL2 with "HC_code") as "HC_code".
    { apply (cmpt_code_size C_cmpt). }
    iDestruct (mkregion_sepM_to_sepL2 with "HC_data") as "HC_data".
    { apply (cmpt_data_size C_cmpt). }
    iDestruct (mkregion_sepM_to_sepL2 with "HC_imports") as "HC_imports".
    { by pose proof (cmpt_import_size C_cmpt) as H ; cbn in *. }

    iEval (rewrite /cmpt_exp_tbl_mregion) in "HC_etbl".
    iDestruct (big_sepM_union with "HC_etbl") as "[HC_etbl HC_etbl_entries]".
    { eapply cmpt_exp_tbl_entries_disjoint. }
    iDestruct (big_sepM_union with "HC_etbl") as "[HC_etbl_pcc HC_etbl_cgp]".
    { eapply cmpt_exp_tbl_pcc_cgp_disjoint. }
    iDestruct (mkregion_sepM_to_sepL2 with "HC_etbl_entries") as "HC_etbl_entries".
    { apply cmpt_exp_tbl_entries_size. }
    iDestruct (mkregion_sepM_to_sepL2 with "HC_etbl_pcc") as "HC_etbl_pcc".
    { cbn; apply cmpt_exp_tbl_pcc_size. }
    iDestruct (mkregion_sepM_to_sepL2 with "HC_etbl_cgp") as "HC_etbl_cgp".
    { cbn; apply cmpt_exp_tbl_cgp_size. }
    rewrite (finz_seq_between_singleton (cmpt_exp_tbl_pcc C_cmpt))
    ; last (apply cmpt_exp_tbl_pcc_size).
    rewrite (finz_seq_between_singleton (cmpt_exp_tbl_cgp C_cmpt))
    ; last (apply cmpt_exp_tbl_cgp_size).
    rewrite !big_sepL2_singleton.
    iFrame.
  Qed.

  (** Same, for a compartment whose private data have been replaced. *)
  Lemma initialise_compartment_with_data_gen
    (φ : Addr → Word → iProp Σ) (C_cmpt : cmpt) (data : list Word)
    (Hdata : (cmpt_b_cgp C_cmpt + length data)%a = Some (cmpt_e_cgp C_cmpt)) :
    ([∗ map] k↦y ∈ mk_initial_cmpt (cmpt_with_data C_cmpt data Hdata), φ k y)
    -∗
    ([∗ list] k;v ∈ finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_a_code C_cmpt); cmpt_imports C_cmpt, φ k v) ∗
    ([∗ list] k;v ∈ finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt); cmpt_code C_cmpt, φ k v) ∗
    ([∗ list] k;v ∈ finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt); data, φ k v).
  Proof.
    iIntros "Hcmpt_C".
    iDestruct (initialise_compartment_gen φ (cmpt_with_data C_cmpt data Hdata) with "Hcmpt_C")
      as "(Himports & Hcode & Hdata & _)".
    iFrame.
  Qed.

End initial_resources_generic.

Section initial_resources_binary.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}.

  (** The compartment of an adversary is identical in both runs. Its export
      table is placed in invariants holding the points-to of both runs. *)
  Lemma initialise_adversary_compartment_binary {E : coPset} ( C_cmpt : cmpt ) ( C : CmptName ) :
    let PCC := WCap RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_b_pcc C_cmpt) in
    let CGP := WCap RW Global (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) (cmpt_b_cgp C_cmpt) in
    let exp_tbl_addrs :=
      (finz.seq_between (cmpt_exp_tbl_entries_start C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt)) in
    ([∗ map] k↦y ∈ mk_initial_cmpt C_cmpt, k ↦ₐ y ∗ k ↣ₐ y)
    ={E}=∗
    ([∗ list] k;v ∈ finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_a_code C_cmpt); cmpt_imports C_cmpt,
       k ↦ₐ v ∗ k ↣ₐ v) ∗
    ([∗ list] k;v ∈ finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt); cmpt_code C_cmpt,
       k ↦ₐ v ∗ k ↣ₐ v) ∗
    ([∗ list] k;v ∈ finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt); cmpt_data C_cmpt,
       k ↦ₐ v ∗ k ↣ₐ v) ∗
    inv (export_table_PCCN (nroot.@C))
      (cmpt_exp_tbl_pcc C_cmpt ↦ₐ PCC ∗ cmpt_exp_tbl_pcc C_cmpt ↣ₐ PCC) ∗
    inv (export_table_CGPN (nroot.@C))
      (cmpt_exp_tbl_cgp C_cmpt ↦ₐ CGP ∗ cmpt_exp_tbl_cgp C_cmpt ↣ₐ CGP) ∗
    ([∗ list] a;v ∈ exp_tbl_addrs ; cmpt_exp_tbl_entries C_cmpt,
       inv (export_table_entryN (nroot .@ C) a) (a ↦ₐ v ∗ a ↣ₐ v)).
  Proof.
    intros PCC CGP exp_tbl_addrs.
    iIntros "Hcmpt_C".
    iDestruct (initialise_compartment_gen (λ k v, (k ↦ₐ v ∗ k ↣ₐ v)%I) with "Hcmpt_C")
      as "(HC_imports & HC_code & HC_data & HC_etbl_pcc & HC_etbl_cgp & HC_etbl_entries)".
    iFrame "HC_imports HC_code HC_data".

    iMod (inv_alloc (export_table_PCCN (nroot .@ C)) E _ with "HC_etbl_pcc")%I as "$".
    iMod (inv_alloc (export_table_CGPN (nroot .@ C)) E _ with "HC_etbl_cgp")%I as "$".

    iStopProof.
    subst exp_tbl_addrs.
    generalize (cmpt_exp_tbl_entries C_cmpt) as lv.
    generalize (finz.seq_between (cmpt_exp_tbl_entries_start C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt)) as la.
    clear PCC CGP.
    induction la; iIntros (lv) "H"; first done.
    iDestruct (big_sepL2_length with "H") as "%Hlen".
    destruct lv as [|v lv]; simplify_eq.
    iDestruct "H" as "[H IH]".
    iMod (IHla with "IH") as "$".
    iMod (inv_alloc (export_table_entryN (nroot .@ C) a) E _ with "H")%I as "$".
    done.
  Qed.

  (** The switcher is identical in both runs. Each run has its own trusted
      stack, its own [mtdc] register, and its own logical call stack. *)
  Lemma initialise_switcher_compartment_binary
    {E : coPset} (switcher_cmpt : cmptSwitcher) (switcherN : namespace) :
    let swlayout :=  (cmptSwitcher_switcherLayout switcher_cmpt) in
    ([∗ map] k↦y ∈ mk_initial_switcher switcher_cmpt, k ↦ₐ y ∗ k ↣ₐ y) -∗
    can_alloc_pred (ot_switcher switcher_cmpt) -∗
    cstack_full [] -∗
    cstack_full_spec [] -∗
    mtdc ↦ₛᵣ WCap RWL Local (b_trusted_stack switcher_cmpt) (e_trusted_stack switcher_cmpt)
      (b_trusted_stack switcher_cmpt) -∗
    mtdc ↣ₛᵣ WCap RWL Local (b_trusted_stack switcher_cmpt) (e_trusted_stack switcher_cmpt)
      (b_trusted_stack switcher_cmpt)
    ={E}=∗
    seal_pred (ot_switcher switcher_cmpt) ot_switcher_propC ∗
    na_inv cerise_nais switcherN switcher_inv_binary ∗
    [[ (b_stack switcher_cmpt), (e_stack switcher_cmpt) ]] ↦ₐ [[ ( stack_content switcher_cmpt ) ]] ∗
    [[ (b_stack switcher_cmpt), (e_stack switcher_cmpt) ]] ↣ₐ [[ ( stack_content switcher_cmpt ) ]].
  Proof.
    intros.
    iIntros "Hcmpt_switcher Hseal_store Hcstk_full Hcstk_full_spec Hmtdc Hsmtdc".
    rewrite /mk_initial_switcher.
    iDestruct (big_sepM_union with "Hcmpt_switcher") as "[Hswitcher Hstack]".
    { eapply cmpt_switcher_stack_mregion_disjoint ; eauto. }
    iDestruct (big_sepM_union with "Hswitcher") as "[Hswitcher Htrusted_stack]".
    { eapply cmpt_switcher_trusted_stack_mregion_disjoint ; eauto. }

    rewrite /cmpt_switcher_code_mregion.
    iDestruct (big_sepM_union with "Hswitcher") as "[Hswitcher_sealing Hswitcher]".
    { eapply cmpt_switcher_code_stack_mregion_disjoint ; eauto. }
    iEval (rewrite /mkregion) in "Hswitcher_sealing".
    rewrite finz_seq_between_singleton.
    2: { apply switcher_call_entry_point. }
    iEval (cbn) in "Hswitcher_sealing".
    iDestruct (big_sepM_insert with "Hswitcher_sealing")
      as "[[Hswitcher_sealing Hsswitcher_sealing] _]"; first done.
    iDestruct (mkregion_sepM_to_sepL2 with "Hswitcher") as "Hswitcher".
    { apply switcher_size. }
    iDestruct (big_sepL2_sep with "Hswitcher") as "[Hswitcher Hsswitcher]".
    rewrite /cmpt_switcher_trusted_stack_mregion.
    iDestruct (mkregion_sepM_to_sepL2 with "Htrusted_stack") as "Htrusted_stack".
    { apply (trusted_stack_size switcher_cmpt). }
    iDestruct (big_sepL2_sep with "Htrusted_stack") as "[Htrusted_stack Hstrusted_stack]".
    iMod (seal_store_update_alloc _ ( ot_switcher_propC ) with "Hseal_store")
      as "#Hsealed_pred_ot_switcher".

    (* Switcher state of the implementation run *)
    iAssert ( switcher_inv )
      with "[Hswitcher Hswitcher_sealing Htrusted_stack Hcstk_full Hmtdc]" as "Hswitcher".
    {
      rewrite /switcher_inv /codefrag /region_pointsto /=.
      replace ((a_switcher_call switcher_cmpt) ^+ length switcher_instrs)%a
        with (e_switcher switcher_cmpt).
      2: { pose proof (switcher_size switcher_cmpt) as H.
           solve_addr+H.
      }
      iFrame "∗#".
      iExists (tl (trusted_stack_content switcher_cmpt)).
      iSplitR; first (iPureIntro; apply (ot_switcher_size switcher_cmpt)).
      pose proof (trusted_stack_content_base_zeroed switcher_cmpt) as Htstk_head.
      pose proof (trusted_stack_size switcher_cmpt) as Htstk_size.
      destruct (trusted_stack_content switcher_cmpt); cbn in Htstk_head; simplify_eq.
      rewrite finz_seq_between_cons; last solve_addr+Htstk_size.
      iDestruct "Htrusted_stack" as "[Hbase_stack Htrusted_stack]".
      iFrame.
      iSplitL; last (iPureIntro ; by rewrite finz_add_0).
      iSplit; iPureIntro; solve_addr.
    }

    (* Switcher state of the specification run *)
    iAssert ( switcher_inv_spec )
      with "[Hsswitcher Hsswitcher_sealing Hstrusted_stack Hcstk_full_spec Hsmtdc]" as "Hsswitcher".
    {
      rewrite /switcher_inv_spec /spec_codefrag /spec_region_pointsto /=.
      replace ((a_switcher_call switcher_cmpt) ^+ length switcher_instrs)%a
        with (e_switcher switcher_cmpt).
      2: { pose proof (switcher_size switcher_cmpt) as H.
           solve_addr+H.
      }
      iFrame "∗#".
      iExists (tl (trusted_stack_content switcher_cmpt)).
      pose proof (trusted_stack_content_base_zeroed switcher_cmpt) as Htstk_head.
      pose proof (trusted_stack_size switcher_cmpt) as Htstk_size.
      destruct (trusted_stack_content switcher_cmpt); cbn in Htstk_head; simplify_eq.
      rewrite finz_seq_between_cons; last solve_addr+Htstk_size.
      iDestruct "Hstrusted_stack" as "[Hsbase_stack Hstrusted_stack]".
      iFrame.
      iSplitL; last (iPureIntro ; by rewrite finz_add_0).
      iSplit; iPureIntro; solve_addr.
    }
    iMod (na_inv_alloc cerise_nais _ switcherN (switcher_inv ∗ switcher_inv_spec)%I
           with "[$Hswitcher $Hsswitcher]") as "#Hswitcher".

    rewrite /cmpt_switcher_stack_mregion.
    iDestruct (mkregion_sepM_to_sepL2 with "Hstack") as "Hstack".
    { apply (stack_size switcher_cmpt). }
    iDestruct (big_sepL2_sep with "Hstack") as "[Hstack Hsstack]".
    iModIntro.
    iFrame "#∗".
  Qed.

  (** The initial register files of both runs are identical. All registers
      but [PC], [cgp] and [csp] contain zero. *)
  Lemma initial_registers_pair (reg : Reg) :
    (∀ (r: RegName), r ∉ ({[ PC; cgp; csp ]} : gset RegName) → reg !! r = Some (WInt 0)) →
    ([∗ map] r↦w ∈ delete csp (delete cgp (delete PC reg)), r ↦ᵣ w) -∗
    ([∗ map] r↦w ∈ delete csp (delete cgp (delete PC reg)), r ↣ᵣ w) -∗
    ([∗ map] r↦w ∈ delete csp (delete cgp (delete PC reg)), r ↦ᵣ w ∗ r ↣ᵣ w ∗ ⌜ w = WInt 0 ⌝).
  Proof.
    iIntros (Hreg) "Hreg Hsreg".
    iDestruct (big_sepM_sep_2 with "Hreg Hsreg") as "Hregs".
    iApply (big_sepM_impl with "Hregs").
    iIntros "!>" (r w Hr) "[$ $]".
    iPureIntro.
    rewrite !lookup_delete_Some in Hr.
    destruct Hr as (Hcsp & Hcgp & HPC & Hr).
    assert (reg !! r = Some (WInt 0)) as Hr0.
    { apply Hreg. set_solver. }
    rewrite Hr0 in Hr; by simplify_eq.
  Qed.

End initial_resources_binary.

Section initial_resources_exported.
  Context {Σ : gFunctors} `{MP: MachineParameters}.

  (** Splits the initial memory of a compartment whose private data have
      been replaced, including its export table. *)
  Lemma initialise_compartment_with_data_exp_tbl_gen
    (φ : Addr → Word → iProp Σ) (C_cmpt : cmpt) (data : list Word)
    (Hdata : (cmpt_b_cgp C_cmpt + length data)%a = Some (cmpt_e_cgp C_cmpt)) :
    let PCC := WCap RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_b_pcc C_cmpt) in
    let CGP := WCap RW Global (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) (cmpt_b_cgp C_cmpt) in
    ([∗ map] k↦y ∈ mk_initial_cmpt (cmpt_with_data C_cmpt data Hdata), φ k y)
    -∗
    ([∗ list] k;v ∈ finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_a_code C_cmpt); cmpt_imports C_cmpt, φ k v) ∗
    ([∗ list] k;v ∈ finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt); cmpt_code C_cmpt, φ k v) ∗
    ([∗ list] k;v ∈ finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt); data, φ k v) ∗
    φ (cmpt_exp_tbl_pcc C_cmpt) PCC ∗
    φ (cmpt_exp_tbl_cgp C_cmpt) CGP ∗
    ([∗ list] k;v ∈ finz.seq_between (cmpt_exp_tbl_entries_start C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt);
                    cmpt_exp_tbl_entries C_cmpt, φ k v).
  Proof.
    intros PCC CGP.
    iIntros "Hcmpt_C".
    iDestruct (initialise_compartment_gen φ (cmpt_with_data C_cmpt data Hdata) with "Hcmpt_C")
      as "(Himports & Hcode & Hdata & Hetbl_pcc & Hetbl_cgp & Hetbl_entries)".
    iFrame.
  Qed.

End initial_resources_exported.
