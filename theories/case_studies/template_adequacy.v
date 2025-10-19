From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel interp_weakening monotone.
From cap_machine Require Import switcher assert logrel.
From cap_machine Require Import mkregion_helpers.
From cap_machine Require Import region_invariants_revocation region_invariants_allocation.
From iris.program_logic Require Import adequacy.
From iris.base_logic Require Import invariants.
From cap_machine Require Import compartment_layout switcher_adequacy.
From cap_machine Require Import disjoint_regions_tactics.
From cap_machine Require Import interp_switcher_call interp_switcher_return.

Class memory_layout `{MP: MachineParameters} := {

    (* switcher *)
    switcher_layout : @switcherLayout MP;
    switcher_cmpt : cmptSwitcher;

    (* assert *)
    assert_cmpt : cmptAssert;

    (* main compartment *)
    main_cmpt : cmpt ;

    (* adversary compartments *)
    adv_cmpts : list cmpt ;

    (* disjointness *)
    cmpts_disjoints :
    ## (main_cmpt :: adv_cmpts) ;

    switcher_cmpt_disjoints :
    Forall (switcher_cmpt_disjoint switcher_cmpt) (main_cmpt :: adv_cmpts) ;

    assert_cmpt_disjoints :
    Forall (assert_cmpt_disjoint assert_cmpt) (main_cmpt :: adv_cmpts) ;

    assert_switcher_disjoints :
    assert_switcher_disjoint assert_cmpt switcher_cmpt;
  }.

Definition mk_import_entry_point (C_cmpt : cmpt) (n : Z) :=
  WCap RO Global
    (cmpt_exp_tbl_pcc C_cmpt)
    (cmpt_exp_tbl_entries_end C_cmpt)
    ((cmpt_exp_tbl_entries_start C_cmpt) ^+ n)%a.

Definition mk_import_table (C_cmpt : cmpt) :=
  (fun '(a,b) => mk_import_entry_point a b) <$> (import_table C_cmpt).

Definition mk_export_entry_point (nargs : Z) (offset : Z)  :=
  WInt (encode_entry_point nargs offset) .

Definition mk_export_table (C_cmpt : cmpt) :=
  (fun '(a,b) => mk_export_entry_point a b) <$> (export_table C_cmpt).


Definition mk_initial_memory `{memory_layout} (mem: Mem) :=
  mk_initial_switcher switcher_cmpt ∪
    mk_initial_assert assert_cmpt ∪
    mk_initial_cmpt main_cmpt ∪
    ⋃ (mk_initial_cmpt <$> (adv_cmpts)).

Definition is_initial_registers `{memory_layout} (reg: Reg) :=
  reg !! PC = Some (WCap RX Global (cmpt_b_pcc main_cmpt) (cmpt_e_pcc main_cmpt) (cmpt_a_code main_cmpt)) ∧
  reg !! cgp = Some (WCap RW Global (cmpt_b_cgp main_cmpt) (cmpt_e_cgp main_cmpt) (cmpt_b_cgp main_cmpt)) ∧
  reg !! csp = Some (WCap RWL Local (b_stack switcher_cmpt) (e_stack switcher_cmpt) (b_stack switcher_cmpt)) ∧
  (∀ (r: RegName), r ∉ ({[ PC; cgp; csp ]} : gset RegName) → reg !! r = Some (WInt 0)).

Program Definition is_initial_sregisters `{@memory_layout MP} (sreg : SReg) :=
  sreg !! MTDC = Some (WCap RWL Local
                         (@b_trusted_stack MP switcher_layout)
                         (@e_trusted_stack MP switcher_layout)
                         (@b_trusted_stack MP switcher_layout)).

Definition is_initial_memory `{@memory_layout MP} (mem: Mem) :=
  let b_switcher := (@b_switcher MP switcher_layout) in
  let e_switcher := (@e_switcher MP switcher_layout) in
  let a_switcher_call := (@a_switcher_call MP switcher_layout) in
  let ot_switcher := (@ot_switcher MP switcher_layout) in
  let switcher_entry :=
    WSentry XSRW_ Local
      b_switcher
      e_switcher
      a_switcher_call
  in


  let b_assert := b_assert assert_cmpt in
  let e_assert := e_assert assert_cmpt in
  let assert_sentry := WSentry RX Global b_assert e_assert b_assert in

  mem = mk_initial_memory mem

  (* instantiating main cmpt *)
  ∧ (cmpt_imports main_cmpt) =
  switcher_entry :: assert_sentry :: (mk_import_table main_cmpt)
  ∧ (cmpt_exp_tbl_entries main_cmpt) = mk_export_table main_cmpt

  (* instantiating adversary cmpts *)
  ∧ Forall
      (fun adv_cmpt =>
           Forall is_z (cmpt_code adv_cmpt) (* only instructions *)
           ∧ Forall is_z (cmpt_data adv_cmpt) (* TODO generalise: either z or in_region *)
           ∧ (cmpt_imports main_cmpt) = switcher_entry :: mk_import_table adv_cmpt
           ∧ (cmpt_exp_tbl_entries main_cmpt) = mk_export_table adv_cmpt
           ∧ (cmpt_imports adv_cmpt) !! 0 = Some switcher_entry
      )
      adv_cmpts

  (* initial stack *)
  ∧ Forall is_z (stack_content switcher_cmpt)
.

Lemma mk_initial_cmpt_main_disjoint `{Layout: @memory_layout MP} (m : Mem) :
  mk_initial_switcher switcher_cmpt ∪ mk_initial_assert assert_cmpt
    ##ₘ mk_initial_cmpt main_cmpt.
Proof.
  pose proof switcher_cmpt_disjoints as [HswitcherMain _]%Forall_cons.
  pose proof assert_cmpt_disjoints as [HassertMain _]%Forall_cons.
  rewrite map_disjoint_union_l.
  repeat split.
  - symmetry; apply disjoint_switcher_cmpts_mkinitial; done.
  - symmetry; apply disjoint_assert_cmpts_mkinitial; done.
Qed.


Lemma mk_initial_cmpt_adv_disjoint `{Layout: @memory_layout MP} (m : Mem) :
  Forall
    ( fun adv_cmpt =>
        mk_initial_switcher switcher_cmpt ∪ mk_initial_assert assert_cmpt ∪ mk_initial_cmpt main_cmpt ##ₘ mk_initial_cmpt adv_cmpt
    )
    adv_cmpts.
Proof.
  (* pose proof cmpts_disjoints as Hdis. *)
  (* pose proof switcher_cmpt_disjoints as (_ & _ & HswitcherC). *)
  (* pose proof assert_cmpt_disjoints as (_ & _ & HassertC). *)
  (* do 3 rewrite map_disjoint_union_l. *)
  (* repeat split. *)
  (* - symmetry; apply disjoint_switcher_cmpts_mkinitial; done. *)
  (* - symmetry; apply disjoint_assert_cmpts_mkinitial; done. *)
  (* - apply disjoint_cmpts_mkinitial; done. *)
  (* - apply disjoint_cmpts_mkinitial; done. *)
Admitted.

Definition flagN : namespace := nroot .@ "cmdc" .@ "fail_flag".
Definition switcherN : namespace := nroot .@ "cmdc" .@ "switcher_flag".
Definition assertN : namespace := nroot .@ "cmdc" .@ "assert_flag".

Module single_adversary.


Section Adequacy.
  Context (Σ: gFunctors).
  Context {cname : CmptNameG}.
  Context {B C : CmptName}.
  Context {inv_preg: invGpreS Σ}.
  Context {mem_preg: gen_heapGpreS Addr Word Σ}.
  Context {reg_preg: gen_heapGpreS RegName Word Σ}.
  Context {sreg_preg: gen_heapGpreS SRegName Word Σ}.
  Context {entry_preg : entryGpreS Σ}.
  Context {seal_store_preg: sealStorePreG Σ}.
  Context {na_invg: na_invG Σ}.
  Context {sts_preg: STS_preG Addr region_type Σ}.
  Context {cstack_preg: CSTACK_preG Σ }.
  Context {heappreg: heapGpreS Σ}.
  Context `{MP: MachineParameters}.
  Context { HCNames : CNames = (list_to_set [B;C]) }.
  Context { HCNamesNoDup : NoDup [B;C] }.


  Lemma cmdc_adequacy' `{Layout: @memory_layout MP}
    (reg reg': Reg) (sreg sreg': SReg) (m m': Mem)
    (es: list cap_lang.expr):
    is_initial_registers reg →
    is_initial_sregisters sreg →
    is_initial_memory m →

    (* from actual example *)
    (∀ `{ceriseG Σ, sealStoreG Σ, NA: logrel_na_invs Σ, subG Σ' Σ} rmap,
        dom rmap = all_registers_s ∖ {[ PC; r_adv ]} →

      (W0 : WORLD)
      (Ws : list WORLD) (Cs : list CmptName)
      (cstk : CSTK),
       let imports := cmpt_imports main_cmpt in
       let pc_b := cmpt_b_pcc main_cmpt in
       let pc_e := cmpt_e_pcc main_cmpt in
       let pc_e := cmpt_a_code main_cmpt in
       let cgp_b := cmpt_b_cgp main_cmpt in
       let cgp_e := cmpt_e_cgp main_cmpt in
       let csp_b := b_stack switcher_cmpt in
       let csp_e := e_stack switcher_cmpt in
       let b_assert := b_assert assert_cmpt in
       let e_assert := e_assert assert_cmpt in
       let a_flag := flag_assert assert_cmpt in

      → dom rmap = all_registers_s ∖ {[PC; cgp; csp]}
          (* → SubBounds pc_b pc_e pc_a (pc_a ^+ length dle_main_code)%a *)
      (* → (cgp_b + length dle_main_data)%a = Some cgp_e *)
      (* → (pc_b + length imports)%a = Some pc_a *)
      (* → cgp_b ∉ dom W0.1 *)
      (* → (cgp_b ^+ 1)%a ∉ dom W0.1 *)
      → frame_match Ws Cs cstk W0 C
      → na_inv logrel.logrel_nais assertN (assert_inv b_assert e_assert a_flag)
      ∗ na_inv logrel.logrel_nais switcherN switcher_inv
      ∗ na_own logrel.logrel_nais ⊤
      ∗ PC ↦ᵣ WCap RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
      ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w)
      ∗ [[pc_b,pc_a]]↦ₐ[[imports]]
      ∗ codefrag pc_a dle_main_code
      ∗ [[cgp_b,cgp_e]]↦ₐ[[dle_main_data]]
      ∗ region W0 C
      ∗ sts_full_world W0 C
      ∗ interp_continuation cstk Ws Cs
      ∗ cstack_frag cstk
      ∗ (∀
           (* TODO determine how to get all the entry points *)
           interp W0 C (WSealed switcher.ot_switcher C_f)
         ∗ WSealed switcher.ot_switcher C_f ↦□ₑ 1
         ... )

      ∗ (∀ C, C ∈ adv_cmpts -> interp W0 C (WCap RWL Local csp_b csp_e csp_b))

      ⊢ WP Seq (Instr Executable)
          {{ v, ⌜v = HaltedV⌝ → na_own logrel.logrel_nais ⊤ }}

(* inspired from cerise *)
    (∀ `{ceriseG Σ, sealStoreG Σ, NA: logrel_na_invs Σ, subG Σ' Σ} rmap,
        dom rmap = all_registers_s ∖ {[ PC; r_adv ]} →
     ⊢ inv invN (minv_sep I vinit)
       ∗ @na_own _ (@logrel_na_invG _ NA) logrel_nais ⊤ (*XXX*)
       ∗ @na_inv _ _ _ (@logrel_na_invG _ NA) logrel_nais assertN (assertInv AssertLib vinit)

       (* Registers *)
       ∗ PC ↦ᵣ LCap RWX (prog_start P) (prog_end P) (prog_start P) vinit
       ∗ r_adv ↦ᵣ LCap RWX (prog_start Adv) (prog_end Adv) (prog_start Adv) vinit
       ∗ ([∗ map] r↦w ∈ (register_to_lregister rmap vinit), r ↦ᵣ w ∗ ⌜is_zL w = true⌝)

       (* Memory *)
       (* P program *)
       ∗ ([∗ map] a↦w ∈ (memory_to_lmemory (prog_region P) vinit), a ↦ₐ w)
       (* Adv program  *)
       ∗ ([∗ map] a↦w ∈ (memory_to_lmemory (prog_region Adv) vinit), a ↦ₐ w)
       (* Linking Table *)
       ∗ ([∗ map] a↦w ∈ (memory_to_lmemory (assert_tbl_region tbl_assert_tbl AssertLib) vinit), a ↦ₐ w)

       ∗ EC⤇ ecur
       ∗ ([∗ set] o ∈ gset_all_otypes, can_alloc_pred o)
       ∗ ( [∗ map] tidx ↦ eid ∈ etbl_all, enclave_all tidx eid)

       -∗ WP Seq (Instr Executable) {{ λ _, True }}) →

    rtc erased_step ([Seq (Instr Executable)], (reg, sreg, m)) (es, (reg', sreg', m')) →
    m' !! (flag_assert assert_cmpt) = Some (WInt 0%Z).
  Proof.


End Adequacy.

Lemma template_adequacy
  `{MP: MachineParameters}
  (Σ : gFunctors)
  (P Adv: prog) (AssertLib : assert_library) (tbl_assert_tbl : assert_tbl)
  (r_adv : RegName)
  (m m': Mem) (reg reg': Reg)
  (etbl etbl' : ETable) (ecur ecur' : ENum)
  (es: list cap_lang.expr)
  :
  let I := (adequacy_flag_inv AssertLib) in
  let vinit := 0%nat in
  let RA := reserved_addresses_assert AssertLib vinit in

  let dom_etbl_all := seq 0 ecur : list TIndex in
  let dom_etbl_dead := filter (fun tidx => tidx ∉ dom etbl ) dom_etbl_all : list TIndex in
  let dummy_I := 0 : EIdentity in
  let etbl_dead := create_gmap_default dom_etbl_dead dummy_I : ETable in
  let etbl_all := etbl ∪ etbl_dead in

  is_initial_memory P Adv AssertLib tbl_assert_tbl m →
  is_complete_memory m →
  is_initial_registers P Adv AssertLib tbl_assert_tbl reg r_adv →
  is_complete_registers reg m →
  is_initial_etable etbl ecur ->

  Forall (fun w => adv_condition Adv w) (prog_instrs Adv) →
  minv I m →

  let filtered_map := λ (m : gmap Addr Word), filter (fun '(a, _) => a ∉ minv_dom I) m in
  (∀ `{ceriseG Σ', sealStoreG Σ', NA: logrel_na_invs Σ', subG Σ Σ'} rmap,
     dom rmap = all_registers_s ∖ {[ PC; r_adv ]} →
     ⊢ inv invN (minv_sep I vinit)
     ∗ na_own logrel_nais ⊤ (*XXX*)
     ∗ na_inv logrel_nais assertN (assertInv AssertLib vinit)

     (* Registers *)
     ∗ PC ↦ᵣ LCap RWX (prog_start P) (prog_end P) (prog_start P) vinit
     ∗ r_adv ↦ᵣ LCap RWX (prog_start Adv) (prog_end Adv) (prog_start Adv) vinit
     ∗ ([∗ map] r↦w ∈ (register_to_lregister rmap vinit), r ↦ᵣ w ∗ ⌜is_zL w = true⌝)

     (* Memory *)
     (* P program *)
     ∗ ([∗ map] a↦w ∈ (memory_to_lmemory (prog_region P) vinit), a ↦ₐ w)
     (* Adv program  *)
     ∗ ([∗ map] a↦w ∈ (memory_to_lmemory (prog_region Adv) vinit), a ↦ₐ w)
     (* Linking Table *)
     ∗ ([∗ map] a↦w ∈ (memory_to_lmemory (assert_tbl_region tbl_assert_tbl AssertLib) vinit), a ↦ₐ w)

     ∗ EC⤇ ecur
     ∗ ([∗ set] o ∈ gset_all_otypes, can_alloc_pred o)
     ∗ ( [∗ map] tidx ↦ eid ∈ etbl_all, enclave_all tidx eid)

       -∗ WP Seq (Instr Executable) {{ λ _, True }}) →

  rtc erased_step
    ([Seq (Instr Executable)] , {| reg := reg ; mem := m ; etable := etbl ; enumcur := ecur |})
    (es, {| reg := reg' ; mem := m' ; etable := etbl' ; enumcur := ecur' |}) →
  minv I m'.
Proof.
  set (Σ' := #[invΣ; gen_heapΣ LAddr LWord; gen_heapΣ RegName LWord;
               na_invΣ; sealStorePreΣ; EnclavesAgreePreΣ; EnclavesExclPreΣ; ECPreΣ; Σ]).
  intros.
  eapply (@template_adequacy' Σ'); eauto; try typeclasses eauto.
Qed.

End single_adversary.

Module multiple_adversaries.

Section Adequacy.
  Context (Σ: gFunctors).
  Context {cname : CmptNameG}.
  Context {B C : CmptName}.
  Context {inv_preg: invGpreS Σ}.
  Context {mem_preg: gen_heapGpreS Addr Word Σ}.
  Context {reg_preg: gen_heapGpreS RegName Word Σ}.
  Context {sreg_preg: gen_heapGpreS SRegName Word Σ}.
  Context {entry_preg : entryGpreS Σ}.
  Context {seal_store_preg: sealStorePreG Σ}.
  Context {na_invg: na_invG Σ}.
  Context {sts_preg: STS_preG Addr region_type Σ}.
  Context {cstack_preg: CSTACK_preG Σ }.
  Context {heappreg: heapGpreS Σ}.
  Context `{MP: MachineParameters}.
  Context { HCNames : CNames = (list_to_set [B;C]) }.
  Context { HCNamesNoDup : NoDup [B;C] }.



    (∀ `{ceriseG Σ, sealStoreG Σ, NA: logrel_na_invs Σ, subG Σ' Σ} rmap,
        dom rmap = all_registers_s ∖ {[ PC; r_adv ]} →
     ⊢ inv invN (minv_sep I vinit)
       ∗ @na_own _ (@logrel_na_invG _ NA) logrel_nais ⊤ (*XXX*)
       ∗ @na_inv _ _ _ (@logrel_na_invG _ NA) logrel_nais assertN (assertInv AssertLib vinit)

       (* Registers *)
       ∗ PC ↦ᵣ LCap RWX (prog_start P) (prog_end P) (prog_start P) vinit
       ∗ r_adv ↦ᵣ LCap RWX (prog_start Adv) (prog_end Adv) (prog_start Adv) vinit
       ∗ ([∗ map] r↦w ∈ (register_to_lregister rmap vinit), r ↦ᵣ w ∗ ⌜is_zL w = true⌝)

       (* Memory *)
       (* P program *)
       ∗ ([∗ map] a↦w ∈ (memory_to_lmemory (prog_region P) vinit), a ↦ₐ w)
       (* Adv program  *)
       ∗ ([∗ map] a↦w ∈ (memory_to_lmemory (prog_region Adv) vinit), a ↦ₐ w)
       (* Linking Table *)
       ∗ ([∗ map] a↦w ∈ (memory_to_lmemory (assert_tbl_region tbl_assert_tbl AssertLib) vinit), a ↦ₐ w)

       ∗ EC⤇ ecur
       ∗ ([∗ set] o ∈ gset_all_otypes, can_alloc_pred o)
       ∗ ( [∗ map] tidx ↦ eid ∈ etbl_all, enclave_all tidx eid)

       -∗ WP Seq (Instr Executable) {{ λ _, True }}) →

End Adequacy.

End multiple_adversaries.
