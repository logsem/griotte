From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import adequacy.
From iris.base_logic Require Import invariants.
From griotte Require Import sts_multiple_updates.
From griotte Require Import logrel_binary interp_weakening_binary monotone_binary.
From griotte Require Import region_invariants_revocation_binary region_invariants_allocation_binary.
From griotte Require Import world_interp_allocation_compartments_binary stack_world_resources_binary.
From griotte Require Import switcher_preamble_binary interp_switcher_call_binary interp_switcher_return_binary.
From griotte Require Import switcher_adequacy_binary.
From griotte Require Import stack_callee_secret_binary stack_callee_secret_spec_binary.
From griotte Require Import stack_callee_secret_spec_run_binary.
From griotte Require Import mkregion_helpers disjoint_regions_tactics.
From griotte Require Import adequacy_helpers_binary compartment_layout.


(** * Adequacy of the trusted-callee stack confidentiality example

    The memory layout contains:
    - the switcher compartment;
    - the trusted compartment [T], whose private data is the secret, and
      which exports the entry point [T.f];
    - the adversary compartment [B], which imports [T.f].

    The two runs start from the same registers, and from memories that only
    differ in the secret of [T]. They either both halt, or both do not
    halt. *)
Class stack_callee_secret_memory_layout `{MP: MachineParameters} := {

    (* switcher *)
    switcher_cmpt : cmptSwitcher;

    (* trusted compartment T, its data region holds the secret *)
    T_cmpt : cmpt ;
    T_data_size :
    (cmpt_b_cgp T_cmpt + length (stack_callee_secret_data 0))%a = Some (cmpt_e_cgp T_cmpt);

    (* adv compartment B *)
    B_cmpt : cmpt ;
    offset_B_adv : nat;

    (* disjointness *)
    cmpts_disjoints : T_cmpt ## B_cmpt ;

    switcher_cmpt_disjoints :
    switcher_cmpt_disjoint T_cmpt switcher_cmpt
    ∧ switcher_cmpt_disjoint B_cmpt switcher_cmpt ;
  }.

(** We instantiate the switcher layout with the memory layout. *)
Local Instance memory_layout_switcherLayout `{stack_callee_secret_memory_layout} : switcherLayout.
Proof.
  exact (cmptSwitcher_switcherLayout switcher_cmpt).
Defined.

Local Instance memory_layout_switcherLayoutWf `{stack_callee_secret_memory_layout} : switcherLayoutWf.
Proof.
  pose proof (ot_switcher_size switcher_cmpt).
  pose proof (switcher_size switcher_cmpt).
  pose proof (switcher_call_entry_point switcher_cmpt).
  pose proof (switcher_return_entry_point switcher_cmpt).
  refine (mkSwitcherLayoutWf _ _ _ _ _); cbn in *; auto.
Defined.

(** The compartment T, holding [secret] in its data region. *)
Definition T_cmpt_secret `{stack_callee_secret_memory_layout} (secret : Z) : cmpt :=
  cmpt_with_data T_cmpt (stack_callee_secret_data secret) T_data_size.

Definition mk_initial_memory `{stack_callee_secret_memory_layout} (secret : Z) : Mem :=
  mk_initial_switcher switcher_cmpt ∪
    mk_initial_cmpt (T_cmpt_secret secret) ∪
    mk_initial_cmpt B_cmpt.

(** We describe the initial register file, the same in both runs. *)
Definition is_initial_registers `{stack_callee_secret_memory_layout} (reg: Reg) :=
  (* pc points-to T's PCC *)
  reg !! PC = Some (WCap RX Global (cmpt_b_pcc T_cmpt) (cmpt_e_pcc T_cmpt) (cmpt_a_code T_cmpt)) ∧
  (* cgp points-to T's CGP *)
  reg !! cgp = Some (WCap RW Global (cmpt_b_cgp T_cmpt) (cmpt_e_cgp T_cmpt) (cmpt_b_cgp T_cmpt)) ∧
  (* csp points-to the stack pointer (defined by the switcher's compartment) *)
  reg !! csp = Some (WCap RWL Local (b_stack switcher_cmpt) (e_stack switcher_cmpt) (b_stack switcher_cmpt)) ∧
  (* all the other registers are initialised at 0 *)
  (∀ (r: RegName), r ∉ ({[ PC; cgp; csp ]} : gset RegName) → reg !! r = Some (WInt 0)).

(** We describe the initial sregister file, ie., mtdc,
    which contains the trusted stack capability. *)
Definition is_initial_sregisters `{stack_callee_secret_memory_layout} (sreg : SReg) :=
  sreg !! MTDC = Some (WCap RWL Local
                         (b_trusted_stack switcher_cmpt)
                         (e_trusted_stack switcher_cmpt)
                         (b_trusted_stack switcher_cmpt)).

(** We describe the initial memory, for a given secret. *)
Definition is_initial_memory `{stack_callee_secret_memory_layout} (secret : Z) (mem: Mem) :=
  let b_switcher := (b_switcher switcher_cmpt) in
  let e_switcher := (e_switcher switcher_cmpt) in
  let a_switcher_call := (a_switcher_call switcher_cmpt) in
  let ot_switcher := (ot_switcher switcher_cmpt) in
  let switcher_entry :=
    WSentry XSRW_ Local
      b_switcher
      e_switcher
      a_switcher_call
  in
  let B_adv :=
    SCap RO Global
      (cmpt_exp_tbl_pcc B_cmpt)
      (cmpt_exp_tbl_entries_end B_cmpt)
      (cmpt_exp_tbl_entries_start B_cmpt)
  in
  let T_f :=
    SCap RO Global
      (cmpt_exp_tbl_pcc T_cmpt)
      (cmpt_exp_tbl_entries_end T_cmpt)
      (cmpt_exp_tbl_entries_start T_cmpt)
  in

  mem = mk_initial_memory secret
  (* instantiating T *)
  ∧ (cmpt_imports T_cmpt) = stack_callee_secret_imports B_adv
  ∧ (cmpt_code T_cmpt) = stack_callee_secret_code
  ∧ (cmpt_exp_tbl_entries T_cmpt) = stack_callee_secret_export_table_entries

  (* instantiating B *)
  ∧ (cmpt_imports B_cmpt) = [switcher_entry; WSealed ot_switcher T_f]
  ∧ Forall is_z (cmpt_code B_cmpt) (* only instructions *)
  ∧ Forall (is_initial_data_word B_cmpt) (cmpt_data B_cmpt)
  ∧ (cmpt_exp_tbl_entries B_cmpt) = [WInt (encode_entry_point stack_callee_secret_B_adv_args offset_B_adv)]
.

(** We derive some disjointness properties *)
Lemma mk_initial_cmpt_B_disjoint `{Layout: stack_callee_secret_memory_layout} (secret : Z) :
  mk_initial_switcher switcher_cmpt ∪ mk_initial_cmpt (T_cmpt_secret secret)
    ##ₘ mk_initial_cmpt B_cmpt.
Proof.
  pose proof cmpts_disjoints as HTB.
  pose proof switcher_cmpt_disjoints as (_ & HswitcherB).
  rewrite map_disjoint_union_l.
  split.
  - symmetry; apply disjoint_switcher_cmpts_mkinitial; done.
  - apply disjoint_cmpts_mkinitial; exact HTB.
Qed.

Lemma mk_initial_cmpt_T_disjoint `{Layout: stack_callee_secret_memory_layout} (secret : Z) :
  mk_initial_switcher switcher_cmpt ##ₘ mk_initial_cmpt (T_cmpt_secret secret).
Proof.
  pose proof switcher_cmpt_disjoints as (HswitcherT & _).
  symmetry; apply disjoint_switcher_cmpts_mkinitial; exact HswitcherT.
Qed.

(** The sealed entry points of two disjoint compartments are different. *)
Lemma sealed_entry_points_neq `{MP: MachineParameters}
  (C1 C2 : cmpt) (o : OType) (g1 g2 : Locality) (a1 a2 : Addr) :
  C1 ## C2 ->
  WSealed o (SCap RO g1 (cmpt_exp_tbl_pcc C1) (cmpt_exp_tbl_entries_end C1) a1)
  ≠ WSealed o (SCap RO g2 (cmpt_exp_tbl_pcc C2) (cmpt_exp_tbl_entries_end C2) a2).
Proof.
  intros Hdisjoint Heq.
  apply (exported_entry_point_disjoint C1 C2 RO RO g1 g2 a1 a2 Hdisjoint).
  inversion Heq; congruence.
Qed.

Ltac solve_entry_neq :=
  first
    [ solve [ intros ?; simplify_eq ]
    | apply sealed_entry_points_neq; apply cmpts_disjoints
    | apply not_eq_sym; apply sealed_entry_points_neq; apply cmpts_disjoints ].

(** One direction of the adequacy theorem: if the run with [secret1] halts,
    then the run with [secret2] halts. The binary specification is used with
    the run with [secret1] as implementation, and the run with [secret2] as
    specification. *)
Section Adequacy.
  Context (Σ: gFunctors).
  Context {cname : CmptNameG}.
  Context {B : CmptName}.
  Context {inv_preg: invGpreS Σ}.
  Context {mem_preg: gen_heapGpreS Addr Word Σ}.
  Context {reg_preg: gen_heapGpreS RegName Word Σ}.
  Context {sreg_preg: gen_heapGpreS SRegName Word Σ}.
  Context {entry_preg : entryGpreS Σ}.
  Context {seal_store_preg: sealStorePreG Σ}.
  Context {na_inv_preg: na_invGpreS Σ}.
  Context {sts_preg: STS_preG Addr region_type Σ}.
  Context {cstack_preg: CSTACK_preG Σ }.
  Context {relpreg: relGpreS Σ}.
  Context {spec_preg: specGpreS Σ}.
  Context `{MP: MachineParameters}.
  Context { HCNames : CNames = {[ B ]} }.

  Definition switcherN : namespace := nroot .@ "stack_callee_secret" .@ "switcher".
  Definition TN : namespace := nroot .@ "stack_callee_secret" .@ "T".

  Lemma stack_callee_secret_adequacy_one_sided `{Layout: stack_callee_secret_memory_layout}
    (reg : Reg) (sreg : SReg) (m1 m2 : Mem) (secret1 secret2 : Z) :
    is_initial_registers reg →
    is_initial_sregisters sreg →
    is_initial_memory secret1 m1 →
    is_initial_memory secret2 m2 →
    halts (reg, sreg, m1) → halts (reg, sreg, m2).
  Proof.
    intros Hreg Hsreg Hm1 Hm2.
    destruct Hm1 as (Hm1 & T_imports & T_code & T_exp_tbl
                     & B_imports & B_code & B_data & B_exp_tbl).
    destruct Hm2 as (Hm2 & _).
    subst m1 m2.

    (* 1 - We use the adequacy of the binary model, with the exported
       entry points for which we want to know the number of arguments. *)
    apply (binary_adequacy Σ
             {[ WSealed (ot_switcher switcher_cmpt)
                  (SCap RO Global (cmpt_exp_tbl_pcc B_cmpt) (cmpt_exp_tbl_entries_end B_cmpt)
                     (cmpt_exp_tbl_entries_start B_cmpt)) := stack_callee_secret_B_adv_args;
                WSealed (ot_switcher switcher_cmpt)
                  (SCap RO Local (cmpt_exp_tbl_pcc B_cmpt) (cmpt_exp_tbl_entries_end B_cmpt)
                     (cmpt_exp_tbl_entries_start B_cmpt)) := stack_callee_secret_B_adv_args;
                WSealed (ot_switcher switcher_cmpt)
                  (SCap RO Global (cmpt_exp_tbl_pcc T_cmpt) (cmpt_exp_tbl_entries_end T_cmpt)
                     (cmpt_exp_tbl_entries_start T_cmpt)) := stack_callee_secret_f_args;
                WSealed (ot_switcher switcher_cmpt)
                  (SCap RO Local (cmpt_exp_tbl_pcc T_cmpt) (cmpt_exp_tbl_entries_end T_cmpt)
                     (cmpt_exp_tbl_entries_start T_cmpt)) := stack_callee_secret_f_args ]}).
    iIntros (ceriseg specg) "#Hspec Hj Hna Hreg Hsreg Hmem Hreg_s Hsreg_s Hmem_s #Hentries".

    iDestruct (big_sepM_insert with "Hentries") as "[#Hentry_B_adv #Hentries1]".
    { repeat (rewrite lookup_insert_ne; last solve_entry_neq).
      by rewrite lookup_empty. }
    iDestruct (big_sepM_insert with "Hentries1") as "[#Hentry_B_adv' #Hentries2]".
    { repeat (rewrite lookup_insert_ne; last solve_entry_neq).
      by rewrite lookup_empty. }
    iDestruct (big_sepM_insert with "Hentries2") as "[#Hentry_T_f #Hentries3]".
    { repeat (rewrite lookup_insert_ne; last solve_entry_neq).
      by rewrite lookup_empty. }
    iDestruct (big_sepM_insert with "Hentries3") as "[#Hentry_T_f' _]".
    { by rewrite lookup_empty. }
    set (B_adv := (SCap RO Global (cmpt_exp_tbl_pcc B_cmpt) (cmpt_exp_tbl_entries_end B_cmpt)
                     (cmpt_exp_tbl_entries_start B_cmpt))).

    (* 2 - We initialise the ghost resources of the model *)
    (* 2.1 The seal store, for sealing capabilities.
       We only use the switcher's otype. *)
    iMod (seal_store_init ({[ (ot_switcher switcher_cmpt) ]} : gset _)) as (seal_storeg) "Hseal_store".
    (* 2.2 The call stacks of both runs, initialised to empty. *)
    iMod (gen_cstack_init []) as (cstackg) "[Hcstk_full Hcstk_frag]".
    iMod (gen_cstack_spec_init []) as (cstackg_spec) "[Hcstk_full_spec Hcstk_frag_spec]".
    (* 2.3 The world interpretations *)
    iMod (world_interp_init) as (relg stsg) "Hworld_interp".
    iEval (rewrite HCNames big_sepS_singleton) in "Hworld_interp".
    set (W0 := (∅, (∅, ∅))).

    (* 3 - Get initial sregister mtdc, in both runs *)
    iDestruct (big_sepM_lookup with "Hsreg") as "Hmtdc"; eauto.
    iDestruct (big_sepM_lookup with "Hsreg_s") as "Hsmtdc"; eauto.

    (* 4 - Separate all compartments *)
    rewrite /mk_initial_memory.
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hcmpt_B]".
    { eapply mk_initial_cmpt_B_disjoint. }
    iDestruct (big_sepM_union with "Hmem") as "[Hcmpt_switcher Hcmpt_T]".
    { eapply mk_initial_cmpt_T_disjoint. }
    iDestruct (big_sepM_union with "Hmem_s") as "[Hmem_s Hscmpt_B]".
    { eapply mk_initial_cmpt_B_disjoint. }
    iDestruct (big_sepM_union with "Hmem_s") as "[Hscmpt_switcher Hscmpt_T]".
    { eapply mk_initial_cmpt_T_disjoint. }
    iDestruct (big_sepM_sep_2 with "Hcmpt_switcher Hscmpt_switcher") as "Hcmpt_switcher".
    iDestruct (big_sepM_sep_2 with "Hcmpt_B Hscmpt_B") as "Hcmpt_B".

    (* 4.1 Switcher compartment *)
    iEval (rewrite big_sepS_singleton) in "Hseal_store".
    iMod ( initialise_switcher_compartment_binary (Σ := Σ) _ switcherN
             with "Hcmpt_switcher Hseal_store Hcstk_full Hcstk_full_spec Hmtdc Hsmtdc" )
      as "(#Hsealed_pred_ot_switcher & #Hswitcher & Hstack & Hsstack)".

    (* 4.2 CMPT B *)
    iMod (initialise_adversary_compartment_binary (Σ := Σ) _ B with "Hcmpt_B")
      as "(HB_imports & HB_code & HB_data & #HB_etbl_pcc & #HB_etbl_cgp & #HB_etbl_entries)".
    iEval (rewrite B_exp_tbl) in "HB_etbl_entries".
    rewrite (finz_seq_between_singleton (cmpt_exp_tbl_entries_start B_cmpt)%a).
    2: {
      pose proof (cmpt_exp_tbl_entries_size B_cmpt) as H1.
      rewrite B_exp_tbl in H1; solve_addr+H1.
    }
    iDestruct "HB_etbl_entries" as "/= [ HB_etbl_B_adv _ ]".

    (* 4.3 CMPT T, with a different secret in each run *)
    iDestruct (initialise_compartment_with_data_exp_tbl_gen with "Hcmpt_T")
      as "(HT_imports & HT_code & HT_data & HT_etbl_pcc & HT_etbl_cgp & HT_etbl_entries)".
    iDestruct (initialise_compartment_with_data_exp_tbl_gen with "Hscmpt_T")
      as "(HsT_imports & HsT_code & HsT_data & HsT_etbl_pcc & HsT_etbl_cgp & HsT_etbl_entries)".
    iAssert (
      codefrag (cmpt_a_code T_cmpt) (cmpt_code T_cmpt)
     )%I with "[HT_code]" as "HT_code".
    { rewrite /codefrag /region_pointsto.
      replace (cmpt_a_code T_cmpt ^+ length (cmpt_code T_cmpt))%a
        with (cmpt_e_pcc T_cmpt).
      2: { pose proof (cmpt_code_size T_cmpt) as H ; solve_addr+H. }
      done.
    }
    iAssert (
      spec_codefrag (cmpt_a_code T_cmpt) (cmpt_code T_cmpt)
     )%I with "[HsT_code]" as "HsT_code".
    { rewrite /spec_codefrag /spec_region_pointsto.
      replace (cmpt_a_code T_cmpt ^+ length (cmpt_code T_cmpt))%a
        with (cmpt_e_pcc T_cmpt).
      2: { pose proof (cmpt_code_size T_cmpt) as H ; solve_addr+H. }
      done.
    }
    assert ((cmpt_b_cgp T_cmpt + 1)%a = Some (cmpt_e_cgp T_cmpt)) as HT_data_size.
    { pose proof T_data_size as H.
      rewrite /stack_callee_secret_data /= in H.
      solve_addr+H. }
    iDestruct (region_pointsto_single with "HT_data") as "[%v [HT_secret %Hv]]"
    ; first exact HT_data_size.
    iDestruct (spec_region_pointsto_single with "HsT_data") as "[%sv [HsT_secret %Hsv]]"
    ; first exact HT_data_size.
    rewrite /stack_callee_secret_data in Hv Hsv; simplify_eq.
    rewrite T_exp_tbl /stack_callee_secret_export_table_entries.
    assert (finz.seq_between (cmpt_exp_tbl_entries_start T_cmpt) (cmpt_exp_tbl_entries_end T_cmpt)
            = [cmpt_exp_tbl_entries_start T_cmpt]) as HT_entries.
    { apply finz_seq_between_singleton.
      pose proof (cmpt_exp_tbl_entries_size T_cmpt) as H.
      by rewrite T_exp_tbl /= in H. }
    rewrite HT_entries.
    iEval (rewrite big_sepL2_singleton) in "HT_etbl_entries".
    iEval (rewrite big_sepL2_singleton) in "HsT_etbl_entries".
    rewrite T_imports T_code.

    (* 4.4 The invariants of T *)
    iMod (na_inv_alloc cerise_nais _ TN
            (stack_callee_secret_inv (cmpt_b_pcc T_cmpt) (cmpt_a_code T_cmpt) (cmpt_b_cgp T_cmpt)
               B_adv secret1 secret2)
           with "[HT_imports HsT_imports HT_code HsT_code HT_secret HsT_secret]") as "#HT".
    { iNext.
      rewrite /stack_callee_secret_inv /region_pointsto /spec_region_pointsto.
      iFrame.
    }
    iMod (inv_alloc (export_table_PCCN TN) ⊤
            (cmpt_exp_tbl_pcc T_cmpt
               ↦ₐ WCap RX Global (cmpt_b_pcc T_cmpt) (cmpt_e_pcc T_cmpt) (cmpt_b_pcc T_cmpt)
             ∗ cmpt_exp_tbl_pcc T_cmpt
               ↣ₐ WCap RX Global (cmpt_b_pcc T_cmpt) (cmpt_e_pcc T_cmpt) (cmpt_b_pcc T_cmpt)
            )%I with "[$HT_etbl_pcc $HsT_etbl_pcc]")%I
      as "#Hinv_T_etbl_PCC".
    iMod (inv_alloc (export_table_CGPN TN) ⊤
            (cmpt_exp_tbl_cgp T_cmpt
               ↦ₐ WCap RW Global (cmpt_b_cgp T_cmpt) (cmpt_e_cgp T_cmpt) (cmpt_b_cgp T_cmpt)
             ∗ cmpt_exp_tbl_cgp T_cmpt
               ↣ₐ WCap RW Global (cmpt_b_cgp T_cmpt) (cmpt_e_cgp T_cmpt) (cmpt_b_cgp T_cmpt)
            )%I with "[$HT_etbl_cgp $HsT_etbl_cgp]")%I
      as "#Hinv_T_etbl_CGP".
    iMod (inv_alloc (export_table_entryN TN (cmpt_exp_tbl_entries_start T_cmpt)) ⊤
            (cmpt_exp_tbl_entries_start T_cmpt ↦ₐ stack_callee_secret_exp_tbl_entry_f
             ∗ cmpt_exp_tbl_entries_start T_cmpt ↣ₐ stack_callee_secret_exp_tbl_entry_f
            )%I with "[$HT_etbl_entries $HsT_etbl_entries]")%I
      as "#Hinv_T_etbl_entry_f".

    (* 4.5 The entry point T.f is safe to share, in any world *)
    iAssert (
        ∀ W, interp W B
               (WSealed (ot_switcher switcher_cmpt)
                  (SCap RO Global (cmpt_exp_tbl_pcc T_cmpt) (cmpt_exp_tbl_entries_end T_cmpt)
                     (cmpt_exp_tbl_entries_start T_cmpt)),
                WSealed (ot_switcher switcher_cmpt)
                  (SCap RO Global (cmpt_exp_tbl_pcc T_cmpt) (cmpt_exp_tbl_entries_end T_cmpt)
                     (cmpt_exp_tbl_entries_start T_cmpt)))
      )%I as "#Hinterp_T_f".
    {
      iIntros (W).
      pose proof (cmpt_exp_tbl_pcc_size T_cmpt) as H0.
      pose proof (cmpt_exp_tbl_cgp_size T_cmpt) as H1.
      pose proof (cmpt_exp_tbl_entries_size T_cmpt) as H2.
      pose proof (cmpt_import_size T_cmpt) as H3.
      pose proof (cmpt_code_size T_cmpt) as H4.
      rewrite T_exp_tbl /= in H2.
      rewrite T_imports in H3.
      rewrite T_code in H4.
      replace (cmpt_exp_tbl_entries_start T_cmpt)
        with ((cmpt_exp_tbl_pcc T_cmpt) ^+ 2)%a by solve_addr+H0 H1.
      replace (cmpt_exp_tbl_cgp T_cmpt)
        with (cmpt_exp_tbl_pcc T_cmpt ^+ 1)%a by solve_addr+H0.
      assert (cmpt_exp_tbl_pcc T_cmpt <= cmpt_exp_tbl_pcc T_cmpt ^+ 2 < cmpt_exp_tbl_entries_end T_cmpt)%a
        as Htbl_size by solve_addr+H0 H1 H2.
      assert (SubBounds (cmpt_b_pcc T_cmpt) (cmpt_e_pcc T_cmpt) (cmpt_a_code T_cmpt)
                (cmpt_a_code T_cmpt ^+ length stack_callee_secret_code)%a) as HsubBounds_T.
      { rewrite /SubBounds. solve_addr+H3 H4. }
      iApply (stack_callee_secret_f_interp
                (cmpt_b_pcc T_cmpt) (cmpt_e_pcc T_cmpt) (cmpt_a_code T_cmpt)
                (cmpt_b_cgp T_cmpt) (cmpt_e_cgp T_cmpt)
                (cmpt_exp_tbl_pcc T_cmpt) (cmpt_exp_tbl_entries_end T_cmpt)
                B_adv secret1 secret2 W B switcherN TN
                Htbl_size HsubBounds_T H3 T_data_size).
      iFrame "#".
    }

    (* 5 - Initialise the world for B *)
    (* 5.1 Make the compartment B safe to share *)
    iMod (
       alloc_compartment_interp with "[$HB_imports] [$HB_code] [$HB_data] [] [$Hworld_interp]"
      ) as "(Hworld_interp_B & #HB_code & #HB_data & _)"; eauto.
    { apply Forall_true; intros; done. }
    { apply Forall_true; intros; done. }
    { apply Forall_true; intros; done. }
    { rewrite B_imports.
      iIntros "_".
      (* Switcher entry point *)
      iApply big_sepL_cons; iSplitL.
      { iSplit; [| iIntros (???) "!> _" ] ; iApply interp_switcher_call ; done. }
      (* T.f *)
      iApply big_sepL_cons; iSplitL; last done.
      iSplit; [| iIntros (???) "!> _" ] ; iApply "Hinterp_T_f".
    }

    assert (
        Forall
          (λ k : finz MemNum, std (std_update_compartment (∅, (∅, ∅)) B_cmpt) !! k = None)
          (finz.seq_between (b_stack switcher_cmpt) (e_stack switcher_cmpt))
      ) as Hstack_disjoint_B.
    { apply Forall_forall; intros a Ha; cbn.
      pose proof switcher_cmpt_disjoints as (_ & Hb).
      eapply switcher_cmpt_disjoint_std_update_compartment; eauto.
    }

    (* 5.2 Allocate the stack in the world,
       with Revoked state because we need to keep the points-to predicates *)
    iMod ( world_interp_extend_revoked_sepL2 _ _
             (finz.seq_between (b_stack switcher_cmpt) (e_stack switcher_cmpt))
             RWL interpC
           with "[$Hworld_interp_B]")
           as "(Hworld_interp_B & Hrel_stk_B)"; first eapply Hstack_disjoint_B.

    (* The world for B is now ready initial world. *)
    match goal with
    | H: _ |- context [  (world_interp ?W B) ] => set (Winit_B := W)
    end.

    (* 6 - Derive that the entry point of B is safe to share in the initial
       world. It holds because interp is monotone with future world. *)
    assert ( related_sts_priv_world (std_update_compartment W0 B_cmpt) Winit_B)
      as Hrelated_W'_Winit_B.
    {
      rewrite /Winit_B.
      apply related_sts_pub_priv_world.
      eapply related_sts_pub_update_multiple.
      eapply Forall_impl; eauto.
      intros a Ha; cbn in *.
      by rewrite not_elem_of_dom.
    }

    iAssert (interp Winit_B B
               (WCap RX Global (cmpt_b_pcc B_cmpt) (cmpt_e_pcc B_cmpt) (cmpt_b_pcc B_cmpt)%a,
                WCap RX Global (cmpt_b_pcc B_cmpt) (cmpt_e_pcc B_cmpt) (cmpt_b_pcc B_cmpt)%a)
            )%I as "#Hinterp_pcc_B".
    { iApply interp_monotone_nl; eauto. }

    iAssert (interp Winit_B B
               (WCap RW Global (cmpt_b_cgp B_cmpt) (cmpt_e_cgp B_cmpt) (cmpt_b_cgp B_cmpt)%a,
                WCap RW Global (cmpt_b_cgp B_cmpt) (cmpt_e_cgp B_cmpt) (cmpt_b_cgp B_cmpt)%a)
            )%I as "#Hinterp_cgp_B".
    { iApply interp_monotone_nl; eauto. }

    iAssert ( interp Winit_B B (WSealed (ot_switcher switcher_cmpt) B_adv,
                                WSealed (ot_switcher switcher_cmpt) B_adv)) as "#Hinterp_B".
    { iApply (ot_switcher_interp_entry _ _ _ _ stack_callee_secret_B_adv_args offset_B_adv); eauto
      ; last (rewrite /stack_callee_secret_B_adv_args; lia).
      pose proof (cmpt_exp_tbl_entries_size B_cmpt) as H1.
      pose proof (cmpt_exp_tbl_entries_size B_cmpt) as H2.
      rewrite B_exp_tbl in H2.
      solve_addr+H1 H2.
    }

    (* The stack is revoked in the initial world of B *)
    assert ( revoked_addresses Winit_B
               ( finz.seq_between (b_stack switcher_cmpt) (e_stack switcher_cmpt) ) )
      as Hrevoked_stack_B.
    { subst Winit_B.
      rewrite /revoked_addresses Forall_forall.
      intros a Ha.
      by apply std_sta_update_multiple_lookup_in_i.
    }
    iDestruct ( StackWorldResources_from_rel_stack Winit_B B with "Hrel_stk_B" ) as "Hrevoked_stack_B".
    iClear "HB_etbl_pcc HB_etbl_cgp HB_code HB_data Hinterp_pcc_B Hinterp_cgp_B".

    (* 7 - Extract registers, in both runs *)
    destruct Hreg as (HPC & Hcgp & Hcsp & Hreg_zero).
    iDestruct (big_sepM_delete _ _ PC with "Hreg") as "[HPC Hreg]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cgp with "Hreg") as "[Hcgp Hreg]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ csp with "Hreg") as "[Hcsp Hreg]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ PC with "Hreg_s") as "[HsPC Hreg_s]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cgp with "Hreg_s") as "[Hscgp Hreg_s]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ csp with "Hreg_s") as "[Hscsp Hreg_s]"; first by simplify_map_eq.
    iDestruct (initial_registers_pair reg Hreg_zero with "Hreg Hreg_s") as "Hregs".

    (* 8 - The initial continuation is empty *)
    iAssert (interp_continuation [] [] []) as "HK".
    { by rewrite /interp_continuation /interp_cont /=. }

    (* 9 - The side conditions of the specification *)
    assert (dom (delete csp (delete cgp (delete PC reg))) = all_registers_s ∖ {[ PC ; cgp ; csp]})
      as Hrmap_dom.
    { rewrite !dom_delete_L.
      rewrite regmap_full_dom; first done.
      intros r.
      destruct (decide (r = PC)); simplify_eq.
      { eexists; eapply HPC. }
      destruct (decide (r = cgp)); simplify_eq.
      { eexists; eapply Hcgp. }
      destruct (decide (r = csp)); simplify_eq.
      { eexists; eapply Hcsp. }
      eexists (WInt 0).
      apply Hreg_zero.
      clear -n n0 n1; set_solver.
    }
    assert (SubBounds (cmpt_b_pcc T_cmpt) (cmpt_e_pcc T_cmpt) (cmpt_a_code T_cmpt)
              (cmpt_a_code T_cmpt ^+ length stack_callee_secret_code)%a) as HsubBounds.
    { rewrite /SubBounds.
      pose proof (cmpt_import_size T_cmpt) as HT_imports_size.
      pose proof (cmpt_code_size T_cmpt) as HT_code_size.
      rewrite -T_code.
      solve_addr+HT_imports_size HT_code_size.
    }
    assert ((cmpt_b_pcc T_cmpt + length (stack_callee_secret_imports B_adv))%a
            = Some (cmpt_a_code T_cmpt)) as Himports_contiguous.
    { pose proof (cmpt_import_size T_cmpt) as HT_imports_size.
      by rewrite -HT_imports_size T_imports.
    }

    (* 10 - We can apply the specification! *)
    iModIntro.
    iApply (stack_callee_secret_run_spec (B := B)
              (cmpt_b_pcc T_cmpt) (cmpt_e_pcc T_cmpt) (cmpt_a_code T_cmpt)
              (cmpt_b_cgp T_cmpt) (cmpt_e_cgp T_cmpt)
              (b_stack switcher_cmpt) (e_stack switcher_cmpt)
              _ B_adv Winit_B [] [] [] _ _ secret1 secret2 switcherN TN
              Hrmap_dom HsubBounds Himports_contiguous Hrevoked_stack_B
             with "[$Hswitcher $HT $Hspec $Hna $Hj
                    $HPC $HsPC $Hcgp $Hscgp $Hcsp $Hscsp $Hregs
                    $Hstack $Hsstack $Hworld_interp_B $HK $Hcstk_frag $Hcstk_frag_spec
                    $Hinterp_B $Hentry_B_adv $Hrevoked_stack_B]").
  Qed.
End Adequacy.


(** We initialise concretely the compartments name typeclass. *)

Inductive CmptNames_SCS := | B.
Local Instance CmptNames_SCS_eq_dec : EqDecision CmptNames_SCS.
Proof. intros C C'; destruct C,C'; solve_decision. Qed.
Local Instance CmptNames_SCS_finite : finite.Finite CmptNames_SCS.
Proof.
  refine {| finite.enum := [B] |}.
  + apply NoDup_singleton.
  + intros []; left.
Defined.

Local Program Instance CmptNames_SCS_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_SCS; |}.

(** END-TO-END THEOREM *)
Theorem stack_callee_secret_adequacy `{Layout: stack_callee_secret_memory_layout}
  (reg : Reg) (sreg : SReg) (m1 m2 : Mem) (secret1 secret2 : Z) :
  is_initial_registers reg →
  is_initial_sregisters sreg →
  is_initial_memory secret1 m1 →
  is_initial_memory secret2 m2 →
  (∃ es c, rtc erased_step ([Seq (Instr Executable)], (reg, sreg, m1)) (Seq (Instr Halted) :: es, c)) ↔
  (∃ es c, rtc erased_step ([Seq (Instr Executable)], (reg, sreg, m2)) (Seq (Instr Halted) :: es, c)).
Proof.
  intros Hreg Hsreg Hm1 Hm2.
  set ( cnames := CmptNames_SCS_CmptNameG ).
  set (Σ := #[invΣ
              ; gen_heapΣ Addr Word; gen_heapΣ RegName Word; gen_heapΣ SRegName Word
              ; entryPreΣ ; CSTACK_preΣ
              ; na_invΣ; sealStorePreΣ
              ; STS_preΣ Addr region_type ; relPreΣ
              ; savedPredΣ (WorldT * CmptName * (Word * Word))
              ; specΣ
      ]).
  assert (CNames = {[ B ]}) as HCNames.
  { rewrite /CNames /=. set_solver. }
  apply (halts_equiv (reg, sreg, m1) (reg, sreg, m2)).
  - eapply (@stack_callee_secret_adequacy_one_sided Σ cnames B); eauto; try typeclasses eauto.
  - eapply (@stack_callee_secret_adequacy_one_sided Σ cnames B); eauto; try typeclasses eauto.
Qed.
