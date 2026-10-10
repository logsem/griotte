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
From griotte Require Import adequacy_helpers_binary compartment_layout adequacy_common_binary.
From griotte Require Import contextual_equivalence_binary.


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

Local Instance memory_layout_switcherLayoutWf `{stack_callee_secret_memory_layout} : switcherLayoutWf :=
  cmptSwitcher_switcherLayoutWf switcher_cmpt.

(** The compartment T, holding [secret] in its data region. *)
Definition T_cmpt_secret `{stack_callee_secret_memory_layout} (secret : Z) : cmpt :=
  cmpt_with_data T_cmpt (stack_callee_secret_data secret) T_data_size.

Definition mk_initial_memory `{stack_callee_secret_memory_layout} (secret : Z) : Mem :=
  mk_initial_switcher switcher_cmpt ∪
    mk_initial_cmpt (T_cmpt_secret secret) ∪
    mk_initial_cmpt B_cmpt.

(** We describe the initial register file, the same in both runs. *)
Definition is_initial_registers `{stack_callee_secret_memory_layout} :=
  is_initial_registers_of switcher_cmpt T_cmpt.

(** We describe the initial sregister file, ie., mtdc,
    which contains the trusted stack capability. *)
Definition is_initial_sregisters `{stack_callee_secret_memory_layout} :=
  is_initial_sregisters_of switcher_cmpt.

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
    pose proof cmpts_disjoints as HTB.
    pose proof switcher_cmpt_disjoints as (Hsw_T & Hsw_B).

    (* 1 - We give names to the exported entry points for which we want to
       know the number of arguments. *)
    change (SCap RO Global (cmpt_exp_tbl_pcc B_cmpt) (cmpt_exp_tbl_entries_end B_cmpt)
              (cmpt_exp_tbl_entries_start B_cmpt))
      with (cmpt_export B_cmpt (cmpt_exp_tbl_entries_start B_cmpt)) in T_imports.
    change (SCap RO Global (cmpt_exp_tbl_pcc T_cmpt) (cmpt_exp_tbl_entries_end T_cmpt)
              (cmpt_exp_tbl_entries_start T_cmpt))
      with (cmpt_export T_cmpt (cmpt_exp_tbl_entries_start T_cmpt)) in B_imports.
    set (B_adv := cmpt_export B_cmpt (cmpt_exp_tbl_entries_start B_cmpt)).
    set (T_f := cmpt_export T_cmpt (cmpt_exp_tbl_entries_start T_cmpt)).

    (* 2 - We use the adequacy of the binary model, which initialises the
       program logic resources of both runs, and the entry points. *)
    apply (binary_adequacy Σ
             (exported_entries (ot_switcher switcher_cmpt)
                [(B_adv, stack_callee_secret_B_adv_args); (T_f, stack_callee_secret_f_args)])).
    iIntros (ceriseg specg) "#Hspec Hj Hna Hreg Hsreg Hmem Hreg_s Hsreg_s Hmem_s Hentries".
    iDestruct (entries_split with "Hentries")
      as "([#Hentry_B_adv #Hentry_B_adv'] & [#Hentry_T_f #Hentry_T_f'] & _)".
    { apply NoDup_cons; split; last apply NoDup_singleton.
      rewrite list_elem_of_singleton.
      intros Heq; cbn in Heq.
      apply (cmpt_export_disjoint T_cmpt B_cmpt
               (cmpt_exp_tbl_entries_start T_cmpt) (cmpt_exp_tbl_entries_start B_cmpt) HTB).
      symmetry; exact Heq. }
    { by repeat constructor. }

    (* 3 - We initialise the seal store, the call stacks of both runs, and
       the world interpretation of B *)
    iMod (initialise_world_binary [B] {[ ot_switcher switcher_cmpt ]})
      as (seal_storeg relg stsg cstackg cstackg_spec)
           "(Hseal_store & Hcstk_full & Hcstk_frag & Hcstk_full_spec & Hcstk_frag_spec
            & [Hworld_interp_B _])";
      [rewrite HCNames; set_solver+ | apply NoDup_singleton |].

    (* 4 - Get initial sregister mtdc, in both runs *)
    iDestruct (big_sepM_lookup with "Hsreg") as "Hmtdc"; first exact Hsreg.
    iDestruct (big_sepM_lookup with "Hsreg_s") as "Hsmtdc"; first exact Hsreg.

    (* 5 - Separate all compartments *)
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

    (* 5.1 Switcher compartment *)
    iEval (rewrite big_sepS_singleton) in "Hseal_store".
    iMod ( initialise_switcher_compartment_binary (Σ := Σ) _ switcherN
             with "Hcmpt_switcher Hseal_store Hcstk_full Hcstk_full_spec Hmtdc Hsmtdc" )
      as "(#Hsealed_pred_ot_switcher & #Hswitcher & Hstack & Hsstack)".

    (* 5.2 CMPT B *)
    iMod (initialise_adversary_compartment_binary (Σ := Σ) _ B with "Hcmpt_B")
      as "(HB_imports & HB_code & HB_data & #HB_etbl_pcc & #HB_etbl_cgp & #HB_etbl_entries)".

    (* 5.3 CMPT T, with a different secret in each run *)
    iDestruct (initialise_compartment_with_data_exp_tbl_gen with "Hcmpt_T")
      as "(HT_imports & HT_code & HT_data & HT_etbl_pcc & HT_etbl_cgp & HT_etbl_entries)".
    iDestruct (initialise_compartment_with_data_exp_tbl_gen with "Hscmpt_T")
      as "(HsT_imports & HsT_code & HsT_data & HsT_etbl_pcc & HsT_etbl_cgp & HsT_etbl_entries)".
    iDestruct (cmpt_code_codefrag with "HT_code") as "HT_code".
    iDestruct (cmpt_code_spec_codefrag with "HsT_code") as "HsT_code".
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

    (* 6 - The invariants of T *)
    iMod (na_inv_alloc cerise_nais _ TN
            (stack_callee_secret_inv (cmpt_b_pcc T_cmpt) (cmpt_a_code T_cmpt) (cmpt_b_cgp T_cmpt)
               B_adv secret1 secret2)
           with "[$HT_imports $HsT_imports $HT_code $HsT_code $HT_secret $HsT_secret]") as "#HT".
    iMod (inv_alloc (export_table_PCCN TN) ⊤
            (cmpt_exp_tbl_pcc T_cmpt
               ↦ₐ WCap RX Global (cmpt_b_pcc T_cmpt) (cmpt_e_pcc T_cmpt) (cmpt_b_pcc T_cmpt)
             ∗ cmpt_exp_tbl_pcc T_cmpt
               ↣ₐ WCap RX Global (cmpt_b_pcc T_cmpt) (cmpt_e_pcc T_cmpt) (cmpt_b_pcc T_cmpt))%I
           with "[$HT_etbl_pcc $HsT_etbl_pcc]")
      as "#Hinv_T_etbl_PCC".
    iMod (inv_alloc (export_table_CGPN TN) ⊤
            (cmpt_exp_tbl_cgp T_cmpt
               ↦ₐ WCap RW Global (cmpt_b_cgp T_cmpt) (cmpt_e_cgp T_cmpt) (cmpt_b_cgp T_cmpt)
             ∗ cmpt_exp_tbl_cgp T_cmpt
               ↣ₐ WCap RW Global (cmpt_b_cgp T_cmpt) (cmpt_e_cgp T_cmpt) (cmpt_b_cgp T_cmpt))%I
           with "[$HT_etbl_cgp $HsT_etbl_cgp]")
      as "#Hinv_T_etbl_CGP".
    iMod (inv_alloc (export_table_entryN TN (cmpt_exp_tbl_entries_start T_cmpt)) ⊤
            (cmpt_exp_tbl_entries_start T_cmpt ↦ₐ stack_callee_secret_exp_tbl_entry_f
             ∗ cmpt_exp_tbl_entries_start T_cmpt ↣ₐ stack_callee_secret_exp_tbl_entry_f)%I
           with "[$HT_etbl_entries $HsT_etbl_entries]")
      as "#Hinv_T_etbl_entry_f".

    (* 7 - The entry point T.f is safe to share, in any world *)
    pose proof (main_code_size_obligations _ _ _ T_imports T_code)
      as (HsubBounds & Himports_contiguous).
    iAssert (∀ W, interp W B (WSealed (ot_switcher switcher_cmpt) T_f,
                              WSealed (ot_switcher switcher_cmpt) T_f))%I
      as "#Hinterp_T_f".
    { iIntros (W).
      pose proof (cmpt_exp_tbl_pcc_size T_cmpt) as H0.
      pose proof (cmpt_exp_tbl_cgp_size T_cmpt) as H1.
      pose proof (cmpt_exp_tbl_entries_size T_cmpt) as H2.
      rewrite T_exp_tbl /= in H2.
      iEval (rewrite /T_f /cmpt_export /=) in "Hentry_T_f".
      iEval (rewrite /T_f /cmpt_export /=) in "Hentry_T_f'".
      rewrite /T_f /cmpt_export.
      replace (cmpt_exp_tbl_entries_start T_cmpt)
        with ((cmpt_exp_tbl_pcc T_cmpt) ^+ 2)%a by solve_addr+H0 H1.
      replace (cmpt_exp_tbl_cgp T_cmpt)
        with (cmpt_exp_tbl_pcc T_cmpt ^+ 1)%a by solve_addr+H0.
      iApply (stack_callee_secret_f_interp
                (cmpt_b_pcc T_cmpt) (cmpt_e_pcc T_cmpt) (cmpt_a_code T_cmpt)
                (cmpt_b_cgp T_cmpt) (cmpt_e_cgp T_cmpt)
                (cmpt_exp_tbl_pcc T_cmpt) (cmpt_exp_tbl_entries_end T_cmpt)
                B_adv secret1 secret2 W B switcherN TN
                ltac:(solve_addr+H0 H1 H2) HsubBounds Himports_contiguous T_data_size).
      iFrame "#".
    }

    (* 8 - Initialise the world of B: its compartment becomes permanent, and
       the stack is allocated as revoked, because we keep its points-to
       predicates. *)
    iMod (initialise_adversary_world_revoked_binary _ switcher_cmpt _ B
           with "HB_imports HB_code HB_data [] Hworld_interp_B")
      as "(Hworld_interp_B & #Hinterp_pcc_B & #Hinterp_cgp_B & #Hrevoked_stack_B)"; auto.
    { rewrite B_imports.
      iIntros "_".
      (* Switcher entry point *)
      iSplit.
      { iSplit; [| iIntros (???) "!> _" ] ; iApply interp_switcher_call ; done. }
      (* T.f *)
      iSplit; last done.
      iSplit; [| iIntros (???) "!> _" ] ; iApply "Hinterp_T_f".
    }

    (* 9 - The exported entry point of B is safe to share *)
    iAssert (interp (adv_world_revoked (∅, (∅, ∅)) switcher_cmpt B_cmpt) B
               (WSealed (ot_switcher switcher_cmpt) B_adv, WSealed (ot_switcher switcher_cmpt) B_adv))
      as "#Hinterp_B".
    { iApply (adversary_export_interp_binary _ _ _ _ _ 0 stack_callee_secret_B_adv_args offset_B_adv
               with "Hswitcher Hsealed_pred_ot_switcher HB_etbl_pcc HB_etbl_cgp HB_etbl_entries
                     Hinterp_pcc_B Hinterp_cgp_B Hentry_B_adv Hentry_B_adv'").
      - by rewrite B_exp_tbl.
      - pose proof (cmpt_exp_tbl_entries_size B_cmpt); solve_addr.
      - rewrite /stack_callee_secret_B_adv_args; lia.
    }

    (* 10 - Extract registers, in both runs *)
    iDestruct (initial_registers_split_binary with "Hreg Hreg_s")
      as (rmap) "(HPC & HsPC & Hcgp & Hscgp & Hcsp & Hscsp & Hregs & %Hrmap_dom)";
      first exact Hreg.

    (* 11 - The initial continuation is empty *)
    iAssert (interp_continuation [] [] []) as "HK".
    { by rewrite /interp_continuation /interp_cont /=. }

    (* 12 - We can apply the specification! *)
    iModIntro.
    iApply (stack_callee_secret_run_spec (B := B)
              (cmpt_b_pcc T_cmpt) (cmpt_e_pcc T_cmpt) (cmpt_a_code T_cmpt)
              (cmpt_b_cgp T_cmpt) (cmpt_e_cgp T_cmpt)
              (b_stack switcher_cmpt) (e_stack switcher_cmpt)
              _ B_adv _ [] [] [] _ _ secret1 secret2 switcherN TN
              Hrmap_dom HsubBounds Himports_contiguous (adv_world_revoked_stack _ _ _)
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

(** * Contextual equivalence *)

Section ctx_equiv.
  Context `{MP: MachineParameters}.

  (** The trusted part, shared by both programs: the switcher, and the layout,
      the code and the export table of the trusted compartment [T]. *)
  Context (sw : cmptSwitcher) (T : cmpt).
  Context (HT_size :
            (cmpt_b_cgp T + length (stack_callee_secret_data 0))%a = Some (cmpt_e_cgp T)).

  #[local] Instance stack_callee_secret_switcherLayout : switcherLayout := cmptSwitcher_switcherLayout sw.

  Context (HT_code : cmpt_code T = stack_callee_secret_code)
          (HT_exports : cmpt_exp_tbl_entries T = stack_callee_secret_export_table_entries).

  (** The program is the trusted compartment [T], holding [secret] in its data
      region. *)
  Definition stack_callee_secret_prog (secret : Z) : cmpt :=
    cmpt_with_data T (stack_callee_secret_data secret) HT_size.

  (** The context is the adversary compartment [B_adv]. It imports the switcher
      and the entry point [T.f] exported by [T], and exports the entry point
      [B.adv] imported by [T]. *)
  #[local] Instance stack_callee_secret_linking : Linking cmpt cmpt := {
    is_context B_adv :=
      is_adv_cmpt
        [switcher_entry sw; WSealed (ot_switcher sw) (cmpt_export T (cmpt_exp_tbl_entries_start T))]
        [stack_callee_secret_B_adv_args] B_adv;
    link B_adv P σ :=
      let '(reg, sreg, m) := σ in
      P ## B_adv ∧
      switcher_cmpt_disjoint P sw ∧
      switcher_cmpt_disjoint B_adv sw ∧
      cmpt_imports P = stack_callee_secret_imports (cmpt_export B_adv (cmpt_exp_tbl_entries_start B_adv)) ∧
      is_initial_registers_of sw P reg ∧
      is_initial_sregisters_of sw sreg ∧
      m = mk_initial_switcher sw ∪ mk_initial_cmpt P ∪ mk_initial_cmpt B_adv
  }.

  (** END-TO-END THEOREM *)
  Theorem stack_callee_secret_ctx_equiv (secret1 secret2 : Z) :
    ctx_equiv (stack_callee_secret_prog secret1) (stack_callee_secret_prog secret2).
  Proof.
    intros B_adv [ [reg1 sreg1] m1] [ [reg2 sreg2] m2] HB Hl1 Hl2.
    destruct HB as (HB_imports & HB_code & HB_data & HB_exports).
    inversion HB_exports as [|? w ? ? (off & ->) Hnil]; subst.
    inversion Hnil; subst.
    destruct Hl1 as (HTB & Hsw_T & Hsw_B & Himports & Hreg1 & Hsreg1 & ->).
    destruct Hl2 as (_ & _ & _ & _ & Hreg2 & Hsreg2 & ->).
    assert (reg2 = reg1) as ->.
    { by eapply (is_initial_registers_of_unique sw T). }
    assert (sreg2 = sreg1) as ->.
    { by eapply is_initial_sregisters_of_unique. }
    set (Layout :=
           {| switcher_cmpt := sw;
              T_cmpt := T;
              T_data_size := HT_size;
              B_cmpt := B_adv;
              offset_B_adv := off;
              cmpts_disjoints := HTB;
              switcher_cmpt_disjoints := conj Hsw_T Hsw_B |}).
    rewrite /halt_equiv /halts.
    apply (stack_callee_secret_adequacy (Layout := Layout) _ _ _ _ secret1 secret2); try done.
    all: by repeat split.
  Qed.

End ctx_equiv.
