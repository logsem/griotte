From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import adequacy.
From iris.base_logic Require Import invariants.
From griotte Require Import sts_multiple_updates.
From griotte Require Import logrel_binary interp_weakening_binary monotone_binary.
From griotte Require Import region_invariants_revocation_binary region_invariants_allocation_binary.
From griotte Require Import world_interp_allocation_compartments_binary stack_world_resources_binary.
From griotte Require Import switcher_preamble_binary interp_switcher_call_binary interp_switcher_return_binary.
From griotte Require Import switcher_adequacy_binary.
From griotte Require Import cmdc_binary cmdc_spec_binary.
From griotte Require Import mkregion_helpers disjoint_regions_tactics.
From griotte Require Import adequacy_helpers_binary compartment_layout adequacy_common_binary.


(** * Adequacy of the CMDC confidentiality example

    The memory layout contains:
    - the switcher compartment;
    - the trusted compartment [main], whose private data holds the secrets
      [secret_b] and [secret_c];
    - the adversary compartments [B] and [C].

    The two runs start from the same registers, and from memories that only
    differ in the secrets of [main]. They either both halt, or both do not
    halt. *)
Class cmdc_conf_memory_layout `{MP: MachineParameters} := {

    (* switcher *)
    switcher_cmpt : cmptSwitcher;

    (* main compartment, its data region holds b, c, and the secrets *)
    main_cmpt : cmpt ;
    main_data_size :
    (cmpt_b_cgp main_cmpt + length (cmdc_conf_main_data 0 0))%a = Some (cmpt_e_cgp main_cmpt);

    (* adv compartments B and C *)
    B_cmpt : cmpt ;
    offset_B_f : nat;
    C_cmpt : cmpt ;
    offset_C_g : nat;

    (* disjointness *)
    cmpts_disjoints :
    main_cmpt ## B_cmpt
    ∧ main_cmpt ## C_cmpt
    ∧ B_cmpt ## C_cmpt ;

    switcher_cmpt_disjoints :
    switcher_cmpt_disjoint main_cmpt switcher_cmpt
    ∧ switcher_cmpt_disjoint B_cmpt switcher_cmpt
    ∧ switcher_cmpt_disjoint C_cmpt switcher_cmpt ;
  }.

(** We instantiate the switcher layout with the memory layout. *)
Local Instance memory_layout_switcherLayout `{cmdc_conf_memory_layout} : switcherLayout.
Proof.
  exact (cmptSwitcher_switcherLayout switcher_cmpt).
Defined.

Local Instance memory_layout_switcherLayoutWf `{cmdc_conf_memory_layout} : switcherLayoutWf :=
  cmptSwitcher_switcherLayoutWf switcher_cmpt.

(** The main compartment, holding the [secrets] [(secret_b, secret_c)] in
    its data region. *)
Definition main_cmpt_secrets `{cmdc_conf_memory_layout} (secrets : Z * Z) : cmpt :=
  cmpt_with_data main_cmpt (cmdc_conf_main_data secrets.1 secrets.2) main_data_size.

Definition mk_initial_memory `{cmdc_conf_memory_layout} (secrets : Z * Z) : Mem :=
  mk_initial_switcher switcher_cmpt ∪
    mk_initial_cmpt (main_cmpt_secrets secrets) ∪
    mk_initial_cmpt B_cmpt ∪
    mk_initial_cmpt C_cmpt.

(** We describe the initial register file, the same in both runs. *)
Definition is_initial_registers `{cmdc_conf_memory_layout} :=
  is_initial_registers_of switcher_cmpt main_cmpt.

(** We describe the initial sregister file, ie., mtdc,
    which contains the trusted stack capability. *)
Definition is_initial_sregisters `{cmdc_conf_memory_layout} :=
  is_initial_sregisters_of switcher_cmpt.

(** We describe the initial memory, for given secrets. *)
Definition is_initial_memory `{cmdc_conf_memory_layout} (secrets : Z * Z) (mem: Mem) :=
  let b_switcher := (b_switcher switcher_cmpt) in
  let e_switcher := (e_switcher switcher_cmpt) in
  let a_switcher_call := (a_switcher_call switcher_cmpt) in
  let switcher_entry :=
    WSentry XSRW_ Local
      b_switcher
      e_switcher
      a_switcher_call
  in
  let B_f :=
    SCap RO Global
      (cmpt_exp_tbl_pcc B_cmpt)
      (cmpt_exp_tbl_entries_end B_cmpt)
      (cmpt_exp_tbl_entries_start B_cmpt)
  in
  let C_g :=
    SCap RO Global
      (cmpt_exp_tbl_pcc C_cmpt)
      (cmpt_exp_tbl_entries_end C_cmpt)
      (cmpt_exp_tbl_entries_start C_cmpt)
  in

  mem = mk_initial_memory secrets
  (* instantiating main *)
  ∧ (cmpt_imports main_cmpt) = cmdc_conf_main_imports B_f C_g
  ∧ (cmpt_code main_cmpt) = cmdc_conf_main_code
  ∧ (cmpt_exp_tbl_entries main_cmpt) = []

  (* instantiating B *)
  ∧ (cmpt_imports B_cmpt) = [switcher_entry]
  ∧ Forall is_z (cmpt_code B_cmpt) (* only instructions *)
  ∧ Forall (is_initial_data_word B_cmpt) (cmpt_data B_cmpt)
  ∧ (cmpt_exp_tbl_entries B_cmpt) = [WInt (encode_entry_point cmdc_conf_B_f_args offset_B_f)]

  (* instantiating C *)
  ∧ (cmpt_imports C_cmpt) = [switcher_entry]
  ∧ Forall is_z (cmpt_code C_cmpt) (* only instructions *)
  ∧ Forall (is_initial_data_word C_cmpt) (cmpt_data C_cmpt)
  ∧ (cmpt_exp_tbl_entries C_cmpt) = [WInt (encode_entry_point cmdc_conf_C_g_args offset_C_g)]
.

(** We derive some disjointness properties *)
Lemma mk_initial_cmpt_C_disjoint `{Layout: cmdc_conf_memory_layout} (secrets : Z * Z) :
  mk_initial_switcher switcher_cmpt ∪ mk_initial_cmpt (main_cmpt_secrets secrets) ∪ mk_initial_cmpt B_cmpt
    ##ₘ mk_initial_cmpt C_cmpt.
Proof.
  pose proof cmpts_disjoints as (_ & HmainC & HBC).
  pose proof switcher_cmpt_disjoints as (_ & _ & HswitcherC).
  do 2 rewrite map_disjoint_union_l.
  repeat split.
  - symmetry; apply disjoint_switcher_cmpts_mkinitial; done.
  - apply disjoint_cmpts_mkinitial; exact HmainC.
  - apply disjoint_cmpts_mkinitial; done.
Qed.

Lemma mk_initial_cmpt_B_disjoint `{Layout: cmdc_conf_memory_layout} (secrets : Z * Z) :
  mk_initial_switcher switcher_cmpt ∪ mk_initial_cmpt (main_cmpt_secrets secrets)
    ##ₘ mk_initial_cmpt B_cmpt.
Proof.
  pose proof cmpts_disjoints as (HmainB & _ & _).
  pose proof switcher_cmpt_disjoints as (_ & HswitcherB & _).
  rewrite map_disjoint_union_l.
  split.
  - symmetry; apply disjoint_switcher_cmpts_mkinitial; done.
  - apply disjoint_cmpts_mkinitial; exact HmainB.
Qed.

Lemma mk_initial_cmpt_main_disjoint `{Layout: cmdc_conf_memory_layout} (secrets : Z * Z) :
  mk_initial_switcher switcher_cmpt ##ₘ mk_initial_cmpt (main_cmpt_secrets secrets).
Proof.
  pose proof switcher_cmpt_disjoints as (HswitcherMain & _ & _).
  symmetry; apply disjoint_switcher_cmpts_mkinitial; exact HswitcherMain.
Qed.

(** One direction of the adequacy theorem: if the run with [secrets1]
    halts, then the run with [secrets2] halts. The binary specification is
    used with the run with [secrets1] as implementation, and the run with
    [secrets2] as specification. *)
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
  Context {na_inv_preg: na_invGpreS Σ}.
  Context {sts_preg: STS_preG Addr region_type Σ}.
  Context {cstack_preg: CSTACK_preG Σ }.
  Context {relpreg: relGpreS Σ}.
  Context {spec_preg: specGpreS Σ}.
  Context `{MP: MachineParameters}.
  Context { HCNames : CNames = (list_to_set [B;C]) }.
  Context { HCNamesNoDup : NoDup [B;C] }.

  Definition switcherN : namespace := nroot .@ "cmdc_conf" .@ "switcher".

  Lemma cmdc_conf_adequacy_one_sided `{Layout: cmdc_conf_memory_layout}
    (reg : Reg) (sreg : SReg) (m1 m2 : Mem) (secrets1 secrets2 : Z * Z) :
    is_initial_registers reg →
    is_initial_sregisters sreg →
    is_initial_memory secrets1 m1 →
    is_initial_memory secrets2 m2 →
    halts (reg, sreg, m1) → halts (reg, sreg, m2).
  Proof.
    intros Hreg Hsreg Hm1 Hm2.
    destruct Hm1 as (Hm1
                    & main_imports & main_code & main_exp_tbl
                    & B_imports & B_code & B_data & B_exp_tbl
                    & C_imports & C_code & C_data & C_exp_tbl
                   ).
    destruct Hm2 as (Hm2 & _).
    subst m1 m2.
    destruct secrets1 as [secret_b1 secret_c1].
    destruct secrets2 as [secret_b2 secret_c2].
    pose proof cmpts_disjoints as (HmainB & HmainC & HBC).
    pose proof switcher_cmpt_disjoints as (Hsw_main & Hsw_B & Hsw_C).

    (* 1 - We give a name to the exported entry points for which we want
       to know the number of arguments. *)
    set (B_f := cmpt_export B_cmpt (cmpt_exp_tbl_entries_start B_cmpt)).
    set (C_g := cmpt_export C_cmpt (cmpt_exp_tbl_entries_start C_cmpt)).

    (* 2 - We use the adequacy of the binary model, which initialises the
       program logic resources of both runs, and the entry points. *)
    apply (binary_adequacy Σ
             (exported_entries (ot_switcher switcher_cmpt)
                [(B_f, cmdc_conf_B_f_args); (C_g, cmdc_conf_C_g_args)])).
    iIntros (ceriseg specg) "#Hspec Hj Hna Hreg Hsreg Hmem Hreg_s Hsreg_s Hmem_s Hentries".
    iDestruct (entries_split with "Hentries")
      as "([#Hentry_Bf #Hentry_Bf'] & [#Hentry_Cg #Hentry_Cg'] & _)".
    { cbn; apply NoDup_cons; split; last apply NoDup_singleton.
      rewrite list_elem_of_singleton.
      by apply cmpt_export_disjoint.
    }
    { by repeat constructor. }

    (* 3 - We initialise the seal store, the call stacks of both runs, and
       the world interpretations of B and C *)
    iMod (initialise_world_binary [B;C] {[ ot_switcher switcher_cmpt ]})
      as (seal_storeg relg stsg cstackg cstackg_spec)
           "(Hseal_store & Hcstk_full & Hcstk_frag & Hcstk_full_spec & Hcstk_frag_spec
            & [Hworld_interp_B [Hworld_interp_C _]])";
      [done | exact HCNamesNoDup |].

    (* 4 - Get initial sregister mtdc, in both runs *)
    iDestruct (big_sepM_lookup with "Hsreg") as "Hmtdc"; first exact Hsreg.
    iDestruct (big_sepM_lookup with "Hsreg_s") as "Hsmtdc"; first exact Hsreg.

    (* 5 - Separate all compartments *)
    rewrite /mk_initial_memory.
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hcmpt_C]".
    { eapply mk_initial_cmpt_C_disjoint. }
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hcmpt_B]".
    { eapply mk_initial_cmpt_B_disjoint. }
    iDestruct (big_sepM_union with "Hmem") as "[Hcmpt_switcher Hcmpt_main]".
    { eapply mk_initial_cmpt_main_disjoint. }
    iDestruct (big_sepM_union with "Hmem_s") as "[Hmem_s Hscmpt_C]".
    { eapply mk_initial_cmpt_C_disjoint. }
    iDestruct (big_sepM_union with "Hmem_s") as "[Hmem_s Hscmpt_B]".
    { eapply mk_initial_cmpt_B_disjoint. }
    iDestruct (big_sepM_union with "Hmem_s") as "[Hscmpt_switcher Hscmpt_main]".
    { eapply mk_initial_cmpt_main_disjoint. }
    iDestruct (big_sepM_sep_2 with "Hcmpt_switcher Hscmpt_switcher") as "Hcmpt_switcher".
    iDestruct (big_sepM_sep_2 with "Hcmpt_B Hscmpt_B") as "Hcmpt_B".
    iDestruct (big_sepM_sep_2 with "Hcmpt_C Hscmpt_C") as "Hcmpt_C".

    (* 5.1 Switcher compartment *)
    iEval (rewrite big_sepS_singleton) in "Hseal_store".
    iMod ( initialise_switcher_compartment_binary (Σ := Σ) _ switcherN
             with "Hcmpt_switcher Hseal_store Hcstk_full Hcstk_full_spec Hmtdc Hsmtdc" )
      as "(#Hsealed_pred_ot_switcher & #Hswitcher & Hstack & Hsstack)".

    (* 5.2 CMPT B *)
    iMod (initialise_adversary_compartment_binary (Σ := Σ) _ B with "Hcmpt_B")
      as "(HB_imports & HB_code & HB_data & #HB_etbl_pcc & #HB_etbl_cgp & #HB_etbl_entries)".

    (* 5.3 CMPT C *)
    iMod (initialise_adversary_compartment_binary (Σ := Σ) _ C with "Hcmpt_C")
      as "(HC_imports & HC_code & HC_data & #HC_etbl_pcc & #HC_etbl_cgp & #HC_etbl_entries)".

    (* 5.4 CMPT MAIN, with different secrets in each run *)
    iDestruct (initialise_compartment_with_data_gen with "Hcmpt_main")
      as "(Hmain_imports & Hmain_code & Hmain_data)".
    iDestruct (initialise_compartment_with_data_gen with "Hscmpt_main")
      as "(Hsmain_imports & Hsmain_code & Hsmain_data)".
    iDestruct (cmpt_code_codefrag with "Hmain_code") as "Hmain_code".
    iDestruct (cmpt_code_spec_codefrag with "Hsmain_code") as "Hsmain_code".
    rewrite main_imports main_code.

    (* 6 - Initialise the worlds of B and C: their compartments become
       permanent, and the stack is allocated as revoked, because we keep
       its points-to predicates. *)
    iMod (initialise_adversary_world_revoked_binary _ switcher_cmpt _ B
           with "HB_imports HB_code HB_data [] Hworld_interp_B")
      as "(Hworld_interp_B & #Hinterp_pcc_B & #Hinterp_cgp_B & #Hrevoked_stack_B)"; auto.
    { rewrite B_imports.
      iIntros "_".
      iSplit; last done.
      iSplit; [| iIntros (???) "!> _" ] ; iApply interp_switcher_call ; done.
    }
    iMod (initialise_adversary_world_revoked_binary _ switcher_cmpt _ C
           with "HC_imports HC_code HC_data [] Hworld_interp_C")
      as "(Hworld_interp_C & #Hinterp_pcc_C & #Hinterp_cgp_C & #Hrevoked_stack_C)"; auto.
    { rewrite C_imports.
      iIntros "_".
      iSplit; last done.
      iSplit; [| iIntros (???) "!> _" ] ; iApply interp_switcher_call ; done.
    }

    (* 7 - The exported entry points of B and C are safe to share *)
    iAssert (interp (adv_world_revoked (∅, (∅, ∅)) switcher_cmpt B_cmpt) B
               (WSealed (ot_switcher switcher_cmpt) B_f, WSealed (ot_switcher switcher_cmpt) B_f))
      as "#Hinterp_B".
    { iApply (adversary_export_interp_binary _ _ _ _ _ 0 cmdc_conf_B_f_args offset_B_f
               with "Hswitcher Hsealed_pred_ot_switcher HB_etbl_pcc HB_etbl_cgp HB_etbl_entries
                     Hinterp_pcc_B Hinterp_cgp_B Hentry_Bf Hentry_Bf'").
      - by rewrite B_exp_tbl.
      - pose proof (cmpt_exp_tbl_entries_size B_cmpt); solve_addr.
      - rewrite /cmdc_conf_B_f_args; lia.
    }
    iAssert (interp (adv_world_revoked (∅, (∅, ∅)) switcher_cmpt C_cmpt) C
               (WSealed (ot_switcher switcher_cmpt) C_g, WSealed (ot_switcher switcher_cmpt) C_g))
      as "#Hinterp_C".
    { iApply (adversary_export_interp_binary _ _ _ _ _ 0 cmdc_conf_C_g_args offset_C_g
               with "Hswitcher Hsealed_pred_ot_switcher HC_etbl_pcc HC_etbl_cgp HC_etbl_entries
                     Hinterp_pcc_C Hinterp_cgp_C Hentry_Cg Hentry_Cg'").
      - by rewrite C_exp_tbl.
      - pose proof (cmpt_exp_tbl_entries_size C_cmpt); solve_addr.
      - rewrite /cmdc_conf_C_g_args; lia.
    }

    (* 8 - Extract registers, in both runs *)
    iDestruct (initial_registers_split_binary with "Hreg Hreg_s")
      as (rmap) "(HPC & HsPC & Hcgp & Hscgp & Hcsp & Hscsp & Hregs & %Hrmap_dom)";
      first exact Hreg.

    (* 9 - The initial continuation is empty *)
    iAssert (interp_continuation [] [] []) as "HK".
    { by rewrite /interp_continuation /interp_cont /=. }

    (* 10 - The side conditions of the specification *)
    pose proof (main_code_size_obligations _ _ _ main_imports main_code)
      as (HsubBounds & Himports_contiguous).
    pose proof main_data_size as Hmain_data_size; cbn in Hmain_data_size.
    assert (cmpt_b_cgp main_cmpt ∉ dom (std (adv_world_revoked (∅, (∅, ∅)) switcher_cmpt B_cmpt)))
      as Hcgp_b.
    { apply (main_cgp_not_in_adv_world _ _ main_cmpt); [done | done | | ].
      - rewrite /= dom_empty_L; set_solver+.
      - rewrite elem_of_finz_seq_between; solve_addr+Hmain_data_size.
    }
    assert ((cmpt_b_cgp main_cmpt ^+ 1)%a
              ∉ dom (std (adv_world_revoked (∅, (∅, ∅)) switcher_cmpt C_cmpt)))
      as Hcgp_c.
    { apply (main_cgp_not_in_adv_world _ _ main_cmpt); [done | done | | ].
      - rewrite /= dom_empty_L; set_solver+.
      - rewrite elem_of_finz_seq_between; solve_addr+Hmain_data_size.
    }

    (* 11 - We can apply the specification! *)
    iModIntro.
    iApply (cmdc_spec (B := B) (C := C)
              (cmpt_b_pcc main_cmpt) (cmpt_e_pcc main_cmpt) (cmpt_a_code main_cmpt)
              (cmpt_b_cgp main_cmpt) (cmpt_e_cgp main_cmpt)
              (b_stack switcher_cmpt) (e_stack switcher_cmpt)
              _ B_f C_g _ _ [] [] [] _ _
              secret_b1 secret_c1 secret_b2 secret_c2 switcherN
              Hrmap_dom HsubBounds main_data_size Himports_contiguous Hcgp_b Hcgp_c
              (adv_world_revoked_stack _ _ _) (adv_world_revoked_stack _ _ _)
             with "[$Hswitcher $Hspec $Hna $Hj
                    $HPC $HsPC $Hcgp $Hscgp $Hcsp $Hscsp $Hregs
                    $Hmain_imports $Hsmain_imports $Hmain_code $Hsmain_code $Hmain_data $Hsmain_data
                    $Hstack $Hsstack $Hworld_interp_B $Hworld_interp_C
                    $HK $Hcstk_frag $Hcstk_frag_spec
                    $Hinterp_B $Hinterp_C $Hentry_Bf $Hentry_Cg
                    $Hrevoked_stack_B $Hrevoked_stack_C]").
  Qed.
End Adequacy.


(** We initialise concretely the compartments name typeclass. *)

Inductive CmptNames_CMDC := | B | C.
Local Instance CmptNames_CMDC_eq_dec : EqDecision CmptNames_CMDC.
Proof. intros C C'; destruct C,C'; solve_decision. Qed.
Local Instance CmptNames_CMDC_finite : finite.Finite CmptNames_CMDC.
Proof.
  refine {| finite.enum := [B; C] |}.
  + constructor; [ by rewrite list_elem_of_singleton | apply NoDup_singleton ].
  + intros [|]; [ left | right; left ].
Defined.

Local Program Instance CmptNames_CMDC_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_CMDC; |}.

(** END-TO-END THEOREM *)
Theorem cmdc_conf_adequacy `{Layout: cmdc_conf_memory_layout}
  (reg : Reg) (sreg : SReg) (m1 m2 : Mem) (secrets1 secrets2 : Z * Z) :
  is_initial_registers reg →
  is_initial_sregisters sreg →
  is_initial_memory secrets1 m1 →
  is_initial_memory secrets2 m2 →
  (∃ es c, rtc erased_step ([Seq (Instr Executable)], (reg, sreg, m1)) (Seq (Instr Halted) :: es, c)) ↔
  (∃ es c, rtc erased_step ([Seq (Instr Executable)], (reg, sreg, m2)) (Seq (Instr Halted) :: es, c)).
Proof.
  intros Hreg Hsreg Hm1 Hm2.
  set ( cnames := CmptNames_CMDC_CmptNameG ).
  set (Σ := #[invΣ
              ; gen_heapΣ Addr Word; gen_heapΣ RegName Word; gen_heapΣ SRegName Word
              ; entryPreΣ ; CSTACK_preΣ
              ; na_invΣ; sealStorePreΣ
              ; STS_preΣ Addr region_type ; relPreΣ
              ; savedPredΣ (WorldT * CmptName * (Word * Word))
              ; specΣ
      ]).
  assert (NoDup [B;C]) as HNoDup.
  { apply NoDup_cons; split ; [set_solver | apply NoDup_singleton]. }
  apply (halts_equiv (reg, sreg, m1) (reg, sreg, m2)).
  - eapply (@cmdc_conf_adequacy_one_sided Σ cnames B C); eauto; try typeclasses eauto.
  - eapply (@cmdc_conf_adequacy_one_sided Σ cnames B C); eauto; try typeclasses eauto.
Qed.
