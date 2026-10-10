From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import adequacy.
From iris.base_logic Require Import invariants.
From griotte Require Import sts_multiple_updates.
From griotte Require Import logrel_binary interp_weakening_binary monotone_binary.
From griotte Require Import region_invariants_revocation_binary region_invariants_allocation_binary.
From griotte Require Import world_interp_allocation_compartments_binary stack_world_resources_binary.
From griotte Require Import switcher_preamble_binary interp_switcher_call_binary interp_switcher_return_binary.
From griotte Require Import switcher_adequacy_binary.
From griotte Require Import stack_secret_binary stack_secret_spec_binary.
From griotte Require Import mkregion_helpers disjoint_regions_tactics.
From griotte Require Import adequacy_helpers_binary compartment_layout adequacy_common_binary.
From griotte Require Import contextual_equivalence_binary.


(** * Adequacy of the stack confidentiality example

    The memory layout contains:
    - the switcher compartment;
    - the trusted compartment [main], whose private data is the secret;
    - the adversary compartment [B].

    The two runs start from the same registers, and from memories that only
    differ in the secret of [main]. They either both halt, or both do not
    halt. *)
Class stack_secret_memory_layout `{MP: MachineParameters} := {

    (* switcher *)
    switcher_cmpt : cmptSwitcher;

    (* main compartment, its data region holds the secret *)
    main_cmpt : cmpt ;
    main_data_size :
    (cmpt_b_cgp main_cmpt + length (stack_secret_main_data 0))%a = Some (cmpt_e_cgp main_cmpt);

    (* adv compartment B *)
    B_cmpt : cmpt ;
    offset_B_f : nat;

    (* the stack has room for the frame word of main, the four words spilled
       by the switcher, and the stale copy of the secret *)
    stack_size_secret :
    (b_stack switcher_cmpt ^+ 5 < e_stack switcher_cmpt)%a;

    (* disjointness *)
    cmpts_disjoints : main_cmpt ## B_cmpt ;

    switcher_cmpt_disjoints :
    switcher_cmpt_disjoint main_cmpt switcher_cmpt
    ∧ switcher_cmpt_disjoint B_cmpt switcher_cmpt ;
  }.

(** We instantiate the switcher layout with the memory layout. *)
Local Instance memory_layout_switcherLayout `{stack_secret_memory_layout} : switcherLayout.
Proof.
  exact (cmptSwitcher_switcherLayout switcher_cmpt).
Defined.

Local Instance memory_layout_switcherLayoutWf `{stack_secret_memory_layout} : switcherLayoutWf :=
  cmptSwitcher_switcherLayoutWf switcher_cmpt.

(** The main compartment, holding [secret] in its data region. *)
Definition main_cmpt_secret `{stack_secret_memory_layout} (secret : Z) : cmpt :=
  cmpt_with_data main_cmpt (stack_secret_main_data secret) main_data_size.

Definition mk_initial_memory `{stack_secret_memory_layout} (secret : Z) : Mem :=
  mk_initial_switcher switcher_cmpt ∪
    mk_initial_cmpt (main_cmpt_secret secret) ∪
    mk_initial_cmpt B_cmpt.

(** We describe the initial register file, the same in both runs. *)
Definition is_initial_registers `{stack_secret_memory_layout} :=
  is_initial_registers_of switcher_cmpt main_cmpt.

(** We describe the initial sregister file, ie., mtdc,
    which contains the trusted stack capability. *)
Definition is_initial_sregisters `{stack_secret_memory_layout} :=
  is_initial_sregisters_of switcher_cmpt.

(** We describe the initial memory, for a given secret. *)
Definition is_initial_memory `{stack_secret_memory_layout} (secret : Z) (mem: Mem) :=
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

  mem = mk_initial_memory secret
  (* instantiating main *)
  ∧ (cmpt_imports main_cmpt) = stack_secret_main_imports B_f
  ∧ (cmpt_code main_cmpt) = stack_secret_main_code
  ∧ (cmpt_exp_tbl_entries main_cmpt) = []

  (* instantiating B *)
  ∧ (cmpt_imports B_cmpt) = [switcher_entry]
  ∧ Forall is_z (cmpt_code B_cmpt) (* only instructions *)
  ∧ Forall (is_initial_data_word B_cmpt) (cmpt_data B_cmpt)
  ∧ (cmpt_exp_tbl_entries B_cmpt) = [WInt (encode_entry_point stack_secret_B_f_args offset_B_f)]
.

(** We derive some disjointness properties *)
Lemma mk_initial_cmpt_B_disjoint `{Layout: stack_secret_memory_layout} (secret : Z) :
  mk_initial_switcher switcher_cmpt ∪ mk_initial_cmpt (main_cmpt_secret secret)
    ##ₘ mk_initial_cmpt B_cmpt.
Proof.
  pose proof cmpts_disjoints as HmainB.
  pose proof switcher_cmpt_disjoints as (_ & HswitcherB).
  rewrite map_disjoint_union_l.
  split.
  - symmetry; apply disjoint_switcher_cmpts_mkinitial; done.
  - apply disjoint_cmpts_mkinitial; exact HmainB.
Qed.

Lemma mk_initial_cmpt_main_disjoint `{Layout: stack_secret_memory_layout} (secret : Z) :
  mk_initial_switcher switcher_cmpt ##ₘ mk_initial_cmpt (main_cmpt_secret secret).
Proof.
  pose proof switcher_cmpt_disjoints as (HswitcherMain & _).
  symmetry; apply disjoint_switcher_cmpts_mkinitial; exact HswitcherMain.
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

  Definition switcherN : namespace := nroot .@ "stack_secret" .@ "switcher".

  Lemma stack_secret_adequacy_one_sided `{Layout: stack_secret_memory_layout}
    (reg : Reg) (sreg : SReg) (m1 m2 : Mem) (secret1 secret2 : Z) :
    is_initial_registers reg →
    is_initial_sregisters sreg →
    is_initial_memory secret1 m1 →
    is_initial_memory secret2 m2 →
    halts (reg, sreg, m1) → halts (reg, sreg, m2).
  Proof.
    intros Hreg Hsreg Hm1 Hm2.
    destruct Hm1 as (Hm1 & main_imports & main_code & main_exp_tbl
                     & B_imports & B_code & B_data & B_exp_tbl).
    destruct Hm2 as (Hm2 & _).
    subst m1 m2.
    pose proof cmpts_disjoints as HmainB.
    pose proof switcher_cmpt_disjoints as (Hsw_main & Hsw_B).

    (* 1 - We give a name to the exported entry point for which we want to
       know the number of arguments. *)
    set (B_f := cmpt_export B_cmpt (cmpt_exp_tbl_entries_start B_cmpt)).

    (* 2 - We use the adequacy of the binary model, which initialises the
       program logic resources of both runs, and the entry points. *)
    apply (binary_adequacy Σ
             (exported_entries (ot_switcher switcher_cmpt) [(B_f, stack_secret_B_f_args)])).
    iIntros (ceriseg specg) "#Hspec Hj Hna Hreg Hsreg Hmem Hreg_s Hsreg_s Hmem_s Hentries".
    iDestruct (entries_split with "Hentries") as "([#Hentry_Bf #Hentry_Bf'] & _)".
    { apply NoDup_singleton. }
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
    iDestruct (big_sepM_union with "Hmem") as "[Hcmpt_switcher Hcmpt_main]".
    { eapply mk_initial_cmpt_main_disjoint. }
    iDestruct (big_sepM_union with "Hmem_s") as "[Hmem_s Hscmpt_B]".
    { eapply mk_initial_cmpt_B_disjoint. }
    iDestruct (big_sepM_union with "Hmem_s") as "[Hscmpt_switcher Hscmpt_main]".
    { eapply mk_initial_cmpt_main_disjoint. }
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

    (* 5.3 CMPT MAIN, with a different secret in each run *)
    iDestruct (initialise_compartment_with_data_gen with "Hcmpt_main")
      as "(Hmain_imports & Hmain_code & Hmain_data)".
    iDestruct (initialise_compartment_with_data_gen with "Hscmpt_main")
      as "(Hsmain_imports & Hsmain_code & Hsmain_data)".
    iDestruct (cmpt_code_codefrag with "Hmain_code") as "Hmain_code".
    iDestruct (cmpt_code_spec_codefrag with "Hsmain_code") as "Hsmain_code".
    rewrite main_imports main_code.

    (* 6 - Initialise the world of B: its compartment becomes permanent, and
       the stack is allocated as revoked, because we keep its points-to
       predicates. *)
    iMod (initialise_adversary_world_revoked_binary _ switcher_cmpt _ B
           with "HB_imports HB_code HB_data [] Hworld_interp_B")
      as "(Hworld_interp_B & #Hinterp_pcc_B & #Hinterp_cgp_B & #Hrevoked_stack_B)"; auto.
    { rewrite B_imports.
      iIntros "_".
      iSplit; last done.
      iSplit; [| iIntros (???) "!> _" ] ; iApply interp_switcher_call ; done.
    }

    (* 7 - The exported entry point of B is safe to share *)
    iAssert (interp (adv_world_revoked (∅, (∅, ∅)) switcher_cmpt B_cmpt) B
               (WSealed (ot_switcher switcher_cmpt) B_f, WSealed (ot_switcher switcher_cmpt) B_f))
      as "#Hinterp_B".
    { iApply (adversary_export_interp_binary _ _ _ _ _ 0 stack_secret_B_f_args offset_B_f
               with "Hswitcher Hsealed_pred_ot_switcher HB_etbl_pcc HB_etbl_cgp HB_etbl_entries
                     Hinterp_pcc_B Hinterp_cgp_B Hentry_Bf Hentry_Bf'").
      - by rewrite B_exp_tbl.
      - pose proof (cmpt_exp_tbl_entries_size B_cmpt); solve_addr.
      - rewrite /stack_secret_B_f_args; lia.
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

    (* 11 - We can apply the specification! *)
    iModIntro.
    iApply (stack_secret_spec (B := B)
              (cmpt_b_pcc main_cmpt) (cmpt_e_pcc main_cmpt) (cmpt_a_code main_cmpt)
              (cmpt_b_cgp main_cmpt) (cmpt_e_cgp main_cmpt)
              (b_stack switcher_cmpt) (e_stack switcher_cmpt)
              _ B_f _ [] [] [] _ _ secret1 secret2 switcherN
              Hrmap_dom HsubBounds main_data_size Himports_contiguous stack_size_secret
              (adv_world_revoked_stack _ _ _)
             with "[$Hswitcher $Hspec $Hna $Hj
                    $HPC $HsPC $Hcgp $Hscgp $Hcsp $Hscsp $Hregs
                    $Hmain_imports $Hsmain_imports $Hmain_code $Hsmain_code $Hmain_data $Hsmain_data
                    $Hstack $Hsstack $Hworld_interp_B $HK $Hcstk_frag $Hcstk_frag_spec
                    $Hinterp_B $Hentry_Bf $Hrevoked_stack_B]").
  Qed.
End Adequacy.


(** We initialise concretely the compartments name typeclass. *)

Inductive CmptNames_SS := | B.
Local Instance CmptNames_SS_eq_dec : EqDecision CmptNames_SS.
Proof. intros C C'; destruct C,C'; solve_decision. Qed.
Local Instance CmptNames_SS_finite : finite.Finite CmptNames_SS.
Proof.
  refine {| finite.enum := [B] |}.
  + apply NoDup_singleton.
  + intros []; left.
Defined.

Local Program Instance CmptNames_SS_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_SS; |}.

(** END-TO-END THEOREM *)
Theorem stack_secret_adequacy `{Layout: stack_secret_memory_layout}
  (reg : Reg) (sreg : SReg) (m1 m2 : Mem) (secret1 secret2 : Z) :
  is_initial_registers reg →
  is_initial_sregisters sreg →
  is_initial_memory secret1 m1 →
  is_initial_memory secret2 m2 →
  (∃ es c, rtc erased_step ([Seq (Instr Executable)], (reg, sreg, m1)) (Seq (Instr Halted) :: es, c)) ↔
  (∃ es c, rtc erased_step ([Seq (Instr Executable)], (reg, sreg, m2)) (Seq (Instr Halted) :: es, c)).
Proof.
  intros Hreg Hsreg Hm1 Hm2.
  set ( cnames := CmptNames_SS_CmptNameG ).
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
  - eapply (@stack_secret_adequacy_one_sided Σ cnames B); eauto; try typeclasses eauto.
  - eapply (@stack_secret_adequacy_one_sided Σ cnames B); eauto; try typeclasses eauto.
Qed.

(** * Contextual equivalence *)

Section ctx_equiv.
  Context `{MP: MachineParameters}.

  (** The trusted part, shared by both programs: the switcher, the layout and
      the code of the main compartment, and the size of the stack. *)
  Context (sw : cmptSwitcher) (main : cmpt).
  Context (Hmain_size :
            (cmpt_b_cgp main + length (stack_secret_main_data 0))%a = Some (cmpt_e_cgp main)).
  Context (Hmain_code : cmpt_code main = stack_secret_main_code)
          (Hmain_exports : cmpt_exp_tbl_entries main = [])
          (Hstack_size : (b_stack sw ^+ 5 < e_stack sw)%a).

  #[local] Instance stack_secret_switcherLayout : switcherLayout := cmptSwitcher_switcherLayout sw.

  (** The program is the main compartment, holding [secret] in its data region. *)
  Definition stack_secret_prog (secret : Z) : cmpt :=
    cmpt_with_data main (stack_secret_main_data secret) Hmain_size.

  (** The context is the adversary compartment [B_adv]. It imports the switcher,
      and exports the entry point [B.f] imported by [main]. *)
  #[local] Instance stack_secret_linking : Linking cmpt cmpt := {
    is_context B_adv := is_adv_cmpt [switcher_entry sw] [stack_secret_B_f_args] B_adv;
    link B_adv P σ :=
      let '(reg, sreg, m) := σ in
      P ## B_adv ∧
      switcher_cmpt_disjoint P sw ∧
      switcher_cmpt_disjoint B_adv sw ∧
      cmpt_imports P = stack_secret_main_imports (cmpt_export B_adv (cmpt_exp_tbl_entries_start B_adv)) ∧
      is_initial_registers_of sw P reg ∧
      is_initial_sregisters_of sw sreg ∧
      m = mk_initial_switcher sw ∪ mk_initial_cmpt P ∪ mk_initial_cmpt B_adv
  }.

  (** END-TO-END THEOREM *)
  Theorem stack_secret_ctx_equiv (secret1 secret2 : Z) :
    ctx_equiv (stack_secret_prog secret1) (stack_secret_prog secret2).
  Proof.
    intros B_adv [ [reg1 sreg1] m1] [ [reg2 sreg2] m2] HB Hl1 Hl2.
    destruct HB as (HB_imports & HB_code & HB_data & HB_exports).
    inversion HB_exports as [|? w ? ? (off & ->) Hnil]; subst.
    inversion Hnil; subst.
    destruct Hl1 as (HmainB & Hsw_main & Hsw_B & Himports & Hreg1 & Hsreg1 & ->).
    destruct Hl2 as (_ & _ & _ & _ & Hreg2 & Hsreg2 & ->).
    assert (reg2 = reg1) as ->.
    { by eapply (is_initial_registers_of_unique sw main). }
    assert (sreg2 = sreg1) as ->.
    { by eapply is_initial_sregisters_of_unique. }
    set (Layout :=
           {| switcher_cmpt := sw;
              main_cmpt := main;
              main_data_size := Hmain_size;
              B_cmpt := B_adv;
              offset_B_f := off;
              stack_size_secret := Hstack_size;
              cmpts_disjoints := HmainB;
              switcher_cmpt_disjoints := conj Hsw_main Hsw_B |}).
    rewrite /halt_equiv /halts.
    apply (stack_secret_adequacy (Layout := Layout) _ _ _ _ secret1 secret2); try done.
    all: by repeat split.
  Qed.

End ctx_equiv.
