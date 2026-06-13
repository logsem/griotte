From iris.proofmode Require Import proofmode.
From griotte Require Import logrel interp_weakening monotone.
From griotte Require Import cmdc cmdc_spec.
From griotte Require Import switcher assert_spec logrel.
From griotte Require Import mkregion_helpers.
From griotte Require Import
  region_invariants_revocation region_invariants_allocation world_interp_allocation_compartments.
From iris.program_logic Require Import adequacy.
From iris.base_logic Require Import invariants.
From griotte Require Import disjoint_regions_tactics.
From griotte Require Import switcher_preamble interp_switcher_call interp_switcher_return.
From griotte Require Import compartment_layout switcher_adequacy adequacy_helpers.


(** We define the memory layout typeclass,
    which describes the initial memory layout.

    It contains:
    - the switcher compartment
    - the assert compartment
    - the main compartment
    - the adversaries compartments (B and C for the CMDC)

    And it describes that all the compartments are disjoints from each others. *)
Class memory_layout `{MP: MachineParameters} := {

    (* switcher *)
    switcher_cmpt : cmptSwitcher;

    (* assert *)
    assert_cmpt : cmptAssert;

    (* main compartment *)
    main_cmpt : cmpt ;

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

    assert_cmpt_disjoints :
    assert_cmpt_disjoint main_cmpt assert_cmpt
    ∧ assert_cmpt_disjoint B_cmpt assert_cmpt
    ∧ assert_cmpt_disjoint C_cmpt assert_cmpt ;

    assert_switcher_disjoints :
    assert_switcher_disjoint assert_cmpt switcher_cmpt;
  }.


(** We instantiate the switcher and assert layout with the memory layout. *)
Local Instance memory_layout_switcherLayout `{memory_layout} : switcherLayout.
Proof.
  exact (cmptSwitcher_switcherLayout switcher_cmpt).
Defined.

Local Instance memory_layout_switcherLayoutWf `{memory_layout} : switcherLayoutWf.
Proof.
  pose proof (ot_switcher_size switcher_cmpt).
  pose proof (switcher_size switcher_cmpt).
  pose proof (switcher_call_entry_point switcher_cmpt).
  pose proof (switcher_return_entry_point switcher_cmpt).
  refine (mkSwitcherLayoutWf _ _ _ _ _); cbn in *; auto.
Defined.

Local Instance memory_layout_assertLayout `{memory_layout} : assertLayout.
Proof.
  exact (cmptAssert_assertLayout assert_cmpt).
Defined.

Definition mk_initial_memory `{memory_layout} (mem: Mem) :=
  mk_initial_switcher switcher_cmpt ∪
    mk_initial_assert assert_cmpt ∪
    mk_initial_cmpt main_cmpt ∪
    mk_initial_cmpt B_cmpt ∪
    mk_initial_cmpt C_cmpt.


(** We describe the initial register file. *)
Definition is_initial_registers `{memory_layout} (reg: Reg) :=
  (* pc points-to main's PCC *)
  reg !! PC = Some (WCap RX Global (cmpt_b_pcc main_cmpt) (cmpt_e_pcc main_cmpt) (cmpt_a_code main_cmpt)) ∧
  (* cgp points-to main's CGP *)
  reg !! cgp = Some (WCap RW Global (cmpt_b_cgp main_cmpt) (cmpt_e_cgp main_cmpt) (cmpt_b_cgp main_cmpt)) ∧
  (* csp points-to the stack pointer (defined by the switcher's compartment) *)
  reg !! csp = Some (WCap RWL Local (b_stack switcher_cmpt) (e_stack switcher_cmpt) (b_stack switcher_cmpt)) ∧
  (* all the other registers are initialised at 0 *)
  (∀ (r: RegName), r ∉ ({[ PC; cgp; csp ]} : gset RegName) → reg !! r = Some (WInt 0)).

(** We describe the initial sregister file, ie., mtdc,
    which contains the trusted stack capability. *)
Program Definition is_initial_sregisters `{@memory_layout MP} (sreg : SReg) :=
  sreg !! MTDC = Some (WCap RWL Local
                         (b_trusted_stack switcher_cmpt)
                         (e_trusted_stack switcher_cmpt)
                         (b_trusted_stack switcher_cmpt)).

(** We describe the initial memory. *)
Definition is_initial_memory `{@memory_layout MP} (mem: Mem) :=
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

  mem = mk_initial_memory mem
  (* instantiating main *)
  ∧ (cmpt_imports main_cmpt) = cmdc_main_imports B_f C_g
  ∧ (cmpt_code main_cmpt) = cmdc_main_code
  ∧ (cmpt_data main_cmpt) = cmdc_main_data
  ∧ (cmpt_exp_tbl_entries main_cmpt) = []

  (* instantiating B *)
  ∧ (cmpt_imports B_cmpt) = [switcher_entry]
  ∧ Forall is_z (cmpt_code B_cmpt) (* only instructions *)
  ∧ Forall (is_initial_data_word B_cmpt) (cmpt_data B_cmpt)
  ∧ (cmpt_exp_tbl_entries B_cmpt) = [WInt (encode_entry_point cmdc_B_f_args offset_B_f)]

  (* instantiating C *)
  ∧ (cmpt_imports C_cmpt) = [switcher_entry]
  ∧ Forall is_z (cmpt_code C_cmpt) (* only instructions *)
  ∧ Forall (is_initial_data_word C_cmpt) (cmpt_data C_cmpt)
  ∧ (cmpt_exp_tbl_entries C_cmpt) = [WInt (encode_entry_point cmdc_C_g_args offset_C_g)]
.

(** We derive some disjointness properties *)
Lemma mk_initial_cmpt_C_disjoint `{Layout: @memory_layout MP} (m : Mem) :
  mk_initial_switcher switcher_cmpt ∪ mk_initial_assert assert_cmpt ∪ mk_initial_cmpt main_cmpt ∪ mk_initial_cmpt B_cmpt
    ##ₘ mk_initial_cmpt C_cmpt.
Proof.
  pose proof cmpts_disjoints as (_ & HmainC & HBC).
  pose proof switcher_cmpt_disjoints as (_ & _ & HswitcherC).
  pose proof assert_cmpt_disjoints as (_ & _ & HassertC).
  do 3 rewrite map_disjoint_union_l.
  repeat split.
  - symmetry; apply disjoint_switcher_cmpts_mkinitial; done.
  - symmetry; apply disjoint_assert_cmpts_mkinitial; done.
  - apply disjoint_cmpts_mkinitial; done.
  - apply disjoint_cmpts_mkinitial; done.
Qed.

Lemma mk_initial_cmpt_B_disjoint `{Layout: @memory_layout MP} (m : Mem) :
  mk_initial_switcher switcher_cmpt ∪ mk_initial_assert assert_cmpt ∪ mk_initial_cmpt main_cmpt
    ##ₘ mk_initial_cmpt B_cmpt.
Proof.
  pose proof cmpts_disjoints as (HmainB & _ & _).
  pose proof switcher_cmpt_disjoints as (_ & HswitcherB & _).
  pose proof assert_cmpt_disjoints as (_ & HassertB & _).
  do 2 rewrite map_disjoint_union_l.
  repeat split.
  - symmetry; apply disjoint_switcher_cmpts_mkinitial; done.
  - symmetry; apply disjoint_assert_cmpts_mkinitial; done.
  - apply disjoint_cmpts_mkinitial; done.
Qed.

Lemma mk_initial_cmpt_main_disjoint `{Layout: @memory_layout MP} (m : Mem) :
  mk_initial_switcher switcher_cmpt ∪ mk_initial_assert assert_cmpt
    ##ₘ mk_initial_cmpt main_cmpt.
Proof.
  pose proof switcher_cmpt_disjoints as (HswitcherMain & _ & _).
  pose proof assert_cmpt_disjoints as (HassertMain & _ & _).
  rewrite map_disjoint_union_l.
  repeat split.
  - symmetry; apply disjoint_switcher_cmpts_mkinitial; done.
  - symmetry; apply disjoint_assert_cmpts_mkinitial; done.
Qed.

(** We prove that, in the initial configuration,
    at any step of execution, the assert flag contains 0
    (which means that assert never failed).

    We start by showing an helper lemma [cmdc_adequacy'] that pre-initialises
    Iris typeclasses, as well as the compartment names. *)
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
  Context {relpreg: relGpreS Σ}.
  Context `{MP: MachineParameters}.
  Context { HCNames : CNames = (list_to_set [B;C]) }.
  Context { HCNamesNoDup : NoDup [B;C] }.

  Definition flagN : namespace := nroot .@ "cmdc" .@ "fail_flag".
  Definition switcherN : namespace := nroot .@ "cmdc" .@ "switcher_flag".
  Definition assertN : namespace := nroot .@ "cmdc" .@ "assert_flag".


  Lemma cmdc_adequacy' `{Layout: @memory_layout MP}
    (reg reg': Reg) (sreg sreg': SReg) (m m': Mem)
    (es: list griotte_lang.expr):
    is_initial_registers reg →
    is_initial_sregisters sreg →
    is_initial_memory m →
    rtc erased_step ([Seq (Instr Executable)], (reg, sreg, m)) (es, (reg', sreg', m')) →
    m' !! (flag_assert assert_cmpt) = Some (WInt 0%Z).
  Proof.
    (* 1 - We use the Iris adequacy theorem *)
    intros Hreg Hsreg Hm Hstep.
    pose proof (@wp_invariance Σ griotte_lang _ NotStuck) as WPI. cbn in WPI.
    pose (fun (c: ExecConf) => c.2 !! (flag_assert assert_cmpt) = Some (WInt 0%Z)) as state_is_good.
    specialize (WPI (Seq (Instr Executable)) (reg, sreg, m) es (reg', sreg', m')
                  (state_is_good (reg', sreg', m'))).
    eapply WPI. 2: assumption. intros Hinv κs. clear WPI.

    pose proof Hm as Hm'.
    destruct Hm as (Hm
                    & main_imports & main_code & main_data & main_exp_tbl
                    & B_imports & B_code & B_data & B_exp_tbl
                    & C_imports & C_code & C_data & C_exp_tbl
                   ).

    (* 2 - We give a name to the exported entry points for which we want
       to know the number of arguments. *)
    set (B_f :=
       (WCap RO Global (cmpt_exp_tbl_pcc B_cmpt)
                         (cmpt_exp_tbl_entries_end B_cmpt) (cmpt_exp_tbl_entries_start B_cmpt))
      ).
    set (C_g :=
       (WCap RO Global (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt)
         (cmpt_exp_tbl_entries_start C_cmpt))
      ).

    (* 3 - We initialise the CeriseG program logic resources *)
    (* 3.1 Registers, special registers, and memory *)
    iMod (gen_heap_init (reg:Reg)) as (reg_heapg) "(Hreg_ctx & Hreg & _)".
    iMod (gen_heap_init (sreg:SReg)) as (sreg_heapg) "(Hsreg_ctx & Hsreg & _)".
    iMod (gen_heap_init (m:Mem)) as (mem_heapg) "(Hmem_ctx & Hmem & _)".
    (* 3.2 The seal store, for sealing capabilities.
            We only use the switcher's otype in the CMDC. *)
    iMod (seal_store_init ({[ (ot_switcher switcher_cmpt) ]} : gset _)) as (seal_storeg) "Hseal_store".
    (* 3.3 The entry point resources, to keep track of the number of arguments. *)
    iMod (
       entry_init (
           {[
               (seal_capability B_f (ot_switcher switcher_cmpt)) := cmdc_B_f_args;
               (borrow (seal_capability B_f (ot_switcher switcher_cmpt))) := cmdc_B_f_args;
               (seal_capability C_g (ot_switcher switcher_cmpt)) := cmdc_C_g_args;
               (borrow (seal_capability C_g (ot_switcher switcher_cmpt))) := cmdc_C_g_args
           ]}

         )
      ) as (entry_g) "Hentries".

    (* 3.4 The NA invariant. *)
    iMod (@na_alloc Σ na_invg) as (cerise_nais) "Hna".
    (* 3.5 We instantiate the CeriseG typeclass. *)
    pose cerise_na_invs := Build_cerise_na_invs _ na_invg cerise_nais.
    pose ceriseg := CeriseG Σ Hinv cerise_na_invs mem_heapg reg_heapg sreg_heapg entry_g.

    (* 3.6 The call stack resource, initialised to empty. *)
    iMod (gen_cstack_init []) as (cstackg) "[Hcstk_full Hcstk_frag]".

    (* 4 - We initialise the world interpretations *)
    iMod (world_interp_init) as (relg stsg) "Hworld_interp".
    iDestruct (big_sepS_elements with "Hworld_interp") as "Hworld_interp".
    rewrite HCNames.
    setoid_rewrite elements_list_to_set; auto.
    iDestruct (big_sepL_cons with "Hworld_interp") as "[Hworld_interp_B Hworld_interp_C]".
    iDestruct (big_sepL_cons with "Hworld_interp_C") as "[Hworld_interp_C _]".
    set (W0 := (∅, (∅, ∅))).

    (* We already pose the CMDC specification that we well be using. *)
    pose proof (
        @cmdc_spec_full Σ ceriseg seal_storeg _ _ _ _ _ _ _ _ B C
      ) as Spec.


    (* * * ----- The goal now is to get the initialised resources to match the spec ----- * * *)

    (* 5 - Initialise each individual entry resources *)
    assert (B_f ≠ C_g) as Hneq_entries.
    { pose proof cmpts_disjoints as (_&_&Hdisjoint).
      apply exported_entry_point_disjoint.
      done.
    }

    iDestruct (big_sepM_insert_delete with "Hentries") as "[#Hentry_Bf Hentries]"
    ; repeat (rewrite delete_insert_ne ; last (subst B_f C_g ; intro ; simplify_eq; by rewrite H H0 H1 in Hneq_entries)).
    iDestruct (big_sepM_insert_delete with "Hentries") as "[Hentry_Bf' Hentries]"
    ; repeat (rewrite delete_insert_ne ; last (subst B_f C_g ; intro ; simplify_eq; by rewrite H H0 H1 in Hneq_entries)).
    iDestruct (big_sepM_insert_delete with "Hentries") as "[#Hentry_Cg Hentries]"
    ; repeat (rewrite delete_insert_ne ; last (subst B_f C_g ; intro ; simplify_eq; by rewrite H H0 H1 in Hneq_entries)).
    iDestruct (big_sepM_insert_delete with "Hentries") as "[Hentry_Cg' _]"
    ; repeat (rewrite delete_insert_ne ; last (subst B_f C_g ; intro ; simplify_eq; by rewrite H H0 H1 in Hneq_entries)).
    subst B_f C_g; cbn.
    set (B_f := (SCap RO Global (cmpt_exp_tbl_pcc B_cmpt) (cmpt_exp_tbl_entries_end B_cmpt)
                   (cmpt_exp_tbl_entries_start B_cmpt))).
    set (B_f' := (SCap RO Local (cmpt_exp_tbl_pcc B_cmpt) (cmpt_exp_tbl_entries_end B_cmpt)
                   (cmpt_exp_tbl_entries_start B_cmpt))).
    set (C_g := (SCap RO Global (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt)
                   (cmpt_exp_tbl_entries_start C_cmpt))).
    set (C_g' := (SCap RO Local (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt)
                   (cmpt_exp_tbl_entries_start C_cmpt))).

    (* 6 - Get initial sregister mtdc *)
    iDestruct (big_sepM_lookup with "Hsreg") as "Hmtdc"; eauto.

    (* 7 - Separate all compartments *)
    rewrite {2}Hm.
    rewrite /mk_initial_memory.
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hcmpt_C]".
    { eapply mk_initial_cmpt_C_disjoint; eauto. }
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hcmpt_B]".
    { eapply mk_initial_cmpt_B_disjoint; eauto. }
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hcmpt_main]".
    { eapply mk_initial_cmpt_main_disjoint; eauto. }
    iDestruct (big_sepM_union with "Hmem") as "[Hcmpt_switcher Hcmpt_assert]".
    { pose proof assert_switcher_disjoints; symmetry; eapply disjoint_assert_switcher_mkinitial ; eauto. }

    (* 7.1 Assert compartment *)
    iMod ( initialise_assert_compartment (Σ := Σ) _ assertN flagN with "Hcmpt_assert" )
      as "[#Hassert_flag #Hassert]".

    (* 7.2 Switcher compartment *)
    rewrite big_sepS_singleton.
    iMod ( initialise_switcher_compartment (Σ := Σ) _ switcherN with "Hcmpt_switcher Hseal_store Hcstk_full Hmtdc" )
      as "(#Hsealed_pred_ot_switcher & #Hswitcher & Hstack)".

    (* 7.3 CMPT B *)
    iMod (initialise_adversary_compartment (Σ := Σ) _ B with "Hcmpt_B")
      as "(HB_imports & HB_code & HB_data & #HB_etbl_pcc & #HB_etbl_cgp & #HB_etbl_entries)".
    iEval (rewrite B_exp_tbl) in "HB_etbl_entries".
    rewrite (finz_seq_between_singleton (cmpt_exp_tbl_entries_start B_cmpt)%a).
    2: {
      pose proof (cmpt_exp_tbl_entries_size B_cmpt) as H1.
      rewrite B_exp_tbl in H1; solve_addr+H1.
    }
    iDestruct "HB_etbl_entries" as "/= [ HB_etbl_B_f _ ]".

    (* 7.4 CMPT B *)
    iMod (initialise_adversary_compartment (Σ := Σ) _ C with "Hcmpt_C")
      as "(HC_imports & HC_code & HC_data & #HC_etbl_pcc & #HC_etbl_cgp & #HC_etbl_entries)".
    iEval (rewrite C_exp_tbl) in "HC_etbl_entries".
    rewrite (finz_seq_between_singleton (cmpt_exp_tbl_entries_start C_cmpt)%a).
    2: {
      pose proof (cmpt_exp_tbl_entries_size C_cmpt) as H1.
      rewrite C_exp_tbl in H1; solve_addr+H1.
    }
    iDestruct "HC_etbl_entries" as "/= [ HC_etbl_C_g _ ]".

    (* 7.5 CMPT MAIN *)
    iMod (initialise_compartment (Σ := Σ) with "Hcmpt_main")
      as "(Hmain_imports & Hmain_code & Hmain_data & Hmain_etbl_pcc & Hmain_etbl_cgp & Hmain_etbl_entries)".
    iAssert (
      codefrag (cmpt_a_code main_cmpt) (cmpt_code main_cmpt)
     )%I with "[Hmain_code]" as "Hmain_code".
    { rewrite /codefrag.
      replace (cmpt_a_code main_cmpt ^+ length (cmpt_code main_cmpt))%a
        with (cmpt_e_pcc main_cmpt).
      2: { pose proof (cmpt_code_size main_cmpt) as H ; solve_addr+H. }
      done.
    }
    rewrite main_imports main_code main_data.

    (* 8 Initialise the world for B *)
    (* 8.1 Make the compartment B safe to share *)
    iMod (
       alloc_compartment_interp with "[$HB_imports] [$HB_code] [$HB_data] [] [$Hworld_interp_B]"
      ) as "(Hworld_interp_B & #HB_code & #HB_data & _)"; eauto.
    { apply Forall_true; intros; done. }
    { apply Forall_true; intros; done. }
    { apply Forall_true; intros; done. }
    { rewrite B_imports.
      iIntros "_".
      iSplit; last done.
      iSplit; [| iIntros (???) "!> _" ] ; iApply interp_switcher_call ; done.
    }

    assert (
        Forall
          (λ k : finz MemNum, std (std_update_compartment (∅, (∅, ∅)) B_cmpt) !! k = None)
          (finz.seq_between (b_stack switcher_cmpt) (e_stack switcher_cmpt))
      ) as Hstack_disjoint_B.
    { apply Forall_forall; intros a Ha; cbn.
      pose proof switcher_cmpt_disjoints as (_ & [Hb _]).
      eapply switcher_cmpt_disjoint_std_update_compartment; eauto.
    }

    (* 8.2 Allocate the stack in the world,
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

    (* 9 - Derive that PCC, CGP and entry points are safe to share in the initial world.
     It holds because interp is monotone with future world. *)
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
               (WCap RX Global (cmpt_b_pcc B_cmpt) (cmpt_e_pcc B_cmpt) (cmpt_b_pcc B_cmpt)%a)
            )%I as "#Hinterp_pcc_B".
    { iApply interp_monotone_nl; eauto. }

    iAssert (interp Winit_B B
               (WCap RW Global (cmpt_b_cgp B_cmpt) (cmpt_e_cgp B_cmpt) (cmpt_b_cgp B_cmpt)%a)
            )%I as "#Hinterp_cgp_B".
    { iApply interp_monotone_nl; eauto. }

    iAssert ( interp Winit_B B (WSealed (ot_switcher switcher_cmpt) B_f)) with
      "[HB_code HB_data Hentry_Bf']" as "#Hinterp_B".
    { iApply (ot_switcher_interp_entry _ _ _ _ cmdc_B_f_args offset_B_f); eauto
      ; last (rewrite /cmdc_B_f_args; lia).
      pose proof (cmpt_exp_tbl_entries_size B_cmpt) as H1.
      pose proof (cmpt_exp_tbl_entries_size B_cmpt) as H2.
      rewrite B_exp_tbl in H2.
      solve_addr+H1 H2.
    }

    (* Bonus for CMDC - We already derive the revoked stack resources  *)
    assert ( revoked_addresses Winit_B ( finz.seq_between (b_stack switcher_cmpt) (e_stack switcher_cmpt) ) ) as Hrevoked_stack_B.
    { subst Winit_B.
      rewrite /revoked_addresses Forall_forall.
      intros a Ha.
      by apply std_sta_update_multiple_lookup_in_i.
    }
    iDestruct ( StackWorldResources_from_rel_stack with "Hrel_stk_B" ) as "Hrevoked_stack_B"; eauto.

    iClear "HB_etbl_pcc HB_etbl_cgp HB_code HB_data Hinterp_pcc_B Hinterp_cgp_B".


    (* 9 Initialise the world for B *)
    (* 9.1 Make the compartment C safe to share *)
    iMod (
       alloc_compartment_interp with "[$HC_imports] [$HC_code] [$HC_data] [] [$Hworld_interp_C]"
      ) as "(Hworld_interp_C & #HC_code & #HC_data & _)"; eauto.
    { apply Forall_true; intros; done. }
    { apply Forall_true; intros; done. }
    { apply Forall_true; intros; done. }
    { rewrite C_imports.
      iIntros "_".
      iSplit; last done.
      iSplit; [| iIntros (???) "!> _" ] ; iApply interp_switcher_call ; done.
    }

    assert (
        Forall
          (λ k : finz MemNum, (std_update_compartment (∅, (∅, ∅)) C_cmpt).1 !! k = None)
          (finz.seq_between (b_stack switcher_cmpt) (e_stack switcher_cmpt))
      ) as Hstack_disjoint_C.
    { apply Forall_forall; intros a Ha; cbn.
      pose proof switcher_cmpt_disjoints as (_ & [_ Hc]).
      eapply switcher_cmpt_disjoint_std_update_compartment; eauto.
    }

    (* 9.2 Allocate the stack in the world,
       with Revoked state because we need to keep the points-to predicates *)
    iMod ( world_interp_extend_revoked_sepL2 _ _
             (finz.seq_between (b_stack switcher_cmpt) (e_stack switcher_cmpt))
             RWL interpC
           with "[$Hworld_interp_C]")
           as "(Hworld_interp_C & Hrel_stk_C)".
    { eapply Hstack_disjoint_C. }

    (* The world for C is now ready initial world. *)
    match goal with
    | H: _ |- context [  (world_interp ?W C) ] => set (Winit_C := W)
    end.

    (* 10 - Derive that PCC, CGP and entry points are safe to share in the initial world.
     It holds because interp is monotone with future world. *)
    iAssert (interp Winit_C C
               (WCap RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_b_pcc C_cmpt)%a)
            )%I as "#Hinterp_pcc_C".
    { iApply interp_monotone_nl; eauto.
      iPureIntro.
      rewrite /Winit_C.
      apply related_sts_pub_priv_world.
      eapply related_sts_pub_update_multiple.
      eapply Forall_impl; eauto.
      intros a Ha; cbn in *.
      by rewrite not_elem_of_dom.
    }

    iAssert (interp Winit_C C
               (WCap RW Global (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) (cmpt_b_cgp C_cmpt)%a)
            )%I as "#Hinterp_cgp_C".
    { iApply interp_monotone_nl; eauto.
      iPureIntro.
      rewrite /Winit_C.
      apply related_sts_pub_priv_world.
      eapply related_sts_pub_update_multiple.
      eapply Forall_impl; eauto.
      intros a Ha; cbn in *.
      by rewrite not_elem_of_dom.
    }

    iAssert ( interp Winit_C C (WSealed (ot_switcher switcher_cmpt) C_g)) with
      "[HC_code HC_data Hentry_Cg']" as "#Hinterp_C".
    { iApply (ot_switcher_interp_entry _ _ _ _ cmdc_C_g_args offset_C_g); eauto
      ; last (rewrite /cmdc_C_g_args; lia).
      pose proof (cmpt_exp_tbl_entries_size C_cmpt) as H1.
      pose proof (cmpt_exp_tbl_entries_size C_cmpt) as H2.
      rewrite C_exp_tbl in H2.
      solve_addr+H1 H2.
    }

    (* Bonus for CMDC - We already derive the revoked stack resources  *)
    assert ( revoked_addresses Winit_C ( finz.seq_between (b_stack switcher_cmpt) (e_stack switcher_cmpt) ) ) as Hrevoked_stack_C.
    { subst Winit_C.
      rewrite /revoked_addresses Forall_forall.
      intros a Ha.
      by apply std_sta_update_multiple_lookup_in_i.
    }
    iDestruct ( StackWorldResources_from_rel_stack with "Hrel_stk_C" ) as "Hrevoked_stack_C"; eauto.
    iClear "HC_etbl_pcc HC_etbl_cgp HC_code HC_data Hinterp_pcc_C Hinterp_cgp_C".


    (* 11 - Extract registers *)
    destruct Hreg as (HPC & Hcgp & Hcsp & Hreg).
    iDestruct (big_sepM_delete _ _ PC with "Hreg") as "[HPC Hreg]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cgp with "Hreg") as "[Hcgp Hreg]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ csp with "Hreg") as "[Hcsp Hreg]"; first by simplify_map_eq.

    (* 12 - We can apply the specification! *)
    iPoseProof (Spec _ _ _ _ _ _ _
                  _ _ _ _ _
                  [] [] _ (fun _ => True)%I assertN switcherN []
                 with "[ $Hassert $Hswitcher $Hna
                        $Hworld_interp_B $Hworld_interp_C
                        $HPC $Hcgp $Hcsp $Hreg
                        $Hmain_imports $Hmain_code $Hmain_data $Hstack
                        $Hinterp_B $Hinterp_C $Hcstk_frag $Hrevoked_stack_B $Hrevoked_stack_C
                        $Hentry_Bf $Hentry_Cg
                        ]") as "Hspec"; eauto.
    { solve_ndisj. }
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
      apply Hreg.
      clear -n n0 n1; set_solver.
    }
    { intros r Hdom.
     rewrite !dom_delete_L in Hdom.
     destruct (decide (r = PC)); simplify_eq.
     { set_solver+Hdom. }
     destruct (decide (r = cgp)); simplify_eq.
     { set_solver+Hdom. }
     destruct (decide (r = csp)); simplify_eq.
     { set_solver+Hdom. }
     rewrite !lookup_delete_ne //.
     apply Hreg.
     clear -n n0 n1; set_solver.
    }
    { rewrite /SubBounds.
      pose proof (cmpt_import_size main_cmpt) as Hmain_imports.
      pose proof (cmpt_code_size main_cmpt) as Hmain_code.
      rewrite -main_code.
      solve_addr+Hmain_imports Hmain_code.
    }
    { pose proof (cmpt_data_size main_cmpt) as Hmain_data.
      by rewrite -main_data.
    }
    { pose proof (cmpt_import_size main_cmpt) as Hmain_imports.
      by rewrite -Hmain_imports main_imports.
    }
    { subst Winit_B.
      intro Hcontra.
      assert ( cmpt_b_cgp main_cmpt ∈ finz.seq_between (cmpt_b_cgp main_cmpt) (cmpt_e_cgp main_cmpt)
             ) as Hb_cgp_in.
      { pose proof (cmpt_data_size main_cmpt) as H.
        rewrite elem_of_finz_seq_between.
        rewrite main_data in H; cbn.
        solve_addr+H.
      }
      apply elem_of_dom_std_multiple_update in Hcontra.
      clear -Hcontra Hb_cgp_in B_imports.
      destruct Hcontra as [Hcontra|Hcontra].
      - pose proof switcher_cmpt_disjoints as (Hdis&_&_); set_solver.
      - pose proof cmpts_disjoints as (Hdis&_&_).
        apply elem_of_dom_std_multiple_update in Hcontra.
        destruct Hcontra as [Hcontra|Hcontra].
        + assert (cmpt_b_cgp main_cmpt ∈ finz.seq_between (cmpt_b_pcc B_cmpt) (cmpt_e_pcc B_cmpt)).
          { pose proof (cmpt_import_size B_cmpt) as Hsize ; rewrite B_imports in Hsize.
            pose proof (cmpt_code_size B_cmpt).
            rewrite elem_of_finz_seq_between in Hcontra.
            rewrite elem_of_finz_seq_between.
            solve_addr.
          }
          set_solver.
        + apply elem_of_dom_std_multiple_update in Hcontra.
          destruct Hcontra as [Hcontra|Hcontra].
          * set_solver.
          * apply elem_of_dom_std_multiple_update in Hcontra.
            destruct Hcontra as [Hcontra|Hcontra].
            ** assert (cmpt_b_cgp main_cmpt ∈ finz.seq_between (cmpt_b_pcc B_cmpt) (cmpt_e_pcc B_cmpt))
               ; last set_solver.
               rewrite !elem_of_finz_seq_between in Hcontra |- *.
               pose proof (cmpt_import_size B_cmpt) as Hsize ; rewrite B_imports in Hsize.
               solve_addr.
            ** rewrite /= dom_empty_L in Hcontra; set_solver+Hcontra.
    }
    { subst Winit_C.
      intro Hcontra.
      assert ( (cmpt_b_cgp main_cmpt ^+1)%a ∈ finz.seq_between (cmpt_b_cgp main_cmpt) (cmpt_e_cgp main_cmpt)
             ) as Hb_cgp_in.
      { pose proof (cmpt_data_size main_cmpt) as H.
        rewrite elem_of_finz_seq_between.
        rewrite main_data in H; cbn.
        solve_addr+H.
      }
      apply elem_of_dom_std_multiple_update in Hcontra.
      clear -Hcontra Hb_cgp_in C_imports.
      destruct Hcontra as [Hcontra|Hcontra].
      - pose proof switcher_cmpt_disjoints as (Hdis&_&_); set_solver.
      - pose proof cmpts_disjoints as (_&Hdis&_).
        apply elem_of_dom_std_multiple_update in Hcontra.
        destruct Hcontra as [Hcontra|Hcontra].
        + assert ((cmpt_b_cgp main_cmpt ^+ 1)%a ∈ finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt)).
          { pose proof (cmpt_import_size C_cmpt) as Hsize ; rewrite C_imports in Hsize.
            pose proof (cmpt_code_size C_cmpt).
            rewrite elem_of_finz_seq_between in Hcontra.
            rewrite elem_of_finz_seq_between.
            solve_addr.
          }
          set_solver.
        + apply elem_of_dom_std_multiple_update in Hcontra.
          destruct Hcontra as [Hcontra|Hcontra].
          * set_solver.
          * apply elem_of_dom_std_multiple_update in Hcontra.
            destruct Hcontra as [Hcontra|Hcontra].
            ** assert ((cmpt_b_cgp main_cmpt ^+ 1)%a ∈ finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt))
               ; last set_solver.
               rewrite !elem_of_finz_seq_between in Hcontra |- *.
               pose proof (cmpt_import_size C_cmpt) as Hsize ; rewrite C_imports in Hsize.
               solve_addr.
            ** rewrite /= dom_empty_L in Hcontra; set_solver+Hcontra.
    }
    { iNext; iIntros "H". proofmode.wp_end; by iIntros. }

    (* We use the post-condition *)
    iModIntro.
    iExists (fun σ _ _ => ( ((gen_heap_interp σ.1.1) ∗ (gen_heap_interp σ.1.2)) ∗ (gen_heap_interp σ.2)))%I.
    iExists (fun _ => True)%I. cbn. iFrame.

    (* We open the assert invariant,
       which contains the points-to predicate of the assert flag pointing to zero *)
    iIntros "[ [Hreg' Hsreg'] Hmem']". iExists (⊤ ∖ ↑flagN).
    iInv flagN as ">Hflag" "Hclose".
    (* By validity of the heap RA, we can deduce that the memory address,
       in the level of the opsem, is zero *)
    iDestruct (gen_heap_valid with "Hmem' Hflag") as %Hm'_flag.
    iModIntro. iPureIntro. rewrite /state_is_good //=.
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
Theorem cmdc_adequacy `{Layout: memory_layout}
  (reg reg': Reg) (sreg sreg': SReg) (m m': Mem)
  (es: list griotte_lang.expr):
  is_initial_registers reg →
  is_initial_sregisters sreg →
  is_initial_memory m →
  rtc erased_step ([Seq (Instr Executable)], (reg, sreg, m)) (es, (reg', sreg', m')) →
  m' !! (flag_assert assert_cmpt) = Some (WInt 0%Z).
Proof.
  intros ? ? ? ?.
  set ( cnames := CmptNames_CMDC_CmptNameG ).
  set (Σ := #[invΣ
              ; gen_heapΣ Addr Word; gen_heapΣ RegName Word; gen_heapΣ SRegName Word
              ; entryPreΣ ; CSTACK_preΣ
              ; na_invΣ; sealStorePreΣ
              ; STS_preΣ Addr region_type ; relPreΣ
              ; savedPredΣ (((STS_std_states Addr region_type) * (STS_states * STS_rels)) * CmptName * Word)
      ]).
  eapply (@cmdc_adequacy' Σ cnames B C); eauto; try typeclasses eauto.
  apply NoDup_cons; split ; [set_solver | apply NoDup_singleton].
Qed.
