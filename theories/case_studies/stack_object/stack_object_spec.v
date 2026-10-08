From iris.proofmode Require Import proofmode.
From griotte Require Import region_invariants_allocation region_invariants_revocation interp_weakening monotone.
From griotte Require Import rules logrel world_interp_stack monotone proofmode register_tactics.
From griotte Require Import fetch_spec assert_spec switcher interp_switcher_call switcher_spec_call switcher_spec_return.
From griotte Require Import stack_object.
From griotte Require Import proofmode.
From griotte Require Import stack_object_spec_states stack_object_spec_world_call
  stack_object_spec_run_blocks_1 stack_object_spec_run_blocks_2.

Section SO.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Context {C : CmptName}.

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

  Lemma so_init_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : Reg)

    (b_so_exp_tbl e_so_exp_tbl : Addr)

    (C_f : Sealable)

    (W0 : WORLD)

    (Ws : list WORLD)
    (Cs : list CmptName)

    (Nassert Nswitcher Nso_code SON : namespace)

    (cstk : CSTK)
    :

    let imports := so_main_imports C_f in

    Nswitcher ## Nassert ->
    Nswitcher ## Nso_code ->
    Nassert ## Nso_code ->

    (b_so_exp_tbl <= b_so_exp_tbl ^+ 2 < e_so_exp_tbl)%a ->

    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp]} ->
    (forall r, r ∈ (dom rmap) -> is_Some (rmap !! r) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length so_main_code)%a ->

    (cgp_b + length so_main_data)%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    frame_match Ws Cs cstk W0 C ->
    (
      na_inv cerise_nais Nassert (assert_inv b_assert e_assert a_flag)
      ∗ na_inv cerise_nais Nswitcher switcher_inv
      ∗ na_inv cerise_nais Nso_code
          ([[ pc_b , pc_a ]] ↦ₐ [[ imports ]] ∗ codefrag pc_a so_main_code)
    ∗ inv (export_table_PCCN SON) (b_so_exp_tbl ↦ₐ WCap RX Global pc_b pc_e pc_b)
    ∗ inv (export_table_CGPN SON) ((b_so_exp_tbl ^+ 1)%a ↦ₐ WCap RW Global cgp_b cgp_e cgp_b)
    ∗ inv (export_table_entryN SON (b_so_exp_tbl ^+ 2)%a)
        ((b_so_exp_tbl ^+ 2)%a ↦ₐ WInt (encode_entry_point 2 (length (imports ++ SO_main_code_run))))
      ∗ na_own cerise_nais ⊤

      (* initial register file *)
      ∗ PC ↦ᵣ WCap RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

      (* initial memory layout *)
      ∗ world_interp W0 C

      ∗ interp_continuation cstk Ws Cs

      ∗ cstack_frag cstk

      ∗ interp W0 C (WSealed ot_switcher C_f)
      ∗ (WSealed ot_switcher C_f) ↦□ₑ 0
      ∗ interp W0 C (WCap RWL Local csp_b csp_e csp_b)

      ∗ WSealed ot_switcher (SCap RO Global b_so_exp_tbl e_so_exp_tbl (b_so_exp_tbl ^+ 2)%a) ↦□ₑ 2
      ∗ WSealed ot_switcher (SCap RO Local b_so_exp_tbl e_so_exp_tbl (b_so_exp_tbl ^+ 2)%a) ↦□ₑ 2
      ∗ seal_pred ot_switcher ot_switcher_propC

      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    (* Outline of the proof:
       - [so_world_run_call]: revoke the world, to get the stack frame;
       - [so_run_blocks_1_spec]: blocks 0-2, fetch the imports and jump to
         the switcher;
       - [switcher_call_args_0] and [switcher_cc_specification]: call to
         [C.adv];
       - [so_run_blocks_2_spec]: block 2, halt. *)
    intros imports; subst imports.
    iIntros (HNswitcher_assert HNswitcher_so HNassert_so Hsize_so_exp_tbl Hrmap_dom Hrmap_init HsubBounds
               Hcgp_contiguous Himports_contiguous Hframe_match)
      "(#Hassert & #Hswitcher
      & #Hso_code
      & #Hso_exp_tbl_PCC
      & #Hso_exp_tbl_CGP
      & #Hso_exp_tbl_f
      & Hna
      & HPC & Hcgp & Hcsp & Hrmap
      & Hworld_interp_C
      & HK
      & Hcstk_frag
      & #Hinterp_W0_C_f
      & #HentryC_f
      & #Hinterp_W0_csp
      & #Hentry_f & #Hentry_f'
      & #Hot_switcher
      )".
    assert (so_code_bounds pc_b pc_e pc_a C_f) as Hbounds by done.
    iMod (na_inv_acc with "Hso_code Hna")
      as "((>Himports_main & >Hcode_main) & Hna & Hso_code_close)"; auto.
    iRegionSplit "Himports_main" as "(Himport_switcher & Himport_assert & Himport_C_f)".
    iExtractList "Hrmap" [cra;ct0;ct1;cs0;cs1]
      as ["Hcra"; "Hct0"; "Hct1"; "Hcs0"; "Hcs1"].

    (* Revoke the world, to get the stack frame *)
    iMod (so_world_run_call with "Hinterp_W0_csp Hinterp_W0_C_f Hworld_interp_C")
      as (stk_mem) "(Hworld_interp_C & #Hinterp_W1_C_f & Hstack_revoked & %Hrevoked_stk & Hstk)".

    (* Blocks 0-2: fetch the imports and jump to the switcher *)
    iApply (so_run_blocks_1_spec with
             "[- $HPC $Hct0 $Hct1 $Hcs0 $Hcs1 $Hcra $Himport_switcher $Himport_C_f
              $Hcode_main]"); first done.
    iNext; iIntros "(HPC & Hct0 & Hct1 & Hcs0 & Hcs1 & Hcra & Himport_switcher & Himport_C_f
                    & Hcode_main)".
    iMod ("Hso_code_close" with "[$Hna Himport_switcher Himport_assert Himport_C_f $Hcode_main]")
      as "Hna".
    { iNext. iRegionMerge. iFrame. }
    iInsertRegs "Hrmap" ["Hct0"].
    iDestruct (switcher_call_args_0 (revoke W0) C with "Hrmap")
      as (arg_rmap rmap') "(%Hrmap'_dom & %Harg_rmap & Hrmap_arg & Hrmap)".
    { rewrite dom_insert_L !dom_delete_L Hrmap_dom; set_solver+. }

    (* Call to [C.adv] *)
    iApply (switcher_cc_specification with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $HentryC_f $Hrmap_arg $Hrmap
              $Hstk $Hworld_interp_C $Hstack_revoked $Hcstk_frag
              $Hinterp_W1_C_f $HK]"); [done|done|].
    iSplit; first done.
    iNext.
    iIntros (W2 rmap'' stk_mem' l')
      "(_ & _ & _ & _ & _ & _ & _ & _ & Hna & _ & _ & _ & HPC & _)".
    iEval (cbn [updatePcPerm]) in "HPC".

    (* Block 2: halt *)
    iMod (na_inv_acc with "Hso_code Hna")
      as "((>Himports_main & >Hcode_main) & Hna & Hso_code_close)"; auto.
    iApply (so_run_blocks_2_spec with "[$HPC $Hcode_main Himports_main Hna Hso_code_close]");
      first done.
    iNext; iIntros "(HPC & Hcode_main)".
    iMod ("Hso_code_close" with "[$Hna $Himports_main $Hcode_main]") as "Hna".
    wp_end; iIntros "_"; iFrame.
  Qed.

End SO.
