From iris.proofmode Require Import proofmode.
From griotte Require Import sts_multiple_updates.
From griotte Require Import logrel_binary interp_weakening_binary monotone_binary.
From griotte Require Import region_invariants_revocation_binary.
From griotte Require Import rules proofmode proofmode_binary register_tactics_binary.
From griotte Require Import world_ghost_theory_binary world_interp_stack_binary stack_world_resources_binary.
From griotte Require Import switcher_preamble_binary switcher_spec_call_binary switcher_spec_call_diag_binary.
From griotte Require Import cmdc_spec_states_binary cmdc_spec_world_binary
  cmdc_spec_init_blocks_1_binary cmdc_spec_call_blocks_2_binary
  cmdc_spec_prep_blocks_3_binary cmdc_spec_halt_blocks_4_binary.

(** * Binary specification of the CMDC confidentiality example

    Both runs execute [cmdc_conf_main_code], with different secrets in the
    private data of [main] ([secret_b1], [secret_c1] in the implementation
    run, [secret_b2], [secret_c2] in the specification run).

    [main] stores [secret_c] into [c], and calls [B.f] with a capability to
    [b]. The cell [b] is shared with [B] as a permanent region of the world
    of [B]. After [B.f] returns, [main] opens the world of [B] at [b] and
    keeps it open: [B] does not run anymore, and [main] owns the points-to
    of [b]. *)

Section CMDC.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}
  .
  Context {B C : CmptName}.

  Implicit Types W : WORLD.

  Lemma cmdc_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : Reg)

    (B_f C_g : Sealable)

    (W_init_B : WORLD)
    (W_init_C : WORLD)

    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName)

    (stk_mem stk_mem_spec : list Word)
    (secret_b1 secret_c1 secret_b2 secret_c2 : Z)

    (Nswitcher : namespace)
    :

    let imports := cmdc_conf_main_imports B_f C_g in

    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp]} ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length cmdc_conf_main_code)%a ->

    (cgp_b + length (cmdc_conf_main_data secret_b1 secret_c1))%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    cgp_b ∉ dom (std W_init_B) ->
    (cgp_b ^+ 1)%a ∉ dom (std W_init_C) ->

    (* The stack region is revoked in the worlds of B and C. *)
    revoked_addresses W_init_B (finz.seq_between csp_b csp_e) ->
    revoked_addresses W_init_C (finz.seq_between csp_b csp_e) ->

    (
      na_inv cerise_nais Nswitcher switcher_inv_binary
      ∗ spec_ctx
      ∗ na_own cerise_nais ⊤
      ∗ ⤇ Seq (Instr Executable)

      (* initial register files *)
      ∗ PC ↦ᵣ WCap RX Global pc_b pc_e pc_a
      ∗ PC ↣ᵣ WCap RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b
      ∗ cgp ↣ᵣ WCap RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
      ∗ csp ↣ᵣ WCap RWL Local csp_b csp_e csp_b
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ r ↣ᵣ w ∗ ⌜ w = WInt 0 ⌝ )

      (* initial memory layout *)
      ∗ [[ pc_b , pc_a ]] ↦ₐ [[ imports ]]
      ∗ [[ pc_b , pc_a ]] ↣ₐ [[ imports ]]
      ∗ codefrag pc_a cmdc_conf_main_code
      ∗ spec_codefrag pc_a cmdc_conf_main_code
      ∗ [[ cgp_b , cgp_e ]] ↦ₐ [[ cmdc_conf_main_data secret_b1 secret_c1 ]]
      ∗ [[ cgp_b , cgp_e ]] ↣ₐ [[ cmdc_conf_main_data secret_b2 secret_c2 ]]
      ∗ [[ csp_b , csp_e ]] ↦ₐ [[ stk_mem ]]
      ∗ [[ csp_b , csp_e ]] ↣ₐ [[ stk_mem_spec ]]

      ∗ world_interp W_init_B B
      ∗ world_interp W_init_C C

      ∗ interp_continuation stk Ws Cs
      ∗ cstack_frag (map fst stk)
      ∗ cstack_frag_spec (map snd stk)

      ∗ interp W_init_B B (WSealed ot_switcher B_f, WSealed ot_switcher B_f)
      ∗ interp W_init_C C (WSealed ot_switcher C_g, WSealed ot_switcher C_g)

      ∗ (WSealed ot_switcher B_f) ↦□ₑ cmdc_conf_B_f_args
      ∗ (WSealed ot_switcher C_g) ↦□ₑ cmdc_conf_C_g_args

      (* initial stack are revoked in both worlds *)
      ∗ StackRevokedResources W_init_B B (finz.seq_between csp_b csp_e)
      ∗ StackRevokedResources W_init_C C (finz.seq_between csp_b csp_e)

      ⊢ WP Seq (Instr Executable)
          {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }})%I.
  Proof.
    (* Outline of the proof:
       - [cmdc_init_blocks_1_spec]: block 0, store [secret_c] into [c],
         erase [b], and prepare the argument [b] of the call to [B.f],
       - [cmdc_call_blocks_2_spec cmdc_call_B]: blocks 1-3, fetch the
         imports and jump to the switcher,
       - [cmdc_world_share]: share [b] in the world of [B],
       - [switcher_cc_specification_diag]: call to [B.f],
       - [cmdc_world_return]: get [b] back from the world of [B],
       - [cmdc_prep_blocks_3_spec]: block 4, erase [c], store [secret_b]
         into [b], and prepare the argument [c] of the call to [C.g],
       - [cmdc_call_blocks_2_spec cmdc_call_C]: blocks 5-7, fetch the
         imports and jump to the switcher,
       - [cmdc_world_share]: share [c] in the world of [C],
       - [switcher_cc_specification_diag]: call to [C.g],
       - [cmdc_halt_blocks_4_spec]: block 7, halt. *)
    intros imports; subst imports.
    iIntros (Hrmap_dom HsubBounds Hcgp_contiguous Himports_contiguous Hcgp_b Hcgp_c
               Hrevoked_stack_B Hrevoked_stack_C)
      "(#Hswitcher & #Hspec & Hna & Hj
      & HPC & HsPC & Hcgp & Hscgp & Hcsp & Hscsp & Hrmap
      & Himports_main & Hsimports_main & Hcode_main & Hscode_main
      & Hcgp_main & Hscgp_main & Hcsp_stk & Hscsp_stk
      & Hworld_interp_B & Hworld_interp_C
      & HK & Hcstk_frag & Hcstk_frag_spec
      & #Hinterp_Winit_B_f & #Hinterp_Winit_C_g
      & #HentryB_f & #HentryC_g
      & #Hstack_revoked_B & #Hstack_revoked_C)".
    iExtractList "Hrmap" [ca0;ca1;ctp;ct0;ct1;cs0;cs1;cra]
      as ["Hca0";"Hca1";"Hctp";"Hct0";"Hct1";"Hcs0";"Hcs1";"Hcra"].
    iDestruct "Hca0" as "(Hca0 & Hsca0 & ->)".
    iDestruct "Hca1" as "(Hca1 & Hsca1 & ->)".
    iDestruct "Hctp" as "(Hctp & Hsctp & ->)".
    iDestruct "Hct0" as "(Hct0 & Hsct0 & ->)".
    iDestruct "Hct1" as "(Hct1 & Hsct1 & ->)".
    iDestruct "Hcs0" as "(Hcs0 & Hscs0 & ->)".
    iDestruct "Hcs1" as "(Hcs1 & Hscs1 & ->)".
    iDestruct "Hcra" as "(Hcra & Hscra & ->)".
    iRegionSplit "Hcgp_main" as "(Hcgp_b & Hcgp_c & Hsecret_b & Hsecret_c)".
    iSpecRegionSplit "Hscgp_main" as "(Hscgp_b & Hscgp_c & Hssecret_b & Hssecret_c)".
    iRegionSplit "Himports_main" as "(Himport_switcher & Himport_B_f & Himport_C_g)".
    iSpecRegionSplit "Hsimports_main" as "(Hsimport_switcher & Hsimport_B_f & Hsimport_C_g)".
    assert (cmdc_code_bounds pc_b pc_e pc_a) as Hbounds.
    { split; first done. exact Himports_contiguous. }

    (* Block 0: store secret_c into c, erase b, and prepare the argument b *)
    iApply (cmdc_init_blocks_1_spec with
             "[- $Hspec $Hj $HPC $HsPC $Hcgp $Hscgp $Hca0 $Hsca0 $Hct0 $Hsct0 $Hct1 $Hsct1
              $Hcgp_b $Hscgp_b $Hcgp_c $Hscgp_c $Hsecret_c $Hssecret_c $Hcode_main $Hscode_main]");
      [done|done|].
    iNext; iIntros "(Hj & HPC & HsPC & Hcgp & Hscgp & Hca0 & Hsca0
                    & [%wct0 [Hct0 Hsct0]] & [%wct1 [Hct1 Hsct1]]
                    & Hcgp_b & Hscgp_b & Hcgp_c & Hscgp_c & _ & _ & Hcode_main & Hscode_main)".

    (* Blocks 1-3: fetch the imports and jump to the switcher *)
    iApply (cmdc_call_blocks_2_spec cmdc_call_B pc_b pc_e pc_a B_f C_g with
             "[- $Hspec $Hj $HPC $HsPC $Hctp $Hsctp $Hct0 $Hsct0 $Hct1 $Hsct1 $Hcs0 $Hscs0
              $Hcra $Hscra $Himport_switcher $Hsimport_switcher $Himport_B_f $Hsimport_B_f
              $Hcode_main $Hscode_main]"); first done.
    iNext; iIntros "(Hj & HPC & HsPC & Hctp & Hsctp & Hct0 & Hsct0 & Hct1 & Hsct1
                    & Hcs0 & Hscs0 & Hcra & Hscra & Himport_switcher & Hsimport_switcher
                    & _ & _ & Hcode_main & Hscode_main)".

    (* Share b in the world of B *)
    iMod (cmdc_world_share _ _ _ (cgp_b ^+ 1)%a with
           "Hworld_interp_B Hstack_revoked_B Hinterp_Winit_B_f Hcgp_b Hscgp_b Hcsp_stk")
      as "(Hworld_interp_B & #Hrel_cgp_b & #Hinterp_ca0 & #Hinterp_B_f
           & Hstack_revoked_B' & %Hrevoked_B & %Hcgp_b_stk & Hcsp_stk)";
      [solve_addr|done|done|].
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap Hsrmap]".
    iDestruct (big_sepM_sep with "Hsrmap") as "[Hsrmap _]".
    iInsertRegs "Hrmap" ["Hca1"; "Hctp"; "Hct0"].
    iInsertRegsSpec "Hsrmap" ["Hsca1"; "Hsctp"; "Hsct0"].
    iDestruct (switcher_call_args_1_binary with "Hca0 Hsca0 Hinterp_ca0 Hrmap Hsrmap")
      as (arg_rmap arg_smap rmap' smap')
           "(%Hrmap'_dom & %Hsmap'_dom & %Harg_rmap & %Harg_smap & Hrmap_arg & Hrmap & Hsrmap)".
    { rewrite !dom_insert_L !dom_delete_L Hrmap_dom; set_solver+. }
    { rewrite !dom_insert_L !dom_delete_L Hrmap_dom; set_solver+. }

    (* Call to B.f *)
    iApply (switcher_cc_specification_diag with
             "[- $Hswitcher $Hspec $Hna $Hj
              $HPC $HsPC $Hcgp $Hscgp $Hcra $Hscra $Hcsp $Hscsp $Hct1 $Hsct1
              $Hcs0 $Hscs0 $Hcs1 $Hscs1 $Hrmap $Hsrmap $Hrmap_arg
              $Hcsp_stk $Hscsp_stk $Hworld_interp_B $Hstack_revoked_B'
              $Hcstk_frag $Hcstk_frag_spec
              $Hinterp_B_f $HentryB_f $HK]"); [done..|].
    iSplit; first done.
    iNext.
    clear dependent arg_rmap arg_smap rmap' smap' rmap.
    iIntros (W_ret_B rmap stk_mem' stk_mem_spec' l)
      "( _ & _ & _ & %Hrelated_pub_B & _ & %Hrmap_dom & _ & _
      & Hna & Hj & %Hcsp_bounds
      & Hworld_interp_B & Hcstk_frag & Hcstk_frag_spec
      & HPC & HsPC & Hcgp & Hscgp & Hcra & Hscra & Hcs0 & Hscs0 & Hcs1 & Hscs1 & Hcsp & Hscsp
      & [%warg0 (Hca0 & Hsca0 & _)] & [%warg1 (Hca1 & Hsca1 & _)]
      & Hrmap & Hcsp_stk & Hscsp_stk & HK)".
    iEval (cbn [updatePcPerm]) in "HPC".
    iEval (cbn [updatePcPerm]) in "HsPC".
    change_pc_to (pc_a ^+ cmdc_block_offset 4)%a.

    (* Get b back from the world of B *)
    destruct Hcsp_bounds as (Hcsp_b4 & _ & _).
    iMod (cmdc_world_return with "Hworld_interp_B Hrel_cgp_b") as (wb swb) "[Hcgp_b Hscgp_b]";
      [done|solve_addr|done|].
    iExtractList "Hrmap" [ctp;ct0;ct1] as ["Hctp";"Hct0";"Hct1"].
    iDestruct "Hctp" as "(Hctp & Hsctp & ->)".
    iDestruct "Hct0" as "(Hct0 & Hsct0 & ->)".
    iDestruct "Hct1" as "(Hct1 & Hsct1 & ->)".

    (* Block 4: erase c, store secret_b into b, and prepare the argument c *)
    iApply (cmdc_prep_blocks_3_spec with
             "[- $Hspec $Hj $HPC $HsPC $Hcgp $Hscgp $Hca0 $Hsca0 $Hct0 $Hsct0 $Hct1 $Hsct1
              $Hcgp_b $Hscgp_b $Hcgp_c $Hscgp_c $Hsecret_b $Hssecret_b $Hcode_main $Hscode_main]");
      [done|done|].
    iNext; iIntros "(Hj & HPC & HsPC & Hcgp & Hscgp & Hca0 & Hsca0
                    & [%wct0' [Hct0 Hsct0]] & [%wct1' [Hct1 Hsct1]]
                    & _ & _ & Hcgp_c & Hscgp_c & _ & _ & Hcode_main & Hscode_main)".

    (* Blocks 5-7: fetch the imports and jump to the switcher *)
    iApply (cmdc_call_blocks_2_spec cmdc_call_C pc_b pc_e pc_a B_f C_g with
             "[- $Hspec $Hj $HPC $HsPC $Hctp $Hsctp $Hct0 $Hsct0 $Hct1 $Hsct1 $Hcs0 $Hscs0
              $Hcra $Hscra $Himport_switcher $Hsimport_switcher $Himport_C_g $Hsimport_C_g
              $Hcode_main $Hscode_main]"); first done.
    iNext; iIntros "(Hj & HPC & HsPC & Hctp & Hsctp & Hct0 & Hsct0 & Hct1 & Hsct1
                    & Hcs0 & Hscs0 & Hcra & Hscra & _ & _ & _ & _ & Hcode_main & Hscode_main)".

    (* Share c in the world of C *)
    iMod (cmdc_world_share _ _ _ (cgp_b ^+ 2)%a with
           "Hworld_interp_C Hstack_revoked_C Hinterp_Winit_C_g Hcgp_c Hscgp_c Hcsp_stk")
      as "(Hworld_interp_C & _ & #Hinterp_ca0_C & #Hinterp_C_g
           & Hstack_revoked_C' & %Hrevoked_C & _ & Hcsp_stk)";
      [solve_addr|done|done|].
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap Hsrmap]".
    iDestruct (big_sepM_sep with "Hsrmap") as "[Hsrmap _]".
    iInsertRegs "Hrmap" ["Hca1"; "Hctp"; "Hct0"].
    iInsertRegsSpec "Hsrmap" ["Hsca1"; "Hsctp"; "Hsct0"].
    iDestruct (switcher_call_args_1_binary with "Hca0 Hsca0 Hinterp_ca0_C Hrmap Hsrmap")
      as (arg_rmap arg_smap rmap' smap')
           "(%Hrmap'_dom & %Hsmap'_dom & %Harg_rmap & %Harg_smap & Hrmap_arg & Hrmap & Hsrmap)".
    { rewrite !dom_insert_L !dom_delete_L Hrmap_dom; set_solver+. }
    { rewrite !dom_insert_L !dom_delete_L Hrmap_dom; set_solver+. }

    (* Call to C.g *)
    iApply (switcher_cc_specification_diag with
             "[- $Hswitcher $Hspec $Hna $Hj
              $HPC $HsPC $Hcgp $Hscgp $Hcra $Hscra $Hcsp $Hscsp $Hct1 $Hsct1
              $Hcs0 $Hscs0 $Hcs1 $Hscs1 $Hrmap $Hsrmap $Hrmap_arg
              $Hcsp_stk $Hscsp_stk $Hworld_interp_C $Hstack_revoked_C'
              $Hcstk_frag $Hcstk_frag_spec
              $Hinterp_C_g $HentryC_g $HK]"); [done..|].
    iSplit; first done.
    iNext.
    iIntros (W_ret_C rmap'' stk_mem'' stk_mem_spec'' l')
      "( _ & _ & _ & _ & _ & _ & _ & _
      & Hna & Hj & _ & _ & _ & _
      & HPC & HsPC
      & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _)".
    iEval (cbn [updatePcPerm]) in "HPC".
    iEval (cbn [updatePcPerm]) in "HsPC".
    change_pc_to (pc_a ^+ cmdc_instr_offset 7 1)%a.

    (* Block 7: halt *)
    iApply (cmdc_halt_blocks_4_spec with "[$Hspec $Hj $HPC $HsPC $Hcode_main $Hscode_main Hna]");
      first done.
    iNext; iIntros "Hj".
    wp_end; iIntros "_"; iFrame.
  Qed.

End CMDC.
