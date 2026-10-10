From iris.proofmode Require Import proofmode.
From griotte Require Import sts_multiple_updates.
From griotte Require Import logrel_binary interp_weakening_binary monotone_binary.
From griotte Require Import region_invariants_revocation_binary.
From griotte Require Import rules proofmode proofmode_binary register_tactics_binary.
From griotte Require Import world_ghost_theory_binary world_interp_stack_binary stack_world_resources_binary.
From griotte Require Import switcher_preamble_binary switcher_spec_call_binary switcher_spec_call_diag_binary.
From griotte Require Export write_only_secret_spec_world_binary.
From griotte Require Import write_only_secret_spec_states_binary
  write_only_secret_spec_init_blocks_1_binary write_only_secret_spec_call_blocks_2_binary
  write_only_secret_spec_halt_blocks_3_binary.

(** * Binary specification of the write-only sharing example

    Both runs execute [write_only_secret_main_code], with a different secret
    in the private data of [main] ([secret1] in the implementation run,
    [secret2] in the specification run). The specification holds for
    arbitrary secrets, and is used in both directions of the adequacy
    theorem.

    The cell holding the secret is shared with [B] as a permanent region of
    the world of [B], with the safety predicate [write_only_pred] of
    [write_only_secret_spec_world_binary]. *)

(** ** Specification of [main] *)
Section Write_only_secret.
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
  Context {B : CmptName}.

  Implicit Types W : WORLD.

  Lemma write_only_secret_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : Reg)

    (B_f : Sealable)

    (W_init : WORLD)

    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName)

    (stk_mem stk_mem_spec : list Word)
    (secret1 secret2 : Z)

    (Nswitcher : namespace)
    :

    let imports := write_only_secret_main_imports B_f in

    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp]} ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length write_only_secret_main_code)%a ->

    (cgp_b + length (write_only_secret_main_data secret1))%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    cgp_b ∉ dom (std W_init) ->

    (* The stack region is revoked in the world of B. *)
    revoked_addresses W_init (finz.seq_between csp_b csp_e) ->

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
      ∗ codefrag pc_a write_only_secret_main_code
      ∗ spec_codefrag pc_a write_only_secret_main_code
      ∗ [[ cgp_b , cgp_e ]] ↦ₐ [[ write_only_secret_main_data secret1 ]]
      ∗ [[ cgp_b , cgp_e ]] ↣ₐ [[ write_only_secret_main_data secret2 ]]
      ∗ [[ csp_b , csp_e ]] ↦ₐ [[ stk_mem ]]
      ∗ [[ csp_b , csp_e ]] ↣ₐ [[ stk_mem_spec ]]

      ∗ world_interp W_init B
      ∗ interp_continuation stk Ws Cs
      ∗ cstack_frag (map fst stk)
      ∗ cstack_frag_spec (map snd stk)

      ∗ interp W_init B (WSealed ot_switcher B_f, WSealed ot_switcher B_f)
      ∗ (WSealed ot_switcher B_f) ↦□ₑ write_only_secret_B_f_args
      ∗ StackRevokedResources W_init B (finz.seq_between csp_b csp_e)

      ⊢ WP Seq (Instr Executable)
          {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }})%I.
  Proof.
    (* Outline of the proof:
       - [write_only_secret_init_blocks_1_spec]: block 0, restrict [cgp] to
         the permission [WO], in [ca0],
       - [write_only_secret_call_blocks_2_spec]: blocks 1-3, fetch the
         imports and jump to the switcher,
       - [write_only_secret_world_share]: share the secret cell in the
         world of [B],
       - [switcher_cc_specification_diag]: call to [B.f],
       - [write_only_secret_halt_blocks_3_spec]: block 3, halt. *)
    intros imports; subst imports.
    iIntros (Hrmap_dom HsubBounds Hcgp_contiguous Himports_contiguous Hcgp_b Hrevoked_stack)
      "(#Hswitcher & #Hspec & Hna & Hj
      & HPC & HsPC & Hcgp & Hscgp & Hcsp & Hscsp & Hrmap
      & Himports_main & Hsimports_main & Hcode_main & Hscode_main
      & Hcgp_main & Hscgp_main & Hcsp_stk & Hscsp_stk
      & Hworld_interp_B & HK & Hcstk_frag & Hcstk_frag_spec
      & #Hinterp_Winit_B_f & #HentryB_f & #Hstack_revoked_B)".
    rewrite /write_only_secret_main_data /= in Hcgp_contiguous.
    rewrite /write_only_secret_main_imports /= in Himports_contiguous.
    iExtractList "Hrmap" [ctp;ct0;ct1;cs0;cs1;cra;ca0]
      as ["Hctp";"Hct0";"Hct1";"Hcs0";"Hcs1";"Hcra";"Hca0"].
    iDestruct "Hctp" as "(Hctp & Hsctp & ->)".
    iDestruct "Hct0" as "(Hct0 & Hsct0 & ->)".
    iDestruct "Hct1" as "(Hct1 & Hsct1 & ->)".
    iDestruct "Hcs0" as "(Hcs0 & Hscs0 & ->)".
    iDestruct "Hcs1" as "(Hcs1 & Hscs1 & ->)".
    iDestruct "Hcra" as "(Hcra & Hscra & ->)".
    iDestruct "Hca0" as "(Hca0 & Hsca0 & ->)".
    iRegionSplit "Hcgp_main" as "Hsecret".
    iSpecRegionSplit "Hscgp_main" as "Hssecret".
    iRegionSplit "Himports_main" as "(Himport_switcher & Himport_B_f)".
    iSpecRegionSplit "Hsimports_main" as "(Hsimport_switcher & Hsimport_B_f)".
    assert (write_only_secret_code_bounds pc_b pc_e pc_a) as Hbounds.
    { split; first done. exact Himports_contiguous. }

    (* Block 0: the write-only capability *)
    iApply (write_only_secret_init_blocks_1_spec with
             "[- $Hspec $Hj $HPC $HsPC $Hcgp $Hscgp $Hca0 $Hsca0 $Hcode_main $Hscode_main]");
      first done.
    iNext; iIntros "(Hj & HPC & HsPC & Hcgp & Hscgp & Hca0 & Hsca0 & Hcode_main & Hscode_main)".

    (* Blocks 1-3: fetch the imports and jump to the switcher *)
    iApply (write_only_secret_call_blocks_2_spec pc_b pc_e pc_a B_f with
             "[- $Hspec $Hj $HPC $HsPC $Hctp $Hsctp $Hct0 $Hsct0 $Hct1 $Hsct1 $Hcs0 $Hscs0
              $Hcra $Hscra $Himport_switcher $Hsimport_switcher $Himport_B_f $Hsimport_B_f
              $Hcode_main $Hscode_main]"); first done.
    iNext; iIntros "(Hj & HPC & HsPC & Hctp & Hsctp & Hct0 & Hsct0 & Hct1 & Hsct1
                    & Hcs0 & Hscs0 & Hcra & Hscra & _ & _ & _ & _ & Hcode_main & Hscode_main)".

    (* Share the secret cell in the world of B *)
    iMod (write_only_secret_world_share with
           "Hworld_interp_B Hstack_revoked_B Hinterp_Winit_B_f Hsecret Hssecret Hcsp_stk")
      as "(Hworld_interp_B & #Hinterp_ca0 & #Hinterp_B_f
           & Hstack_revoked_B' & %Hrevoked_B & Hcsp_stk)";
      [exact Hcgp_contiguous|done|done|].
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap Hsrmap]".
    iDestruct (big_sepM_sep with "Hsrmap") as "[Hsrmap _]".
    iInsertRegs "Hrmap" ["Hctp"; "Hct0"].
    iInsertRegsSpec "Hsrmap" ["Hsctp"; "Hsct0"].
    iDestruct (switcher_call_args_1_binary with "Hca0 Hsca0 Hinterp_ca0 Hrmap Hsrmap")
      as (arg_rmap arg_smap rmap' smap')
           "(%Hrmap'_dom & %Hsmap'_dom & %Harg_rmap & %Harg_smap & Hrmap_arg & Hrmap & Hsrmap)".
    { rewrite !dom_insert_L !dom_delete_L Hrmap_dom; set_solver+. }
    { rewrite !dom_insert_L !dom_delete_L Hrmap_dom; set_solver+. }

    (* Call to B.f *)
    iEval (rewrite /write_only_secret_B_f_args) in "HentryB_f".
    iApply (switcher_cc_specification_diag _ _ B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 with
             "[- $Hswitcher $Hspec $Hna $Hj
              $HPC $HsPC $Hcgp $Hscgp $Hcra $Hscra $Hcsp $Hscsp $Hct1 $Hsct1
              $Hcs0 $Hscs0 $Hcs1 $Hscs1 $Hrmap $Hsrmap $Hrmap_arg
              $Hcsp_stk $Hscsp_stk $Hworld_interp_B $Hstack_revoked_B'
              $Hcstk_frag $Hcstk_frag_spec
              $Hinterp_B_f $HentryB_f $HK]"); [done..|].
    iSplit; first done.
    iNext.
    iIntros (W2 rmap'' stk_mem' stk_mem_spec' l')
      "( _ & _ & _ & _ & _ & _ & _ & _
      & Hna & Hj & _ & _ & _ & _
      & HPC & HsPC
      & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _)".
    iEval (cbn [updatePcPerm]) in "HPC".
    iEval (cbn [updatePcPerm]) in "HsPC".

    (* Block 3: halt *)
    iApply (write_only_secret_halt_blocks_3_spec with
             "[$Hspec $Hj $HPC $HsPC $Hcode_main $Hscode_main Hna]");
      first done.
    iNext; iIntros "Hj".
    wp_end; iIntros "_"; iFrame.
  Qed.

End Write_only_secret.
