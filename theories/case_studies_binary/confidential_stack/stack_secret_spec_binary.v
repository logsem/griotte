From iris.proofmode Require Import proofmode.
From griotte Require Import sts_multiple_updates.
From griotte Require Import logrel_binary interp_weakening_binary monotone_binary.
From griotte Require Import region_invariants_revocation_binary.
From griotte Require Import rules proofmode proofmode_binary register_tactics_binary.
From griotte Require Import stack_world_resources_binary.
From griotte Require Import switcher_preamble_binary switcher_spec_call_binary switcher_spec_call_diag_binary.
From griotte Require Import stack_secret_spec_states_binary stack_secret_spec_world_binary
  stack_secret_spec_init_blocks_1_binary stack_secret_spec_call_blocks_2_binary
  stack_secret_spec_halt_blocks_3_binary.

(** * Binary specification of the stack confidentiality example

    Both runs execute [stack_secret_main_code], with a different secret in
    the private data of the trusted compartment ([secret1] in the
    implementation run, [secret2] in the specification run). The
    specification holds for arbitrary secrets, and is used in both
    directions of the adequacy theorem.

    [main] calls the adversary with its stack pointer at [csp_b + 1]: the
    word at [csp_b], which holds the secret, stays privately owned by [main]
    during the call, and the switcher receives the stack from [csp_b + 1] to
    [csp_e], whose word at [csp_b + 5] also holds the secret. *)

Section Stack_secret.
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
  Implicit Types C : CmptName.

  (** The stack must contain the frame word of [main], the four words
      spilled by the switcher, and the stale copy. *)
  Lemma stack_secret_spec

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

    let imports := stack_secret_main_imports B_f in

    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp]} ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length stack_secret_main_code)%a ->

    (cgp_b + length (stack_secret_main_data secret1))%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->
    (csp_b ^+ 5 < csp_e)%a ->

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
      ∗ codefrag pc_a stack_secret_main_code
      ∗ spec_codefrag pc_a stack_secret_main_code
      ∗ [[ cgp_b , cgp_e ]] ↦ₐ [[ stack_secret_main_data secret1 ]]
      ∗ [[ cgp_b , cgp_e ]] ↣ₐ [[ stack_secret_main_data secret2 ]]
      ∗ [[ csp_b , csp_e ]] ↦ₐ [[ stk_mem ]]
      ∗ [[ csp_b , csp_e ]] ↣ₐ [[ stk_mem_spec ]]

      ∗ world_interp W_init B
      ∗ interp_continuation stk Ws Cs
      ∗ cstack_frag (map fst stk)
      ∗ cstack_frag_spec (map snd stk)

      ∗ interp W_init B (WSealed ot_switcher B_f, WSealed ot_switcher B_f)
      ∗ (WSealed ot_switcher B_f) ↦□ₑ stack_secret_B_f_args
      ∗ StackRevokedResources W_init B (finz.seq_between csp_b csp_e)

      ⊢ WP Seq (Instr Executable)
          {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }})%I.
  Proof.
    (* Outline of the proof:
       - [stack_secret_stack_split]: split the stack at [csp_b] and
         [csp_b + 5],
       - [stack_secret_init_blocks_1_spec]: block 0, store the secret at
         [csp_b] and [csp_b + 5], and move the stack pointer to [csp_b + 1],
       - [stack_secret_call_blocks_2_spec]: blocks 1-3, fetch the imports
         and jump to the switcher,
       - [stack_secret_world_call]: give the stack above [csp_b] to the
         switcher,
       - [switcher_cc_specification_diag]: call to [B.f],
       - [stack_secret_halt_blocks_3_spec]: block 3, halt. *)
    intros imports; subst imports.
    iIntros (Hrmap_dom HsubBounds Hcgp_contiguous Himports_contiguous Hcsp_size Hrevoked_stack)
      "(#Hswitcher & #Hspec & Hna & Hj
      & HPC & HsPC & Hcgp & Hscgp & Hcsp & Hscsp & Hrmap
      & Himports_main & Hsimports_main & Hcode_main & Hscode_main
      & Hcgp_main & Hscgp_main & Hcsp_stk & Hscsp_stk
      & Hworld_interp_B & HK & Hcstk_frag & Hcstk_frag_spec
      & #Hinterp_Winit_B_f & #HentryB_f & #Hstack_revoked_B)".
    rewrite /stack_secret_main_data /= in Hcgp_contiguous.
    rewrite /stack_secret_main_imports /= in Himports_contiguous.
    iExtractList "Hrmap" [ctp;ct0;ct1;cs0;cs1;cra]
      as ["Hctp";"Hct0";"Hct1";"Hcs0";"Hcs1";"Hcra"].
    iDestruct "Hctp" as "(Hctp & Hsctp & ->)".
    iDestruct "Hct0" as "(Hct0 & Hsct0 & ->)".
    iDestruct "Hct1" as "(Hct1 & Hsct1 & ->)".
    iDestruct "Hcs0" as "(Hcs0 & Hscs0 & ->)".
    iDestruct "Hcs1" as "(Hcs1 & Hscs1 & ->)".
    iDestruct "Hcra" as "(Hcra & Hscra & ->)".
    iRegionSplit "Hcgp_main" as "Hsecret".
    iSpecRegionSplit "Hscgp_main" as "Hssecret".
    iRegionSplit "Himports_main" as "(Himport_switcher & Himport_B_f)".
    iSpecRegionSplit "Hsimports_main" as "(Hsimport_switcher & Hsimport_B_f)".
    assert (stack_secret_code_bounds pc_b pc_e pc_a) as Hbounds.
    { split; first done. exact Himports_contiguous. }

    (* Split the stack: [csp_b] is the frame word of [main], [csp_b + 5]
       the stale copy, the rest is untouched. *)
    iDestruct (stack_secret_stack_split with "Hcsp_stk Hscsp_stk")
      as (w_stk0 sw_stk0 stk_lo sstk_lo w_stk5 sw_stk5 stk_hi sstk_hi)
           "(%Hlen_lo & %Hlen_lo_spec & Hstk0 & Hsstk0 & Hstk_lo & Hsstk_lo
            & Hstk5 & Hsstk5 & Hstk_hi & Hsstk_hi)";
      first done.

    (* Block 0: store the secret at csp_b and csp_b + 5 *)
    iApply (stack_secret_init_blocks_1_spec with
             "[- $Hspec $Hj $HPC $HsPC $Hcgp $Hscgp $Hcsp $Hscsp $Hct0 $Hsct0
              $Hsecret $Hssecret $Hstk0 $Hsstk0 $Hstk5 $Hsstk5 $Hcode_main $Hscode_main]");
      [done|exact Hcgp_contiguous|done|].
    iNext; iIntros "(Hj & HPC & HsPC & Hcgp & Hscgp & Hcsp & Hscsp & Hct0 & Hsct0
                    & _ & _ & _ & _ & Hstk5 & Hsstk5 & Hcode_main & Hscode_main)".

    (* Blocks 1-3: fetch the imports and jump to the switcher *)
    iApply (stack_secret_call_blocks_2_spec pc_b pc_e pc_a B_f with
             "[- $Hspec $Hj $HPC $HsPC $Hctp $Hsctp $Hct0 $Hsct0 $Hct1 $Hsct1 $Hcs0 $Hscs0
              $Hcra $Hscra $Himport_switcher $Hsimport_switcher $Himport_B_f $Hsimport_B_f
              $Hcode_main $Hscode_main]"); first done.
    iNext; iIntros "(Hj & HPC & HsPC & Hctp & Hsctp & Hct0 & Hsct0 & Hct1 & Hsct1
                    & Hcs0 & Hscs0 & Hcra & Hscra & _ & _ & _ & _ & Hcode_main & Hscode_main)".

    (* Give the stack above csp_b, with the stale copy, to the switcher *)
    iDestruct (stack_secret_world_call with
                "Hstack_revoked_B Hstk_lo Hsstk_lo Hstk5 Hsstk5 Hstk_hi Hsstk_hi")
      as "(#Hstack_revoked_B' & %Hrevoked_stack' & Hcsp_stk & Hscsp_stk)";
      [done..|].
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap Hsrmap]".
    iDestruct (big_sepM_sep with "Hsrmap") as "[Hsrmap _]".
    iInsertRegs "Hrmap" ["Hctp"; "Hct0"].
    iInsertRegsSpec "Hsrmap" ["Hsctp"; "Hsct0"].
    iDestruct (switcher_call_args_0_binary W_init B with "Hrmap Hsrmap")
      as (arg_rmap arg_smap rmap' smap')
           "(%Hrmap'_dom & %Hsmap'_dom & %Harg_rmap & %Harg_smap & Hrmap_arg & Hrmap & Hsrmap)".
    { rewrite !dom_insert_L !dom_delete_L Hrmap_dom; set_solver+. }
    { rewrite !dom_insert_L !dom_delete_L Hrmap_dom; set_solver+. }

    (* Call to B.f *)
    iEval (rewrite /stack_secret_B_f_args) in "HentryB_f".
    iApply (switcher_cc_specification_diag _ W_init B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 with
             "[- $Hswitcher $Hspec $Hna $Hj
              $HPC $HsPC $Hcgp $Hscgp $Hcra $Hscra $Hcsp $Hscsp $Hct1 $Hsct1
              $Hcs0 $Hscs0 $Hcs1 $Hscs1 $Hrmap $Hsrmap $Hrmap_arg
              $Hcsp_stk $Hscsp_stk $Hworld_interp_B $Hstack_revoked_B'
              $Hcstk_frag $Hcstk_frag_spec
              $Hinterp_Winit_B_f $HentryB_f $HK]"); [done..|].
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
    iApply (stack_secret_halt_blocks_3_spec with
             "[$Hspec $Hj $HPC $HsPC $Hcode_main $Hscode_main Hna]");
      first done.
    iNext; iIntros "Hj".
    wp_end; iIntros "_"; iFrame.
  Qed.

End Stack_secret.
