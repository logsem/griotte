From iris.proofmode Require Import proofmode.
From griotte Require Import logrel_binary.
From griotte Require Import rules proofmode proofmode_binary register_tactics_binary.
From griotte Require Import stack_world_resources_binary.
From griotte Require Import switcher_preamble_binary switcher_spec_call_diag_binary.
From griotte Require Import stack_callee_secret_spec_states_binary stack_callee_secret_spec_world_binary
  stack_callee_secret_spec_run_blocks_1_binary stack_callee_secret_spec_run_blocks_2_binary.

(** * Binary specification of the initial code of the trusted callee example

    [T.run] calls the adversary [B.adv] with its whole stack, and halts when
    [B.adv] returns. The code of [T] is kept in its invariant while [B.adv]
    runs, because [B.adv] may call [T.f]. *)

Section Stack_callee_secret_run.
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

  Lemma stack_callee_secret_run_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : Reg)

    (B_adv : Sealable)

    (W_init : WORLD)

    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName)

    (stk_mem stk_mem_spec : list Word)
    (secret1 secret2 : Z)

    (Nswitcher TN : namespace)
    :

    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp]} ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length stack_callee_secret_code)%a ->
    (pc_b + length (stack_callee_secret_imports B_adv))%a = Some pc_a ->

    (* The stack region is revoked in the world of B. *)
    revoked_addresses W_init (finz.seq_between csp_b csp_e) ->

    (
      na_inv cerise_nais Nswitcher switcher_inv_binary
      ∗ na_inv cerise_nais TN (stack_callee_secret_inv pc_b pc_a cgp_b B_adv secret1 secret2)
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

      (* initial stack *)
      ∗ [[ csp_b , csp_e ]] ↦ₐ [[ stk_mem ]]
      ∗ [[ csp_b , csp_e ]] ↣ₐ [[ stk_mem_spec ]]

      ∗ world_interp W_init B
      ∗ interp_continuation stk Ws Cs
      ∗ cstack_frag (map fst stk)
      ∗ cstack_frag_spec (map snd stk)

      ∗ interp W_init B (WSealed ot_switcher B_adv, WSealed ot_switcher B_adv)
      ∗ (WSealed ot_switcher B_adv) ↦□ₑ stack_callee_secret_B_adv_args
      ∗ StackRevokedResources W_init B (finz.seq_between csp_b csp_e)

      ⊢ WP Seq (Instr Executable)
          {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }})%I.
  Proof.
    (* Outline of the proof:
       - open the invariant of [T];
       - [stack_callee_secret_run_blocks_1_spec]: blocks 0-2, fetch the
         imports and jump to the switcher;
       - close the invariant of [T], and [switcher_call_args_0_binary]: the
         arguments of the call;
       - [switcher_cc_specification_diag]: call to [B.adv];
       - reopen the invariant of [T], and
         [stack_callee_secret_run_blocks_2_spec]: block 2, halt. *)
    iIntros (Hrmap_dom HsubBounds Himports_contiguous Hrevoked_stack)
      "(#Hswitcher & #HT & #Hspec & Hna & Hj
      & HPC & HsPC & Hcgp & Hscgp & Hcsp & Hscsp & Hrmap
      & Hcsp_stk & Hscsp_stk
      & Hworld_interp_B & HK & Hcstk_frag & Hcstk_frag_spec
      & #Hinterp_Winit_B_adv & #HentryB_adv & #Hstack_revoked_B)".
    rewrite /stack_callee_secret_inv.
    rewrite /stack_callee_secret_imports /= in Himports_contiguous.
    assert (stack_callee_secret_code_bounds pc_b pc_e pc_a) as Hbounds.
    { split; first done. exact Himports_contiguous. }
    iExtractList "Hrmap" [ctp;ct0;ct1;cs0;cs1;cra]
      as ["Hctp";"Hct0";"Hct1";"Hcs0";"Hcs1";"Hcra"].
    iDestruct "Hctp" as "(Hctp & Hsctp & ->)".
    iDestruct "Hct0" as "(Hct0 & Hsct0 & ->)".
    iDestruct "Hct1" as "(Hct1 & Hsct1 & ->)".
    iDestruct "Hcs0" as "(Hcs0 & Hscs0 & ->)".
    iDestruct "Hcs1" as "(Hcs1 & Hscs1 & ->)".
    iDestruct "Hcra" as "(Hcra & Hscra & ->)".

    (* Open the invariant of T *)
    iMod (na_inv_acc with "HT Hna")
      as "((>Himports_main & >Hsimports_main & >Hcode_main & >Hscode_main & >Hsecret & >Hssecret)
          & Hna & HT_close)"; auto.
    iDestruct (stack_callee_secret_imports_split with "Himports_main Hsimports_main")
      as "(Himport_switcher & Hsimport_switcher & Himport_B_adv & Hsimport_B_adv)";
      first done.

    (* Blocks 0-2: fetch the imports and jump to the switcher *)
    iApply (stack_callee_secret_run_blocks_1_spec pc_b pc_e pc_a B_adv with
             "[- $Hspec $Hj $HPC $HsPC $Hctp $Hsctp $Hct0 $Hsct0 $Hct1 $Hsct1 $Hcs0 $Hscs0
              $Hcra $Hscra $Himport_switcher $Hsimport_switcher $Himport_B_adv $Hsimport_B_adv
              $Hcode_main $Hscode_main]"); first done.
    iNext; iIntros "(Hj & HPC & HsPC & Hctp & Hsctp & Hct0 & Hsct0 & Hct1 & Hsct1
                    & Hcs0 & Hscs0 & Hcra & Hscra
                    & Himport_switcher & Hsimport_switcher & Himport_B_adv & Hsimport_B_adv
                    & Hcode_main & Hscode_main)".

    (* Close the invariant of T before giving control to the adversary *)
    iDestruct (stack_callee_secret_imports_merge with
                "Himport_switcher Hsimport_switcher Himport_B_adv Hsimport_B_adv")
      as "[Himports_main Hsimports_main]"; first done.
    iMod ("HT_close" with
           "[$Hna $Himports_main $Hsimports_main $Hcode_main $Hscode_main $Hsecret $Hssecret]")
      as "Hna".

    (* The arguments of the call to the adversary *)
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap Hsrmap]".
    iDestruct (big_sepM_sep with "Hsrmap") as "[Hsrmap _]".
    iInsertRegs "Hrmap" ["Hctp"; "Hct0"].
    iInsertRegsSpec "Hsrmap" ["Hsctp"; "Hsct0"].
    iDestruct (switcher_call_args_0_binary W_init B with "Hrmap Hsrmap")
      as (arg_rmap arg_smap rmap' smap')
           "(%Hrmap'_dom & %Hsmap'_dom & %Harg_rmap & %Harg_smap & Hrmap_arg & Hrmap & Hsrmap)".
    { rewrite !dom_insert_L !dom_delete_L Hrmap_dom; set_solver+. }
    { rewrite !dom_insert_L !dom_delete_L Hrmap_dom; set_solver+. }

    (* Call to B.adv *)
    iEval (rewrite /stack_callee_secret_B_adv_args) in "HentryB_adv".
    iApply (switcher_cc_specification_diag _ W_init B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 with
             "[- $Hswitcher $Hspec $Hna $Hj
              $HPC $HsPC $Hcgp $Hscgp $Hcra $Hscra $Hcsp $Hscsp $Hct1 $Hsct1
              $Hcs0 $Hscs0 $Hcs1 $Hscs1 $Hrmap $Hsrmap $Hrmap_arg
              $Hcsp_stk $Hscsp_stk $Hworld_interp_B $Hstack_revoked_B
              $Hcstk_frag $Hcstk_frag_spec
              $Hinterp_Winit_B_adv $HentryB_adv $HK]"); [done..|].
    iSplit; first done.
    iNext.
    iIntros (W2 rmap'' stk_mem' stk_mem_spec' l')
      "( _ & _ & _ & _ & _ & _ & _ & _
      & Hna & Hj & _ & _ & _ & _
      & HPC & HsPC
      & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _)".
    iEval (cbn [updatePcPerm]) in "HPC".
    iEval (cbn [updatePcPerm]) in "HsPC".

    (* Block 2: halt, in the reopened invariant of T *)
    iMod (na_inv_acc with "HT Hna")
      as "((>Himports_main & >Hsimports_main & >Hcode_main & >Hscode_main & >Hsecret & >Hssecret)
          & Hna & HT_close)"; auto.
    iApply (stack_callee_secret_run_blocks_2_spec with
             "[- $Hspec $Hj $HPC $HsPC $Hcode_main $Hscode_main]");
      first done.
    iNext; iIntros "(Hj & Hcode_main & Hscode_main)".
    iMod ("HT_close" with
           "[$Hna $Himports_main $Hsimports_main $Hcode_main $Hscode_main $Hsecret $Hssecret]")
      as "Hna".
    wp_end; iIntros "_"; iFrame.
  Qed.

End Stack_callee_secret_run.
