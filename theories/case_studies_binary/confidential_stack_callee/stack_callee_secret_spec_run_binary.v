From iris.proofmode Require Import proofmode.
From griotte Require Import sts_multiple_updates.
From griotte Require Import logrel_binary interp_weakening_binary monotone_binary.
From griotte Require Import region_invariants_revocation_binary.
From griotte Require Import rules proofmode proofmode_binary register_tactics_binary map_simpl.
From griotte Require Import switcher_preamble_binary switcher_spec_call_binary.
From griotte Require Import fetch_spec_binary switcher_spec_call_diag_binary.
From griotte Require Import stack_callee_secret_binary stack_callee_secret_spec_binary.

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
    iIntros (Hrmap_dom HsubBounds Himports_contiguous Hrevoked_stack)
      "(#Hswitcher & #HT & #Hspec & Hna & Hj
      & HPC & HsPC & Hcgp & Hscgp & Hcsp & Hscsp & Hrmap
      & Hcsp_stk & Hscsp_stk
      & Hworld_interp_B & HK & Hcstk_frag & Hcstk_frag_spec
      & #Hinterp_Winit_B_adv & #HentryB_adv & #Hstack_revoked_B)".
    rewrite /stack_callee_secret_inv.
    assert (length (stack_callee_secret_imports B_adv) = 2) as Himports_len by reflexivity.
    rewrite Himports_len in Himports_contiguous.

    (* Open the invariant of T *)
    iMod (na_inv_acc with "HT Hna")
      as "((>Himports_main & >Hsimports_main & >Hcode_main & >Hscode_main & >Hsecret & >Hssecret)
          & Hna & HT_close)"; auto.
    codefrag_facts "Hcode_main".

    (* Extract the needed registers from the register map *)
    iExtractList "Hrmap" [ctp;ct0;ct1;cs0;cs1;cra]
      as ["Hctp";"Hct0";"Hct1";"Hcs0";"Hcs1";"Hcra"].
    iDestruct "Hctp" as "(Hctp & Hsctp & ->)".
    iDestruct "Hct0" as "(Hct0 & Hsct0 & ->)".
    iDestruct "Hct1" as "(Hct1 & Hsct1 & ->)".
    iDestruct "Hcs0" as "(Hcs0 & Hscs0 & ->)".
    iDestruct "Hcs1" as "(Hcs1 & Hscs1 & ->)".
    iDestruct "Hcra" as "(Hcra & Hscra & ->)".

    (* Extract the imports *)
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_switcher Himports_main]".
    { transitivity (Some (pc_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_B_adv Himports_main]".
    { transitivity (Some (pc_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (spec_region_pointsto_cons with "Hsimports_main") as "[Hsimport_switcher Hsimports_main]".
    { transitivity (Some (pc_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (spec_region_pointsto_cons with "Hsimports_main") as "[Hsimport_B_adv Hsimports_main]".
    { transitivity (Some (pc_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)

    (* Unfold the code, so that the focusing tactics see its blocks *)
    rewrite /stack_callee_secret_code /stack_callee_secret_code_run.
    rewrite -!app_assoc.

    (* --------------------------------------------------- *)
    (* -------------- BLOCK 0 and 1 : FETCH -------------- *)
    (* --------------------------------------------------- *)

    focus_block_0_lockstep "Hscode_main" "Hcode_main" as "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    iApply (fetch_spec_lockstep with
             "[- $Hspec $Hj $HPC $HsPC $Hctp $Hsctp $Hct0 $Hsct0 $Hct1 $Hsct1 $Hcode $Hscode]"); eauto.
    { solve_addr. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher Hsimport_switcher".
    iNext ; iIntros "(Hj & HPC & HsPC & Hctp & Hsctp & Hct0 & Hsct0 & Hct1 & Hsct1
                      & Hcode & Hscode & Himport_switcher & Hsimport_switcher)".
    iEval (cbn) in "Hctp".
    iEval (cbn) in "Hsctp".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode_main" "Hcode_main".

    focus_block_lockstep 1 "Hscode_main" "Hcode_main" as a_fetch2 Ha_fetch2
      "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    iApply (fetch_spec_lockstep with
             "[- $Hspec $Hj $HPC $HsPC $Hct1 $Hsct1 $Hct0 $Hsct0 $Hcs0 $Hscs0 $Hcode $Hscode
                 $Himport_B_adv $Hsimport_B_adv]"); eauto.
    { solve_addr. }
    iNext ; iIntros "(Hj & HPC & HsPC & Hct1 & Hsct1 & Hct0 & Hsct0 & Hcs0 & Hscs0
                      & Hcode & Hscode & Himport_B_adv & Hsimport_B_adv)".
    iEval (cbn) in "Hct1".
    iEval (cbn) in "Hsct1".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode_main" "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 2: CALL B ----------------- *)
    (* --------------------------------------------------- *)

    replace (encodeInstrsW [Jalr cra ctp; Halt])
      with (encodeInstrsW [Jalr cra ctp] ++ encodeInstrsW [Halt]) by auto.
    rewrite -!app_assoc.
    focus_block_lockstep 2 "Hscode_main" "Hcode_main" as a_callB Ha_callB
      "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.

    (* Jalr cra ctp *)
    iInstr_lockstep "Hscode" "Hcode".

    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode_main" "Hcode_main".

    (* Close the invariant of T before giving control to the adversary *)
    iDestruct (region_pointsto_cons with "[$Himport_B_adv $Himports_main]") as "Himports_main"
    ; [solve_addr|solve_addr|].
    iDestruct (region_pointsto_cons with "[$Himport_switcher $Himports_main]") as "Himports_main"
    ; [solve_addr|solve_addr|].
    iDestruct (spec_region_pointsto_cons with "[$Hsimport_B_adv $Hsimports_main]") as "Hsimports_main"
    ; [solve_addr|solve_addr|].
    iDestruct (spec_region_pointsto_cons with "[$Hsimport_switcher $Hsimports_main]") as "Hsimports_main"
    ; [solve_addr|solve_addr|].
    iMod ("HT_close" with
           "[$Hna $Himports_main $Hsimports_main $Hcode_main $Hscode_main $Hsecret $Hssecret]")
      as "Hna".

    (* Prepare the argument registers for the call to the adversary *)
    iExtractList "Hrmap" [ca0;ca1;ca2;ca3;ca4;ca5]
      as ["Hca0";"Hca1";"Hca2";"Hca3";"Hca4";"Hca5"].
    iDestruct "Hca0" as "(Hca0 & Hsca0 & ->)".
    iDestruct "Hca1" as "(Hca1 & Hsca1 & ->)".
    iDestruct "Hca2" as "(Hca2 & Hsca2 & ->)".
    iDestruct "Hca3" as "(Hca3 & Hsca3 & ->)".
    iDestruct "Hca4" as "(Hca4 & Hsca4 & ->)".
    iDestruct "Hca5" as "(Hca5 & Hsca5 & ->)".
    iPoseProof (arg_rmap_zero_interp W_init B stack_callee_secret_B_adv_args ca0) as "Hi0".
    iPoseProof (arg_rmap_zero_interp W_init B stack_callee_secret_B_adv_args ca1) as "Hi1".
    iPoseProof (arg_rmap_zero_interp W_init B stack_callee_secret_B_adv_args ca2) as "Hi2".
    iPoseProof (arg_rmap_zero_interp W_init B stack_callee_secret_B_adv_args ca3) as "Hi3".
    iPoseProof (arg_rmap_zero_interp W_init B stack_callee_secret_B_adv_args ca4) as "Hi4".
    iPoseProof (arg_rmap_zero_interp W_init B stack_callee_secret_B_adv_args ca5) as "Hi5".
    iPoseProof (arg_rmap_zero_interp W_init B stack_callee_secret_B_adv_args ct0) as "Hi6".
    iDestruct (arg_rmap_prepare W_init B stack_callee_secret_B_adv_args
                with "Hca0 Hsca0 Hi0 Hca1 Hsca1 Hi1 Hca2 Hsca2 Hi2 Hca3 Hsca3 Hi3
                      Hca4 Hsca4 Hi4 Hca5 Hsca5 Hi5 Hct0 Hsct0 Hi6")
      as "Hrmap_arg".

    (* The other registers *)
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap Hsrmap]".
    iDestruct (big_sepM_sep with "Hsrmap") as "[Hsrmap _]".
    iInsertList "Hrmap" [ctp].
    iInsertListSpec "Hsrmap" [ctp].

    iApply (switcher_cc_specification_diag _ W_init B with
             "[- $Hswitcher $Hspec $Hna $Hj $Hinterp_Winit_B_adv $HentryB_adv
              $HPC $HsPC $Hcgp $Hscgp $Hcra $Hscra $Hcsp $Hscsp $Hct1 $Hsct1
              $Hcs0 $Hscs0 $Hcs1 $Hscs1 $Hrmap $Hsrmap $Hrmap_arg
              $Hcsp_stk $Hscsp_stk $Hworld_interp_B $Hstack_revoked_B
              $Hcstk_frag $Hcstk_frag_spec $HK]"); eauto; iFrame "%".
    { repeat first [rewrite dom_insert_L | rewrite dom_delete_L].
      rewrite Hrmap_dom; set_solver. }
    { repeat first [rewrite dom_insert_L | rewrite dom_delete_L].
      rewrite Hrmap_dom; set_solver. }
    { apply is_arg_rmap_of. }
    { apply is_arg_rmap_of. }

    iNext.
    iIntros (W2 rmap' stk_mem' stk_mem_spec' l')
      "( _ & _ & _ & _ & _ & _ & _ & _
      & Hna & Hj & _ & _ & _ & _
      & HPC & HsPC
      & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _)".
    iEval (cbn) in "HPC".
    iEval (cbn) in "HsPC".

    (* --------------------------------------------------- *)
    (* ------------------ BLOCK 3: HALT ------------------ *)
    (* --------------------------------------------------- *)

    iMod (na_inv_acc with "HT Hna")
      as "((>Himports_main & >Hsimports_main & >Hcode_main & >Hscode_main & >Hsecret & >Hssecret)
          & Hna & HT_close)"; auto.
    focus_block_lockstep 3 "Hscode_main" "Hcode_main" as a_halt Ha_halt
      "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.

    (* Halt *)
    iInstr_spec_lookup "Hscode" as "Hsi" "Hscode".
    iMod (step_halt with "[$Hspec $Hj $HsPC $Hsi]") as "(Hj & HsPC & Hsi)";
      [solve_ndisj|solve_pure|solve_pure|].
    iSpecialize ("Hscode" with "Hsi").
    (* Halt *)
    iInstr "Hcode".

    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode_main" "Hcode_main".
    iMod ("HT_close" with
           "[$Hna $Himports_main $Hsimports_main $Hcode_main $Hscode_main $Hsecret $Hssecret]")
      as "Hna".
    wp_end.
    iIntros "_".
    iFrame.
  Qed.

End Stack_callee_secret_run.
