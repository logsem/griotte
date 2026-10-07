From iris.proofmode Require Import proofmode.
From griotte Require Import sts_multiple_updates.
From griotte Require Import logrel_binary interp_weakening_binary monotone_binary.
From griotte Require Import region_invariants_revocation_binary.
From griotte Require Import rules proofmode proofmode_binary register_tactics_binary map_simpl.
From griotte Require Import world_ghost_theory_binary world_interp_stack_binary stack_world_resources_binary.
From griotte Require Import switcher_preamble_binary switcher_spec_call_binary.
From griotte Require Import fetch_spec_binary switcher_spec_call_diag_binary cmdc_binary.

(** * Binary specification of the CMDC confidentiality example, after the call to [B.f]

    The trusted compartment [main] has returned from [B.f]. The world of [B]
    is not needed anymore: [main] owns the points-to of the cell [b], in
    both runs. It erases [c], stores [secret_b] into [b], and calls [C.g]
    with a capability to [c]. *)

Section CMDC_post_B.
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
  Context {C : CmptName}.

  Implicit Types W : WORLD.

  Lemma cmdc_spec_post_B

    (pc_b pc_e pc_a a_post : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : Reg)

    (C_g : Sealable)

    (W_init_C : WORLD)

    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName)

    (stk_mem stk_mem_spec : list Word)
    (wb swb wc swc wca0 swca0 wca1 swca1 wcra : Word)
    (secret_b1 secret_b2 : Z)

    (Nswitcher : namespace)
    :

    dom rmap = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length cmdc_conf_main_code)%a ->
    (pc_a + length cmdc_conf_pre_B_code)%a = Some a_post ->

    (cgp_b + 4)%a = Some cgp_e ->
    (pc_b + 3)%a = Some pc_a ->

    (cgp_b ^+ 1)%a ∉ dom (std W_init_C) ->

    (* The stack region is revoked in the world of C. *)
    revoked_addresses W_init_C (finz.seq_between csp_b csp_e) ->

    (
      na_inv cerise_nais Nswitcher switcher_inv_binary
      ∗ spec_ctx
      ∗ na_own cerise_nais ⊤
      ∗ ⤇ Seq (Instr Executable)

      (* register files *)
      ∗ PC ↦ᵣ WCap RX Global pc_b pc_e a_post
      ∗ PC ↣ᵣ WCap RX Global pc_b pc_e a_post
      ∗ cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b
      ∗ cgp ↣ᵣ WCap RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
      ∗ csp ↣ᵣ WCap RWL Local csp_b csp_e csp_b
      ∗ cra ↦ᵣ wcra
      ∗ cra ↣ᵣ wcra
      ∗ cs0 ↦ᵣ WInt 0
      ∗ cs0 ↣ᵣ WInt 0
      ∗ cs1 ↦ᵣ WInt 0
      ∗ cs1 ↣ᵣ WInt 0
      ∗ ca0 ↦ᵣ wca0
      ∗ ca0 ↣ᵣ swca0
      ∗ ca1 ↦ᵣ wca1
      ∗ ca1 ↣ᵣ swca1
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ r ↣ᵣ w ∗ ⌜ w = WInt 0 ⌝ )

      (* memory *)
      ∗ pc_b ↦ₐ WSentry XSRW_ Local b_switcher e_switcher a_switcher_call
      ∗ pc_b ↣ₐ WSentry XSRW_ Local b_switcher e_switcher a_switcher_call
      ∗ (pc_b ^+ 2)%a ↦ₐ WSealed ot_switcher C_g
      ∗ (pc_b ^+ 2)%a ↣ₐ WSealed ot_switcher C_g
      ∗ codefrag pc_a cmdc_conf_main_code
      ∗ spec_codefrag pc_a cmdc_conf_main_code
      ∗ cgp_b ↦ₐ wb
      ∗ cgp_b ↣ₐ swb
      ∗ (cgp_b ^+ 1)%a ↦ₐ wc
      ∗ (cgp_b ^+ 1)%a ↣ₐ swc
      ∗ (cgp_b ^+ 2)%a ↦ₐ WInt secret_b1
      ∗ (cgp_b ^+ 2)%a ↣ₐ WInt secret_b2
      ∗ [[ csp_b , csp_e ]] ↦ₐ [[ stk_mem ]]
      ∗ [[ csp_b , csp_e ]] ↣ₐ [[ stk_mem_spec ]]

      ∗ world_interp W_init_C C
      ∗ interp_continuation stk Ws Cs
      ∗ cstack_frag (map fst stk)
      ∗ cstack_frag_spec (map snd stk)

      ∗ interp W_init_C C (WSealed ot_switcher C_g, WSealed ot_switcher C_g)
      ∗ (WSealed ot_switcher C_g) ↦□ₑ cmdc_conf_C_g_args
      ∗ StackRevokedResources W_init_C C (finz.seq_between csp_b csp_e)

      ⊢ WP Seq (Instr Executable)
          {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }})%I.
  Proof.
    iIntros (Hrmap_dom HsubBounds Ha_post Hcgp_contiguous Himports_contiguous Hcgp_c Hrevoked_stack_C)
      "(#Hswitcher & #Hspec & Hna & Hj
      & HPC & HsPC & Hcgp & Hscgp & Hcsp & Hscsp & Hcra & Hscra
      & Hcs0 & Hscs0 & Hcs1 & Hscs1 & Hca0 & Hsca0 & Hca1 & Hsca1 & Hrmap
      & Himport_switcher & Hsimport_switcher & Himport_C_g & Hsimport_C_g
      & Hcode_main & Hscode_main
      & Hcgp_b & Hscgp_b & Hcgp_c & Hscgp_c & Hsecret_b & Hssecret_b
      & Hcsp_stk & Hscsp_stk
      & Hworld_interp_C & HK & Hcstk_frag & Hcstk_frag_spec
      & #Hinterp_Winit_C_g & #HentryC_g & #Hstack_revoked_C)".

    (* Extract the needed registers from the register map *)
    iExtractList "Hrmap" [ctp;ct0;ct1] as ["Hctp";"Hct0";"Hct1"].
    iDestruct "Hctp" as "(Hctp & Hsctp & ->)".
    iDestruct "Hct0" as "(Hct0 & Hsct0 & ->)".
    iDestruct "Hct1" as "(Hct1 & Hsct1 & ->)".

    (* --------------------------------------------------- *)
    (* --------------- BLOCK 4: PREP CALL ---------------- *)
    (* --------------------------------------------------- *)

    set (cgp_c := (cgp_b ^+ 1)%a).
    (* Expose the block structure of the code, for the block focusing *)
    rewrite /cmdc_conf_main_code.
    focus_block_nochangePC_lockstep 4 "Hscode_main" "Hcode_main" as a_prepC Ha_prepC
      "Hscode" "Hscls" "Hcode" "Hcls".
    assert (a_prepC = a_post) as ->.
    { rewrite /cmdc_conf_pre_B_code in Ha_post.
      simpl in Ha_post, Ha_prepC.
      solve_addr.
    }
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.

    (* Lea cgp 1%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: transitivity (Some cgp_c); auto; subst cgp_c; solve_addr.

    (* Store cgp 0%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: subst cgp_c; solve_addr.

    (* Mov ca0 cgp *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Lea cgp 1%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: transitivity (Some (cgp_b ^+ 2)%a); auto; subst cgp_c; solve_addr.

    (* Load ct0 cgp *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split; [done| solve_addr].

    (* Lea cgp (-2)%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: transitivity (Some cgp_b%a); auto; solve_addr.

    (* Store cgp ct0 *)
    iInstr_spec_lookup "Hscode" as "Hsi" "Hscode".
    iMod (step_store_success_reg _ _ _ _ _ _ _ _ _ _ _ RW
             with "[$HsPC $Hsi $Hsct0 $Hscgp $Hscgp_b $Hj]")
      as "(Hj & HsPC & Hsi & Hsct0 & Hscgp & Hscgp_b)"
    ; auto; try solve_pure.
    { solve_addr. }
    iSpecSeq.
    iSpecialize ("Hscode" with "[$]").
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_store_success_reg _ _ _ _ _ _ _ _ _ _ _
             with "[$HPC $Hi $Hct0 Hcgp $Hcgp_b]"); auto; try solve_pure.
    { solve_addr. }
    { by cbn. }
    iIntros "!> (HPC & Hi & Hct0 & Hcgp & Hcgp_b)".
    wp_pure.
    iSpecialize ("Hcode" with "[$]").

    (* GetA ct0 ca0 *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Add ct1 ct0 1%Z *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Subseg ca0 ct0 ct1 *)
    iInstr_lockstep "Hscode" "Hcode".
    1,3: transitivity (Some (cgp_c ^+1)%a); auto; subst cgp_c; solve_addr.
    1,2: subst cgp_c; solve_addr.

    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode_main" "Hcode_main".

    (* --------------------------------------------------- *)
    (* -------------- BLOCK 5 and 6: FETCH --------------- *)
    (* --------------------------------------------------- *)

    focus_block_lockstep 5 "Hscode_main" "Hcode_main" as a_fetch3 Ha_fetch3
      "Hscode" "Hscls" "Hcode" "Hcls".
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

    focus_block_lockstep 6 "Hscode_main" "Hcode_main" as a_fetch4 Ha_fetch4
      "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    iApply (fetch_spec_lockstep with
             "[- $Hspec $Hj $HPC $HsPC $Hct1 $Hsct1 $Hct0 $Hsct0 $Hcs0 $Hscs0 $Hcode $Hscode
                 $Himport_C_g $Hsimport_C_g]"); eauto.
    { solve_addr. }
    iNext ; iIntros "(Hj & HPC & HsPC & Hct1 & Hsct1 & Hct0 & Hsct0 & Hcs0 & Hscs0
                      & Hcode & Hscode & Himport_C_g & Hsimport_C_g)".
    iEval (cbn) in "Hct1".
    iEval (cbn) in "Hsct1".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode_main" "Hcode_main".

    (* --------------------------------------------------- *)
    (* ---------------- BLOCK 7: CALL C ------------------ *)
    (* --------------------------------------------------- *)

    focus_block_lockstep 7 "Hscode_main" "Hcode_main" as a_callC Ha_callC
      "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.

    (* Jalr cra ctp *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Relinquish [c] and prove that the capability pointing to it is safe to share *)
    iDestruct (big_sepL2_disjoint_pointsto with "[$Hcsp_stk $Hcgp_c]") as "%Hcgp_c_stk".

    iDestruct ( init_PermRes W_init_C C cgp_c RW interpC (WInt 0, WInt 0)
                with "[] [$Hcgp_c] [$Hscgp_c] []" ) as "Hcgp_c".
    { done. }
    { iApply future_priv_mono_interp_z. }
    { iApply interp_int. }
    iMod (world_interp_extend_perm with "Hworld_interp_C Hcgp_c")
      as "(Hworld_interp_C & Hrel_cgp_c)"; auto.

    set (W3 := (<s[cgp_c:=Permanent]s>W_init_C)).
    assert (related_sts_priv_world W_init_C W3) as HWinit_privC_W3.
    { subst W3; by eapply related_sts_priv_world_fresh_Permanent. }

    iAssert (interp W3 C (WCap RW Global cgp_c (cgp_c ^+ 1)%a cgp_c,
                          WCap RW Global cgp_c (cgp_c ^+ 1)%a cgp_c)) as "#Hinterp_W3_C_c".
    { iEval (rewrite interp_diag_eq // /interp1_diag /=).
      rewrite (finz_seq_between_cons cgp_c); last (subst cgp_c; solve_addr).
      rewrite (finz_seq_between_empty (cgp_c ^+ 1)%a); last (subst cgp_c; solve_addr).
      iApply big_sepL_singleton.
      iExists RW, interp.
      iEval (cbn).
      iSplit; first done.
      iSplit; first (iPureIntro ; by apply persistent_cond_interp).
      iSplit; first iFrame "Hrel_cgp_c".
      iSplit; first (iNext ; by iApply zcond_interp).
      iSplit; first (iNext ; by iApply rcond_interp).
      iSplit; first (iNext ; by iApply wcond_interp).
      subst W3.
      iSplit.
      + iApply (monoReq_interp _ _ _ _  Permanent); last done.
        by rewrite lookup_insert_eq.
      + iPureIntro.
        by rewrite lookup_insert_eq.
    }

    (* Prove that the adversary's entry point is safe to share *)
    iAssert (interp W3 C (WSealed ot_switcher C_g, WSealed ot_switcher C_g)) as "#Hinterp_W3_C_g".
    { iApply (interp_monotone_sd with "[%] Hinterp_Winit_C_g"); eauto. }

    (* Prepare the argument registers for the call to the adversary *)
    iExtractList "Hrmap" [ca2;ca3;ca4;ca5] as ["Hca2";"Hca3";"Hca4";"Hca5"].
    iDestruct "Hca2" as "(Hca2 & Hsca2 & ->)".
    iDestruct "Hca3" as "(Hca3 & Hsca3 & ->)".
    iDestruct "Hca4" as "(Hca4 & Hsca4 & ->)".
    iDestruct "Hca5" as "(Hca5 & Hsca5 & ->)".
    assert (ca1 ∉ dom_arg_rmap cmdc_conf_C_g_args) as Hca1_notin.
    { rewrite /cmdc_conf_C_g_args /dom_arg_rmap /=. set_solver. }
    iPoseProof (arg_rmap_interp W3 C cmdc_conf_C_g_args ca0 with "Hinterp_W3_C_c") as "Hi0".
    iPoseProof (arg_rmap_notin_interp W3 C cmdc_conf_C_g_args ca1 (wca1, swca1) Hca1_notin) as "Hi1".
    iPoseProof (arg_rmap_zero_interp W3 C cmdc_conf_C_g_args ca2) as "Hi2".
    iPoseProof (arg_rmap_zero_interp W3 C cmdc_conf_C_g_args ca3) as "Hi3".
    iPoseProof (arg_rmap_zero_interp W3 C cmdc_conf_C_g_args ca4) as "Hi4".
    iPoseProof (arg_rmap_zero_interp W3 C cmdc_conf_C_g_args ca5) as "Hi5".
    iPoseProof (arg_rmap_zero_interp W3 C cmdc_conf_C_g_args ct0) as "Hi6".
    iDestruct (arg_rmap_prepare W3 C cmdc_conf_C_g_args
                with "Hca0 Hsca0 Hi0 Hca1 Hsca1 Hi1 Hca2 Hsca2 Hi2 Hca3 Hsca3 Hi3
                      Hca4 Hsca4 Hi4 Hca5 Hsca5 Hi5 Hct0 Hsct0 Hi6")
      as "Hrmap_arg".

    (* The other registers *)
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap Hsrmap]".
    iDestruct (big_sepM_sep with "Hsrmap") as "[Hsrmap _]".
    iInsertList "Hrmap" [ctp].
    iInsertListSpec "Hsrmap" [ctp].

    (* Prepare the stack resources required by the cross-compartment call specification *)
    assert ( revoked_addresses W3 (finz.seq_between csp_b csp_e) ) as Hrevoked_stack_C_W3.
    { rewrite /revoked_addresses Forall_forall.
      rewrite /revoked_addresses Forall_forall in Hrevoked_stack_C.
      intros a Ha; cbn in *.
      rewrite lookup_insert_ne; last (intros ->; set_solver+Hcgp_c_stk Ha).
      by apply Hrevoked_stack_C.
    }
    iDestruct (StackRevokedResources_mono_priv with "Hstack_revoked_C") as "Hstack_revoked_C'"; eauto.

    iApply (switcher_cc_specification_diag _ W3 C with
             "[- $Hswitcher $Hspec $Hna $Hj
              $HPC $HsPC $Hcgp $Hscgp $Hcra $Hscra $Hcsp $Hscsp $Hct1 $Hsct1
              $Hcs0 $Hscs0 $Hcs1 $Hscs1 $Hrmap $Hsrmap $Hrmap_arg
              $Hcsp_stk $Hscsp_stk $Hworld_interp_C $Hstack_revoked_C'
              $Hcstk_frag $Hcstk_frag_spec
              $Hinterp_W3_C_g $HentryC_g $HK]"); eauto; iFrame "%".
    { repeat first [rewrite dom_insert_L | rewrite dom_delete_L].
      rewrite Hrmap_dom; set_solver. }
    { repeat first [rewrite dom_insert_L | rewrite dom_delete_L].
      rewrite Hrmap_dom; set_solver. }
    { apply is_arg_rmap_of. }
    { apply is_arg_rmap_of. }

    iNext.
    iIntros (W4_C rmap' stk_mem' stk_mem_spec' l')
      "( _ & _ & _ & _ & _ & _ & _ & _
      & Hna & Hj & _ & _ & _ & _
      & HPC & HsPC
      & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _)".
    iEval (cbn) in "HPC".
    iEval (cbn) in "HsPC".

    (* Halt *)
    iInstr_spec_lookup "Hscode" as "Hsi" "Hscode".
    iMod (step_halt with "[$Hspec $Hj $HsPC $Hsi]") as "(Hj & HsPC & Hsi)";
      [solve_ndisj|solve_pure|solve_pure|].
    iSpecialize ("Hscode" with "Hsi").
    (* Halt *)
    iInstr "Hcode".
    wp_end.
    iIntros "_".
    iFrame.
  Qed.

End CMDC_post_B.
