From iris.proofmode Require Import proofmode.
From griotte Require Import sts_multiple_updates.
From griotte Require Import logrel_binary interp_weakening_binary monotone_binary.
From griotte Require Import region_invariants_revocation_binary.
From griotte Require Import rules proofmode proofmode_binary register_tactics_binary map_simpl.
From griotte Require Import world_ghost_theory_binary world_interp_stack_binary stack_world_resources_binary.
From griotte Require Import switcher_preamble_binary switcher_spec_call_binary.
From griotte Require Import fetch_spec_binary switcher_spec_call_diag_binary.
From griotte Require Import cmdc_binary cmdc_spec_post_B_binary.

(** * Binary specification of the CMDC confidentiality example

    Both runs execute [cmdc_conf_main_code], with different secrets in the
    private data of [main] ([secret_b1], [secret_c1] in the implementation
    run, [secret_b2], [secret_c2] in the specification run).

    [main] stores [secret_c] into [c], and calls [B.f] with a capability to
    [b]. The cell [b] is shared with [B] as a permanent region of the world
    of [B]. After [B.f] returns, [main] opens the world of [B] at [b] and
    keeps it open: [B] does not run anymore, and [main] owns the points-to
    of [b]. The rest of the execution is specified by [cmdc_spec_post_B]. *)

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
    codefrag_facts "Hcode_main".
    rewrite /cmdc_conf_main_data /= in Hcgp_contiguous.
    rewrite /cmdc_conf_main_imports /= in Himports_contiguous.
    iDestruct (big_sepL2_length with "Hcsp_stk") as "%Hlen_stack".

    (* Extract the needed registers from the register map *)
    iExtractList "Hrmap" [ca0;ctp;ct0;ct1;cs0;cs1;cra]
      as ["Hca0";"Hctp";"Hct0";"Hct1";"Hcs0";"Hcs1";"Hcra"].
    iDestruct "Hca0" as "(Hca0 & Hsca0 & ->)".
    iDestruct "Hctp" as "(Hctp & Hsctp & ->)".
    iDestruct "Hct0" as "(Hct0 & Hsct0 & ->)".
    iDestruct "Hct1" as "(Hct1 & Hsct1 & ->)".
    iDestruct "Hcs0" as "(Hcs0 & Hscs0 & ->)".
    iDestruct "Hcs1" as "(Hcs1 & Hscs1 & ->)".
    iDestruct "Hcra" as "(Hcra & Hscra & ->)".

    (* Extract the addresses of b, c, secret_b and secret_c, in both runs *)
    iDestruct (region_pointsto_cons with "Hcgp_main") as "[Hcgp_b Hcgp_main]".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Hcgp_main") as "[Hcgp_c Hcgp_main]".
    { transitivity (Some (cgp_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Hcgp_main") as "[Hsecret_b Hcgp_main]".
    { transitivity (Some (cgp_b ^+ 3)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Hcgp_main") as "[Hsecret_c _]".
    { transitivity (Some (cgp_b ^+ 4)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (spec_region_pointsto_cons with "Hscgp_main") as "[Hscgp_b Hscgp_main]".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (spec_region_pointsto_cons with "Hscgp_main") as "[Hscgp_c Hscgp_main]".
    { transitivity (Some (cgp_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (spec_region_pointsto_cons with "Hscgp_main") as "[Hssecret_b Hscgp_main]".
    { transitivity (Some (cgp_b ^+ 3)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (spec_region_pointsto_cons with "Hscgp_main") as "[Hssecret_c _]".
    { transitivity (Some (cgp_b ^+ 4)%a); auto; solve_addr. }
    { solve_addr. }

    (* Extract the imports, in both runs *)
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_switcher Himports_main]".
    { transitivity (Some (pc_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_B_f Himports_main]".
    { transitivity (Some (pc_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_C_g _]".
    { transitivity (Some (pc_b ^+ 3)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (spec_region_pointsto_cons with "Hsimports_main") as "[Hsimport_switcher Hsimports_main]".
    { transitivity (Some (pc_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (spec_region_pointsto_cons with "Hsimports_main") as "[Hsimport_B_f Hsimports_main]".
    { transitivity (Some (pc_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (spec_region_pointsto_cons with "Hsimports_main") as "[Hsimport_C_g _]".
    { transitivity (Some (pc_b ^+ 3)%a); auto; solve_addr. }
    { solve_addr. }


    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 0 : INIT ------------------ *)
    (* --------------------------------------------------- *)

    focus_block_0_lockstep "Hscode_main" "Hcode_main" as "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.

    (* Lea cgp 3%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: transitivity (Some (cgp_b ^+ 3)%a); auto; solve_addr.

    (* Load ct0 cgp *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split; [done| solve_addr].
    iEval (cbn) in "Hct0"; iEval (cbn) in "Hsct0".

    (* Lea cgp (-2)%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr.

    (* Store cgp ct0 *)
    iInstr_spec_lookup "Hscode" as "Hsi" "Hscode".
    iMod (step_store_success_reg _ _ _ _ _ _ _ _ _ _ _ RW
             with "[$HsPC $Hsi $Hsct0 $Hscgp $Hscgp_c $Hj]")
      as "(Hj & HsPC & Hsi & Hsct0 & Hscgp & Hscgp_c)"
    ; auto; try solve_pure.
    { solve_addr. }
    iSpecSeq.
    iSpecialize ("Hscode" with "[$]").
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_store_success_reg _ _ _ _ _ _ _ _ _ _ _
             with "[$HPC $Hi $Hct0 Hcgp $Hcgp_c]"); auto; try solve_pure.
    { solve_addr. }
    { by cbn. }
    iIntros "!> (HPC & Hi & Hct0 & Hcgp & Hcgp_c)".
    wp_pure.
    iSpecialize ("Hcode" with "[$]").

    (* Lea cgp (-1)%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: transitivity (Some cgp_b%a); auto; solve_addr.

    (* Store cgp 0%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: solve_addr.

    (* Mov ca0 cgp *)
    iInstr_lockstep "Hscode" "Hcode".

    (* GetA ct0 ca0 *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Add ct1 ct0 1%Z *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Subseg ca0 ct0 ct1 *)
    iInstr_lockstep "Hscode" "Hcode".
    1,3: transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr.
    1,2: solve_addr.

    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode_main" "Hcode_main".

    (* --------------------------------------------------- *)
    (* -------------- BLOCK 1 and 2 : FETCH -------------- *)
    (* --------------------------------------------------- *)

    focus_block_lockstep 1 "Hscode_main" "Hcode_main" as a_fetch1 Ha_fetch1
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

    focus_block_lockstep 2 "Hscode_main" "Hcode_main" as a_fetch2 Ha_fetch2
      "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    iApply (fetch_spec_lockstep with
             "[- $Hspec $Hj $HPC $HsPC $Hct1 $Hsct1 $Hct0 $Hsct0 $Hcs0 $Hscs0 $Hcode $Hscode
                 $Himport_B_f $Hsimport_B_f]"); eauto.
    { solve_addr. }
    iNext ; iIntros "(Hj & HPC & HsPC & Hct1 & Hsct1 & Hct0 & Hsct0 & Hcs0 & Hscs0
                      & Hcode & Hscode & Himport_B_f & Hsimport_B_f)".
    iEval (cbn) in "Hct1".
    iEval (cbn) in "Hsct1".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode_main" "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 3: CALL B ----------------- *)
    (* --------------------------------------------------- *)

    focus_block_lockstep 3 "Hscode_main" "Hcode_main" as a_callB Ha_callB
      "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.

    (* Jalr cra ctp *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Relinquish [b] and prove that the capability pointing to it is safe to share *)
    iDestruct (big_sepL2_disjoint_pointsto with "[$Hcsp_stk $Hcgp_b]") as "%Hcgp_b_stk".
    assert ( cgp_b ∉ finz.seq_between (csp_b ^+ 4)%a csp_e ) as Hcgp_b_stk'.
    { clear -Hcgp_b_stk.
      apply not_elem_of_finz_seq_between.
      apply not_elem_of_finz_seq_between in Hcgp_b_stk.
      destruct Hcgp_b_stk; [left|right]; solve_addr.
    }

    iDestruct ( init_PermRes W_init_B B cgp_b RW interpC (WInt 0, WInt 0)
                with "[] [$Hcgp_b] [$Hscgp_b] []" ) as "Hcgp_b".
    { done. }
    { iApply future_priv_mono_interp_z. }
    { iApply interp_int. }
    iMod (world_interp_extend_perm with "Hworld_interp_B Hcgp_b")
      as "(Hworld_interp_B & #Hrel_cgp_b)"; auto.

    set (W1 := (<s[cgp_b:=Permanent]s>W_init_B)).
    assert (related_sts_priv_world W_init_B W1) as HWinit_privB_W1.
    { subst W1; eapply related_sts_priv_world_fresh_Permanent. }

    iAssert (interp W1 B (WCap RW Global cgp_b (cgp_b ^+ 1)%a cgp_b,
                          WCap RW Global cgp_b (cgp_b ^+ 1)%a cgp_b)) as "#Hinterp_W1_B_b".
    { iEval (rewrite interp_diag_eq // /interp1_diag /=).
      rewrite (finz_seq_between_cons cgp_b); last solve_addr.
      rewrite (finz_seq_between_empty (cgp_b ^+ 1)%a); last solve_addr.
      iApply big_sepL_singleton.
      iExists RW, interp.
      iEval (cbn).
      iSplit; first done.
      iSplit; first (iPureIntro ; by apply persistent_cond_interp).
      iSplit; first iFrame "Hrel_cgp_b".
      iSplit; first (iNext ; by iApply zcond_interp).
      iSplit; first (iNext ; by iApply rcond_interp).
      iSplit; first (iNext ; by iApply wcond_interp).
      subst W1.
      iSplit.
      + iApply (monoReq_interp _ _ _ _  Permanent); last done.
        rewrite /std_update.
        by rewrite lookup_insert_eq.
      + iPureIntro.
        by rewrite lookup_insert_eq.
    }

    (* Prove that the adversary's entry point is safe to share *)
    iAssert (interp W1 B (WSealed ot_switcher B_f, WSealed ot_switcher B_f)) as "#Hinterp_W1_B_f".
    { iApply (interp_monotone_sd with "[%] Hinterp_Winit_B_f"); eauto. }

    (* Prepare the argument registers for the call to the adversary *)
    iExtractList "Hrmap" [ca1;ca2;ca3;ca4;ca5] as ["Hca1";"Hca2";"Hca3";"Hca4";"Hca5"].
    iDestruct "Hca1" as "(Hca1 & Hsca1 & ->)".
    iDestruct "Hca2" as "(Hca2 & Hsca2 & ->)".
    iDestruct "Hca3" as "(Hca3 & Hsca3 & ->)".
    iDestruct "Hca4" as "(Hca4 & Hsca4 & ->)".
    iDestruct "Hca5" as "(Hca5 & Hsca5 & ->)".
    iPoseProof (arg_rmap_interp W1 B cmdc_conf_B_f_args ca0 with "Hinterp_W1_B_b") as "Hi0".
    iPoseProof (arg_rmap_zero_interp W1 B cmdc_conf_B_f_args ca1) as "Hi1".
    iPoseProof (arg_rmap_zero_interp W1 B cmdc_conf_B_f_args ca2) as "Hi2".
    iPoseProof (arg_rmap_zero_interp W1 B cmdc_conf_B_f_args ca3) as "Hi3".
    iPoseProof (arg_rmap_zero_interp W1 B cmdc_conf_B_f_args ca4) as "Hi4".
    iPoseProof (arg_rmap_zero_interp W1 B cmdc_conf_B_f_args ca5) as "Hi5".
    iPoseProof (arg_rmap_zero_interp W1 B cmdc_conf_B_f_args ct0) as "Hi6".
    iDestruct (arg_rmap_prepare W1 B cmdc_conf_B_f_args
                with "Hca0 Hsca0 Hi0 Hca1 Hsca1 Hi1 Hca2 Hsca2 Hi2 Hca3 Hsca3 Hi3
                      Hca4 Hsca4 Hi4 Hca5 Hsca5 Hi5 Hct0 Hsct0 Hi6")
      as "Hrmap_arg".

    (* The other registers *)
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap Hsrmap]".
    iDestruct (big_sepM_sep with "Hsrmap") as "[Hsrmap _]".
    iInsertList "Hrmap" [ctp].
    iInsertListSpec "Hsrmap" [ctp].

    (* Prepare the stack resources required by the cross-compartment call specification *)
    assert ( revoked_addresses W1 (finz.seq_between csp_b csp_e) ) as Hrevoked_stack_B_W1.
    { rewrite /revoked_addresses Forall_forall.
      rewrite /revoked_addresses Forall_forall in Hrevoked_stack_B.
      intros a Ha; cbn in *.
      rewrite lookup_insert_ne; last (intros ->; set_solver+Hcgp_b_stk Ha).
      by apply Hrevoked_stack_B.
    }
    iDestruct (StackRevokedResources_mono_priv with "Hstack_revoked_B") as "Hstack_revoked_B_W1"; eauto.

    iApply (switcher_cc_specification_diag _ W1 B with
             "[- $Hswitcher $Hspec $Hna $Hj
              $HPC $HsPC $Hcgp $Hscgp $Hcra $Hscra $Hcsp $Hscsp $Hct1 $Hsct1
              $Hcs0 $Hscs0 $Hcs1 $Hscs1 $Hrmap $Hsrmap $Hrmap_arg
              $Hcsp_stk $Hscsp_stk $Hworld_interp_B $Hstack_revoked_B_W1
              $Hcstk_frag $Hcstk_frag_spec
              $Hinterp_W1_B_f $HentryB_f $HK]"); eauto; iFrame "%".
    { repeat first [rewrite dom_insert_L | rewrite dom_delete_L].
      rewrite Hrmap_dom; set_solver. }
    { repeat first [rewrite dom_insert_L | rewrite dom_delete_L].
      rewrite Hrmap_dom; set_solver. }
    { apply is_arg_rmap_of. }
    { apply is_arg_rmap_of. }

    iNext.
    iIntros (W2_B rmap' stk_mem' stk_mem_spec' l')
      "( _ & _ & _
      & %HW1_pubB_W2 & _ & %Hdom_rmap' & _ & _
      & Hna & Hj & %Hcsp_bounds
      & Hworld_interp_B & Hcstk_frag & Hcstk_frag_spec
      & HPC & HsPC & Hcgp & Hscgp & Hcra & Hscra & Hcs0 & Hscs0 & Hcs1 & Hscs1 & Hcsp & Hscsp
      & [%warg0 (Hca0 & Hsca0 & _)] & [%warg1 (Hca1 & Hsca1 & _)]
      & Hrmap & Hcsp_stk & Hscsp_stk & HK)".
    iEval (cbn) in "HPC".
    iEval (cbn) in "HsPC".

    (* We open the world of B at [b], to get its points-to predicates in both runs.
       The address [b] is still Permanent, as public future worlds preserve
       Permanent regions. The world of B stays open: B does not run anymore. *)
    assert (std W2_B !! cgp_b = Some Permanent) as HW2_B_cgp_b.
    { eapply region_state_pub_perm in HW1_pubB_W2; eauto.
      subst W1.
      rewrite std_update_multiple_insert_commute; last done.
      rewrite !lookup_insert_eq; done.
    }

    rewrite (open_world_interp_empty _ B).
    iDestruct (
       open_world_interp_permanent with "[$Hworld_interp_B] [$Hrel_cgp_b]"
      ) as "(_ & _ & [%v Hcgp_b] )"; auto.
    { set_solver+. }
    {
      eapply (region_state_priv_perm W2_B); eauto.
      eapply revoke_related_sts_priv_world.
    }
    iEval (cbn) in "Hcgp_b".
    iDestruct (PermRes_acc with "Hcgp_b") as "[ (>Hcgp_b & >Hscgp_b & _) _]".

    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode_main" "Hcode_main".

    (* --------------------------------------------------- *)
    (* -------- BLOCKS 4 to 7: AFTER THE CALL TO B ------- *)
    (* --------------------------------------------------- *)

    assert ((pc_a + length cmdc_conf_pre_B_code)%a = Some (a_callB ^+ 1)%a) as Ha_post.
    { rewrite /cmdc_conf_pre_B_code.
      simpl in Ha_callB |- *.
      solve_addr.
    }

    iApply (cmdc_spec_post_B
              pc_b pc_e pc_a (a_callB ^+ 1)%a cgp_b cgp_e csp_b csp_e rmap' C_g W_init_C
              stk Ws Cs _ _ _ _ _ _ _ _ _ _ _ secret_b1 secret_b2 Nswitcher
              Hdom_rmap' HsubBounds Ha_post Hcgp_contiguous Himports_contiguous Hcgp_c Hrevoked_stack_C
             with "[$Hswitcher $Hspec $Hna $Hj
                    $HPC $HsPC $Hcgp $Hscgp $Hcsp $Hscsp $Hcra $Hscra
                    $Hcs0 $Hscs0 $Hcs1 $Hscs1 $Hca0 $Hsca0 $Hca1 $Hsca1 $Hrmap
                    $Himport_switcher $Hsimport_switcher $Himport_C_g $Hsimport_C_g
                    $Hcode_main $Hscode_main
                    $Hcgp_b $Hscgp_b $Hcgp_c $Hscgp_c $Hsecret_b $Hssecret_b
                    $Hcsp_stk $Hscsp_stk
                    $Hworld_interp_C $HK $Hcstk_frag $Hcstk_frag_spec
                    $Hinterp_Winit_C_g $HentryC_g $Hstack_revoked_C]").
  Qed.

End CMDC.
