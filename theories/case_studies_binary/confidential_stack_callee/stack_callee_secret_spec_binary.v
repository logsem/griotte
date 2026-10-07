From iris.proofmode Require Import proofmode.
From griotte Require Import sts_multiple_updates.
From griotte Require Import logrel_binary interp_weakening_binary monotone_binary.
From griotte Require Import region_invariants_revocation_binary.
From griotte Require Import rules proofmode proofmode_binary register_tactics_binary map_simpl.
From griotte Require Import world_ghost_theory_binary world_interp_stack_binary stack_world_resources_binary.
From griotte Require Import switcher_preamble_binary switcher_spec_return_binary.
From griotte Require Import stack_callee_secret_binary.

(** * Binary specification of the entry point of the trusted callee

    Both runs execute [stack_callee_secret_code], with a different secret in
    the private data of the trusted compartment [T] ([secret1] in the
    implementation run, [secret2] in the specification run). The code, the
    imports and the private data of [T] are kept in a non-atomic invariant,
    because [T.f] can be called at any time by the adversary.

    [T.f] satisfies the entry-point predicate of the switcher
    ([execute_entry_point]): it writes the secret at the base of its stack
    frame, and returns through the switcher, whose return path clears this
    frame. The specification of [T.f] holds in any world, for any caller. *)

Section Stack_callee_secret_f.
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

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (** The resources of [T] that are never shared: its imports and code, the
      same in both runs, and its private data, the secret of each run. *)
  Definition stack_callee_secret_inv
    (pc_b pc_a cgp_b : Addr) (B_adv : Sealable) (secret1 secret2 : Z) : iProp Σ :=
    [[ pc_b , pc_a ]] ↦ₐ [[ stack_callee_secret_imports B_adv ]]
    ∗ [[ pc_b , pc_a ]] ↣ₐ [[ stack_callee_secret_imports B_adv ]]
    ∗ codefrag pc_a stack_callee_secret_code
    ∗ spec_codefrag pc_a stack_callee_secret_code
    ∗ cgp_b ↦ₐ WInt secret1
    ∗ cgp_b ↣ₐ WInt secret2.

  (** [T.f] is a valid entry point, in any world [W] and for any caller [C]. *)
  Lemma stack_callee_secret_f_spec
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (B_adv : Sealable)
    (secret1 secret2 : Z)
    (W : WORLD) (C : CmptName)
    (Nswitcher TN : namespace)
    :
    SubBounds pc_b pc_e pc_a (pc_a ^+ length stack_callee_secret_code)%a ->
    (pc_b + length (stack_callee_secret_imports B_adv))%a = Some pc_a ->
    (cgp_b + length (stack_callee_secret_data secret1))%a = Some cgp_e ->

    na_inv cerise_nais Nswitcher switcher_inv_binary
    ∗ na_inv cerise_nais TN (stack_callee_secret_inv pc_b pc_a cgp_b B_adv secret1 secret2)
    ⊢ execute_entry_point
        (WCap RX Global pc_b pc_e (pc_b ^+ Z.of_nat stack_callee_secret_f_offset)%a,
         WCap RX Global pc_b pc_e (pc_b ^+ Z.of_nat stack_callee_secret_f_offset)%a)
        (WCap RW Global cgp_b cgp_e cgp_b, WCap RW Global cgp_b cgp_e cgp_b)
        stack_callee_secret_f_args W C.
  Proof.
    iIntros (HsubBounds Himports_contiguous Hcgp_contiguous) "[#Hswitcher #HT]".
    iIntros (stk Ws Cs regs1 regs2 a_stk e_stk)
      "(#Hspec & HK & %Hframe_match
       & ( %Hfullmap1 & %Hfullmap2 & %Hregs_pc1 & %Hregs_pc2
         & %Hregs_cgp1 & %Hregs_cgp2 & %Hregs_cra1 & %Hregs_cra2
         & %Hregs_csp1 & %Hregs_csp2 & #Hinterp_csp & _ & _ & _)
       & Hrmap & Hsmap & Hj & Hworld_interp & %Hcsp_sync
       & Hcstk_frag & Hcstk_frag_spec & Hna)".
    cbn [fst snd] in Hfullmap1, Hfullmap2, Hregs_pc1, Hregs_pc2, Hregs_cgp1, Hregs_cgp2,
      Hregs_cra1, Hregs_cra2, Hregs_csp1, Hregs_csp2.
    pose proof (regmap_full_dom _ Hfullmap1) as Hdom1.
    pose proof (regmap_full_dom _ Hfullmap2) as Hdom2.
    rewrite /interp_conf /registers_pointsto /spec_registers_pointsto.
    rewrite /stack_callee_secret_inv.
    rewrite /stack_callee_secret_data /= in Hcgp_contiguous.
    assert (length (stack_callee_secret_imports B_adv) = 2) as Himports_len by reflexivity.
    rewrite Himports_len in Himports_contiguous.
    set (csp_b := (a_stk ^+ 4)%a).

    (* Extract the registers, in both runs *)
    iDestruct (big_sepM_delete _ _ PC with "Hrmap") as "[HPC Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cgp with "Hrmap") as "[Hcgp Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ csp with "Hrmap") as "[Hcsp Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cra with "Hrmap") as "[Hcra Hrmap]"; first by simplify_map_eq.
    destruct (Hfullmap1 ct0) as [wct0 Hwct0].
    iDestruct (big_sepM_delete _ _ ct0 with "Hrmap") as "[Hct0 Hrmap]"; first by simplify_map_eq.
    destruct (Hfullmap1 ca0) as [wca0 Hwca0].
    iDestruct (big_sepM_delete _ _ ca0 with "Hrmap") as "[Hca0 Hrmap]"; first by simplify_map_eq.
    destruct (Hfullmap1 ca1) as [wca1 Hwca1].
    iDestruct (big_sepM_delete _ _ ca1 with "Hrmap") as "[Hca1 Hrmap]"; first by simplify_map_eq.
    destruct (Hfullmap1 cnull) as [wcnull Hwcnull].
    iDestruct (big_sepM_delete _ _ cnull with "Hrmap") as "[Hcnull Hrmap]"; first by simplify_map_eq.

    iDestruct (big_sepM_delete _ _ PC with "Hsmap") as "[HsPC Hsmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cgp with "Hsmap") as "[Hscgp Hsmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ csp with "Hsmap") as "[Hscsp Hsmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cra with "Hsmap") as "[Hscra Hsmap]"; first by simplify_map_eq.
    destruct (Hfullmap2 ct0) as [swct0 Hswct0].
    iDestruct (big_sepM_delete _ _ ct0 with "Hsmap") as "[Hsct0 Hsmap]"; first by simplify_map_eq.
    destruct (Hfullmap2 ca0) as [swca0 Hswca0].
    iDestruct (big_sepM_delete _ _ ca0 with "Hsmap") as "[Hsca0 Hsmap]"; first by simplify_map_eq.
    destruct (Hfullmap2 ca1) as [swca1 Hswca1].
    iDestruct (big_sepM_delete _ _ ca1 with "Hsmap") as "[Hsca1 Hsmap]"; first by simplify_map_eq.
    destruct (Hfullmap2 cnull) as [swcnull Hswcnull].
    iDestruct (big_sepM_delete _ _ cnull with "Hsmap") as "[Hscnull Hsmap]"; first by simplify_map_eq.

    (* Open the invariant of T *)
    iMod (na_inv_acc with "HT Hna")
      as "((>Himports_main & >Hsimports_main & >Hcode_main & >Hscode_main & >Hsecret & >Hssecret)
          & Hna & HT_close)"; auto.
    codefrag_facts "Hcode_main".

    (* Revoke the world to get the stack frame of T.f, in both runs *)
    iMod (world_interp_revoke_stack with "[$Hinterp_csp $Hworld_interp]")
      as (l) "(%Hl_unk & Hworld_interp & _ & _
              & >(%stk_mem & %stk_mem_spec & Hstk & Hsstk) & Hrevoked_l & _)".

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)

    (* Unfold the code, so that the focusing tactics see its two blocks *)
    rewrite /stack_callee_secret_code.
    focus_block_nochangePC_lockstep 1 "Hscode_main" "Hcode_main" as a_f Ha_f
      "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    assert ((pc_b ^+ Z.of_nat stack_callee_secret_f_offset)%a = a_f) as Hpc_f.
    { assert (length (stack_callee_secret_imports (SCap RO Global za za za)) = 2)
        as Himports_len' by reflexivity.
      rewrite /stack_callee_secret_f_offset Himports_len'.
      solve_addr. }
    rewrite Hpc_f.

    (* Load ct0 cgp *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split; [done| solve_addr].

    (* The stack frame of T.f may be empty: the Store then fails in the
       implementation run *)
    destruct (decide (csp_b < e_stk)%a) as [Hcsp_size|Hcsp_size]; cycle 1.
    { (* Store csp ct0 *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg with "[$HPC $Hi $Hct0 $Hcsp]") ; try solve_pure.
      { rewrite /withinBounds; subst csp_b; solve_addr. }
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr"; done.
    }
    iDestruct (big_sepL2_length with "Hstk") as %Hstklen.
    iDestruct (big_sepL2_length with "Hsstk") as %Hsstklen.
    rewrite finz_seq_between_length in Hstklen.
    rewrite finz_seq_between_length in Hsstklen.
    rewrite finz_dist_S in Hstklen; last solve_addr+Hcsp_size.
    rewrite finz_dist_S in Hsstklen; last solve_addr+Hcsp_size.
    destruct stk_mem as [|w0 stk_mem]; simplify_eq.
    destruct stk_mem_spec as [|sw0 stk_mem_spec]; simplify_eq.
    assert (is_Some (csp_b + 1)%a) as [a_stk1 Hastk1];[solve_addr+Hcsp_size|].
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha_stk Hstk]"; eauto.
    { solve_addr+Hcsp_size Hastk1. }
    iDestruct (spec_region_pointsto_cons with "Hsstk") as "[Hsa_stk Hsstk]"; eauto.
    { solve_addr+Hcsp_size Hastk1. }

    (* Store csp ct0 *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: rewrite /withinBounds; subst csp_b; solve_addr.

    (* Mov ca0 0 *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Mov ca1 0 *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Jalr cnull cra *)
    iInstr_lockstep "Hscode" "Hcode".

    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode_main" "Hcode_main".
    iEval (cbn) in "HPC".
    iEval (cbn) in "HsPC".

    (* Close the invariant of T *)
    iMod ("HT_close" with
           "[$Hna $Himports_main $Hsimports_main $Hcode_main $Hscode_main $Hsecret $Hssecret]")
      as "Hna".

    (* Put the registers back in the register maps *)
    iInsertList "Hrmap" [cra;cgp;ct0;cnull].
    iInsertListSpec "Hsmap" [cra;cgp;ct0;cnull].

    (* Reassemble the stack frames, which now contain the secrets *)
    iDestruct (region_pointsto_cons with "[$Ha_stk $Hstk]") as "Hstk".
    { exact Hastk1. }
    { subst csp_b; solve_addr+Hastk1 Hcsp_size. }
    iDestruct (spec_region_pointsto_cons with "[$Hsa_stk $Hsstk]") as "Hsstk".
    { exact Hastk1. }
    { subst csp_b; solve_addr+Hastk1 Hcsp_size. }

    (* Return to the caller *)
    iApply (switcher_ret_specification _ W (revoke W) C _ _ e_stk csp_b l _ _ stk Ws Cs
              (WInt 0, WInt 0) (WInt 0, WInt 0)
             with
             "[$Hswitcher $Hspec $Hstk $Hsstk $Hcstk_frag $Hcstk_frag_spec $HK $Hworld_interp
               $Hna $Hj $HPC $HsPC $Hrevoked_l $Hrmap $Hsmap
               $Hca0 $Hsca0 $Hca1 $Hsca1 $Hcsp $Hscsp]"); auto.
    { apply related_pub_revoke_close_list.
      destruct Hl_unk; auto.
    }
    { repeat (rewrite dom_insert_L).
      repeat (rewrite dom_delete_L).
      rewrite Hdom1; set_solver+.
    }
    { repeat (rewrite dom_insert_L).
      repeat (rewrite dom_delete_L).
      rewrite Hdom2; set_solver+.
    }
    { subst csp_b.
      destruct Hcsp_sync as [Hcsp_sync <-].
      auto.
    }
    { destruct Hl_unk; auto. }
    { intros a; destruct Hl_unk as [_ Hl_unk]; destruct (Hl_unk a); auto. }
    { iSplit; iApply interp_int. }
  Qed.

  (** The entry point [T.f], sealed by the switcher, satisfies the sealing
      predicate of the switcher. *)
  Lemma stack_callee_secret_f_ot_switcher_prop
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (b_tbl e_tbl : Addr) (g_tbl : Locality)
    (B_adv : Sealable)
    (secret1 secret2 : Z)
    (W : WORLD) (C : CmptName)
    (Nswitcher TN : namespace)
    :
    (b_tbl <= b_tbl ^+ 2 < e_tbl)%a ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length stack_callee_secret_code)%a ->
    (pc_b + length (stack_callee_secret_imports B_adv))%a = Some pc_a ->
    (cgp_b + length (stack_callee_secret_data secret1))%a = Some cgp_e ->

    na_inv cerise_nais Nswitcher switcher_inv_binary
    ∗ na_inv cerise_nais TN (stack_callee_secret_inv pc_b pc_a cgp_b B_adv secret1 secret2)
    ∗ inv (export_table_PCCN TN)
        (b_tbl ↦ₐ WCap RX Global pc_b pc_e pc_b ∗ b_tbl ↣ₐ WCap RX Global pc_b pc_e pc_b)
    ∗ inv (export_table_CGPN TN)
        ((b_tbl ^+ 1)%a ↦ₐ WCap RW Global cgp_b cgp_e cgp_b
         ∗ (b_tbl ^+ 1)%a ↣ₐ WCap RW Global cgp_b cgp_e cgp_b)
    ∗ inv (export_table_entryN TN (b_tbl ^+ 2)%a)
        ((b_tbl ^+ 2)%a ↦ₐ stack_callee_secret_exp_tbl_entry_f
         ∗ (b_tbl ^+ 2)%a ↣ₐ stack_callee_secret_exp_tbl_entry_f)
    ∗ WSealed ot_switcher (SCap RO g_tbl b_tbl e_tbl (b_tbl ^+ 2)%a) ↦□ₑ stack_callee_secret_f_args
    -∗
    ot_switcher_prop W C
      (WCap RO g_tbl b_tbl e_tbl (b_tbl ^+ 2)%a, WCap RO g_tbl b_tbl e_tbl (b_tbl ^+ 2)%a).
  Proof.
    iIntros (Htbl_size HsubBounds Himports_contiguous Hcgp_contiguous)
      "(#Hswitcher & #HT & #Htbl_pcc & #Htbl_cgp & #Htbl_f & #Hentry_f)".
    rewrite /stack_callee_secret_exp_tbl_entry_f.
    iExists g_tbl, b_tbl, e_tbl, (b_tbl ^+ 2)%a, pc_b, pc_e, cgp_b, cgp_e,
      stack_callee_secret_f_args, (Z.of_nat stack_callee_secret_f_offset), TN.
    iFrame "#".
    iSplit ; first (by iPureIntro).
    iSplit ; first (by iPureIntro).
    iSplit ; first (iPureIntro; solve_addr).
    iSplit ; first (iPureIntro; solve_addr).
    iSplit ; first (iPureIntro; solve_addr).
    iSplit ; first (iPureIntro; rewrite /stack_callee_secret_f_args; lia).
    iIntros "!> %W' %Hrelated !>".
    iApply (stack_callee_secret_f_spec pc_b pc_e pc_a cgp_b cgp_e B_adv secret1 secret2
              W' C Nswitcher TN with "[$Hswitcher $HT]"); eauto.
  Qed.

  (** The entry point [T.f], sealed by the switcher, is safe to share with
      the adversary. *)
  Lemma stack_callee_secret_f_interp
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (b_tbl e_tbl : Addr)
    (B_adv : Sealable)
    (secret1 secret2 : Z)
    (W : WORLD) (C : CmptName)
    (Nswitcher TN : namespace)
    :
    (b_tbl <= b_tbl ^+ 2 < e_tbl)%a ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length stack_callee_secret_code)%a ->
    (pc_b + length (stack_callee_secret_imports B_adv))%a = Some pc_a ->
    (cgp_b + length (stack_callee_secret_data secret1))%a = Some cgp_e ->

    na_inv cerise_nais Nswitcher switcher_inv_binary
    ∗ na_inv cerise_nais TN (stack_callee_secret_inv pc_b pc_a cgp_b B_adv secret1 secret2)
    ∗ inv (export_table_PCCN TN)
        (b_tbl ↦ₐ WCap RX Global pc_b pc_e pc_b ∗ b_tbl ↣ₐ WCap RX Global pc_b pc_e pc_b)
    ∗ inv (export_table_CGPN TN)
        ((b_tbl ^+ 1)%a ↦ₐ WCap RW Global cgp_b cgp_e cgp_b
         ∗ (b_tbl ^+ 1)%a ↣ₐ WCap RW Global cgp_b cgp_e cgp_b)
    ∗ inv (export_table_entryN TN (b_tbl ^+ 2)%a)
        ((b_tbl ^+ 2)%a ↦ₐ stack_callee_secret_exp_tbl_entry_f
         ∗ (b_tbl ^+ 2)%a ↣ₐ stack_callee_secret_exp_tbl_entry_f)
    ∗ WSealed ot_switcher (SCap RO Global b_tbl e_tbl (b_tbl ^+ 2)%a) ↦□ₑ stack_callee_secret_f_args
    ∗ WSealed ot_switcher (SCap RO Local b_tbl e_tbl (b_tbl ^+ 2)%a) ↦□ₑ stack_callee_secret_f_args
    ∗ seal_pred ot_switcher ot_switcher_propC
    -∗
    interp W C
      (WSealed ot_switcher (SCap RO Global b_tbl e_tbl (b_tbl ^+ 2)%a),
       WSealed ot_switcher (SCap RO Global b_tbl e_tbl (b_tbl ^+ 2)%a)).
  Proof.
    iIntros (Htbl_size HsubBounds Himports_contiguous Hcgp_contiguous)
      "(#Hswitcher & #HT & #Htbl_pcc & #Htbl_cgp & #Htbl_f
       & #Hentry_f & #Hentry_f' & #Hsealed_pred_ot_switcher)".
    rewrite interp_sealed_inv.
    iSplit; first done.
    rewrite /interp_sb.
    iExists ot_switcher_prop.
    iFrame "Hsealed_pred_ot_switcher".
    iSplit; first (iPureIntro ; apply persistent_cond_ot_switcher).
    iSplit; first (iIntros (w) ; iApply mono_priv_ot_switcher).
    iSplit; first done.
    iSplit; iNext.
    - iApply (stack_callee_secret_f_ot_switcher_prop
                pc_b pc_e pc_a cgp_b cgp_e b_tbl e_tbl Global B_adv secret1 secret2 W C Nswitcher TN
               with "[$Hswitcher $HT $Htbl_pcc $Htbl_cgp $Htbl_f $Hentry_f]"); eauto.
    - iApply (stack_callee_secret_f_ot_switcher_prop
                pc_b pc_e pc_a cgp_b cgp_e b_tbl e_tbl Local B_adv secret1 secret2 W C Nswitcher TN
               with "[$Hswitcher $HT $Htbl_pcc $Htbl_cgp $Htbl_f $Hentry_f']"); eauto.
  Qed.

End Stack_callee_secret_f.
