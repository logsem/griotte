From iris.proofmode Require Import proofmode.
From griotte Require Import logrel_binary.
From griotte Require Import rules proofmode proofmode_binary register_tactics_binary.
From griotte Require Import switcher_preamble_binary switcher_spec_return_binary.
From griotte Require Import stack_callee_secret_spec_world_binary stack_callee_secret_spec_f_blocks_1_binary.
From griotte Require Export stack_callee_secret_spec_states_binary.

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
    (* Outline of the proof:
       - introduce the state of both machines at the entry point of [T.f];
       - [stack_callee_secret_world_f]: revoke the world, to get the stack
         frame of [T.f];
       - open the invariant of [T], and [stack_callee_secret_f_blocks_1_spec]:
         block 3, write the secret at the base of the stack frame, and jump
         to the switcher; then close the invariant of [T];
       - [switcher_ret_specification]: return to the caller of [T.f]. *)
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
    rewrite /stack_callee_secret_imports /= in Himports_contiguous.
    assert (stack_callee_secret_code_bounds pc_b pc_e pc_a) as Hbounds.
    { split; first done. exact Himports_contiguous. }
    set (csp_b := (a_stk ^+ 4)%a).

    (* Extract the registers, in both runs *)
    iDestruct (big_sepM_delete _ _ PC with "Hrmap") as "[HPC Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cgp with "Hrmap") as "[Hcgp Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ csp with "Hrmap") as "[Hcsp Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cra with "Hrmap") as "[Hcra Hrmap]"; first by simplify_map_eq.
    iExtractList "Hrmap" [ct0;ca0;ca1;cnull] as ["Hct0";"Hca0";"Hca1";"Hcnull"].
    iDestruct (big_sepM_delete _ _ PC with "Hsmap") as "[HsPC Hsmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cgp with "Hsmap") as "[Hscgp Hsmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ csp with "Hsmap") as "[Hscsp Hsmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cra with "Hsmap") as "[Hscra Hsmap]"; first by simplify_map_eq.
    iExtractList "Hsmap" [ct0;ca0;ca1;cnull] as ["Hsct0";"Hsca0";"Hsca1";"Hscnull"].

    (* Revoke the world, to get the stack frame of T.f, in both runs *)
    iMod (stack_callee_secret_world_f with "Hinterp_csp Hworld_interp")
      as (l stk_mem stk_mem_spec)
           "(%Hextract & %Hpub_W_Wfixed & Hworld_interp & Hrevoked_l & Hstk & Hsstk)".

    (* Block 3: write the secret at the base of the stack frame, and return *)
    iMod (na_inv_acc with "HT Hna")
      as "((>Himports_main & >Hsimports_main & >Hcode_main & >Hscode_main & >Hsecret & >Hssecret)
          & Hna & HT_close)"; auto.
    rewrite (stack_callee_secret_f_entry pc_b pc_e pc_a Hbounds).
    iApply (stack_callee_secret_f_blocks_1_spec with
             "[- $Hspec $Hj $HPC $HsPC $Hcgp $Hscgp $Hcsp $Hscsp $Hcra $Hscra
              $Hct0 $Hsct0 $Hca0 $Hsca0 $Hca1 $Hsca1 $Hcnull $Hscnull
              $Hsecret $Hssecret $Hstk $Hsstk $Hcode_main $Hscode_main]");
      [done|done|].
    iNext; iIntros (stk_mem' stk_mem_spec' wcnull' swcnull')
      "(Hj & HPC & HsPC & Hcgp & Hscgp & Hcsp & Hscsp & Hcra & Hscra
      & Hct0 & Hsct0 & Hca0 & Hsca0 & Hca1 & Hsca1 & Hcnull & Hscnull
      & Hsecret & Hssecret & Hstk & Hsstk & Hcode_main & Hscode_main)".
    iMod ("HT_close" with
           "[$Hna $Himports_main $Hsimports_main $Hcode_main $Hscode_main $Hsecret $Hssecret]")
      as "Hna".
    iInsertRegs "Hrmap" ["Hcnull"; "Hct0"; "Hcra"; "Hcgp"].
    iInsertRegsSpec "Hsmap" ["Hscnull"; "Hsct0"; "Hscra"; "Hscgp"].

    (* Return to the caller of T.f *)
    iApply (switcher_ret_specification _ W (revoke W) C _ _ e_stk csp_b l _ _ stk Ws Cs
              (WInt 0, WInt 0) (WInt 0, WInt 0)
             with
             "[$Hswitcher $Hspec $Hstk $Hsstk $Hcstk_frag $Hcstk_frag_spec $HK $Hworld_interp
               $Hna $Hj $HPC $HsPC $Hrevoked_l $Hrmap $Hsmap
               $Hca0 $Hsca0 $Hca1 $Hsca1 $Hcsp $Hscsp]"); auto.
    { rewrite !dom_insert_L !dom_delete_L Hdom1; set_solver+. }
    { rewrite !dom_insert_L !dom_delete_L Hdom2; set_solver+. }
    { subst csp_b.
      destruct Hcsp_sync as [Hcsp_sync <-].
      auto. }
    { destruct Hextract; auto. }
    { intros a; destruct Hextract as [_ Htemp]; destruct (Htemp a); auto. }
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
