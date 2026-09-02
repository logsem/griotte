From iris.proofmode Require Import proofmode.
From griotte Require Import logrel rules.
From griotte Require Import
  region_invariants_revocation wp_rules_interp interp_weakening.
From griotte Require Import
  assert_spec fetch_spec.
From griotte Require Import
  switcher switcher_preamble switcher_spec_call switcher_spec_KtK.
From griotte Require Import
  kvs kvs_preamble kvs_spec_read kvs_spec_addOrUpdate kvs_main
  kvs_main_spec_blocks.
From griotte Require Import map_simpl register_tactics proofmode.

Section KVS_main_spec.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}
    {kvsg:kvsG Σ} {KVS_layout : kvsLayout} {KVS_layout_Wf : kvsLayoutWf}
    {KVS_namespaces : kvs_namespaces}
  .

  Context {B : CmptName}.

  Implicit Types W : WORLD.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

  Lemma kvs_main_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (static_sealed_b static_sealed_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : Reg)
    (KVS_USER_KEY_MAIN : Z)

    (b_assert e_assert : Addr) (a_flag : Addr)
    (B_f : Sealable)

    (W0 : WORLD)
    (Ws : list WORLD)
    (Cs : list CmptName)
    (cstk : CSTK)

    (Nassert Nswitcher : namespace)
    :

    let imports :=
      kvs_main_imports static_sealed_b b_switcher e_switcher a_switcher_call ot_switcher b_assert e_assert B_f
    in

    Nswitcher ## Nassert ->

    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp]} ->
    (forall r, r ∈ (dom rmap) -> is_Some (rmap !! r) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length kvs_main_code)%a ->

    (static_sealed_b + length (kvs_main_static_sealed KVS_USER_KEY_MAIN))%a = Some static_sealed_e ->
    (cgp_b + length (kvs_main_data))%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    frame_match Ws Cs cstk W0 B ->
    (
      na_inv cerise_nais Nassert (assert_inv b_assert e_assert a_flag) ∗
      na_inv cerise_nais Nswitcher switcher_inv ∗
      na_inv cerise_nais (Nkvs.@"physical") kvs_inv ∗
      na_inv cerise_nais (Nkvs.@"logical") logical_kvs_inv ∗

      inv (export_table_PCCN Nkvs_exp_tbl) (b_kvs_exp_tbl ↦ₐ WCap RX Global KVS_pcc_b KVS_pcc_e KVS_pcc_b) ∗
      inv (export_table_CGPN Nkvs_exp_tbl) ((b_kvs_exp_tbl ^+ 1)%a ↦ₐ WCap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b) ∗
      inv (export_table_entryN Nkvs_exp_tbl kvs_addOrUpdate_exp_tbl_addr) (kvs_addOrUpdate_exp_tbl_addr ↦ₐ kvs_exp_tbl_entry_addOrUpdate) ∗
      inv (export_table_entryN Nkvs_exp_tbl kvs_read_exp_tbl_addr) (kvs_read_exp_tbl_addr ↦ₐ kvs_exp_tbl_entry_read) ∗

      na_own cerise_nais ⊤ ∗

      (* initial register file *)
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
      csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b ∗
      ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗

      (* initial memory layout *)
      [[ pc_b , pc_a ]] ↦ₐ [[ imports ]] ∗
      codefrag pc_a kvs_main_code ∗
      [[ cgp_b , cgp_e ]] ↦ₐ [[ (kvs_main_data) ]] ∗
      [[ static_sealed_b , static_sealed_e ]] ↦ₐ [[ kvs_main_static_sealed KVS_USER_KEY_MAIN ]] ∗

      user_kvs_inv KVS_USER_KEY_MAIN ∗
      (KVS_USER_KEY_MAIN, 1) ↦(KVS) ⊥ ∗

      world_interp W0 B ∗
      interp_continuation cstk Ws Cs ∗
      cstack_frag cstk ∗

      interp W0 B (WSealed ot_switcher B_f) ∗
      (WSealed ot_switcher B_f) ↦□ₑ 0 ∗
      interp W0 B (WCap RWL Local csp_b csp_e csp_b)

      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros imports; subst imports.
    iIntros (HNswitcher_assert Hrmap_dom Hrmap_init HsubBounds
               Hstatic_sealed_contiguous Hcgp_contiguous Himports_contiguous Hframe_match
            )
      "(#Hassert & #Hswitcher
      & #Hkvs & #Hkvs_logical
      & #Hkvs_exp_tbl_pcc & #Hkvs_exp_tbl_cgp & #Hkvs_exp_tbl_addOrUpdate & #Hkvs_exp_tbl_read
      & Hna
      & HPC & Hcgp & Hcsp & Hrmap
      & Himports_main & Hcode_main & Hcgp_main & Hstatic_sealed_main
      & HLUKVS & Hkvs_1
      & Hworld_B
      & HK & Hcstk_frag
      & #Hinterp_W0_B_f
      & #HentryB_f
      & #Hinterp_W0_csp
      )".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous ; clear H0.
    assert (withinBounds static_sealed_b (static_sealed_b ^+ 1)%a static_sealed_b = true)
      as Hstatic_sealed_b by solve_addr.
    iDestruct (kvs_main_imports_pointsto pc_b pc_a static_sealed_b
      b_assert e_assert B_f Himports_contiguous with "Himports_main") as
      "(Himport_switcher & Himport_assert & Himport_B_f
       & Himport_kvs_addOrUpdate & Himport_kvs_read & Himport_kvs_erase
       & Himport_sealed_user_key & Himports_main)".
    (* Extract the static sealed user key address  *)
    iDestruct (region_pointsto_single with "Hstatic_sealed_main") as "(% & Hstatic_sealed_b & %Heq')" ; last (rewrite /kvs_main_static_sealed in Heq' ; simplify_eq).
    { rewrite /kvs_main_static_sealed //= in Hstatic_sealed_contiguous. }

    (* Revoke the world to get the stack frame *)
    set (stk_frame_addrs := finz.seq_between csp_b csp_e).
    iAssert ([∗ list] a ∈ stk_frame_addrs, ⌜std W0 !! a = Some Temporary⌝)%I as "Hstk_frm_tmp_W0".
    { iApply (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp_W0_csp"); eauto. }
    iMod (world_interp_revoke_stack with "[$Hinterp_W0_csp $Hworld_B]")
        as (l) "(%Hl_unk & Hworld_B & #Hstack_revoked_W0 & >%Hstack_revoked_W0 & >[%stk_mem Hstk] & [Hrevoked_l _])".
    set (W1 := revoke W0).
    assert (related_sts_priv_world W0 W1) as Hrelared_priv_W0_W1 by eapply revoke_related_sts_priv_world.

    pose proof kvs_exp_tbl_size as Hkvs_exp_tbl_size.
    rewrite /length_kvs_exports_tbl /kvs_nb_exports in Hkvs_exp_tbl_size.
    iApply (kvs_main_add_phase_spec
      pc_b pc_e pc_a cgp_b cgp_e static_sealed_b csp_b csp_e
      rmap KVS_USER_KEY_MAIN b_assert e_assert B_f Nswitcher stk_mem cstk
      with
      "[- $Hswitcher $Hkvs $Hkvs_logical
       $Hkvs_exp_tbl_pcc $Hkvs_exp_tbl_cgp $Hkvs_exp_tbl_addOrUpdate
       $Hna $HPC $Hcgp $Hcsp $Hrmap
       $Himport_switcher $Himport_kvs_addOrUpdate
       $Himport_sealed_user_key $Hcode_main
       $Hstatic_sealed_b $HLUKVS $Hkvs_1 $Hstk $Hcstk_frag]");
      eauto.
    iNext.
    iIntros (rmap_ret)
      "(%Hdom_rmap_ret & Hna & HPC & Hcgp & [%wcra Hcra]
       & Hcs0 & Hcs1 & Hcsp & Hca0 & Hca1 & Hrmap
       & Hstk & Hcstk & Hstatic_sealed_b & HLUKVS & Hkvs_1
       & Himport_switcher & Himport_kvs_addOrUpdate
       & Himport_sealed_user_key & Hcode_main)".
    iEval (cbn [kvs_main_add_phase_instrs]) in "HPC".
    iEval (rewrite /kvs_main_code) in "Hcode_main".

    iExtractList "Hrmap" [ctp;ct0;ct1] as ["[Hctp %]";"[Hct0 %]";"[Hct1 %]"]; simplify_eq.

    (* --------------------------------------------------- *)
    (* -------------- BLOCK 6 and 7 : FETCH -------------- *)
    (* --------------------------------------------------- *)
    focus_block_nochangePC 6 "Hcode_main" as a_fetch1 Ha_fetch1
      "Hcode" "Hcont"; iHide "Hcont" as hcont.
    changePCto a_fetch1.
    iApply (fetch_spec with "[- $HPC $Hctp $Hct0 $Hct1 $Hcode]"); eauto.
    { rewrite /SWITCHER_CALL_OFFSET; solve_addr. }
    replace (pc_b ^+ SWITCHER_CALL_OFFSET)%a with pc_b by (rewrite /SWITCHER_CALL_OFFSET; solve_addr).
    iFrame "Himport_switcher".
    iNext ; iIntros "(HPC & Hctp & Hct0 & Hct1 & Hcode & Himport_switcher)".
    iEval (cbn) in "Hctp".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    focus_block 7 "Hcode_main" as a_fetch2 Ha_fetch2 "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent a_fetch1.
    iApply (fetch_spec with "[- $HPC $Hct1 $Hct0 $Hcs0 $Hcode $Himport_B_f]"); eauto.
    { rewrite /ADV_F_OFFSET; solve_addr. }
    iNext ; iIntros "(HPC & Hct1 & Hct0 & Hcs0 & Hcode & Himport_B_f)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 8: CALL B ----------------- *)
    (* --------------------------------------------------- *)
    focus_block 8 "Hcode_main" as a_call Ha_call "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent a_fetch2.
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* -- Prepare registers  -- *)
    (* -- separate argument registers -- *)
    iExtractList "Hrmap" [ca2;ca3;ca4;ca5] as
      ["[Hca2 %]";"[Hca3 %]";"[Hca4 %]";"[Hca5 %]"]; simplify_eq.

    (* --- other registers --- *)
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iInsertList "Hrmap" [ctp].
    set (rmap_B :=
      <[ctp := WSentry XSRW_ Local b_switcher e_switcher a_switcher_call]>
        (delete ca5 (delete ca4 (delete ca3
          (delete ca2 (delete ct1 (delete ct0 rmap_ret))))))).
    set (stk_mem_B := region_addrs_zeroes csp_b csp_e).

    iAssert (interp W1 B (WSealed ot_switcher B_f)) as "#Hinterp_W1_B_f".
    { iApply monotone.interp_monotone_sd; eauto. }

    assert ( revoked_addresses W1 (finz.seq_between csp_b csp_e) ) as Hstack_revoked_W1.
    {
      rewrite /revoked_addresses Forall_forall.
      rewrite /revoked_addresses Forall_forall in Hstack_revoked_W0.
      intros a Ha; cbn in *.
      by apply Hstack_revoked_W0.
    }
    iDestruct (StackRevokedResources_mono_priv with "Hstack_revoked_W0") as "Hstack_revoked_W1"; eauto.

    iApply (kvs_main_adversary_phase_spec Nswitcher W1 B
             (WCap RW Global cgp_b cgp_e cgp_b)
             (WSentry RX Global pc_b pc_e (a_call ^+ 1)%a)
             (WInt 0) (kvs_user_seal_key Global static_sealed_b)
             csp_b csp_e csp_b B_f stk_mem_B rmap_B cstk Ws Cs).
    { subst rmap_B.
      repeat (rewrite dom_insert_L); repeat (rewrite dom_delete_L).
      rewrite Hdom_rmap_ret; set_solver. }
    iFrame "Hswitcher Hna HPC Hcgp Hcra Hcsp Hct1 Hcs0 Hcs1 Hrmap
      Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0 Hstk Hworld_B Hcstk
      Hstack_revoked_W1 Hinterp_W1_B_f HentryB_f HK".
    iFrame "%".
    clear dependent rmap.
    clear stk_mem.
    iNext.
    iIntros (W2 rmap stk_mem l')
      "( %Hl_unk' & Hrevoked_l' & %Hrevoked_l'
      & %Hrelated_pub_W1ext_W2 & Hrel_stk_C' & %Hdom_rmap & Hfrm_close_W2 & %Hfrm_close_W2
      & Hna & %Hcsp_bounds
      & Hworld_C
      & Hcstk_frag
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hstk & HK)".
    iEval (cbn) in "HPC".
    assert ((a_call ^+ 1)%a =
      (pc_a ^+ length
        (kvs_main_add_phase_instrs ++
         kvs_main_adversary_phase_instrs))%a) as Hread_start.
    { rewrite /kvs_main_add_phase_instrs
        /kvs_main_adversary_phase_instrs.
      solve_addr+Ha_call. }
    iEval (rewrite Hread_start) in "HPC".
    iApply (kvs_main_read_assert_phase_spec
      pc_b pc_e pc_a cgp_b cgp_e static_sealed_b csp_b csp_e
      rmap warg0 warg1
      (WSentry RX Global pc_b pc_e (a_call ^+ 1)%a) (WInt 0)
      KVS_USER_KEY_MAIN b_assert e_assert a_flag Nassert Nswitcher
      stk_mem cstk with
      "[- $Hassert $Hswitcher $Hkvs $Hkvs_logical
       $Hkvs_exp_tbl_pcc $Hkvs_exp_tbl_cgp $Hkvs_exp_tbl_read
       $Hna $HPC $Hcgp $Hcra $Hcs0 $Hcs1 $Hcsp $Hca0 $Hca1
       $Hrmap $Hstk $Hcstk_frag $Hstatic_sealed_b $HLUKVS $Hkvs_1
      $Himport_switcher $Himport_kvs_read $Himport_assert $Hcode_main]");
      eauto.
  Qed.

End KVS_main_spec.
