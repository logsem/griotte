From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel rules.
From cap_machine Require Import
  region_invariants_revocation wp_rules_interp logrel_extra interp_weakening.
From cap_machine Require Import
  assert_spec fetch_spec.
From cap_machine Require Import
  switcher switcher_preamble switcher_spec_call switcher_spec_KtK_call switcher_spec_KtK_return.
From cap_machine Require Import
  kvs kvs_preamble kvs_spec_read kvs_spec_addOrUpdate kvs_main.
From cap_machine Require Import map_simpl register_tactics proofmode.

Section KVS_main_spec.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
    {kvsg:kvsG Σ} {KVS_layout : kvsLayout} {KVS_layout_Wf : kvsLayoutWf}
    {KVS_users: kvs_users} {KVS_namespaces : kvs_namespaces}
  .

  Context {B : CmptName}.

  Implicit Types W : WORLD.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

  Lemma kvs_main_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
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
      kvs_main_imports b_switcher e_switcher a_switcher_call ot_switcher b_assert e_assert B_f
    in

    Nswitcher ## Nassert ->
    KVS_USER_KEY_MAIN ∈ kvs_users_seals_reserved ->

    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp]} ->
    (forall r, r ∈ (dom rmap) -> is_Some (rmap !! r) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length kvs_main_code)%a ->

    (cgp_b + length (kvs_main_data KVS_USER_KEY_MAIN))%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    frame_match Ws Cs cstk W0 B ->
    (
      na_inv logrel_nais Nassert (assert_inv b_assert e_assert a_flag) ∗
      na_inv logrel_nais Nswitcher switcher_inv ∗
      na_inv logrel_nais Nkvs kvs_inv ∗

      inv (export_table_PCCN Nkvs_exp_tbl) (b_kvs_exp_tbl ↦ₐ WCap RX Global KVS_pcc_b KVS_pcc_e KVS_pcc_b) ∗
      inv (export_table_CGPN Nkvs_exp_tbl) ((b_kvs_exp_tbl ^+ 1)%a ↦ₐ WCap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b) ∗
      inv (export_table_entryN Nkvs_exp_tbl kvs_addOrUpdate_exp_tbl_addr) (kvs_addOrUpdate_exp_tbl_addr ↦ₐ kvs_exp_tbl_entry_addOrUpdate) ∗
      inv (export_table_entryN Nkvs_exp_tbl kvs_read_exp_tbl_addr) (kvs_read_exp_tbl_addr ↦ₐ kvs_exp_tbl_entry_read) ∗

      na_own logrel_nais ⊤ ∗

      (* initial register file *)
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
      csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b ∗
      ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗

      (* initial memory layout *)
      [[ pc_b , pc_a ]] ↦ₐ [[ imports ]] ∗
      codefrag pc_a kvs_main_code ∗
      [[ cgp_b , cgp_e ]] ↦ₐ [[ (kvs_main_data KVS_USER_KEY_MAIN) ]] ∗

      ◯(ALLOC)[KVS_USER_KEY_MAIN] ∅ ∗
      region W0 B ∗ sts_full_world W0 B ∗

      interp_continuation cstk Ws Cs ∗
      cstack_frag cstk ∗

      interp W0 B (WSealed ot_switcher B_f) ∗
      (WSealed ot_switcher B_f) ↦□ₑ 0 ∗
      interp W0 B (WCap RWL Local csp_b csp_e csp_b) ∗

      WSealed ot_switcher (KVS_addOrUpdate Global) ↦□ₑ kvs_addOrUpdate_nargs ∗
      WSealed ot_switcher (KVS_addOrUpdate Local) ↦□ₑ kvs_addOrUpdate_nargs ∗
      WSealed ot_switcher (KVS_read Global) ↦□ₑ kvs_read_nargs ∗
      WSealed ot_switcher (KVS_read Local) ↦□ₑ kvs_read_nargs ∗

      seal_pred ot_switcher ot_switcher_propC

      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros imports; subst imports.
    iIntros (HNswitcher_assert HKVS_USER_KEY_MAIN Hrmap_dom Hrmap_init HsubBounds
               Hcgp_contiguous Himports_contiguous Hframe_match
            )
      "(#Hassert & #Hswitcher
      & #Hkvs & #Hkvs_exp_tbl_pcc & #Hkvs_exp_tbl_cgp & #Hkvs_exp_tbl_addOrUpdate & #Hkvs_exp_tbl_read
      & Hna
      & HPC & Hcgp & Hcsp & Hrmap
      & Himports_main & Hcode_main & Hcgp_main
      & Halloc
      & Hr_B & Hsts_B
      & HK & Hcstk_frag
      & #Hinterp_W0_B_f
      & #HentryB_f
      & #Hinterp_W0_csp
      & #Hentry_addOrUpdate & #Hentry_addOrUpdate'
      & #Hentry_read & #Hentry_read'
      & #Hot_switcher
      )".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous ; clear H0.
    (* --- Extract registers ca0 ca1 ct0 ctp ct1 ct2 ct3 cs0 cs1 --- *)
    iExtractList "Hrmap" [cra;ca0;ca1;ca2;ctp;ct0;ct1;cs0]
      as ["Hcra"; "Hca0"; "Hca1"; "Hca2"; "Hctp"; "Hct0"; "Hct1"; "Hcs0"; "Hcs1"].

    (* Extract the imports *)
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_switcher Himports_main]".
    { transitivity (Some (pc_b ^+ ASSERT_OFFSET)%a); auto; rewrite /ASSERT_OFFSET; solve_addr. }
    { rewrite /ASSERT_OFFSET; solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_assert Himports_main]".
    { transitivity (Some (pc_b ^+ ADV_F_OFFSET)%a); auto; rewrite /ASSERT_OFFSET /ADV_F_OFFSET; solve_addr. }
    { rewrite /ADV_F_OFFSET; solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_B_f Himports_main]".
    { transitivity (Some (pc_b ^+ KVS_INSERT_OFFSET)%a); auto; rewrite /ADV_F_OFFSET /KVS_INSERT_OFFSET; solve_addr. }
    { rewrite /KVS_INSERT_OFFSET; solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_kvs_addOrUpdate Himports_main]".
    { transitivity (Some (pc_b ^+ KVS_READ_OFFSET)%a); auto; rewrite /KVS_INSERT_OFFSET /KVS_READ_OFFSET; solve_addr. }
    { rewrite /KVS_READ_OFFSET ; solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_kvs_read Himports_main]".
    { transitivity (Some (pc_b ^+ KVS_ERASE_OFFSET)%a); auto ; rewrite /KVS_READ_OFFSET /KVS_ERASE_OFFSET ; solve_addr. }
    { rewrite /KVS_ERASE_OFFSET; solve_addr. }

    (* Extract cgp_b, which contains the sealed user key *)
    iDestruct (region_pointsto_cons with "Hcgp_main") as "[Hcgp_b Hcgp_main]".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }

    (* Revoke the world to get the stack frame *)
    set (stk_frame_addrs := finz.seq_between csp_b csp_e).
    iAssert ([∗ list] a ∈ stk_frame_addrs, ⌜W0.1 !! a = Some Temporary⌝)%I as "Hstk_frm_tmp_W0".
    { iApply (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp_W0_csp"); eauto. }
    iMod (monotone_revoke_stack_alt with "[$Hinterp_W0_csp $Hsts_B $Hr_B]")
        as (l) "(%Hl_unk & Hsts_B & Hr_B & Hfrm_close_W0 & >%Hfrm_close_W0 & >[%stk_mem Hstk] & [Hrevoked_l %Hrevoked_l])".
    set (W1 := revoke W0).

    (* --------------------------------------------------------------- *)
    (* ----------------- Start the proof of the code ----------------- *)
    (* --------------------------------------------------------------- *)

    (* ------------------------------------------------------------ *)
    (* ------- BLOCK 0 : addOrUpdate(sealedUserKey, 1, 12) -------- *)
    (* ------------------------------------------------------------ *)

    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Lea cgp SEALED_USER_KEY_OFFSET; *)
    iInstr "Hcode".
    { rewrite /SEALED_USER_KEY_OFFSET ; transitivity (Some cgp_b); solve_addr+. }
    (* Load ca0 cgp; *)
    iInstr "Hcode".
    { split; solve_addr. }
    iEval (cbn) in "Hca0".
    (* Mov ca1 1; *)
    iInstr "Hcode".
    destruct ( decide (ca1 = cnull) ) as [|_] ; first done.
    (* Mov ca2 12 *)
    iInstr "Hcode".
    destruct ( decide (ca2 = cnull) ) as [|_]; first done.
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* -------------- BLOCK 1 and 2 : FETCH -------------- *)
    (* --------------------------------------------------- *)

    focus_block 1 "Hcode_main" as a_fetch1 Ha_fetch1 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hctp $Hct0 $Hct1 $Hcode]"); eauto.
    { rewrite /SWITCHER_CALL_OFFSET; solve_addr. }
    replace (pc_b ^+ SWITCHER_CALL_OFFSET)%a with pc_b by (rewrite /SWITCHER_CALL_OFFSET; solve_addr).
    iFrame "Himport_switcher".
    iNext ; iIntros "(HPC & Hctp & Hct0 & Hct1 & Hcode & Himport_switcher)".
    iEval (cbn) in "Hctp".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    focus_block 2 "Hcode_main" as a_fetch2 Ha_fetch2 "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent a_fetch1.
    iApply (fetch_spec with "[- $HPC $Hct1 $Hct0 $Hcs0 $Hcode $Himport_kvs_addOrUpdate]"); eauto.
    { rewrite /KVS_INSERT_OFFSET; solve_addr. }
    iNext ; iIntros "(HPC & Hct1 & Hct0 & Hcs0 & Hcode & Himport_kvs_addOrUpdate)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 3: INSERT ----------------- *)
    (* --------------------------------------------------- *)
    focus_block 3 "Hcode_main" as a_insert_kvs Ha_insert_kvs "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent a_fetch2.
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    pose proof kvs_exp_tbl_size as Hkvs_exp_tbl_size.
    rewrite /length_kvs_exports_tbl /kvs_nb_exports in Hkvs_exp_tbl_size.
    iExtractList "Hrmap" [cs1;ca3;ca4;ca5] as ["Hcs1"; "Hca3"; "Hca4"; "Hca5"].

    (* Use switcher call KtK *)
    set ( rmap_arg :=
           {[ ca0 := kvs_user_seal_key KVS_USER_KEY_MAIN;
              ca1 := WInt 1%nat;
              ca2 := WInt 12%nat;
              ca3 := wca3;
              ca4 := wca4;
              ca5 := wca5;
              ct0 := WInt 0
           ]} : Reg
        ).

    iAssert ([∗ map] rarg↦warg ∈ rmap_arg, rarg ↦ᵣ warg )%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done.
    }
    iInsertList "Hrmap" [ctp].
    set (rmap' := <[ctp := _]> _ ).

    iApply (switcher_cc_specification_known_to_known
              _ _ _ _ _ _ _ _ _ rmap_arg rmap'
             with
             "[- $Hswitcher $Hkvs_exp_tbl_pcc $Hkvs_exp_tbl_cgp $Hkvs_exp_tbl_addOrUpdate
                 $Hna $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
                 $Hstk $Hcstk_frag
                 ]"); auto.
    { rewrite /kvs_addOrUpdate_exp_tbl_addr /kvs_addOrUpdate_exp_tbl_off; solve_addr+Hkvs_exp_tbl_size. }
    { solve_addr+Hkvs_exp_tbl_size. }
    { rewrite /kvs_addOrUpdate_exp_tbl_addr /kvs_addOrUpdate_exp_tbl_off; solve_addr+Hkvs_exp_tbl_size. }
    { rewrite /kvs_addOrUpdate_nargs; lia. }
    {  subst rmap'.
       rewrite dom_insert_L.
       repeat (rewrite dom_delete_L).
       rewrite Hrmap_dom /dom_arg_rmap /=.
       set_solver+.
    }
    { subst rmap_arg; set_solver. }
    iNext.
    iIntros "[
    (%arg_rmap_add & %rmap_add & %Hdom_arg_rmap_add & %Hdom_rmap_add
    & Hna & HPC & Hcgp & Hcra & Hcsp & Hargs & Hrmap & Hstk & Hcstk)
    |
    (%rmap_add & %stk_mem' & %Hdom_rmap_add & Hna
    & HPC & Hcgp & Hcra & Hcsp & Hcs0 & Hcs1 & Hca0 & Hca1 & Hrmap & Hstk & Hcstk_frag
    )
    ]"
    ; iEval (cbn) in "HPC"
    ; cycle 1.
    {
      focus_block 4 "Hcode_main" as a_blk_4  Ha_blk_4 "Hcode" "Hcont"; iHide "Hcont" as hcont
      ; clear dependent a_insert_kvs.
      (* Jnz 2 ca0 *)
      iInstr "Hcode".
      (* Halt *)
      iInstr "Hcode".
      wp_end; iIntros (_); iFrame "Hna".
    }
    clear wca0 wca1 wca2 wct0.
    iExtractList "Hargs" [ca0;ca1;ca2;ca3;ca4;ca5;ct0]
      as ["[Hca0 %Hwca0]";"[Hca1 %Hwca1]";"[Hca2 %Hwca2]";
          "[Hca3 %Hwca3]";"[Hca4 %Hwca4]";"[Hca5 %Hwca5]";"[Hct0 %Hwct0]"].
    iClear "Hargs".
    destruct ( decide (ca0 ∈ dom_arg_rmap kvs_addOrUpdate_nargs) ) as [_|]; last done.
    destruct ( decide (ca1 ∈ dom_arg_rmap kvs_addOrUpdate_nargs) ) as [_|]; last done.
    destruct ( decide (ca2 ∈ dom_arg_rmap kvs_addOrUpdate_nargs) ) as [_|]; last done.
    destruct ( decide (ca3 ∈ dom_arg_rmap kvs_addOrUpdate_nargs) ) as [|_]; first done.
    assert (wca0 = kvs_user_seal_key KVS_USER_KEY_MAIN) as -> by (subst rmap_arg ; simplify_map_eq; done).
    assert (wca1 = WInt 1%nat) as -> by (subst rmap_arg ; simplify_map_eq; done).
    assert (wca2 = WInt 12%nat) as -> by (subst rmap_arg ; simplify_map_eq; done).
    simplify_eq.

    assert ( is_Some (rmap_add !! ctp) ) as [wctp' Hwctp'].
    { apply elem_of_dom; rewrite Hdom_rmap_add; subst rmap'; set_solver+. }
    assert ( is_Some (rmap_add !! ct1) ) as [wct1' Hwct1'].
    { apply elem_of_dom; rewrite Hdom_rmap_add; subst rmap'; set_solver+. }
    assert ( is_Some (rmap_add !! ct2) ) as [wct2' Hwct2'].
    { apply elem_of_dom; rewrite Hdom_rmap_add; subst rmap'.
      rewrite dom_insert_L.
      repeat (rewrite dom_delete_L).
      rewrite Hrmap_dom /dom_arg_rmap /=.
      set_solver+.
    }
    assert ( is_Some (rmap_add !! cnull) ) as [wcnull' Hwcnull'].
    { apply elem_of_dom; rewrite Hdom_rmap_add; subst rmap'.
      rewrite dom_insert_L.
      repeat (rewrite dom_delete_L).
      rewrite Hrmap_dom /dom_arg_rmap /=.
      set_solver+.
    }
    iExtractList "Hrmap" [cs0;cs1;ctp;ct1;ct2;cnull]
      as ["[Hcs0 %Hcs0]";"[Hcs1 %Hcs1]";"[Hctp %Hctp]";"[Hct1 %Hct1]";"[Hct2 %Hct2]";"[Hcnull %Hcnull]"]
    ; simplify_eq.

    (* Use spec addOrUpdate known *)
    iApply (KVS_add_spec
      with "[- $Hkvs $Hna $HPC $Hcgp $Hcra $ Hca0 $Hca1 $Hca2 $Hctp $Hct1 $Hct2 $Hcnull $Halloc]")
    ; auto.
    { pose proof kvs_users_seals_reserved_bounds as H_ukey_bounds.
      rewrite Forall_forall in H_ukey_bounds.
      by apply H_ukey_bounds in HKVS_USER_KEY_MAIN.
    }
    { rewrite /is_uint16 /UINT16_MIN /UINT16_MAX; lia. }
    { set_solver+. }
    iNext;
      iIntros "(Hna & HPC & [% Hcgp] & [% Hcra] & Hca1 & [% Hca2]
                    & [% Hctp] & [% Hct1] & [% Hct2] & [% Hcnull] & Hres)".
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".

    iInsertList "Hrmap" [ctp;ct1;ct2;cnull;ca2;ca3;ca4;ca5;ct0].

    iDestruct "Hres" as "[(Hca0 & Halloc & Hfkey) | (Hca0 & Halloc)]"; cycle 1.
    { (* Case where there was not more empty slot *)
      (* Use switcher return KtK *)
      iApply (switcher_cc_specification_return_known_to_known
             with
             "[- $Hswitcher
                 $Hna $HPC $Hcgp $Hcra $Hcsp $Hcs0 $Hcs1 $Hca0 $Hca1 $Hrmap
                 $Hstk $Hcstk
                 ]"); auto.
      {
        repeat (rewrite dom_insert_L).
        repeat (rewrite dom_delete_L).
        rewrite Hdom_rmap_add; subst rmap'.
        repeat (rewrite dom_insert_L).
        repeat (rewrite dom_delete_L).
        rewrite Hrmap_dom.
        set_solver+.
      }
      subst rmap'.
      iNext; iIntros (rmap')
               "(%Hdom_rmap' & Hna & HPC & Hcgp & Hcra
                             & Hcs0 & Hcs1 & Hcsp & Hca0
                             & Hca1 & Hrmap & Hstk)".
      iEval (cbn) in "HPC".

      focus_block 4 "Hcode_main" as a_blk_4  Ha_blk_4 "Hcode" "Hcont"; iHide "Hcont" as hcont
      ; clear dependent a_insert_kvs.
      (* Jnz 2 ca0 *)
      iInstr "Hcode".
      (* Halt *)
      iInstr "Hcode".
      wp_end; iIntros (_); iFrame "Hna".
    }
    (* Case where insert succeeded  *)
    iApply (switcher_cc_specification_return_known_to_known
             with
             "[- $Hswitcher
                 $Hna $HPC $Hcgp $Hcra $Hcsp $Hcs0 $Hcs1 $Hca0 $Hca1 $Hrmap
                 $Hstk $Hcstk
                 ]"); auto.
    {
      repeat (rewrite dom_insert_L).
      repeat (rewrite dom_delete_L).
      rewrite Hdom_rmap_add; subst rmap'.
      repeat (rewrite dom_insert_L).
      repeat (rewrite dom_delete_L).
      rewrite Hrmap_dom.
      set_solver+.
    }
    subst rmap'.
    iNext; iIntros (rmap')
             "(%Hdom_rmap' & Hna & HPC & Hcgp & Hcra
                             & Hcs0 & Hcs1 & Hcsp & Hca0
                             & Hca1 & Hrmap & Hstk & Hcstk)".
    iEval (cbn) in "HPC".

    focus_block 4 "Hcode_main" as a_blk_4  Ha_blk_4 "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent a_insert_kvs.
    (* Jnz 2 ca0 *)
    iInstr "Hcode".
    (* Jmp 2 *)
    iInstr "Hcode".
    (* Mov ca0 0 *)
    iInstr "Hcode".
    destruct ( decide (ca0 = cnull) ) as [|_] ; first done.
    (* Mov ca1 0 *)
    iInstr "Hcode".
    destruct ( decide (ca0 = cnull) ) as [|_] ; first done.
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    clear dependent Hwctp' rmap_arg rmap_add arg_rmap_add.
    clear wcra wctp wct1 wcs0 w w0 w1 w2 w3 w4 w5.
    iExtractList "Hrmap" [ctp;ct0;ct1] as ["[Hctp %]";"[Hct0 %]";"[Hct1 %]"]; simplify_eq.

    (* --------------------------------------------------- *)
    (* -------------- BLOCK 5 and 6 : FETCH -------------- *)
    (* --------------------------------------------------- *)
    focus_block 5 "Hcode_main" as a_fetch1  Ha_fetch1 "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent Ha_blk_4.
    iApply (fetch_spec with "[- $HPC $Hctp $Hct0 $Hct1 $Hcode]"); eauto.
    { rewrite /SWITCHER_CALL_OFFSET; solve_addr. }
    replace (pc_b ^+ SWITCHER_CALL_OFFSET)%a with pc_b by (rewrite /SWITCHER_CALL_OFFSET; solve_addr).
    iFrame "Himport_switcher".
    iNext ; iIntros "(HPC & Hctp & Hct0 & Hct1 & Hcode & Himport_switcher)".
    iEval (cbn) in "Hctp".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    focus_block 6 "Hcode_main" as a_fetch2 Ha_fetch2 "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent a_fetch1.
    iApply (fetch_spec with "[- $HPC $Hct1 $Hct0 $Hcs0 $Hcode $Himport_B_f]"); eauto.
    { rewrite /ADV_F_OFFSET; solve_addr. }
    iNext ; iIntros "(HPC & Hct1 & Hct0 & Hcs0 & Hcode & Himport_B_f)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 7: CALL B ----------------- *)
    (* --------------------------------------------------- *)
    focus_block 7 "Hcode_main" as a_call Ha_call "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent a_fetch2.
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* -- Prepare registers  -- *)
    (* -- separate argument registers -- *)
    iExtractList "Hrmap" [ca2;ca3;ca4;ca5] as
      ["[Hca2 %]";"[Hca3 %]";"[Hca4 %]";"[Hca5 %]"]; simplify_eq.

    set ( rmap_arg :=
           {[ ca0 := WInt 0;
              ca1 := WInt 0;
              ca2 := WInt 0;
              ca3 := WInt 0;
              ca4 := WInt 0;
              ca5 := WInt 0;
              ct0 := WInt 0
           ]} : Reg
        ).
    iAssert ([∗ map] rarg↦warg ∈ rmap_arg, rarg ↦ᵣ warg ∗ interp W1 B warg )%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg.
      iAssert (interp W1 B (WInt 0)) as "Hinterp_0".
      { iEval (rewrite fixpoint_interp1_eq); done. }
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done.
    }
    (* --- other registers --- *)
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iInsertList "Hrmap" [ctp].

    iAssert (interp W1 B (WSealed ot_switcher B_f)) as "#Hinterp_W1_B_f".
    { iApply monotone.interp_monotone_sd; eauto.
      iPureIntro; apply revoke_related_sts_priv_world.
    }

    iAssert (
        ( [∗ list] a ∈ finz.seq_between csp_b csp_e, closing_revoked_resources W1 B a)
      )%I with "[Hfrm_close_W0]"  as "Hfrm_close_W1".
    {
      iApply (big_sepL_impl with "Hfrm_close_W0").
      iIntros (k a Ha) "!> Hfrm_close_W0".
      iDestruct (mono_priv_closing_revoked_resources with "Hfrm_close_W0") as "$"; auto.
      apply revoke_related_sts_priv_world.
    }

    iApply (switcher_cc_specification _ W1 _ _ _ _ _ _ _ _ _ _ rmap_arg with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap
              $Hstk $Hr_B $Hsts_B $Hcstk $Hfrm_close_W1
              $Hinterp_W1_B_f $HentryB_f $HK]"); eauto; iFrame "%".
    { repeat (rewrite dom_insert_L);repeat (rewrite dom_delete_L).
      rewrite Hdom_rmap'; set_solver.
    }
    { by rewrite /is_arg_rmap. }
    iSplitL "Hrmap_arg".
    { iApply (big_sepM_impl with "Hrmap_arg").
      iModIntro; iIntros (r w Hr) "[$ ?]".
    }
    clear dependent rmap rmap' stk_mem.
    iNext.
    iIntros (W2 rmap stk_mem l')
      "( %Hl_unk' & Hrevoked_l' & %Hrevoked_l'
      & %Hrelated_pub_W1ext_W2 & Hrel_stk_C' & %Hdom_rmap & Hfrm_close_W2 & %Hfrm_close_W2
      & Hna & %Hcsp_bounds
      & Hsts_C & Hr_C
      & Hcstk_frag
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hstk & HK)".
    iEval (cbn) in "HPC".

    (* simplify the knowledge about the new rmap *)
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap Hrmap_zero]".
    iDestruct (big_sepM_pure with "Hrmap_zero") as "%Hrmap_zero".
    assert (∀ r : RegName, r ∈ dom rmap → rmap !! r = Some (WInt 0)) as Hrmap_init.
    { intros r Hr.
      rewrite elem_of_dom in Hr. destruct Hr as [wr Hr].
      pose proof Hr as Hr'.
      eapply map_Forall_lookup in Hr'; eauto.
      by cbn in Hr' ; simplify_eq.
    }
    iClear "Hrmap_zero".

    (* ---- extract the needed registers ct0 ct1 ----  *)
    iExtractList "Hrmap" [ctp;ct0;ct1] as ["Hctp";"Hct0"; "Hct1"].

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 8: PREPARE READ  ----------------- *)
    (* --------------------------------------------------- *)
    focus_block 8 "Hcode_main" as a_blk Ha_blk "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent a_call.
    (* Lea cgp SEALED_USER_KEY_OFFSET; *)
    iInstr "Hcode".
    { rewrite /SEALED_USER_KEY_OFFSET ; transitivity (Some cgp_b); solve_addr+. }
    (* Load ca0 cgp; *)
    iInstr "Hcode".
    { split; solve_addr. }
    iEval (cbn) in "Hca0".
    (* Mov ca1 1 *)
    iInstr "Hcode".
    destruct ( decide (ca1 = cnull) ) as [|_] ; first done.
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* ---------------------------------------------------- *)
    (* -------------- BLOCK 9 and 10 : FETCH -------------- *)
    (* ---------------------------------------------------- *)
    focus_block 9 "Hcode_main" as a_fetch1  Ha_fetch1 "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent Ha_blk.
    iApply (fetch_spec with "[- $HPC $Hctp $Hct0 $Hct1 $Hcode]"); eauto.
    { rewrite /SWITCHER_CALL_OFFSET; solve_addr. }
    replace (pc_b ^+ SWITCHER_CALL_OFFSET)%a with pc_b by (rewrite /SWITCHER_CALL_OFFSET; solve_addr).
    iFrame "Himport_switcher".
    iNext ; iIntros "(HPC & Hctp & Hct0 & Hct1 & Hcode & Himport_switcher)".
    iEval (cbn) in "Hctp".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    focus_block 10 "Hcode_main" as a_fetch2 Ha_fetch2 "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent a_fetch1.
    iApply (fetch_spec with "[- $HPC $Hct1 $Hct0 $Hcs0 $Hcode $Himport_kvs_read]"); eauto.
    { rewrite /KVS_READ_OFFSET; solve_addr. }
    iNext ; iIntros "(HPC & Hct1 & Hct0 & Hcs0 & Hcode & Himport_kvs_read)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".


    (* -------------------------------------------------- *)
    (* ----------------- BLOCK 11: READ ----------------- *)
    (* -------------------------------------------------- *)
    focus_block 11 "Hcode_main" as a_insert_kvs Ha_insert_kvs "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent a_fetch2.
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    iExtractList "Hrmap" [ca2;ca3;ca4;ca5] as ["Hca2";"Hca3"; "Hca4"; "Hca5"].

    (* Use switcher call KtK *)
    clear rmap_arg.
    set ( rmap_arg :=
           {[ ca0 := kvs_user_seal_key KVS_USER_KEY_MAIN;
              ca1 := WInt 1%nat;
              ca2 := wca2;
              ca3 := wca0;
              ca4 := wca1;
              ca5 := wca6;
              ct0 := WInt 0
           ]} : Reg
        ).

    iAssert ([∗ map] rarg↦warg ∈ rmap_arg, rarg ↦ᵣ warg )%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done.
    }
    iInsertList "Hrmap" [ctp].
    set (rmap' := <[ctp := _]> _ ).

    iApply (switcher_cc_specification_known_to_known
              _ _ _ _ _ _ _ _ _ rmap_arg rmap'
             with
             "[- $Hswitcher $Hkvs_exp_tbl_pcc $Hkvs_exp_tbl_cgp $Hkvs_exp_tbl_read
                 $Hna $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
                 $Hstk $Hcstk_frag
                 ]"); auto.
    { rewrite /kvs_read_exp_tbl_addr /kvs_read_exp_tbl_off; solve_addr+Hkvs_exp_tbl_size. }
    { solve_addr+Hkvs_exp_tbl_size. }
    { rewrite /kvs_read_exp_tbl_addr /kvs_read_exp_tbl_off; solve_addr+Hkvs_exp_tbl_size. }
    { rewrite /kvs_read_nargs; lia. }
    {  subst rmap'.
       rewrite dom_insert_L.
       repeat (rewrite dom_delete_L).
       rewrite Hdom_rmap /dom_arg_rmap /=.
       set_solver+.
    }
    { subst rmap_arg; set_solver. }
    iNext.
    iIntros "[
    (%arg_rmap_read & %rmap_read & %Hdom_arg_rmap_read & %Hdom_rmap_read
    & Hna & HPC & Hcgp & Hcra & Hcsp & Hargs & Hrmap & Hstk & Hcstk)
    |
    (%rmap_read & %stk_mem' & %Hdom_rmap_read & Hna
    & HPC & Hcgp & Hcra & Hcsp & Hcs0 & Hcs1 & Hca0 & Hca1 & Hrmap & Hstk & Hcstk_frag
    )
    ]"
    ; iEval (cbn) in "HPC"
    ; cycle 1.
    {
      focus_block 12 "Hcode_main" as a_assert1  Ha_assert1 "Hcode" "Hcont"; iHide "Hcont" as hcont
      ; clear dependent a_insert_kvs.
      (* Jnz 2 ca0 *)
      iInstr "Hcode".
      (* Halt *)
      iInstr "Hcode".
      wp_end; iIntros (_); iFrame "Hna".
    }


    iExtractList "Hargs" [ca0;ca1;ca2;ca3;ca4;ca5;ct0]
      as ["[Hca0 %Hwca0]";"[Hca1 %Hwca1]";"[Hca2 %Hwca2]";
          "[Hca3 %Hwca3]";"[Hca4 %Hwca4]";"[Hca5 %Hwca5]";"[Hct0 %Hwct0]"].
    iClear "Hargs".
    destruct ( decide (ca0 ∈ dom_arg_rmap kvs_addOrUpdate_nargs) ) as [_|]; last done.
    destruct ( decide (ca1 ∈ dom_arg_rmap kvs_addOrUpdate_nargs) ) as [_|]; last done.
    assert (wca7 = kvs_user_seal_key KVS_USER_KEY_MAIN) as -> by (subst rmap_arg ; simplify_map_eq; done).
    assert (wca8 = WInt 1%nat) as -> by (subst rmap_arg ; simplify_map_eq;done).
    simplify_eq.

    assert ( is_Some (rmap_read !! ct1) ) as [wct1' Hwct1'].
    { apply elem_of_dom; rewrite Hdom_rmap_read; subst rmap'; set_solver+. }
    assert ( is_Some (rmap_read !! ct2) ) as [wct2' Hwct2'].
    { apply elem_of_dom; rewrite Hdom_rmap_read; subst rmap'.
      rewrite dom_insert_L.
      repeat (rewrite dom_delete_L).
      rewrite Hdom_rmap /dom_arg_rmap /=.
      set_solver+.
    }
    assert ( is_Some (rmap_read !! cnull) ) as [wcnull' Hwcnull'].
    { apply elem_of_dom; rewrite Hdom_rmap_read; subst rmap'.
      rewrite dom_insert_L.
      repeat (rewrite dom_delete_L).
      rewrite Hdom_rmap /dom_arg_rmap /=.
      set_solver+.
    }
    iExtractList "Hrmap" [cs0;cs1;ct1;ct2;cnull]
      as ["[Hcs0 %Hcs0]";"[Hcs1 %Hcs1]";"[Hct1 %Hct1]";"[Hct2 %Hct2]";"[Hcnull %Hcnull]"]
    ; simplify_eq.

    (* Use spec readOrUpdate known *)
    iApply (KVS_read_spec_in
      with "[- $Hkvs $Hna $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hct1 $Hct2 $Hcnull $Hfkey]")
    ; auto.
    { pose proof kvs_users_seals_reserved_bounds as H_ukey_bounds.
      rewrite Forall_forall in H_ukey_bounds.
      by apply H_ukey_bounds in HKVS_USER_KEY_MAIN.
    }
    { rewrite /is_uint16 /UINT16_MIN /UINT16_MAX; lia. }
    iNext;
      iIntros "(Hna & HPC & [% Hcgp] & [% Hcra] & Hca0 & Hca1
                & [% Hct1] & [% Hct2] & [% Hcnull] & Hfkey)".
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".

    iInsertList "Hrmap" [ct1;ct2;cnull;ca2;ca3;ca4;ca5;ct0].

    (* use KtK return spec  *)
    iApply (switcher_cc_specification_return_known_to_known
             with
             "[- $Hswitcher
                 $Hna $HPC $Hcgp $Hcra $Hcsp $Hcs0 $Hcs1 $Hca0 $Hca1 $Hrmap
                 $Hstk $Hcstk
                 ]"); auto.
    {
      repeat (rewrite dom_insert_L).
      repeat (rewrite dom_delete_L).
      rewrite Hdom_rmap_read; subst rmap'.
      repeat (rewrite dom_insert_L).
      repeat (rewrite dom_delete_L).
      rewrite Hdom_rmap.
      set_solver+.
    }
    clear dependent rmap.
    iNext; iIntros (rmap)
             "(%Hdom_rmap & Hna & HPC & Hcgp & Hcra
                             & Hcs0 & Hcs1 & Hcsp & Hca0
                             & Hca1 & Hrmap & Hstk & Hcstk)".
    iEval (cbn) in "HPC".

    iExtractList "Hrmap" [ct0;ct1;ct2;ct3;ct4;cnull] as
      ["[Hct0 %]";"[Hct1 %]";"[Hct2 %]";"[Hct3 %]";"[Hct4 %]";"[Hcnull %]"]; simplify_eq.
    (* -------------------------------------------------- *)
    (* ---------------- BLOCK 12: ASSERT ---------------- *)
    (* -------------------------------------------------- *)
    focus_block 12 "Hcode_main" as a_assert1  Ha_assert1 "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent a_insert_kvs.
    (* Jnz 2 ca0 *)
    iInstr "Hcode".
    (* Jmp 2 *)
    iInstr "Hcode".
    (* Mov ct0 ca1 *)
    iInstr "Hcode".
    (* Mov ct1 12 *)
    iInstr "Hcode".
    destruct (decide (ct1 = cnull)) as [|_]; first done.
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* -------------------------------------------------- *)
    (* ---------------- BLOCK 13: ASSERT ---------------- *)
    (* -------------------------------------------------- *)
    focus_block 13 "Hcode_main" as a_assert2  Ha_assert2 "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent Ha_assert1.
    iApply (assert_success_spec with
             "[- $Hassert $Hna $HPC $Hct2 $Hct3 $Hct4 $Hct0 $Hct1 $Hcnull $Hcra
              $Hcode $Himport_assert]"); auto.
    { rewrite /ASSERT_OFFSET; solve_addr. }
    iNext; iIntros "(Hna & HPC & Hct2 & Hct3 & Hct4 & Hcra & Hct0 & Hct1 & Hcnull
                    & Hcode & Himport_assert)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* ---------------------------------------------------- *)
    (* ------------------ BLOCK 14: HALT ------------------ *)
    (* ---------------------------------------------------- *)
    focus_block 14 "Hcode_main" as a_halt Ha_halt "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Halt *)
    iInstr "Hcode".
    wp_end; iIntros "_"; iFrame.
  Qed.

End KVS_main_spec.
