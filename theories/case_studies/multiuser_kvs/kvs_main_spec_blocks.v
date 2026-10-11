From iris.proofmode Require Import proofmode.
From griotte Require Import logrel rules.
From griotte Require Import
  memory_region region_invariants_revocation wp_rules_interp interp_weakening.
From griotte Require Import assert_spec fetch_spec.
From griotte Require Import
  switcher switcher_preamble switcher_spec_call switcher_spec_KtK.
From griotte Require Import
  kvs kvs_preamble kvs_spec_read kvs_spec_addOrUpdate kvs_main.
From griotte Require Import map_simpl register_tactics proofmode.

Section KVS_Main_Blocks.
  Context
    {Σ : gFunctors}
    {ceriseg : ceriseG Σ} {sealsg : sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP : MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}
    {kvsg : kvsG Σ} {KVS_layout : kvsLayout}
    {KVS_layout_Wf : kvsLayoutWf}
    {KVS_namespaces : kvs_namespaces}.

  Context {B : CmptName}.

  (** Exact seven-cell import layout of the KVS main compartment.  The final
      empty region is retained explicitly, so consumers cannot accidentally
      drop the unused erase import or change the public layout. *)
  Lemma kvs_main_imports_pointsto
      pc_b pc_a static_sealed_b
      (b_assert e_assert : Addr) (B_f : Sealable) :
    (pc_b + length
      (kvs_main_imports static_sealed_b b_switcher e_switcher
        a_switcher_call ot_switcher b_assert e_assert B_f))%a = Some pc_a ->
    [[pc_b, pc_a]] ↦ₐ
      [[kvs_main_imports static_sealed_b b_switcher e_switcher
          a_switcher_call ot_switcher b_assert e_assert B_f]]
    ⊣⊢
      pc_b ↦ₐ WSentry XSRW_ Local
        b_switcher e_switcher a_switcher_call
      ∗ (pc_b ^+ ASSERT_OFFSET)%a ↦ₐ
        WSentry RX Global b_assert e_assert b_assert
      ∗ (pc_b ^+ ADV_F_OFFSET)%a ↦ₐ WSealed ot_switcher B_f
      ∗ (pc_b ^+ KVS_INSERT_OFFSET)%a ↦ₐ
        WSealed ot_switcher (KVS_addOrUpdate Global)
      ∗ (pc_b ^+ KVS_READ_OFFSET)%a ↦ₐ
        WSealed ot_switcher (KVS_read Global)
      ∗ (pc_b ^+ KVS_ERASE_OFFSET)%a ↦ₐ
        WSealed ot_switcher (KVS_erase Global)
      ∗ (pc_b ^+ SEALED_USER_KEY_OFFSET)%a ↦ₐ
        kvs_user_seal_key Global static_sealed_b
      ∗ region_pointsto (pc_b ^+ 7)%a pc_a [].
  Proof.
    intros Himports.
    rewrite /kvs_main_imports.
    iSplit.
    - iIntros "Himports".
      iDestruct (region_pointsto_cons with "Himports") as "[Hsw Himports]".
      { transitivity (Some (pc_b ^+ 1)%a); auto; solve_addr. }
      { solve_addr. }
      iDestruct (region_pointsto_cons with "Himports") as "[Hassert Himports]".
      { transitivity (Some (pc_b ^+ 2)%a); auto; solve_addr. }
      { solve_addr. }
      iDestruct (region_pointsto_cons with "Himports") as "[HB Himports]".
      { transitivity (Some (pc_b ^+ 3)%a); auto; solve_addr. }
      { solve_addr. }
      iDestruct (region_pointsto_cons with "Himports") as "[Hadd Himports]".
      { transitivity (Some (pc_b ^+ 4)%a); auto; solve_addr. }
      { solve_addr. }
      iDestruct (region_pointsto_cons with "Himports") as "[Hread Himports]".
      { transitivity (Some (pc_b ^+ 5)%a); auto; solve_addr. }
      { solve_addr. }
      iDestruct (region_pointsto_cons with "Himports") as "[Herase Himports]".
      { transitivity (Some (pc_b ^+ 6)%a); auto; solve_addr. }
      { solve_addr. }
      iDestruct (region_pointsto_cons with "Himports") as "[Hkey Himports]".
      { transitivity (Some (pc_b ^+ 7)%a); auto; solve_addr. }
      { solve_addr. }
      rewrite /ASSERT_OFFSET /ADV_F_OFFSET /KVS_INSERT_OFFSET
        /KVS_READ_OFFSET /KVS_ERASE_OFFSET /SEALED_USER_KEY_OFFSET.
      iFrame.
    - iIntros "(Hsw & Hassert & HB & Hadd & Hread & Herase & Hkey & Himports)".
      rewrite /ASSERT_OFFSET /ADV_F_OFFSET /KVS_INSERT_OFFSET
        /KVS_READ_OFFSET /KVS_ERASE_OFFSET /SEALED_USER_KEY_OFFSET.
      iApply (region_pointsto_cons _ (pc_b ^+ 1)%a); [solve_addr|solve_addr|].
      iFrame.
      iApply (region_pointsto_cons _ (pc_b ^+ 2)%a); [solve_addr|solve_addr|].
      iFrame.
      iApply (region_pointsto_cons _ (pc_b ^+ 3)%a); [solve_addr|solve_addr|].
      iFrame.
      iApply (region_pointsto_cons _ (pc_b ^+ 4)%a); [solve_addr|solve_addr|].
      iFrame.
      iApply (region_pointsto_cons _ (pc_b ^+ 5)%a); [solve_addr|solve_addr|].
      iFrame.
      iApply (region_pointsto_cons _ (pc_b ^+ 6)%a); [solve_addr|solve_addr|].
      iFrame.
      iApply (region_pointsto_cons _ (pc_b ^+ 7)%a); [solve_addr|solve_addr|].
      iFrame.
  Qed.

  Definition kvs_main_add_arg_rmap
      (sealed_key wca3 wca4 wca5 : Word) : Reg :=
    {[ ca0 := sealed_key;
       ca1 := WInt 1;
       ca2 := WInt 12;
       ca3 := wca3;
       ca4 := wca4;
       ca5 := wca5;
       ct0 := WInt 0 ]}.

  Definition kvs_main_adversary_arg_rmap : Reg :=
    {[ ca0 := WInt 0;
       ca1 := WInt 0;
       ca2 := WInt 0;
       ca3 := WInt 0;
       ca4 := WInt 0;
       ca5 := WInt 0;
       ct0 := WInt 0 ]}.

  Definition kvs_main_read_arg_rmap (sealed_key : Word) : Reg :=
    {[ ca0 := sealed_key;
       ca1 := WInt 1;
       ca2 := WInt 0;
       ca3 := WInt 0;
       ca4 := WInt 0;
       ca5 := WInt 0;
       ct0 := WInt 0 ]}.

  Lemma kvs_main_add_arg_rmap_is_arg sealed_key wca3 wca4 wca5 :
    is_arg_rmap (kvs_main_add_arg_rmap sealed_key wca3 wca4 wca5) 8.
  Proof. by rewrite /is_arg_rmap /kvs_main_add_arg_rmap. Qed.

  Lemma kvs_main_adversary_arg_rmap_is_arg :
    is_arg_rmap kvs_main_adversary_arg_rmap 8.
  Proof. by rewrite /is_arg_rmap /kvs_main_adversary_arg_rmap. Qed.

  Lemma kvs_main_read_arg_rmap_is_arg sealed_key :
    is_arg_rmap (kvs_main_read_arg_rmap sealed_key) 8.
  Proof. by rewrite /is_arg_rmap /kvs_main_read_arg_rmap. Qed.

  Lemma kvs_main_adversary_arg_rmap_resources (W : WORLD) (C : CmptName) :
    ca0 ↦ᵣ WInt 0 ∗ ca1 ↦ᵣ WInt 0 ∗ ca2 ↦ᵣ WInt 0
    ∗ ca3 ↦ᵣ WInt 0 ∗ ca4 ↦ᵣ WInt 0 ∗ ca5 ↦ᵣ WInt 0
    ∗ ct0 ↦ᵣ WInt 0
    -∗ [∗ map] rarg ↦ warg ∈ kvs_main_adversary_arg_rmap,
        rarg ↦ᵣ warg ∗ interp W C warg.
  Proof.
    iIntros "(Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & Hct0)".
    iAssert (interp W C (WInt 0)) as "#Hint".
    { iApply interp_int. }
    rewrite /kvs_main_adversary_arg_rmap.
    repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
    done.
  Qed.

  Lemma kvs_main_adversary_phase_spec
      (Nswitcher : namespace) (W : WORLD) (C : CmptName)
      (wcgp wcra wcs0 wcs1 : Word)
      (b_stk e_stk a_stk : Addr) (target : Sealable)
      (stk_mem : list Word) (rmap : Reg)
      (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    dom rmap =
      all_registers_s ∖
        ({[PC; cgp; cra; csp; ct1; cs0; cs1]} ∪ dom_arg_rmap 8) ->
    na_inv cerise_nais Nswitcher switcher_inv
    ∗ na_own cerise_nais ⊤
    ∗ PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ wcgp ∗ cra ↦ᵣ wcra
    ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
    ∗ ct1 ↦ᵣ WSealed ot_switcher target
    ∗ interp W C (WSealed ot_switcher target)
    ∗ (WSealed ot_switcher target) ↦□ₑ 0
    ∗ cs0 ↦ᵣ wcs0 ∗ cs1 ↦ᵣ wcs1
    ∗ ca0 ↦ᵣ WInt 0 ∗ ca1 ↦ᵣ WInt 0 ∗ ca2 ↦ᵣ WInt 0
    ∗ ca3 ↦ᵣ WInt 0 ∗ ca4 ↦ᵣ WInt 0 ∗ ca5 ↦ᵣ WInt 0
    ∗ ct0 ↦ᵣ WInt 0
    ∗ ([∗ map] r ↦ w ∈ rmap, r ↦ᵣ w)
    ∗ [[a_stk, e_stk]] ↦ₐ [[stk_mem]]
    ∗ world_interp W C
    ∗ StackRevokedResources W C (finz.seq_between a_stk e_stk)
    ∗ ⌜revoked_addresses W (finz.seq_between a_stk e_stk)⌝
    ∗ cstack_frag cstk
    ∗ interp_continuation cstk Ws Cs
    ∗ ▷ (∀ (W2 : WORLD) (rmap' : Reg) (stk_mem' : list Word) l',
        ⌜extract_temporaries_condition
          W2 (l' ++ finz.seq_between (a_stk ^+ 4)%a e_stk)⌝
        ∗ RevokedResources W2 C l'
        ∗ ⌜revoked_addresses (revoke W2) l'⌝
        ∗ ⌜related_sts_pub_world
            (std_update_multiple W
              (finz.seq_between (a_stk ^+ 4)%a e_stk) Temporary) W2⌝
        ∗ ([∗ list] a ∈ finz.seq_between (a_stk ^+ 4)%a e_stk,
            ⌜std W2 !! a = Some Temporary⌝)
        ∗ ⌜dom rmap' =
            all_registers_s ∖ {[PC; cgp; cra; csp; ca0; ca1; cs0; cs1]}⌝
        ∗ StackRevokedResources W2 C (finz.seq_between a_stk e_stk)
        ∗ ⌜revoked_addresses (revoke W2)
            (finz.seq_between a_stk e_stk)⌝
        ∗ na_own cerise_nais ⊤
        ∗ ⌜(b_stk <= (a_stk ^+ 4)%a
             ∧ (a_stk ^+ 4)%a <= e_stk
             ∧ (a_stk + 4)%a = Some (a_stk ^+ 4)%a)%a⌝
        ∗ world_interp (revoke W2) C
        ∗ cstack_frag cstk
        ∗ PC ↦ᵣ updatePcPerm wcra
        ∗ cgp ↦ᵣ wcgp ∗ cra ↦ᵣ wcra
        ∗ cs0 ↦ᵣ wcs0 ∗ cs1 ↦ᵣ wcs1
        ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
        ∗ (∃ warg0, ca0 ↦ᵣ warg0 ∗ interp W2 C warg0)
        ∗ (∃ warg1, ca1 ↦ᵣ warg1 ∗ interp W2 C warg1)
        ∗ ([∗ map] r ↦ w ∈ rmap', r ↦ᵣ w ∗ ⌜w = WInt 0⌝)
        ∗ [[a_stk, e_stk]] ↦ₐ [[stk_mem']]
        ∗ interp_continuation cstk Ws Cs
        -∗ WP Seq (Instr Executable)
          {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hrmap)
      "(#Hswitcher & Hna & HPC & Hcgp & Hcra & Hcsp
       & Hct1 & #Htarget & #Hentry & Hcs0 & Hcs1
       & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & Hct0
       & Hrmap & Hstk & Hworld & Hrevoked & %Hrevoked
       & Hcstk & HK & Hpost)".
    iApply (switcher_cc_specification Nswitcher W C wcgp wcra wcs0 wcs1
      b_stk e_stk a_stk target stk_mem kvs_main_adversary_arg_rmap
      rmap cstk Ws Cs 0 with
      "[- $Hswitcher $Hna $HPC $Hcgp $Hcra $Hcsp $Hct1
       $Hcs0 $Hcs1 $Hrmap $Hstk $Hworld $Hrevoked $Hcstk $HK
       $Htarget $Hentry $Hpost]").
    - exact Hrmap.
    - apply kvs_main_adversary_arg_rmap_is_arg.
    - iSplitL "Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0".
      + iPoseProof (kvs_main_adversary_arg_rmap_resources W C with
          "[$Hca0 $Hca1 $Hca2 $Hca3 $Hca4 $Hca5 $Hct0]") as "Hargs".
        iApply (big_sepM_impl with "Hargs").
        iModIntro. iIntros (r w Hr) "[Hr _]".
        iFrame.
      + iFrame "∗#%".
  Qed.

  Lemma kvs_main_add_phase_spec
      (pc_b pc_e pc_a cgp_b cgp_e static_sealed_b csp_b csp_e : Addr)
      (rmap : Reg) (KVS_USER_KEY_MAIN : Z)
      (b_assert e_assert : Addr) (B_f : Sealable)
      (Nswitcher : namespace) (stk_mem : list Word) (cstk : CSTK) :
    dom rmap = all_registers_s ∖ {[PC; cgp; csp]} ->
    (forall r, r ∈ dom rmap -> is_Some (rmap !! r)) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length kvs_main_code)%a ->
    withinBounds static_sealed_b (static_sealed_b ^+ 1)%a
      static_sealed_b = true ->
    na_inv cerise_nais Nswitcher switcher_inv
    ∗ na_inv cerise_nais (Nkvs.@"physical") kvs_inv
    ∗ na_inv cerise_nais (Nkvs.@"logical") logical_kvs_inv
    ∗ inv (export_table_PCCN Nkvs_exp_tbl)
        (b_kvs_exp_tbl ↦ₐ WCap RX Global KVS_pcc_b KVS_pcc_e KVS_pcc_b)
    ∗ inv (export_table_CGPN Nkvs_exp_tbl)
        ((b_kvs_exp_tbl ^+ 1)%a ↦ₐ
          WCap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b)
    ∗ inv (export_table_entryN Nkvs_exp_tbl kvs_addOrUpdate_exp_tbl_addr)
        (kvs_addOrUpdate_exp_tbl_addr ↦ₐ kvs_exp_tbl_entry_addOrUpdate)
    ∗ na_own cerise_nais ⊤
    ∗ PC ↦ᵣ WCap RX Global pc_b pc_e pc_a
    ∗ cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b
    ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
    ∗ ([∗ map] r ↦ w ∈ rmap, r ↦ᵣ w)
    ∗ pc_b ↦ₐ
        WSentry XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ (pc_b ^+ KVS_INSERT_OFFSET)%a ↦ₐ
        WSealed ot_switcher (KVS_addOrUpdate Global)
    ∗ (pc_b ^+ SEALED_USER_KEY_OFFSET)%a ↦ₐ
        kvs_user_seal_key Global static_sealed_b
    ∗ codefrag pc_a kvs_main_code
    ∗ static_sealed_b ↦ₐ WInt KVS_USER_KEY_MAIN
    ∗ user_kvs_inv KVS_USER_KEY_MAIN
    ∗ (KVS_USER_KEY_MAIN, 1) ↦(KVS) ⊥
    ∗ [[csp_b, csp_e]] ↦ₐ [[stk_mem]]
    ∗ cstack_frag cstk
    ∗ ▷ (∀ (rmap_ret : Reg),
        ⌜dom rmap_ret =
          all_registers_s ∖ {[PC; csp; cgp; cra; cs0; cs1; ca0; ca1]}⌝
        ∗ na_own cerise_nais ⊤
        ∗ PC ↦ᵣ WCap RX Global pc_b pc_e
            (pc_a ^+ length kvs_main_add_phase_instrs)%a
        ∗ cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b
        ∗ (∃ wcra, cra ↦ᵣ wcra)
        ∗ cs0 ↦ᵣ WInt 0
        ∗ cs1 ↦ᵣ kvs_user_seal_key Global static_sealed_b
        ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
        ∗ ca0 ↦ᵣ WInt 0 ∗ ca1 ↦ᵣ WInt 0
        ∗ ([∗ map] r ↦ w ∈ rmap_ret, r ↦ᵣ w ∗ ⌜w = WInt 0⌝)
        ∗ [[csp_b, csp_e]] ↦ₐ
            [[region_addrs_zeroes csp_b csp_e]]
        ∗ cstack_frag cstk
        ∗ static_sealed_b ↦ₐ WInt KVS_USER_KEY_MAIN
        ∗ user_kvs_inv KVS_USER_KEY_MAIN
        ∗ (KVS_USER_KEY_MAIN, 1) ↦(KVS) WInt 12
        ∗ pc_b ↦ₐ
            WSentry XSRW_ Local b_switcher e_switcher a_switcher_call
        ∗ (pc_b ^+ KVS_INSERT_OFFSET)%a ↦ₐ
            WSealed ot_switcher (KVS_addOrUpdate Global)
        ∗ (pc_b ^+ SEALED_USER_KEY_OFFSET)%a ↦ₐ
            kvs_user_seal_key Global static_sealed_b
        ∗ codefrag pc_a kvs_main_code
        -∗ WP Seq (Instr Executable)
          {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hrmap_dom Hrmap_init HsubBounds Hstatic_sealed_b)
      "(#Hswitcher & #Hkvs & #Hkvs_logical
       & #Hkvs_exp_tbl_pcc & #Hkvs_exp_tbl_cgp
       & #Hkvs_exp_tbl_addOrUpdate
       & Hna & HPC & Hcgp & Hcsp & Hrmap
       & Himport_switcher & Himport_kvs_addOrUpdate
       & Himport_sealed_user_key & Hcode_main
       & Hstatic_sealed_b & HLUKVS & Hkvs_1
       & Hstk & Hcstk_frag & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    iExtractList "Hrmap" [cra;ca0;ca1;ca2;ctp;ct0;ct1;cs0;cs1]
      as ["Hcra"; "Hca0"; "Hca1"; "Hca2"; "Hctp"; "Hct0";
          "Hct1"; "Hcs0"; "Hcs1"].
    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hcs1 $Hct0 $Hct1 $Himport_sealed_user_key $Hcode]"); eauto.
    { rewrite /SEALED_USER_KEY_OFFSET; solve_addr. }
    iNext ; iIntros "(HPC & Hcs1 & Hct0 & Hct1 & Hcode & Himport_sealed_user_key)".
    iEval (cbn) in "Hcs1".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    focus_block 1 "Hcode_main" as a_main1 Ha_main1 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Mov ca0 cs1; *)
    iInstr "Hcode".
    (* Mov ca1 1; *)
    iInstr "Hcode".
    destruct ( decide (ca1 = cnull) ) as [|_] ; first done.
    (* Mov ca2 12 *)
    iInstr "Hcode".
    destruct ( decide (ca2 = cnull) ) as [|_]; first done.
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* -------------- BLOCK 2 and 3 : FETCH -------------- *)
    (* --------------------------------------------------- *)

    focus_block 2 "Hcode_main" as a_fetch1 Ha_fetch1 "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent a_main1.
    iApply (fetch_spec with "[- $HPC $Hctp $Hct0 $Hct1 $Hcode]"); eauto.
    { rewrite /SWITCHER_CALL_OFFSET; solve_addr. }
    replace (pc_b ^+ SWITCHER_CALL_OFFSET)%a with pc_b by (rewrite /SWITCHER_CALL_OFFSET; solve_addr).
    iFrame "Himport_switcher".
    iNext ; iIntros "(HPC & Hctp & Hct0 & Hct1 & Hcode & Himport_switcher)".
    iEval (cbn) in "Hctp".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    focus_block 3 "Hcode_main" as a_fetch2 Ha_fetch2 "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent a_fetch1.
    iApply (fetch_spec with "[- $HPC $Hct1 $Hct0 $Hcs0 $Hcode $Himport_kvs_addOrUpdate]"); eauto.
    { rewrite /KVS_INSERT_OFFSET; solve_addr. }
    iNext ; iIntros "(HPC & Hct1 & Hct0 & Hcs0 & Hcode & Himport_kvs_addOrUpdate)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 4: INSERT ----------------- *)
    (* --------------------------------------------------- *)
    focus_block 4 "Hcode_main" as a_insert_kvs Ha_insert_kvs "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent a_fetch2.
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    pose proof kvs_exp_tbl_size as Hkvs_exp_tbl_size.
    rewrite /length_kvs_exports_tbl /kvs_nb_exports in Hkvs_exp_tbl_size.
    iExtractList "Hrmap" [ca3;ca4;ca5] as ["Hca3"; "Hca4"; "Hca5"].

    (* Use switcher call KtK *)
    set (rmap_arg := kvs_main_add_arg_rmap
      (kvs_user_seal_key Global static_sealed_b) wca3 wca4 wca5).

    iAssert ([∗ map] rarg↦warg ∈ rmap_arg, rarg ↦ᵣ warg )%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg; rewrite /kvs_main_add_arg_rmap.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done.
    }
    iInsertList "Hrmap" [ctp].
    set (rmap' := <[ctp := _]> _ ).

    iPoseProof (KVS_add_spec_known_to_known
                  (WCap RW Global cgp_b cgp_e cgp_b)
                  (WSentry RX Global pc_b pc_e (a_insert_kvs ^+ 1)%a)
                  (WInt 0) (kvs_user_seal_key Global static_sealed_b)
                  csp_b csp_e csp_b rmap_arg cstk ⊤
                  KVS_USER_KEY_MAIN 1 Global static_sealed_b (WInt 12)
                 with "[Hkvs Hkvs_logical]") as "HKVS_f"; auto.
    { rewrite /is_uint16 /UINT16_MIN /UINT16_MAX; lia. }

    iApply (switcher_cc_specification_known_to_known_end_to_end
              Nswitcher
              (WCap RW Global cgp_b cgp_e cgp_b)
              (WSentry RX Global pc_b pc_e (a_insert_kvs ^+ 1)%a)
              (WInt 0) (kvs_user_seal_key Global static_sealed_b)
              csp_b csp_e csp_b stk_mem rmap_arg rmap' cstk
              kvs_addOrUpdate_nargs ⊤ Nkvs_exp_tbl
              b_kvs_exp_tbl kvs_addOrUpdate_exp_tbl_addr e_kvs_exp_tbl
              KVS_pcc_b KVS_pcc_e KVS_cgp_b KVS_cgp_e
              kvs_addOrUpdate_pcc_off
             with
             "[- $Hswitcher $Hkvs_exp_tbl_pcc $Hkvs_exp_tbl_cgp $Hkvs_exp_tbl_addOrUpdate
                 $Hna $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
                 $Hstk $Hcstk_frag
                 $HKVS_f
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
    { apply kvs_main_add_arg_rmap_is_arg. }
    iSplitL "Hkvs Hkvs_logical Hstatic_sealed_b HLUKVS Hkvs_1"; first iFrame.
    iNext.
    iIntros "[
    (%wca0_ret & %wca1_ret & %rmap_ret & %Hdom_rmap_ret
    & Hna & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
    & Hca0 & Hca1 & Hrmap & Hstk & Hcstk & HKVS_post)
    |
    (%rmap_ret & %stk_mem' & %Hdom_rmap_ret & Hna
    & HPC & Hcgp & Hcra & Hcsp & Hcs0 & Hcs1
    & Hca0 & Hca1 & Hrmap & Hstk & Hcstk_frag & HKVS_pre)
    ]"
    ; iEval (cbn) in "HPC"
    ; cycle 1.
    {
      focus_block 5 "Hcode_main" as a_blk_4  Ha_blk_4 "Hcode" "Hcont"; iHide "Hcont" as hcont
      ; clear dependent a_insert_kvs.
      (* Jnz 2 ca0 *)
      iInstr "Hcode".
      (* Halt *)
      iInstr "Hcode".
      wp_end; iIntros (_); iFrame "Hna".
    }
    iDestruct "HKVS_post"
      as "(Hstatic_sealed_b & HLUKVS & %Hwca1_ret
           & [(%Hcan_store & %Hwca0_ret & Hkvs_1)
             | (%Hwca0_ret & Hkvs_1)])".
    all: subst wca1_ret.
    2: { (* Case where there was not more empty slot *)
      subst wca0_ret.
      focus_block 5 "Hcode_main" as a_blk_4  Ha_blk_4 "Hcode" "Hcont"; iHide "Hcont" as hcont
      ; clear dependent a_insert_kvs.
      (* Jnz 2 ca0 *)
      iInstr "Hcode".
      (* Halt *)
      iInstr "Hcode".
      wp_end; iIntros (_); iFrame "Hna".
    }
    subst wca0_ret.
    (* Case where insert succeeded  *)
    focus_block 5 "Hcode_main" as a_blk_4  Ha_blk_4 "Hcode" "Hcont"; iHide "Hcont" as hcont
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
    iApply ("Hpost" $! rmap_ret).
    iFrame "Hna Hcgp Hcs0 Hcs1 Hcsp Hca0 Hca1 Hrmap Hstk Hcstk
      Hstatic_sealed_b HLUKVS Hkvs_1 Himport_switcher
      Himport_kvs_addOrUpdate Himport_sealed_user_key Hcode_main".
    replace (pc_a ^+ length kvs_main_add_phase_instrs)%a
      with (a_blk_4 ^+ 5)%a.
    2: { rewrite /kvs_main_add_phase_instrs. solve_addr. }
    iFrame "HPC".
    iSplit; first done.
    iExists _. iFrame.
  Qed.

  Lemma kvs_main_read_assert_phase_spec
      (pc_b pc_e pc_a cgp_b cgp_e static_sealed_b csp_b csp_e : Addr)
      (rmap : Reg) (wca0 wca1 wcra wcs0 : Word)
      (KVS_USER_KEY_MAIN : Z)
      (b_assert e_assert a_flag : Addr) (Nassert Nswitcher : namespace)
      (stk_mem : list Word) (cstk : CSTK) :
    Nswitcher ## Nassert ->
    dom rmap =
      all_registers_s ∖ {[PC; cgp; cra; csp; ca0; ca1; cs0; cs1]} ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length kvs_main_code)%a ->
    withinBounds static_sealed_b (static_sealed_b ^+ 1)%a
      static_sealed_b = true ->
    na_inv cerise_nais Nassert (assert_inv b_assert e_assert a_flag)
    ∗ na_inv cerise_nais Nswitcher switcher_inv
    ∗ na_inv cerise_nais (Nkvs.@"physical") kvs_inv
    ∗ na_inv cerise_nais (Nkvs.@"logical") logical_kvs_inv
    ∗ inv (export_table_PCCN Nkvs_exp_tbl)
        (b_kvs_exp_tbl ↦ₐ WCap RX Global KVS_pcc_b KVS_pcc_e KVS_pcc_b)
    ∗ inv (export_table_CGPN Nkvs_exp_tbl)
        ((b_kvs_exp_tbl ^+ 1)%a ↦ₐ
          WCap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b)
    ∗ inv (export_table_entryN Nkvs_exp_tbl kvs_read_exp_tbl_addr)
        (kvs_read_exp_tbl_addr ↦ₐ kvs_exp_tbl_entry_read)
    ∗ na_own cerise_nais ⊤
    ∗ PC ↦ᵣ WCap RX Global pc_b pc_e
        (pc_a ^+ length
          (kvs_main_add_phase_instrs ++
           kvs_main_adversary_phase_instrs))%a
    ∗ cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b
    ∗ cra ↦ᵣ wcra ∗ cs0 ↦ᵣ wcs0
    ∗ cs1 ↦ᵣ kvs_user_seal_key Global static_sealed_b
    ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
    ∗ ca0 ↦ᵣ wca0 ∗ ca1 ↦ᵣ wca1
    ∗ ([∗ map] r ↦ w ∈ rmap, r ↦ᵣ w ∗ ⌜w = WInt 0⌝)
    ∗ [[csp_b, csp_e]] ↦ₐ [[stk_mem]]
    ∗ cstack_frag cstk
    ∗ static_sealed_b ↦ₐ WInt KVS_USER_KEY_MAIN
    ∗ user_kvs_inv KVS_USER_KEY_MAIN
    ∗ (KVS_USER_KEY_MAIN, 1) ↦(KVS) WInt 12
    ∗ pc_b ↦ₐ
        WSentry XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ (pc_b ^+ KVS_READ_OFFSET)%a ↦ₐ
        WSealed ot_switcher (KVS_read Global)
    ∗ (pc_b ^+ ASSERT_OFFSET)%a ↦ₐ
        WSentry RX Global b_assert e_assert b_assert
    ∗ codefrag pc_a kvs_main_code
    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (HNswitcher_assert Hdom_rmap HsubBounds Hstatic_sealed_b)
      "(#Hassert & #Hswitcher & #Hkvs & #Hkvs_logical
       & #Hkvs_exp_tbl_pcc & #Hkvs_exp_tbl_cgp & #Hkvs_exp_tbl_read
       & Hna & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
       & Hca0 & Hca1 & Hrmap & Hstk & Hcstk_frag
       & Hstatic_sealed_b & HLUKVS & Hkvs_1
       & Himport_switcher & Himport_kvs_read & Himport_assert
       & Hcode_main)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    pose proof kvs_exp_tbl_size as Hkvs_exp_tbl_size.
    rewrite /length_kvs_exports_tbl /kvs_nb_exports in Hkvs_exp_tbl_size.
    iEval (cbn [kvs_main_add_phase_instrs
      kvs_main_adversary_phase_instrs]) in "HPC".
    iEval (rewrite /kvs_main_code) in "Hcode_main".
    (* Extract all registers used by the read phase while their returned-map
       zero equalities are still attached. *)
    iExtractList "Hrmap" [ctp;ct0;ct1;ca2;ca3;ca4;ca5] as
      ["[Hctp %]"; "[Hct0 %]"; "[Hct1 %]"; "[Hca2 %]";
       "[Hca3 %]"; "[Hca4 %]"; "[Hca5 %]"]; simplify_eq.
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".

    (* ---------------------------------------------------------- *)
    (* ----------------- BLOCK 9: PREPARE READ  ----------------- *)
    (* ---------------------------------------------------------- *)
    focus_block 9 "Hcode_main" as a_blk Ha_blk "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Mov ca0 cs1 *)
    iInstr "Hcode".
    (* Mov ca1 1 *)
    iInstr "Hcode".
    destruct ( decide (ca1 = cnull) ) as [|_] ; first done.
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* ----------------------------------------------------- *)
    (* -------------- BLOCK 10 and 11 : FETCH -------------- *)
    (* ----------------------------------------------------- *)
    focus_block 10 "Hcode_main" as a_fetch1  Ha_fetch1 "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent Ha_blk.
    iApply (fetch_spec with "[- $HPC $Hctp $Hct0 $Hct1 $Hcode]"); eauto.
    { rewrite /SWITCHER_CALL_OFFSET; solve_addr. }
    replace (pc_b ^+ SWITCHER_CALL_OFFSET)%a with pc_b by (rewrite /SWITCHER_CALL_OFFSET; solve_addr).
    iFrame "Himport_switcher".
    iNext ; iIntros "(HPC & Hctp & Hct0 & Hct1 & Hcode & Himport_switcher)".
    iEval (cbn) in "Hctp".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    focus_block 11 "Hcode_main" as a_fetch2 Ha_fetch2 "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent a_fetch1.
    iApply (fetch_spec with "[- $HPC $Hct1 $Hct0 $Hcs0 $Hcode $Himport_kvs_read]"); eauto.
    { rewrite /KVS_READ_OFFSET; solve_addr. }
    iNext ; iIntros "(HPC & Hct1 & Hct0 & Hcs0 & Hcode & Himport_kvs_read)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".


    (* -------------------------------------------------- *)
    (* ----------------- BLOCK 12: READ ----------------- *)
    (* -------------------------------------------------- *)
    focus_block 12 "Hcode_main" as a_insert_kvs Ha_insert_kvs "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent a_fetch2.
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Use switcher call KtK *)
    set (rmap_arg_read := kvs_main_read_arg_rmap
      (kvs_user_seal_key Global static_sealed_b)).

    iAssert ([∗ map] rarg↦warg ∈ rmap_arg_read, rarg ↦ᵣ warg )%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg_read".
    { subst rmap_arg_read; rewrite /kvs_main_read_arg_rmap.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done.
    }
    iInsertList "Hrmap" [ctp].
    set (rmap_read_call := <[ctp := _]> _ ).

    iPoseProof (KVS_read_spec_known_to_known
      (WCap RW Global cgp_b cgp_e cgp_b)
      (WSentry RX Global pc_b pc_e (a_insert_kvs ^+ 1)%a)
      (WInt 0) (kvs_user_seal_key Global static_sealed_b)
      csp_b csp_e csp_b rmap_arg_read cstk ⊤
      KVS_USER_KEY_MAIN 1 Global static_sealed_b (WInt 12)
      with "[Hkvs Hkvs_logical]") as "HKVS_f"; auto.
    { rewrite /is_uint16 /UINT16_MIN /UINT16_MAX; lia. }

    iApply (switcher_cc_specification_known_to_known_end_to_end
              Nswitcher
              (WCap RW Global cgp_b cgp_e cgp_b)
              (WSentry RX Global pc_b pc_e (a_insert_kvs ^+ 1)%a)
              (WInt 0) (kvs_user_seal_key Global static_sealed_b)
              csp_b csp_e csp_b stk_mem rmap_arg_read rmap_read_call cstk
              kvs_read_nargs ⊤ Nkvs_exp_tbl
              b_kvs_exp_tbl kvs_read_exp_tbl_addr e_kvs_exp_tbl
              KVS_pcc_b KVS_pcc_e KVS_cgp_b KVS_cgp_e
              kvs_read_pcc_off
             with
             "[- $Hswitcher $Hkvs_exp_tbl_pcc $Hkvs_exp_tbl_cgp $Hkvs_exp_tbl_read
                 $Hna $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1
                 $Hrmap_arg_read $Hrmap $Hstk $Hcstk_frag
                 $HKVS_f
                 ]"); auto.
    { rewrite /kvs_read_exp_tbl_addr /kvs_read_exp_tbl_off; solve_addr+Hkvs_exp_tbl_size. }
    { solve_addr+Hkvs_exp_tbl_size. }
    { rewrite /kvs_read_exp_tbl_addr /kvs_read_exp_tbl_off; solve_addr+Hkvs_exp_tbl_size. }
    { rewrite /kvs_read_nargs; lia. }
    {  subst rmap_read_call.
       rewrite dom_insert_L.
       repeat (rewrite dom_delete_L).
       rewrite Hdom_rmap /dom_arg_rmap /=.
       set_solver+.
    }
    { apply kvs_main_read_arg_rmap_is_arg. }
    iSplitL "Hkvs Hkvs_logical Hstatic_sealed_b HLUKVS Hkvs_1"; first iFrame.
    iNext.
    iIntros "[
    (%wca0_ret & %wca1_ret & %rmap_read & %Hdom_rmap_read
    & Hna & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
    & Hca0 & Hca1 & Hrmap & Hstk & Hcstk & HKVS_read_post)
    |
    (%rmap_read & %stk_mem' & %Hdom_rmap_read & Hna
    & HPC & Hcgp & Hcra & Hcsp & Hcs0 & Hcs1
    & Hca0 & Hca1 & Hrmap & Hstk & Hcstk_frag & HKVS_read_pre)
    ]"
    ; iEval (cbn) in "HPC"
    ; cycle 1.
    {
      focus_block 13 "Hcode_main" as a_assert1  Ha_assert1 "Hcode" "Hcont"; iHide "Hcont" as hcont
      ; clear dependent a_insert_kvs.
      (* Jnz 2 ca0 *)
      iInstr "Hcode".
      (* Halt *)
      iInstr "Hcode".
      wp_end; iIntros (_); iFrame "Hna".
    }
    iDestruct "HKVS_read_post"
      as "(Hstatic_sealed_b & HLUKVS & Hkvs_1 & %Hwca0_ret & %Hwca1_ret)".
    subst wca0_ret wca1_ret.

    iExtractList "Hrmap" [ct0;ct1;ct2;ct3;ct4;cnull] as
      ["[Hct0 %]";"[Hct1 %]";"[Hct2 %]";"[Hct3 %]";"[Hct4 %]";"[Hcnull %]"]; simplify_eq.
    (* -------------------------------------------------- *)
    (* ---------------- BLOCK 13: ASSERT ---------------- *)
    (* -------------------------------------------------- *)
    focus_block 13 "Hcode_main" as a_assert1  Ha_assert1 "Hcode" "Hcont"; iHide "Hcont" as hcont
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
    (* ---------------- BLOCK 14: ASSERT ---------------- *)
    (* -------------------------------------------------- *)
    focus_block 14 "Hcode_main" as a_assert2  Ha_assert2 "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent Ha_assert1.
    iApply (assert_success_spec with
             "[- $Hassert $Hna $HPC $Hct2 $Hct3 $Hct4 $Hct0 $Hct1 $Hcnull $Hcra
              $Hcode $Himport_assert]"); auto.
    { rewrite /ASSERT_OFFSET; solve_addr. }
    iNext; iIntros "(Hna & HPC & Hct2 & Hct3 & Hct4 & Hcra & Hct0 & Hct1 & Hcnull
                    & Hcode & Himport_assert)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* ---------------------------------------------------- *)
    (* ------------------ BLOCK 15: HALT ------------------ *)
    (* ---------------------------------------------------- *)
    focus_block 15 "Hcode_main" as a_halt Ha_halt "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Halt *)
    iInstr "Hcode".
    wp_end; iIntros "_"; iFrame.
  Qed.

End KVS_Main_Blocks.
