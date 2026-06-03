From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel rules.
From cap_machine Require Import
  switcher kvs kvs_preamble kvs_spec_getFullKey kvs_spec_search kvs_spec_check_uint16.
From cap_machine Require Import proofmode.

Section KVS_spec_read.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {heapg : heapGS Σ}
    {kvsg:kvsG Σ}
    {nainv: logrel_na_invs Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
    {KVS_layout : kvsLayout} {KVS_layout_WF : kvsLayoutWf} {KVS_users: kvs_users} {KVS_namespaces : kvs_namespaces}
  .

  Lemma KVS_read_spec_in_pre
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (wret : Word)
    (user_key nkey : Z)
    (m : kvs_map) (s : kvs_alloc)
    (w : Word)
    :

    let fkey := (kvs_full_key user_key nkey) in

    SubBounds pc_b pc_e pc_a (pc_a ^+ length kvs_read_instrs)%a ->
    (0 <= user_key < top)%Z ->
    is_uint16 nkey ->

    (cgp_b + length kvs_data)%a = Some cgp_e ->

    (
      (* initial register file *)
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ kvs_user_seal_key user_key ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to read *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      (* initial memory layout *)
      codefrag pc_a kvs_read_instrs ∗
      cgp_b ↦ₐ kvs_service_unsealing_key ∗

      ▷ isKVS (cgp_b ^+ 1)%a m s ∗
      fkey ⤇(KVS) w ∗
      ▷ (PC ↦ᵣ updatePcPerm wret ∗
         cgp ↦ᵣ - ∗
         cra ↦ᵣ - ∗
         ca0 ↦ᵣ WInt ASM_TRUE ∗ (* TRUE: the key exists in the map *)
         ca1 ↦ᵣ w ∗ (* result of the read *)
         ct1 ↦ᵣ - ∗ (* scratch *)
         ct2 ↦ᵣ - ∗ (* scratch *)
         cnull ↦ᵣ - ∗
         codefrag pc_a kvs_read_instrs ∗
         cgp_b ↦ₐ kvs_service_unsealing_key ∗
         isKVS (cgp_b ^+ 1)%a m s ∗
         fkey ⤇(KVS) w
         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros fkey.
    iIntros (HsubBounds Hbounds_user_key Hnkey_is_uint16 Hcgp_contiguous)
      "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hct1 & Hct2 & [%wcnull Hcnull] & Hcode & Hcgp_b & HKVS & Hkvs_frag & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.
    iDestruct (kvs_frag_kvs_frag_idx with "Hkvs_frag") as "(%idx & Hkvs_frag)".

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)
    rewrite /kvs_read_instrs /assembled_kvs_read.
    rewrite -/(kvs_getFullKey ca0 ca0 ca1 ct1).
    rewrite -/(kvs_search ca0 ct1 ct2).
    rewrite -/(kvs_check_uint16 ca1 ct1).

    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (KVS_check_uint16_spec_known with "[- $HPC $Hca1 $Hct1 $Hcode]"); eauto;iNext.
    iIntros "(HPC & Hca1 & Hcode & Hct1)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 1 "Hcode" as a_check_uint Ha_check_uint "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* jnz (".read_not_uint16")%asm ct1; *)
    iInstr "Hcode".
    (* jmp (".read_uint16_check_pass")%asm; *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 2 "Hcode" as a_get_full_key Ha_get_full_key "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent Ha_check_uint.
    iApply (KVS_getFullKey_spec with "[- $HPC $Hcgp $Hca0 $Hca1 $Hct1 $Hcgp_b $Hcode]"); eauto; [|iNext].
    { rewrite /withinBounds; solve_addr. }
    iIntros "(HPC & Hcgp & Hca0 & Hca1 & Hct1 & Hcgp_b & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 3 "Hcode" as a_lea Ha_lea "Hcode" "Hcont"; iHide "Hcont" as hcont ; clear dependent Ha_get_full_key.
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)%a); [solve_addr|done]. }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 4 "Hcode" as a_search Ha_search "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_lea.
    iEval (replace (cgp_b ^+ 1)%a with (cgp_b ^+ (1+2*0))%a) in "Hcgp".
    iApply (KVS_search_spec_in with "[- $HPC $Hcgp $Hca0 $Hct1 $Hct2 $HKVS $Hkvs_frag $Hcode]"); eauto.
    { rewrite /withinBounds; solve_addr. }
    { apply kvs_full_key_not_empty; split; auto; lia. }
    iNext; iIntros "(HPC & Hcgp & Hca0 & Hct1 & Hct2 & HKVS & Hcgp_key & Hcgp_val  & Hfkey & %Hcgp_idx & Hkvs_frag & Hcode)".
    iDestruct (isKVS_open_valid with "HKVS Hkvs_frag") as "%Hm_idx".
    iDestruct (isKVS_open_indom_idx with "HKVS") as "%Hidx".
    { by apply elem_of_dom_2 in Hm_idx. }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 5 "Hcode" as a_read Ha_read "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_search.
    (* Sub ct1 ct1 (-1) *)
    iInstr "Hcode".
    (* Jnz 5 ct1 *)
    iInstr "Hcode".
    { injection; intros; lia. }
    (* Lea cgp 1 *)
    iInstr "Hcode".
    { transitivity ( Some ((cgp_b ^+ (2 + 2 * idx))%a) ); solve_addr+Hcgp_idx Hidx. }
    (* Load ca1 cgp *)
    iInstr "Hcode".
    { split; done. }
    (* Mov ca1 0 *)
    iInstr "Hcode".
    (* Jalr cnull cra *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    iDestruct (close_isKVS with "[$HKVS Hcgp_key Hcgp_val Hfkey]") as "HKVS";eauto.
    {
      replace (cgp_b ^+ (1 + 2 * idx))%a with ((cgp_b ^+ 1) ^+ 2 * idx)%a by solve_addr+Hidx.
      replace (cgp_b ^+ (2 + 2 * idx))%a  with ((cgp_b ^+ 1) ^+ (2 * idx + 1))%a by solve_addr+Hidx.
      iFrame.
    }
    iApply "Hpost"; iFrame.
  Qed.

  Lemma KVS_read_spec_in
    (wret wca2 : Word)
    (user_key nkey : Z) (w : Word)
    (E : coPset)
    :
    let fkey := (kvs_full_key user_key nkey) in

    ↑Nkvs ⊆ E ->

    (0 <= user_key < top)%Z ->
    is_uint16 nkey ->

    ( na_inv logrel_nais Nkvs kvs_inv ∗
      na_own logrel_nais E ∗

      (* initial register file *)
      PC ↦ᵣ WCap RX Global KVS_pcc_b KVS_pcc_e kvs_read_pcc_addr ∗
      cgp ↦ᵣ WCap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ kvs_user_seal_key user_key ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to read *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      fkey ⤇(KVS) w ∗

      ▷ (na_own logrel_nais E ∗
         PC ↦ᵣ updatePcPerm wret ∗
         cgp ↦ᵣ - ∗
         cra ↦ᵣ - ∗
         ca0 ↦ᵣ WInt ASM_TRUE ∗ (* TRUE: the key exists in the map *)
         ca1 ↦ᵣ w ∗ (* result of the read *)
         ct1 ↦ᵣ - ∗ (* scratch *)
         ct2 ↦ᵣ - ∗ (* scratch *)
         cnull ↦ᵣ - ∗
         fkey ⤇(KVS) w
         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros fkey.
    iIntros (Hnkvs_E Hbounds_user_key His_uint16_nkey)
      "(#Hkvs_inv & Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hct1 & Hct2 & Hcnull & Hfkey & Hpost)".
    iMod (na_inv_acc with "Hkvs_inv Hna")
      as "( (%m & %s & >Himports & >Hcode & >Hcgp_b & HKVS & Hspred) & Hna & Hkvs_inv_close)"; eauto.
    pose proof (Hcgp_continuous := KVS_size_data).
    pose proof (HKVS_pcc_b' := KVS_size_imports).
    pose proof (Hcode_continuous := KVS_size_code).
    assert (SubBounds KVS_pcc_b KVS_pcc_e kvs_read_pcc_addr (kvs_read_pcc_addr ^+ length kvs_read_instrs)%a) as HSubBounds.
    { rewrite /kvs_read_pcc_addr; cbn in *; solve_addr. }
    codefrag_facts "Hcode"; rename H into Hpc_contiguous.

    rewrite /kvs_service_instrs.
    focus_block_nochangePC 1 "Hcode" as a_read Ha_read "Hcode" "Hcont"; iHide "Hcont" as hcont.
    assert (a_read = kvs_read_pcc_addr) as -> by (rewrite /kvs_read_pcc_addr ; cbn in * ; solve_addr+Hcode_continuous HKVS_pcc_b' Ha_read).
    iApply (KVS_read_spec_in_pre with "[- $HPC]"); last iFrame; eauto.
    iNext; iIntros "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hct1 & Hct2
              & Hcnull & Hcode & Hcgp_b & HKVS & Hfkey)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    iMod ("Hkvs_inv_close" with "[$Hna $Hcode $Hcgp_b $Himports $HKVS $Hspred]") as "Hna" ; auto.
    iApply "Hpost"; iFrame.
  Qed.

End KVS_spec_read.
