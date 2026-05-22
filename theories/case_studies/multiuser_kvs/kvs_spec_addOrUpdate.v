From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel rules.
From cap_machine Require Import switcher kvs kvs_preamble.
From cap_machine Require Import proofmode.

Section KVS_spec_addOrUpdate.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {kvsg:kvsG Σ}
    {nainv: logrel_na_invs Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Lemma KVS_update_spec `{KVS : kvsLayout}
    (pc_b pc_b' pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (wret wca2 : Word)
    (user_key nkey : Z)
    (idx : nat)
    (m : kvs_map)
    :

    let imports :=
      kvs_imports b_switcher e_switcher a_switcher_call ot_switcher
    in
    let fkey := (kvs_full_key user_key nkey) in

    SubBounds pc_b pc_e pc_a (pc_a ^+ length kvs_addOrUpdate_instrs)%a ->
    (0 <= user_key < top)%Z ->

    (cgp_b + length kvs_data)%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_b' ->

    canStore RW wca2 = true ->

    ( na_own logrel_nais ⊤ ∗

      (* initial register file *)
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ kvs_user_seal_key user_key ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to update *)
      ca2 ↦ᵣ wca2 ∗ (* New value *)
      ctp ↦ᵣ - ∗ (* scratch *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      (* initial memory layout *)
      [[ pc_b , pc_b' ]] ↦ₐ [[ imports ]] ∗
      codefrag pc_a kvs_addOrUpdate_instrs ∗
      cgp_b ↦ₐ kvs_service_unsealing_key ∗

      isKVS (cgp_b ^+ 1)%a m ∗
      fkey ⤇(KVS)[ idx ] - ∗

      ▷ (na_own logrel_nais ⊤ ∗
         PC ↦ᵣ updatePcPerm wret ∗
         cgp ↦ᵣ - ∗
         cra ↦ᵣ - ∗
         ca0 ↦ᵣ WInt ASM_TRUE ∗ (* TRUE: the key exists in the map and is updated *)
         ca1 ↦ᵣ WInt 0 ∗
         ca2 ↦ᵣ - ∗
         ctp ↦ᵣ - ∗ (* scratch *)
         ct1 ↦ᵣ - ∗ (* scratch *)
         ct2 ↦ᵣ - ∗ (* scratch *)
         cnull ↦ᵣ - ∗
         isKVS (cgp_b ^+ 1)%a (<[ idx := (fkey, wca2) ]> m) ∗
         fkey ⤇(KVS)[idx] wca2
         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros imports fkey.
    iIntros (HsubBounds Hbounds_user_key Hcgp_contiguous Himports_contiguous HcanStore_wca2)
      "(Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2 & [%wcnull Hcnull] &
        Himports & Hcode & Hcgp_b & HKVS & [%fkey_w Hkvs_frag] & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)
    rewrite /kvs_addOrUpdate_instrs /assembled_kvs_addOrUpdate.
    rewrite -/(kvs_getFullKey ca0 ca0 ca1 ct1).
    rewrite -/(kvs_search ca0 ct1 ct2).
    rewrite -/(kvs_search ctp ct1 ct2).

    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (KVS_getFullKey_spec with "[- $HPC $Hcgp $Hca0 $Hca1 $Hct1 $Hcgp_b $Hcode]"); eauto; [|iNext].
    { rewrite /withinBounds; solve_addr. }
    iIntros "(HPC & Hcgp & Hca0 & Hca1 & Hct1 & Hcgp_b & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 1 "Hcode" as a_lea Ha_lea "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)%a); [solve_addr|done]. }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 2 "Hcode" as a_search Ha_search "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_lea.
    iEval (replace (cgp_b ^+ 1)%a with (cgp_b ^+ (1+2*0))%a) in "Hcgp".
    iApply (KVS_search_spec with "[- $HPC $Hcgp $Hca0 $Hct1 $Hct2 $HKVS $Hkvs_frag $Hcode]"); eauto.
    { rewrite /withinBounds; solve_addr. }
    iNext; iIntros "(HPC & Hcgp & Hca0 & Hct1 & Hct2 & HKVS & Hcgp_key & Hcgp_val  & Hfkey & %Hcgp_idx & Hkvs_frag & Hcode)".
    iDestruct (isKVS_open_valid with "HKVS Hkvs_frag") as "%Hm_idx".
    iDestruct (isKVS_open_indom_idx with "HKVS") as "%Hidx".
    { by apply elem_of_dom_2 in Hm_idx. }
    iEval (cbn) in "Hfkey".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 3 "Hcode" as a_addOrUpdate Ha_addOrUpdate "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_search.
    (* Sub ct1 ct1 (-1) *)
    iInstr "Hcode".
    (* Jnz 5 ct1 *)
    iInstr "Hcode".
    { injection; intros; lia. }
    (* Lea cgp 1 *)
    iInstr "Hcode".
    { transitivity ( Some ((cgp_b ^+ (2 + 2 * idx))%a) ); solve_addr+Hcgp_idx Hidx. }
    (* Store cgp (inr ca2) *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (rules_Store.wp_store_success_reg with "[$HPC $Hi $Hca2 $Hcgp $Hcgp_val]"); try solve_pure.
    iNext; iIntros "(HPC & Hi & Hca2 & Hcgp & Hcgp_val)".
    wp_pure.
    iInstr_close "Hcode".

    (* Mov ca0 0 *)
    iInstr "Hcode".
    (* Mov ca1 0 *)
    iInstr "Hcode".
    (* Jalr cnull cra *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    iMod (isKVS_open_update _ _ idx (kvs_full_key user_key nkey) _ wca2 with "HKVS Hkvs_frag") as "[HKVS Hkvs_frag]".
    iDestruct (kvs_frag_kvs_empty_not_empty_slot with "Hkvs_frag Hfkey") as "%Hk".


    iDestruct (close_isKVS with "[$HKVS Hcgp_key Hcgp_val]") as "HKVS";eauto.
    { by simplify_map_eq. }
    {
      replace (cgp_b ^+ (1 + 2 * idx))%a with ((cgp_b ^+ 1) ^+ 2 * idx)%a by solve_addr+Hidx.
      replace (cgp_b ^+ (2 + 2 * idx))%a  with ((cgp_b ^+ 1) ^+ (2 * idx + 1))%a by solve_addr+Hidx.
      iFrame.
      rewrite /isKVS_entry_empty /=.
      destruct (decide (kvs_full_key user_key nkey = EMPTY_SLOT)); done.
    }

    iApply "Hpost"; iFrame.
  Qed.

End KVS_spec_addOrUpdate.
