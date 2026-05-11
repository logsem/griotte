From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel rules.
From cap_machine Require Import switcher kvs.
From cap_machine Require Import proofmode.

Section KVS_spec.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {nainv: logrel_na_invs Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Definition kvs_map := list (Z * Word).

  Fixpoint isKVS
    (b e : Addr) (m : kvs_map) : iProp Σ :=
    match m with
    | [] => ⌜ b = e ⌝
    | (k,w)::m' => b ↦ₐ WInt k ∗ (b^+1)%a ↦ₐ w ∗ isKVS (b^+2)%a e m'
    end
  .

  Definition kvs_frag (k : Z * Z) (w : Word) : iProp Σ. Admitted.
  Notation "k ⤇(KVS) w" := (kvs_frag k w) (at level 20) : bi_scope.
  Global Instance persistent_kvs_frag k w : Persistent (k ⤇(KVS) w)%I.
  Admitted.

  Lemma KVS_getFullKey_spec `{KVS : kvsLayout}
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (rsealkey rkey rscratch : RegName)
    (user_key nkey : Z)
    (wscratch : Word)
    :
    let instrs := (kvs_getFullKey_instrs rsealkey rsealkey rkey rscratch) in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->
    withinBounds cgp_b cgp_e cgp_b = true ->
    (0 <= user_key < top)%Z ->

    rscratch ≠ cnull ->
    rsealkey ≠ cnull ->
    rkey ≠ cnull ->

    (
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
      rsealkey ↦ᵣ kvs_user_seal_key user_key ∗
      rkey ↦ᵣ WInt nkey ∗
      rscratch ↦ᵣ wscratch ∗

      cgp_b ↦ₐ kvs_service_unsealing_key ∗
      codefrag pc_a instrs ∗
      ▷ (
          PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
          cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
          rsealkey ↦ᵣ WInt (kvs_full_key user_key nkey) ∗
          rkey ↦ᵣ WInt nkey ∗
          rscratch ↦ᵣ kvs_service_unsealing_key ∗

          cgp_b ↦ₐ kvs_service_unsealing_key ∗
          codefrag pc_a instrs -∗

          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros instrs ; subst instrs.
    iIntros (HsubBounds Hbounds_cgp Hbounds_user_key Hrscratch Hrsealkey Hkey)
      "(HPC & Hcgp & Hrsealkey & Hrkey & Hrscratch & Hcgp_b & Hcode & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)

    (* load rscratch cgp; *)
    iInstr "Hcode".
    { split; done. }
    iEval (cbn) in "Hrscratch".

    (* unseal rdst rsealkey rscratch; *)
    iInstr "Hcode"; first done.
    { rewrite /withinBounds; pose proof KVS_OTYPE_size; solve_addr. }
    (* geta rdst rdst; *)
    iInstr "Hcode".

    (* lshiftl rdst rdst 16; *)
    iInstr "Hcode".
    (* lor rdst rdst rkey *)
    iInstr "Hcode".

    replace (Z.lor ((0 ^+ user_key)%a ≪ 16) nkey) with (kvs_full_key user_key nkey).
    2: {
      replace (@finz.to_z MemNum (0 ^+ user_key)%a) with user_key; first done.
      solve_addr.
    }
    iApply "Hpost"; iFrame.
  Qed.

  Lemma KVS_search_spec `{KVS : kvsLayout}
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (rkey ridx rscratch : RegName)
    (user_key nkey : Z)
    (widx wscratch : Word)
    (m : kvs_map) (w : Word)
    :
    let instrs := (kvs_search_instrs rkey ridx rscratch) in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->
    withinBounds cgp_b cgp_e cgp_b = true ->

    rscratch ≠ cnull ->
    ridx ≠ cnull ->
    rkey ≠ cnull ->

    (
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e (cgp_b ^+1)%a ∗
      rkey ↦ᵣ WInt (kvs_full_key user_key nkey) ∗
      ridx ↦ᵣ widx ∗
      rscratch ↦ᵣ kvs_service_unsealing_key ∗

      isKVS (cgp_b ^+ 1)%a cgp_e m ∗
      (user_key, nkey) ⤇(KVS) w ∗

      codefrag pc_a instrs ∗
      ▷ ( ∀ idx,
            (
            ⌜ 0 <= idx ⌝ ∗
            PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
            cgp ↦ᵣ WCap RW Global cgp_b cgp_e (cgp_b ^+ (1+2*idx) )%a ∗
            rkey ↦ᵣ WInt (kvs_full_key user_key nkey) ∗
            ridx ↦ᵣ WInt idx ∗
            rscratch ↦ᵣ kvs_service_unsealing_key ∗

            isKVS (cgp_b ^+ 1)%a cgp_e m ∗

            codefrag pc_a instrs -∗

            WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}
            )
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros instrs ; subst instrs.
    iIntros (HsubBounds Hbounds_cgp Hrscratch Hridx Hkey)
      "(HPC & Hcgp & Hrkey & Hridx & Hrscratch & HKVS & #Hkvs_frag & Hcode & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)

  Admitted.

  Lemma KVS_read `{KVS : kvsLayout}
    (pc_b pc_b' pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (wret wct1 wct2 : Word)
    (user_key nkey : Z)
    (m : kvs_map)
    (w : Word)
    :

    let imports :=
      kvs_imports b_switcher e_switcher a_switcher_call ot_switcher
    in

    SubBounds pc_b pc_e pc_a (pc_a ^+ length kvs_read_instrs)%a ->
    (0 <= user_key < top)%Z ->

    (cgp_b + length kvs_data)%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_b' ->

    ( na_own logrel_nais ⊤ ∗

      (* initial register file *)
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ kvs_user_seal_key user_key ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to read *)
      ct1 ↦ᵣ wct1 ∗ (* scratch *)
      ct2 ↦ᵣ wct2 ∗ (* scratch *)

      (* initial memory layout *)
      [[ pc_b , pc_b' ]] ↦ₐ [[ imports ]] ∗
      codefrag pc_a kvs_read_instrs ∗
      cgp_b ↦ₐ kvs_service_unsealing_key ∗

      isKVS (cgp_b ^+ 1)%a cgp_e m ∗
      (user_key, nkey) ⤇(KVS) w ∗

      ▷ (na_own logrel_nais ⊤ ∗
         PC ↦ᵣ updatePcPerm wret ∗
         cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
         cra ↦ᵣ wret ∗
         ca0 ↦ᵣ WInt ASM_TRUE ∗ (* TRUE: the key exists in the map *)
         ca1 ↦ᵣ w ∗ (* result of the read *)
         ct1 ↦ᵣ wct1 ∗ (* scratch *)
         ct2 ↦ᵣ wct2 (* scratch *)
         -∗ WP Instr Halted {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros imports.
    iIntros (HsubBounds Hbounds_user_key Hcgp_contiguous Himports_contiguous)
      "(Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hct1 & Hct2 & Himports & Hcode & Hcgp_b & HKVS & Hkvs_frag & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)
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
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    (* Store cgp 0%Z; *)
    iInstr "Hcode".
    { solve_addr. }
    iHide "Hφ" as hφ.

  Admitted.

Section KVS_spec.
