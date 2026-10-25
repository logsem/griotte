From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode.
From griotte Require Import logrel rules.
From griotte Require Import wp_rules_interp.
From griotte Require Import switcher kvs.
From griotte Require Export kvs_preamble.

Section KVS_getFullKey.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {relg : relGS Σ}
    {kvsg:kvsG Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
    {KVS_layout : kvsLayout} {KVS_layout_WF : kvsLayoutWf}
  .

  (*** Specification for known code *)
  Lemma KVS_getFullKey_spec
    (pc_b pc_e pc_a : Addr) (off : Z)
    (rdst rsealkey rkey : RegName)
    (user_key nkey : Z) (πnkey : option AId) (l_user_key : Locality) ( user_key_addr : Addr )
    :
    let instrs := (kvs_getFullKey_instrs off rdst rsealkey rkey) in
    is_shadow_address (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a = false ->
    is_shadow_address user_key_addr = false ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->
    (pc_a + off)%a = Some (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ->
    withinBounds user_key_addr (user_key_addr ^+ 1)%a user_key_addr = true ->


    rsealkey ≠ cnull ->
    rkey ≠ cnull ->
    rdst ≠ cnull ->

    (
      PC ↦ₚ WCap true RX Global pc_b pc_e pc_a ∗
      rdst ↦ᵣ - ∗
      rsealkey ↦ᵣ kvs_user_seal_key l_user_key user_key_addr ∗
      rkey ↦ᵣ WInt nkey @@? πnkey ∗

      (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ□ kvs_service_unsealing_key ∗
      user_key_addr ↦ₐ WInt user_key ∗

      codefrag_pers pc_a instrs ∗
      ▷ (
          PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
          rdst ↦ᵣ WInt (kvs_full_key user_key nkey) ∗
          rsealkey ↦ᵣ kvs_user_seal_key l_user_key user_key_addr ∗
          rkey ↦ᵣ WInt nkey @@? πnkey ∗

          (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ□ kvs_service_unsealing_key ∗
          user_key_addr ↦ₐ WInt user_key ∗
          codefrag_pers pc_a instrs -∗

          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros instrs ; subst instrs.
    iIntros (Hunsealing_shadow Huser_key_shadow HsubBounds Hoff Hbounds_user_key_addr Hrsealkey Hkey Hdst)
      "(HPC & [%wdst Hrdst] & Hrsealkey & Hrkey
      & #Ha_unsealing & Ha_user_key & #Hcode & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)
    (* Auipcc rdst off. *)
    iInstr "Hcode".
    (* CLoad rdst rdst 0. *)
    iInstr "Hcode".
    { done. }
    { rewrite /UNSEALING_USER_KEY_OFFSET in Hoff |- *; solve_addr. }
    (* UnSeal rdst rdst rsealkey. *)
    iInstr "Hcode"; try done.
    { rewrite /withinBounds; pose proof KVS_OTYPE_size; solve_addr. }
    (* CLoad rdst rdst 0. *)
    iInstr "Hcode".
    { done. }
    (* LShiftL rdst rdst 16. *)
    iInstr "Hcode".
    (* LOr rdst rdst rkey. *)
    iInstr "Hcode".

    iApply "Hpost"; iFrame "∗ Hcode Ha_unsealing".
  Qed.

  (*** Specification for unknown code *)
  Lemma KVS_getFullKey_spec_invalid_sealed_user_key
    (pc_b pc_e pc_a : Addr) (off : Z)
    (rdst rsealkey rkey : RegName)
    ( wsealkey : LWord )
    :
    let instrs := (kvs_getFullKey_instrs off rdst rsealkey rkey) in
    is_shadow_address (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a = false ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->
    (pc_a + off)%a = Some (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ->

    (is_sealed_with_o wsealkey.(lw) KVS_OTYPE = false \/ get_tag wsealkey.(lw) = false) ->

    rsealkey ≠ cnull ->
    rdst ≠ cnull ->

    (
      PC ↦ₚ WCap true RX Global pc_b pc_e pc_a ∗
      rdst ↦ᵣ - ∗
      rsealkey ↦ᵣ wsealkey ∗

      (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ□ kvs_service_unsealing_key ∗

      codefrag_pers pc_a instrs ∗

      ( rdst ↦ᵣ - ∗
        rsealkey ↦ᵣ wsealkey -∗
        trap_safe (WCap true RX Global pc_b pc_e (pc_a ^+ 3)%a) ⊤
          (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros instrs ; subst instrs.
    iIntros (Hunsealing_shadow HsubBounds Hoff Hnot_sealed_with_kvs_otype Hrsealkey Hdst)
      "(HPC & [%wdst Hrdst] & Hrsealkey
      & #Ha_unsealing & #Hcode & Hfailed)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)
    (* Auipcc rdst off. *)
    iInstr "Hcode".
    (* CLoad rdst rdst 0. *)
    iInstr "Hcode".
    { done. }
    { rewrite /UNSEALING_USER_KEY_OFFSET in Hoff |- *; solve_addr. }
    (* UnSeal rdst rdst rsealkey. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_unseal_unknown' with "[$HPC $Hi $Hrdst $Hrsealkey]"); try solve_pure.
    iIntros "!>" (ret)
      "[(-> & HPC & Hi & Hrdst & Hrsealkey & %Hnot_sealed) | [(% & % & % & % & % & % & %o & %wsb & %π & -> & HPC & Hi & Hrdst & Hrsealkey & %Heq & % & %spec & %Htag & %Hrange)
      | (%tsr & %psr & %gsr & %bsr & %esr & %asr & %πsr & %ot & %sb & %π
         & -> & HPC & Hi & Hrdst & Hrsealkey & %Heq & %Hsealed & %Hinvalid)]]".
    { (* Not a sealing range and a sealed word: the result is untagged, and
         the next instruction fails. *)
      wp_pure.
      iClear "Hi".
      (* CLoad rdst rdst 0. *)
      iInstr_fail "Hcode".
      { intros r sr m st s1 Hr.
        rewrite /exec /= /lookup_reg /= Hr /= decide_False //.
        destruct wsealkey as [ [z | sb | t p g b e a | o sb] π0]; try destruct sb; by destruct s1. }
      iTrap with "Hfailed". }
    {
    destruct Hnot_sealed_with_kvs_otype as [Hnot_sealed_with_kvs_otype | Hclear].
    2: { rewrite spec /= Htag in Hclear; done. }
    rewrite spec in Hnot_sealed_with_kvs_otype.
    rewrite /kvs_service_unsealing_key /lload_word /lift_word /load_word //= in Heq; simplify_eq.
    apply withinBounds_le_addr in Hrange.
    assert (o = KVS_OTYPE) as -> by solve_addr.
    cbn in Hnot_sealed_with_kvs_otype.
    by rewrite Z.eqb_neq in Hnot_sealed_with_kvs_otype.
    }
    wp_pure.
    iClear "Hi".
    (* CLoad rdst rdst 0. *)
    iInstr_fail "Hcode".
    iTrap with "Hfailed".
  Qed.

End KVS_getFullKey.

(** Resolve the premise of [KVS_getFullKey_spec] on the offset of the
    unsealing key, at a call site in one of the entries of the service:
    the address of the fetch is given by a hypothesis [H] on the offset of
    the block, whose closed code length is computed first. *)
Ltac kvs_getFullKey_offset :=
  match goal with
  | H : (_ + ?n)%a = Some ?a |- (?a + _)%a = Some _ =>
      match n with context [length ?l] =>
        let v := eval vm_compute in (length l) in change (length l) with v in H
      end
  end;
  pose proof KVS_size_imports as Himports_size;
  unfold kvs_addOrUpdate_pcc_addr, kvs_read_pcc_addr, kvs_erase_pcc_addr,
    kvs_addOrUpdate_pcc_off, kvs_read_pcc_off, kvs_erase_pcc_off,
    UNSEALING_USER_KEY_OFFSET in *;
  let v := eval vm_compute in length_kvs_imports in
  change length_kvs_imports with v in *;
  let v := eval vm_compute in (length kvs_addOrUpdate_instrs) in
  change (length kvs_addOrUpdate_instrs) with v in *;
  let v := eval vm_compute in (length kvs_read_instrs) in
  change (length kvs_read_instrs) with v in *;
  let v := eval vm_compute in (length kvs_erase_instrs) in
  change (length kvs_erase_instrs) with v in *;
  solve_addr.
