From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode.
From griotte Require Import logrel rules.
From griotte Require Import switcher kvs.
From griotte Require Export kvs_preamble.

Section KVS_search.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {kvsg:kvsG Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Lemma KVS_search_spec_in `{KVS : kvsLayout}
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (rkey ridx ridx_empty rscratch : RegName)
    (pkvs : kvs_physical_map) (idx : nat) (fkey : full_key_t) (w : Word)
    :
    let instrs := (kvs_search_instrs rkey ridx ridx_empty rscratch) in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->
    withinBounds cgp_b cgp_e cgp_b = true ->
    ((cgp_b + (ASM_SIZEOF_KVS_ENTRY*SIZE_MAP)%Z)%a = Some cgp_e)%a ->

    pkvs !! idx = Some (Some (fkey, w)) ->

    rscratch ≠ cnull ->
    ridx ≠ cnull ->
    ridx_empty ≠ cnull ->
    rkey ≠ cnull ->

    (
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
      rkey ↦ᵣ WInt fkey ∗
      ridx ↦ᵣ - ∗
      ridx_empty ↦ᵣ - ∗
      rscratch ↦ᵣ - ∗

      is_physical_kvs cgp_b pkvs ∗

      codefrag pc_a instrs ∗
      ▷ (
          PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
          cgp ↦ᵣ WCap RW Global cgp_b cgp_e (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY*idx) )%a ∗
          rkey ↦ᵣ WInt fkey ∗
          ridx ↦ᵣ WInt idx ∗
          ridx_empty ↦ᵣ - ∗
          rscratch ↦ᵣ - ∗


          (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY*idx))%a ↦ₐ WInt ASM_SOME ∗
          (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY*idx + 1))%a ↦ₐ WInt fkey ∗
          (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY*idx + 2))%a ↦ₐ w ∗

          is_physical_kvs_open cgp_b pkvs idx ∗

          ⌜ withinBounds cgp_b cgp_e (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * idx + 2))%a = true ⌝ ∗

          codefrag pc_a instrs -∗

          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros instrs ; subst instrs.
    iIntros (HsubBounds Hbounds_cgp Hcgp_bound Hpkvs_idx
               Hrscratch Hridx Hridx_empty Hkey)
      "(HPC & Hcgp & Hrkey & [%widx Hridx] & [%widx_empty Hridx_empty] & Hrscratch
      & HKVS & Hcode & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.


    (* mov ridx 0%Z; *)
    iInstr "Hcode".
    (* mov ridx_empty (-1)%Z; *)
    iInstr "Hcode".

    remember 0%Z as n.
    iAssert (⌜ (0 <= n <= SIZE_MAP)%Z ⌝)%I as "%Hn"; first (iPureIntro ; lia).
    rewrite{2} (_ : (cgp_b = (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n))%a)); last by solve_addr.
    assert (forall i, (0 <= i < Z.to_nat n) -> ∀ (k : Z) (w : Word),
                pkvs !! i = Some (Some (k,w)) -> k ≠ fkey)
    as Hfkey_notin_nfirst.
    { rewrite Heqn; intros i Hi; lia. }
    clear Heqn.
    generalize ((if decide (ridx_empty = cnull) then (Z.of_nat 0) else (-1)%Z) ); intros nidx_empty.

    iLöb as "IH" forall (n nidx_empty Hn Hfkey_notin_nfirst).

    (* sub rscratch SIZE_MAP ridx; *)
    iDestruct "Hrscratch" as "[%wrscratch Hrscratch]".
    iInstr "Hcode".
    replace 16 with SIZE_MAP by (by rewrite /SIZE_MAP).
    destruct (decide ((SIZE_MAP - n) = 0)%Z) as [Hneq|Hneq].
    { (* End of the loop. It means that the key wasn't found in the KVS *)
      (* We know that it should be a contradiction, because `fkey⤇(KVS) w`
         witnesses that it exists
       *)
      rewrite Hneq.
      assert ( n = SIZE_MAP ) as -> by lia.
      iDestruct (kvs_physical_map_indom_idx with "HKVS") as "%Hidx".
      { by apply elem_of_dom_2 in Hpkvs_idx. }
      exfalso.
      eapply Hfkey_notin_nfirst; eauto.
    }
    assert (0 ≤ n < SIZE_MAP)%Z as Hn' by lia.
    (* jnz (".loop_body")%asm rscratch; *)
    iInstr "Hcode".
    { by injection. }

    destruct (decide (Z.of_nat idx = n)%Z) as [<- | Hneq'].
    - iDestruct (kvs_physical_map_open_in with "HKVS") as "(HKVS & Hasm_idx)"; eauto.
      iDestruct (destruct_physical_kvs_entry_some with "Hasm_idx") as "(Hbk & Hbw & Hfkey)"; first solve_addr.

      (* load rscratch cgp; *)
      iInstr "Hcode".
      { split; [done |solve_addr]. }
      iEval (cbn) in "Hrscratch".
      (* jnz (".some_index")%asm rscratch; *)
      iInstr "Hcode".

      (* lea cgp 1; *)
      iInstr "Hcode".
      { transitivity (Some ((cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * idx + 1))%a)); solve_addr. }
      (* load rscratch cgp; *)
      iInstr "Hcode".
      { split; [done |solve_addr]. }
      iEval (cbn) in "Hrscratch".
      (* sub rscratch rkey rscratch; *)
      iInstr "Hcode".
      replace (fkey - fkey)%Z with 0%Z by (cbn;lia).
      (* jnz (".not_same_key")%asm rscratch; *)
      iInstr "Hcode".
      (* lea cgp (-1)%Z; *)
      iInstr "Hcode".
      { transitivity (Some (cgp_b ^+ ASM_SIZEOF_KVS_ENTRY * idx)%a); solve_addr. }
      (* jmp (".loop_end_found")%asm; *)
      iInstr "Hcode".
      iApply "Hpost"; iFrame.
      iPureIntro; rewrite /withinBounds; solve_addr.

    - iDestruct (kvs_physical_map_open_neq _ _ _ (Z.to_nat n) with "HKVS")
        as "(%opt_kw' & HKVS & %Hm_idx' & Hkvs_entry & %Hopt_kw')"
      ; eauto; try lia.
      iDestruct (destruct_physical_kvs_entry with "Hkvs_entry") as "(Hn0 & Hn1 & Hn2)"; first solve_addr.
      replace (cgp_b ^+ ASM_SIZEOF_KVS_ENTRY * Z.to_nat n)%a  with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n))%a by solve_addr+Hn.
      replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * Z.to_nat n + 1))%a with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 1))%a by solve_addr+Hn.
      replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * Z.to_nat n + 2))%a with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 2))%a by solve_addr+Hn.
      (* load rscratch cgp; *)
      iInstr "Hcode".
      { split; [done | solve_addr]. }
      iEval (cbn) in "Hrscratch".

      destruct opt_kw' as [ [k' w'] | ].
      + (* jnz (".some_index")%asm rscratch; *)
        iInstr "Hcode".
        (* lea cgp 1; *)
        iInstr "Hcode".
        { transitivity (Some ((cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 1))%a)); last done; solve_addr+Hn Hn' Hcgp_bound. }
        (* load rscratch cgp; *)
        iInstr "Hcode".
        { split; [done | solve_addr]. }
        (* sub rscratch rkey rscratch; *)
        iInstr "Hcode".
        (* jnz (".not_same_key")%asm rscratch; *)
        iInstr "Hcode".
        { injection; cbn; intro; apply Hopt_kw'; cbn; lia. }
        (* lea cgp 2; *)
        iInstr "Hcode".
        { transitivity (Some ( (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * (n+1)))%a)); last done; solve_addr+Hn Hn' Hcgp_bound. }
        (* add ridx ridx 1; *)
        iInstr "Hcode".
        (* jmp (".loop_start"); *)
        iInstr "Hcode".
        { transitivity (Some ( (pc_a ^+ 2)%a)); solve_addr. }

        iDestruct (kvs_physical_map_close with "[$HKVS] [Hn0 Hn1 Hn2]") as "HKVS";eauto.
        {
          iApply destruct_physical_kvs_entry; first solve_addr.
          replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n))%a with (cgp_b ^+ ASM_SIZEOF_KVS_ENTRY * Z.to_nat n)%a by solve_addr+Hn.
          replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 1))%a  with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * Z.to_nat n + 1))%a by solve_addr+Hn.
          replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 2))%a  with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * Z.to_nat n + 2))%a by solve_addr+Hn.
          iFrame.
        }

        iApply ("IH" with
                 "[] [] [$Hcgp] [$Hrkey] [$Hrscratch] [$HKVS] [$Hpost] [$Hridx] [$Hcode] [$HPC] [$Hridx_empty]").
        * iPureIntro; lia.
        * iPureIntro.
          intros idx0 Hidx0_bound k0 w0 Hidx0.
          destruct (decide (idx0 = Z.to_nat n)%Z) as [-> | Hidx']; eauto.
          { rewrite Hm_idx' in Hidx0; simplify_map_eq; done. }
          { eapply Hfkey_notin_nfirst; eauto; lia. }
      + (* jnz (".some_index")%asm rscratch; *)
        iInstr "Hcode".
        (* mov ridx_empty ridx; *)
        iInstr "Hcode".
        (* lea cgp ASM_SIZEOF_KVS_ENTRY; *)
        iInstr "Hcode".
        { transitivity (Some ((cgp_b ^+ ASM_SIZEOF_KVS_ENTRY * (n + 1))%a)); solve_addr+Hn Hn' Hcgp_bound. }
        (* add ridx ridx 1; *)
        iInstr "Hcode".
        (* jmp (".loop_start"); *)
        iInstr "Hcode".
        { transitivity (Some ( (pc_a ^+ 2)%a)); solve_addr. }
        iDestruct (kvs_physical_map_close with "[$HKVS] [Hn0 Hn1 Hn2]") as "HKVS";eauto.
        {
          iApply destruct_physical_kvs_entry; first solve_addr.
          replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n))%a with (cgp_b ^+ ASM_SIZEOF_KVS_ENTRY * Z.to_nat n)%a by solve_addr+Hn.
          replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 1))%a  with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * Z.to_nat n + 1))%a by solve_addr+Hn.
          replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 2))%a  with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * Z.to_nat n + 2))%a by solve_addr+Hn.
          iFrame.
        }

        iApply ("IH" with
                 "[] [] [$Hcgp] [$Hrkey] [$Hrscratch] [$HKVS] [$Hpost] [$Hridx] [$Hcode] [$HPC] [$Hridx_empty]").
        * iPureIntro; lia.
        * iPureIntro.
          intros idx0 Hidx0_bound k0 w0 Hidx0.
          destruct (decide (idx0 = Z.to_nat n)%Z) as [-> | Hidx']; eauto.
          { rewrite Hm_idx' in Hidx0; simplify_map_eq; done. }
          { eapply Hfkey_notin_nfirst; eauto; lia. }
  Qed.

  Lemma KVS_search_spec_empty_slot `{KVS : kvsLayout}
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (rkey ridx ridx_empty rscratch : RegName)
    (pkvs : kvs_physical_map) (ukvs : kvs_user_map) (uk : user_key_t) (mk : map_key_t)
    :
    let instrs := (kvs_search_instrs rkey ridx ridx_empty  rscratch) in
    let fkey := kvs_full_key uk mk in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->
    withinBounds cgp_b cgp_e cgp_b = true ->
    ((cgp_b + (ASM_SIZEOF_KVS_ENTRY*SIZE_MAP)%Z)%a = Some cgp_e)%a ->

    fkey ∉ kvs_keys pkvs ->
    is_uint16 mk ->

    rscratch ≠ cnull ->
    ridx ≠ cnull ->
    ridx_empty ≠ cnull ->
    rkey ≠ cnull ->

    (
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
      rkey ↦ᵣ WInt fkey ∗
      ridx ↦ᵣ - ∗
      ridx_empty ↦ᵣ - ∗
      rscratch ↦ᵣ - ∗

      is_physical_kvs cgp_b pkvs ∗

      codefrag pc_a instrs ∗
      ▷ ( (* An empty slot was found*)
          ( ∃ idx_empty_slot : nat,
            (
            PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
            cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
            rkey ↦ᵣ WInt fkey ∗
            ridx ↦ᵣ WInt (-1)%Z ∗
            ridx_empty ↦ᵣ WInt idx_empty_slot ∗
            rscratch ↦ᵣ - ∗

            is_physical_kvs_open cgp_b pkvs idx_empty_slot ∗
            (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY*idx_empty_slot))%a ↦ₐ WInt ASM_NONE ∗
            (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY*idx_empty_slot + 1))%a ↦ₐ - ∗
            (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY*idx_empty_slot + 2))%a ↦ₐ - ∗

            ⌜ withinBounds cgp_b cgp_e (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * idx_empty_slot + 2))%a = true ⌝ ∗
            ⌜ 0 <= idx_empty_slot ⌝ ∗
            ⌜ pkvs !! idx_empty_slot = Some None ⌝ ∗

            codefrag pc_a instrs
            )
          )
          ∨ (* No empty slot found*)
            (
              PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
              cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
              rkey ↦ᵣ WInt fkey ∗
              ridx ↦ᵣ WInt (-1) ∗
              ridx_empty ↦ᵣ WInt (-1) ∗
              rscratch ↦ᵣ - ∗

              is_physical_kvs cgp_b pkvs ∗

              codefrag pc_a instrs
            ) -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros instrs fkey ; subst instrs.
    iIntros (HsubBounds Hbounds_cgp Hcgp_bound Hs' Hwf_full_key Hrscratch Hridx Hridx_empty Hkey)
      "(HPC & Hcgp & Hrkey & [%wridx Hridx] & [%wridx_empty Hridx_empty] & Hrscratch
        & HKVS & Hcode & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* mov ridx 0%Z; *)
    iInstr "Hcode".
    (* mov ridx_empty (-1)%Z; *)
    iInstr "Hcode".
    destruct (decide (ridx_empty = cnull)) as [|_]; first done.
    remember (-1)%Z as idx_empty.
    rewrite {1}Heqidx_empty.
    rewrite {1}Heqidx_empty.
    rewrite {1}Heqidx_empty.

    remember 0%Z as n.
    iAssert (⌜ (0 <= n <= SIZE_MAP)%Z ⌝)%I as "%Hn"; first (iPureIntro ; lia).
    rewrite{2} (_ : cgp_b = (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n))%a); last by solve_addr.
    assert (forall i, (0 <= i < Z.to_nat n) -> ∀ (k : Z) (w : Word), pkvs !! i = Some (Some (k,w)) -> k ≠ fkey)
    as Hfkey_notin_nfirst.
    { rewrite Heqn; intros i Hi; lia. }

    iAssert (
       if (decide ((Forall (fun idx => pkvs !! idx ≠ Some None) (seq 0 (Z.to_nat n)))))
       then (is_physical_kvs cgp_b pkvs ∗
             ridx_empty ↦ᵣ WInt (-1)
            )
       else ( ∃ (idx_empty : nat),
                ⌜ 0 <= idx_empty < (Z.to_nat n)⌝ ∗
                is_physical_kvs_open cgp_b pkvs idx_empty ∗
                (cgp_b ^+ ASM_SIZEOF_KVS_ENTRY * idx_empty)%a ↦ₐ WInt ASM_NONE ∗
                (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * idx_empty + 1))%a ↦ₐ - ∗
                (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * idx_empty + 2))%a ↦ₐ - ∗
                ridx_empty ↦ᵣ WInt idx_empty ∗
                ⌜ pkvs !! idx_empty = Some None ⌝
            )
      )%I with "[HKVS Hridx_empty]" as "Hloop_inv".
    {
      destruct ( decide (Forall (λ idx : nat, pkvs !! idx ≠ Some None) (seq 0 (Z.to_nat n))) ) as [|Hcontra]; rewrite Heqidx_empty; iFrame.
      exfalso; apply Hcontra.
      rewrite Heqn /=; apply Forall_nil; done.
    }
    clear Heqn Heqidx_empty.

    iLöb as "IH" forall (n Hn Hfkey_notin_nfirst).

    (* sub rscratch SIZE_MAP ridx; *)
    iDestruct "Hrscratch" as "[%wrscratch Hrscratch]".
    iInstr "Hcode".
    replace 16 with SIZE_MAP by (by rewrite /SIZE_MAP).
    destruct (decide ((SIZE_MAP - n) = 0)%Z) as [Hneq|Hneq].
    { (* End of the loop. *)
      rewrite Hneq.
      assert ( n = SIZE_MAP ) as -> by lia.

      (* jnz (".loop_body")%asm rscratch; *)
      iInstr "Hcode".
      (* jmp (".loop_end_not_found")%asm; *)
      iInstr "Hcode".
      (* lea cgp (-(ASM_SIZEOF_KVS_ENTRY*SIZE_MAP))%Z; *)
      iInstr "Hcode".
      { transitivity (Some cgp_b); rewrite /SIZE_MAP in Hcgp_bound |- *; solve_addr. }
      (* mov ridx (-1)%Z; *)
      iInstr "Hcode".
      rewrite (decide_False (Z.of_nat 0)); last done.

      destruct ( decide ( (Forall (λ idx : nat, pkvs !! idx ≠ Some None) (seq 0 (Z.to_nat SIZE_MAP))) )) as [Hnone|Hnone].
      - iDestruct "Hloop_inv" as "(HKVS & Hridx_empty)".
        iApply "Hpost"; iRight; iFrame.

      - iDestruct "Hloop_inv" as
          "(%idx_empty_found & %Hidx_empty_found & HKVS & Hn0 & Hn1 & Hn2 & Hfkey & Hridx_empty)".
        iApply "Hpost"; iLeft; iFrame.
        iPureIntro; split; solve_addr.
    }
    assert (0 ≤ n < SIZE_MAP)%Z as Hn' by lia.
    (* jnz (".loop_body")%asm rscratch; *)
    iInstr "Hcode".
    { by injection. }

    destruct ( decide (Forall (λ idx : nat, pkvs !! idx ≠ Some None) (seq 0 (Z.to_nat n))) ) as [Hnone | Hnone].
    - (* No empty slot have been found yet *)
      iDestruct "Hloop_inv" as "(HKVS & Hridx_empty)".

      iDestruct (kvs_physical_map_open_notin _ _ (Z.to_nat n) with "HKVS")
        as "(%opt_kwidx & %Hm_kwidx & HKVS & Hfkey & %Hneq_fkey)" ; eauto; [lia|].
      iDestruct (destruct_physical_kvs_entry with "Hfkey") as "(Hn0 & Hn1 & Hn2)"; first solve_addr.
      replace (cgp_b ^+ ASM_SIZEOF_KVS_ENTRY * Z.to_nat n)%a  with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n))%a by solve_addr+Hn.
      replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * Z.to_nat n + 1))%a with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 1))%a by solve_addr+Hn.
      replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * Z.to_nat n + 2))%a with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 2))%a by solve_addr+Hn.

      (* load rscratch cgp; *)
      iInstr "Hcode".
      { split; [done |solve_addr]. }
      iEval (cbn) in "Hrscratch".

      destruct opt_kwidx as [ [kidx widx] | ].
      + (* This is not an empty slot. Because we mkow that fkey ∉ s, the key will not match *)
        (* jnz (".some_index")%asm rscratch; *)
        iInstr "Hcode".

        (* lea cgp 1; *)
        iInstr "Hcode".
        { transitivity (Some ((cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 1))%a)); last done; solve_addr+Hn Hn' Hcgp_bound. }
        (* load rscratch cgp; *)
        iInstr "Hcode".
        { split; [done |solve_addr]. }
        (* sub rscratch rkey rscratch; *)
        iInstr "Hcode".
        assert ( WInt (fkey - kidx)%Z ≠ WInt 0 ) as Hfkey_neq.
        { injection; intro; simplify_eq; apply Hneq_fkey; cbn; lia. }
        (* jnz (".not_same_key")%asm rscratch; *)
        iInstr "Hcode".

        (* lea cgp 2; *)
        iInstr "Hcode".
        { transitivity (Some ((cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + ASM_SIZEOF_KVS_ENTRY))%a)) ; last done; solve_addr+Hn Hn' Hcgp_bound. }
        (* add ridx ridx 1; *)
        iInstr "Hcode".
        (* jmp (".loop_start"); *)
        iInstr "Hcode".
        { transitivity (Some ( (pc_a ^+ 2)%a)); solve_addr. }

        iDestruct (kvs_physical_map_close with "[$HKVS] [Hn0 Hn1 Hn2]") as "HKVS";eauto.
        {
          iApply destruct_physical_kvs_entry; first solve_addr.
          replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n))%a with (cgp_b ^+ ASM_SIZEOF_KVS_ENTRY * Z.to_nat n)%a by solve_addr+Hn.
          replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 1))%a  with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * Z.to_nat n + 1))%a by solve_addr+Hn.
          replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 2))%a  with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * Z.to_nat n + 2))%a by solve_addr+Hn.
          iFrame.
        }
        replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + ASM_SIZEOF_KVS_ENTRY))%a with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * (n + 1)))%a by solve_addr+ Hn Hn' Hcgp_bound.

        iApply ("IH" with "[] [] [$Hcgp] [$Hrkey] [$Hrscratch]
         [$Hpost] [$Hridx] [$Hcode] [$HPC] [HKVS Hridx_empty]").
        * iPureIntro; lia.
        * iPureIntro.
          intros idx0 Hidx0_bound k0 w0 Hidx0.
          destruct (decide (idx0 = Z.to_nat n)%Z) as [-> | Hidx']; eauto.
          { rewrite Hm_kwidx in Hidx0; simplify_map_eq; done. }
          { eapply Hfkey_notin_nfirst; eauto; lia. }
        * case_decide as Hnone'; iFrame.
          exfalso.
          apply Hnone'.
          replace ( (seq 0 (Z.to_nat (n + 1))) ) with ( (seq 0 (Z.to_nat n)) ++ [Z.to_nat n] ).
          2: {
            replace [Z.to_nat n] with (seq (Z.to_nat n) 1) by done.
            rewrite -seq_app.
            replace (Z.to_nat n + 1) with (Z.to_nat (n + 1)) by lia.
            done.
          }
          apply Forall_app; split; auto.
          apply Forall_singleton.
          rewrite Hm_kwidx; done.
      + (* This is an empty slot. We will update ridx_empty and keep KVS open *)

        (* jnz (".some_index")%asm rscratch; *)
        iInstr "Hcode".
        (* mov ridx_empty ridx; *)
        iInstr "Hcode".
        (* lea cgp ASM_SIZEOF_KVS_ENTRY; *)
        iInstr "Hcode".
        { transitivity (Some ((cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * (n + 1)))%a)); solve_addr+Hn Hn' Hcgp_bound. }
        (* add ridx ridx 1; *)
        iInstr "Hcode".
        (* jmp (".loop_start"); *)
        iInstr "Hcode".
        { transitivity (Some ( (pc_a ^+ 2)%a)); solve_addr. }

        rewrite {5}(_ : n = (Z.of_nat (Z.to_nat n))); last lia.
        replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n))%a with (cgp_b ^+ ASM_SIZEOF_KVS_ENTRY * Z.to_nat n)%a by solve_addr+Hn.
        replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 1))%a  with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * Z.to_nat n + 1))%a by solve_addr+Hn.
        replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 2))%a  with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * Z.to_nat n + 2))%a by solve_addr+Hn.
        iApply ("IH" with "[] [] [$Hcgp] [$Hrkey] [$Hrscratch]
         [$Hpost] [$Hridx] [$Hcode] [$HPC] [HKVS Hridx_empty Hn0 Hn1 Hn2]").
        * iPureIntro; lia.
        * iPureIntro.
          intros idx0 Hidx0_bound k0 w0 Hidx0.
          destruct (decide (idx0 = Z.to_nat n)%Z) as [-> | Hidx']; eauto.
          { rewrite Hm_kwidx in Hidx0; simplify_map_eq; done. }
          { eapply Hfkey_notin_nfirst; eauto; lia. }
        * case_decide as Hnone'; iFrame; last (iPureIntro; split; auto; lia).
          exfalso.
          replace ( (seq 0 (Z.to_nat (n + 1))) ) with ( (seq 0 (Z.to_nat n)) ++ [Z.to_nat n] ) in Hnone'.
          2: {
            replace [Z.to_nat n] with (seq (Z.to_nat n) 1) by done.
            rewrite -seq_app.
            replace (Z.to_nat n + 1) with (Z.to_nat (n + 1)) by lia.
            done.
          }
          apply Forall_app in Hnone' as [_ Hnone'].
          apply (Forall_singleton _ (Z.to_nat n)) in Hnone'; cbn in *.
          done.

    - (* An empty slot have already been found *)
      iDestruct "Hloop_inv" as
        "(%idx_empty_found & %Hidx_empty_found & HKVS & Hn0 & Hn1 & Hn2 & Hridx_empty
          & %Hpkvs_idx_empty)".

      iDestruct (kvs_physical_map_close _ _ _ None with "[$HKVS] [Hn0 Hn1 Hn2]") as "HKVS";eauto.
      { iApply destruct_physical_kvs_entry; first solve_addr; iFrame. }


      iDestruct (kvs_physical_map_open_notin _ _ (Z.to_nat n) with "HKVS")
        as "(%opt_kwidx & %Hm_kwidx & HKVS & Hfkey & %Hneq_fkey)" ; eauto; [lia|].
      iDestruct (destruct_physical_kvs_entry with "Hfkey") as "(Hn0 & Hn1 & Hn2)"; first solve_addr.
      replace (cgp_b ^+ ASM_SIZEOF_KVS_ENTRY * Z.to_nat n)%a  with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n))%a by solve_addr+Hn.
      replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * Z.to_nat n + 1))%a with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 1))%a by solve_addr+Hn.
      replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * Z.to_nat n + 2))%a with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 2))%a by solve_addr+Hn.

      (* load rscratch cgp; *)
      iInstr "Hcode".
      { split; [done |solve_addr]. }
      iEval (cbn) in "Hrscratch".


      destruct opt_kwidx as [ [kidx widx] | ].
      + (* This is not an empty slot. Because we mkow that fkey ∉ s, the key will not match *)
        (* jnz (".some_index")%asm rscratch; *)
        iInstr "Hcode".

        (* lea cgp 1; *)
        iInstr "Hcode".
        { transitivity (Some ((cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 1))%a)); last done; solve_addr+Hn Hn' Hcgp_bound. }
        (* load rscratch cgp; *)
        iInstr "Hcode".
        { split; [done |solve_addr]. }
        (* sub rscratch rkey rscratch; *)
        iInstr "Hcode".
        assert ( WInt (fkey - kidx)%Z ≠ WInt 0 ) as Hfkey_neq.
        { injection; intro; simplify_eq; apply Hneq_fkey; cbn; lia. }
        (* jnz (".not_same_key")%asm rscratch; *)
        iInstr "Hcode".

        (* lea cgp 2; *)
        iInstr "Hcode".
        { transitivity (Some ((cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + ASM_SIZEOF_KVS_ENTRY))%a)) ; last done; solve_addr+Hn Hn' Hcgp_bound. }
        (* add ridx ridx 1; *)
        iInstr "Hcode".
        (* jmp (".loop_start"); *)
        iInstr "Hcode".
        { transitivity (Some ( (pc_a ^+ 2)%a)); solve_addr. }

        iDestruct (kvs_physical_map_close with "[$HKVS] [Hn0 Hn1 Hn2]") as "HKVS";eauto.
        {
          iApply destruct_physical_kvs_entry; first solve_addr.
          replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n))%a with (cgp_b ^+ ASM_SIZEOF_KVS_ENTRY * Z.to_nat n)%a by solve_addr+Hn.
          replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 1))%a  with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * Z.to_nat n + 1))%a by solve_addr+Hn.
          replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 2))%a  with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * Z.to_nat n + 2))%a by solve_addr+Hn.
          iFrame.
        }
        replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + ASM_SIZEOF_KVS_ENTRY))%a with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * (n + 1)))%a by solve_addr + Hn Hn' Hcgp_bound.

        iDestruct (kvs_physical_map_open_notin _ _ idx_empty_found with "HKVS")
          as "(%opt_kwidx_empty & %Hm_kwidx_empty & HKVS & Hfkey & %Hneq_fkey_empty)" ; eauto; [lia|].
        rewrite Hpkvs_idx_empty in Hm_kwidx_empty; simplify_eq.
        iDestruct (destruct_physical_kvs_entry with "Hfkey") as "(Hn0 & Hn1 & Hn2)"; first solve_addr.

        iApply ("IH" with "[] [] [$Hcgp] [$Hrkey] [$Hrscratch]
         [$Hpost] [$Hridx] [$Hcode] [$HPC] [HKVS Hn0 Hn1 Hn2 Hridx_empty]").
        * iPureIntro; lia.
        * iPureIntro.
          intros idx0 Hidx0_bound k0 w0 Hidx0.
          clear Hidx_empty_found.
          destruct (decide (idx0 = Z.to_nat n)%Z) as [-> | Hidx']; eauto.
          { rewrite Hm_kwidx in Hidx0; simplify_map_eq; done. }
          { eapply Hfkey_notin_nfirst; eauto; lia. }
        * case_decide as Hnone'; iFrame; last (iPureIntro; split; auto; lia).
          exfalso.
          rewrite Forall_forall in Hnone'.
          specialize (Hnone' idx_empty_found).
          apply Hnone'; auto.
          apply elem_of_seq; lia.


      + (* This is an empty slot. We will update ridx_empty and keep KVS open *)

        (* jnz (".some_index")%asm rscratch; *)
        iInstr "Hcode".
        (* mov ridx_empty ridx; *)
        iInstr "Hcode".
        (* lea cgp ASM_SIZEOF_KVS_ENTRY; *)
        iInstr "Hcode".
        { transitivity (Some ((cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * (n + 1)))%a)); solve_addr+Hn Hn' Hcgp_bound. }
        (* add ridx ridx 1; *)
        iInstr "Hcode".
        (* jmp (".loop_start"); *)
        iInstr "Hcode".
        { transitivity (Some ( (pc_a ^+ 2)%a)); solve_addr. }

        rewrite {5}(_ : n = (Z.of_nat (Z.to_nat n))); last lia.
        replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n))%a with (cgp_b ^+ ASM_SIZEOF_KVS_ENTRY * Z.to_nat n)%a by solve_addr+Hn.
        replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 1))%a  with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * Z.to_nat n + 1))%a by solve_addr+Hn.
        replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 2))%a  with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * Z.to_nat n + 2))%a by solve_addr+Hn.
        iApply ("IH" with "[] [] [$Hcgp] [$Hrkey] [$Hrscratch]
         [$Hpost] [$Hridx] [$Hcode] [$HPC] [HKVS Hridx_empty Hn0 Hn1 Hn2]").
        * iPureIntro; lia.
        * iPureIntro.
          intros idx0 Hidx0_bound k0 w0 Hidx0.
          clear Hidx_empty_found.
          destruct (decide (idx0 = Z.to_nat n)%Z) as [-> | Hidx']; eauto.
          { rewrite Hm_kwidx in Hidx0; simplify_map_eq; done. }
          { eapply Hfkey_notin_nfirst; eauto; lia. }
        * case_decide as Hnone'; iFrame; last (iPureIntro; split; auto; lia).
          exfalso.
          replace ( (seq 0 (Z.to_nat (n + 1))) ) with ( (seq 0 (Z.to_nat n)) ++ [Z.to_nat n] ) in Hnone'.
          2: {
            replace [Z.to_nat n] with (seq (Z.to_nat n) 1) by done.
            rewrite -seq_app.
            replace (Z.to_nat n + 1) with (Z.to_nat (n + 1)) by lia.
            done.
          }
          apply Forall_app in Hnone' as [_ Hnone'].
          apply (Forall_singleton _ (Z.to_nat n)) in Hnone'; cbn in *.
          done.
  Qed.

End KVS_search.
