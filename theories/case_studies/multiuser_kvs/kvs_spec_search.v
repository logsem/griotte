From iris.proofmode Require Import proofmode.
From griotte Require Import logrel rules.
From griotte Require Import switcher kvs.
From griotte Require Import proofmode.
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
    (m : kvs_map) (s : kvs_alloc) (idx : nat) (fkey : Z) (w : Word)
    :
    let instrs := (kvs_search_instrs rkey ridx ridx_empty rscratch) in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->
    withinBounds cgp_b cgp_e cgp_b = true ->
    ((cgp_b + (3*SIZE_MAP)%Z)%a = Some cgp_e)%a ->

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

      isKVS cgp_b m s ∗
      fkey ⤇(KVS)[idx] w ∗

      codefrag pc_a instrs ∗
      ▷ (
          PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
          cgp ↦ᵣ WCap RW Global cgp_b cgp_e (cgp_b ^+ (3*idx) )%a ∗
          rkey ↦ᵣ WInt fkey ∗
          ridx ↦ᵣ WInt idx ∗
          ridx_empty ↦ᵣ - ∗
          rscratch ↦ᵣ - ∗

          isKVS_open cgp_b m s idx ∗
          (cgp_b ^+ (3*idx))%a ↦ₐ WInt ASM_SOME ∗
          (cgp_b ^+ (3*idx + 1))%a ↦ₐ WInt fkey ∗
          (cgp_b ^+ (3*idx + 2))%a ↦ₐ w ∗
          fkey ⤇(KVS)[idx] w ∗

          ⌜ withinBounds cgp_b cgp_e (cgp_b ^+ (3 * idx + 2))%a = true ⌝ ∗

          codefrag pc_a instrs -∗

          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros instrs ; subst instrs.
    iIntros (HsubBounds Hbounds_cgp Hcgp_bound Hrscratch Hridx Hridx_empty Hkey)
      "(HPC & Hcgp & Hrkey & [%widx Hridx] & [%widx_empty Hridx_empty] & Hrscratch
      & HKVS & Hkvs_frag & Hcode & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.


    (* mov ridx 0%Z; *)
    iInstr "Hcode".
    (* mov ridx_empty (-1)%Z; *)
    iInstr "Hcode".

    remember 0%Z as n.
    iAssert (⌜ (0 <= n <= SIZE_MAP)%Z ⌝)%I as "%Hn"; first (iPureIntro ; lia).
    rewrite{2} (_ : (cgp_b = (cgp_b ^+ (3 * n))%a)); last by solve_addr.
    assert (forall i, (0 <= i < Z.to_nat n) -> ∀ (k : Z) (w : Word),
                m !! i = Some (Some (k,w)) -> k ≠ fkey)
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

      iDestruct (isKVS_valid with "HKVS Hkvs_frag") as "%Hm_idx".
      iDestruct (isKVS_indom_idx with "HKVS") as "%Hidx".
      { by apply elem_of_dom_2 in Hm_idx. }
      exfalso.
      eapply Hfkey_notin_nfirst; eauto.
    }
    assert (0 ≤ n < SIZE_MAP)%Z as Hn' by lia.
    (* jnz (".loop_body")%asm rscratch; *)
    iInstr "Hcode".
    { by injection. }

    destruct (decide (Z.of_nat idx = n)%Z) as [<- | Hneq'].
    - iDestruct (open_isKVS_kvs_frag_idx with "[$HKVS $Hkvs_frag]") as "(HKVS & (Hbk & Hbw & Hfkey) & Hkvs_frag)".
      (* load rscratch cgp; *)
      iInstr "Hcode".
      { split; [done |solve_addr]. }
      iEval (cbn) in "Hrscratch".
      (* jnz (".some_index")%asm rscratch; *)
      iInstr "Hcode".

      (* lea cgp 1; *)
      iInstr "Hcode".
      { transitivity (Some ((cgp_b ^+ (3 * idx + 1))%a)); solve_addr. }
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
      { transitivity (Some (cgp_b ^+ 3 * idx)%a); solve_addr. }
      (* jmp (".loop_end_found")%asm; *)
      iInstr "Hcode".
      iApply "Hpost"; iFrame.
      iPureIntro; rewrite /withinBounds; solve_addr.

    - iDestruct (open_isKVS_kvs_frag_idx_diff _ _ _ _ (Z.to_nat n) with "[$HKVS $Hkvs_frag]")
        as "(%opt_kw' & Hkvs_frag & HKVS & %Hm_idx' & Hkvs_entry & %Hopt_kw')"
      ; auto; try lia.
      rewrite /isKVS_entry.
      iAssert (
          (cgp_b ^+ 3 * Z.to_nat n)%a ↦ₐ
            (match opt_kw' with
             | Some (k,w) => WInt ASM_SOME
             | None => WInt ASM_NONE
             end)
          ∗
            (cgp_b ^+ (3 * Z.to_nat n + 1))%a ↦ₐ
              (match opt_kw' with
               | Some (k,w) => WInt k
               | None => WInt EMPTY_SLOT
               end)
          ∗
            (cgp_b ^+ (3 * Z.to_nat n + 2))%a ↦ₐ
              (match opt_kw' with
               | Some (k,w) => w
               | None => WInt DEFAULT_VAL
               end)
          ∗ (match opt_kw' with | Some _ => True | None => (Z.to_nat n) ⤇(KVS) NONE end)
        )%I with "[Hkvs_entry]" as "(Hn0 & Hn1 & Hn2 & Hfkey)".
      { destruct opt_kw' as [ [k' w'] | ]; iFrame.
        iDestruct "Hkvs_entry" as "($&$&$)"; auto.
      }
      replace (cgp_b ^+ 3 * Z.to_nat n)%a  with (cgp_b ^+ (3 * n))%a by solve_addr+Hn.
      replace (cgp_b ^+ (3 * Z.to_nat n + 1))%a with (cgp_b ^+ (3 * n + 1))%a by solve_addr+Hn.
      replace (cgp_b ^+ (3 * Z.to_nat n + 2))%a with (cgp_b ^+ (3 * n + 2))%a by solve_addr+Hn.
      (* load rscratch cgp; *)
      iInstr "Hcode".
      { split; [done | solve_addr]. }
      iEval (cbn) in "Hrscratch".

      destruct opt_kw' as [ [k' w'] | ].
      + (* jnz (".some_index")%asm rscratch; *)
        iInstr "Hcode".
        (* lea cgp 1; *)
        iInstr "Hcode".
        { transitivity (Some ((cgp_b ^+ (3 * n + 1))%a)); solve_addr+Hn Hn' Hcgp_bound. }
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
        { transitivity (Some ( (cgp_b ^+ (3 * (n+1)))%a)); solve_addr+Hn Hn' Hcgp_bound. }
        (* add ridx ridx 1; *)
        iInstr "Hcode".
        (* jmp (".loop_start"); *)
        iInstr "Hcode".
        { transitivity (Some ( (pc_a ^+ 2)%a)); solve_addr. }

        iDestruct (close_isKVS with "[$HKVS Hn0 Hn1 Hn2]") as "HKVS";eauto.
        {
          replace (cgp_b ^+ (3 * n))%a with (cgp_b ^+ 3 * Z.to_nat n)%a by solve_addr+Hn.
          replace (cgp_b ^+ (3 * n + 1))%a  with (cgp_b ^+ (3 * Z.to_nat n + 1))%a by solve_addr+Hn.
          replace (cgp_b ^+ (3 * n + 2))%a  with (cgp_b ^+ (3 * Z.to_nat n + 2))%a by solve_addr+Hn.
          iFrame.
        }

        iApply ("IH" with
                 "[] [] [$Hcgp] [$Hrkey] [$Hrscratch] [$HKVS] [$Hkvs_frag] [$Hpost] [$Hridx] [$Hcode] [$HPC] [$Hridx_empty]").
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
        (* lea cgp 3; *)
        iInstr "Hcode".
        { transitivity (Some ((cgp_b ^+ 3 * (n + 1))%a)); solve_addr+Hn Hn' Hcgp_bound. }
        (* add ridx ridx 1; *)
        iInstr "Hcode".
        (* jmp (".loop_start"); *)
        iInstr "Hcode".
        { transitivity (Some ( (pc_a ^+ 2)%a)); solve_addr. }
        iDestruct (close_isKVS with "[$HKVS Hn0 Hn1 Hn2 Hfkey]") as "HKVS";eauto.
        {
          replace (cgp_b ^+ (3 * n))%a with (cgp_b ^+ 3 * Z.to_nat n)%a by solve_addr+Hn.
          replace (cgp_b ^+ (3 * n + 1))%a  with (cgp_b ^+ (3 * Z.to_nat n + 1))%a by solve_addr+Hn.
          replace (cgp_b ^+ (3 * n + 2))%a  with (cgp_b ^+ (3 * Z.to_nat n + 2))%a by solve_addr+Hn.
          iFrame.
        }

        iApply ("IH" with
                 "[] [] [$Hcgp] [$Hrkey] [$Hrscratch] [$HKVS] [$Hkvs_frag] [$Hpost] [$Hridx] [$Hcode] [$HPC] [$Hridx_empty]").
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
    (m : kvs_map) (s : kvs_alloc) (s' : gset Z) (ku kn : Z)
    :
    let instrs := (kvs_search_instrs rkey ridx ridx_empty  rscratch) in
    let fkey := kvs_full_key ku kn in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->
    withinBounds cgp_b cgp_e cgp_b = true ->
    ((cgp_b + (3*SIZE_MAP)%Z)%a = Some cgp_e)%a ->

    kn ∉ s' ->
    wf_kvs_full_key ku kn ->

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

      isKVS cgp_b m s ∗
      ◯(ALLOC)[ku] s' ∗

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

            ◯(ALLOC)[ku] s' ∗
            isKVS_open cgp_b m s idx_empty_slot ∗
            (cgp_b ^+ (3*idx_empty_slot))%a ↦ₐ WInt ASM_NONE ∗
            (cgp_b ^+ (3*idx_empty_slot + 1))%a ↦ₐ WInt EMPTY_SLOT ∗
            (cgp_b ^+ (3*idx_empty_slot + 2))%a ↦ₐ WInt DEFAULT_VAL ∗
            idx_empty_slot ⤇(KVS) NONE ∗

            ⌜ withinBounds cgp_b cgp_e (cgp_b ^+ (3 * idx_empty_slot + 2))%a = true ⌝ ∗
            ⌜ 0 <= idx_empty_slot ⌝ ∗

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

              ◯(ALLOC)[ku] s' ∗
              isKVS cgp_b m s ∗

              codefrag pc_a instrs
            ) -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros instrs fkey ; subst instrs.
    iIntros (HsubBounds Hbounds_cgp Hcgp_bound Hs' Hwf_full_key Hrscratch Hridx Hridx_empty Hkey)
      "(HPC & Hcgp & Hrkey & [%wridx Hridx] & [%wridx_empty Hridx_empty] & Hrscratch & HKVS & Halloc & Hcode & Hpost)".
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
    rewrite{2} (_ : cgp_b = (cgp_b ^+ (3 * n))%a); last by solve_addr.
    assert (forall i, (0 <= i < Z.to_nat n) -> ∀ (k : Z) (w : Word), m !! i = Some (Some (k,w)) -> k ≠ fkey)
    as Hfkey_notin_nfirst.
    { rewrite Heqn; intros i Hi; lia. }

    iAssert (
       if (decide ((Forall (fun idx => m !! idx ≠ Some None) (seq 0 (Z.to_nat n)))))
       then (isKVS cgp_b m s ∗
             ridx_empty ↦ᵣ WInt (-1)
            )
       else ( ∃ (idx_empty : nat),
                ⌜ 0 <= idx_empty < (Z.to_nat n)⌝ ∗
                isKVS_open cgp_b m s idx_empty ∗
                (cgp_b ^+ 3 * idx_empty)%a ↦ₐ WInt ASM_NONE ∗
                (cgp_b ^+ (3 * idx_empty + 1))%a ↦ₐ WInt EMPTY_SLOT ∗
                (cgp_b ^+ (3 * idx_empty + 2))%a ↦ₐ WInt DEFAULT_VAL ∗
                pointsto idx_empty (DfracOwn 1) None ∗
                ridx_empty ↦ᵣ WInt idx_empty
            )
      )%I with "[HKVS Hridx_empty]" as "Hloop_inv".
    {
      destruct ( decide (Forall (λ idx : nat, m !! idx ≠ Some None) (seq 0 (Z.to_nat n))) ) as [|Hcontra]; rewrite Heqidx_empty; iFrame.
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
      (* lea cgp (-(3*SIZE_MAP))%Z; *)
      iInstr "Hcode".
      { transitivity (Some cgp_b); rewrite /SIZE_MAP in Hcgp_bound |- *; solve_addr. }
      (* mov ridx (-1)%Z; *)
      iInstr "Hcode".
      rewrite (decide_False (Z.of_nat 0)); last done.

      destruct ( decide ( (Forall (λ idx : nat, m !! idx ≠ Some None) (seq 0 (Z.to_nat SIZE_MAP))) )) as [Hnone|Hnone].
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

    destruct ( decide (Forall (λ idx : nat, m !! idx ≠ Some None) (seq 0 (Z.to_nat n))) ) as [Hnone | Hnone].
    - (* No empty slot have been found yet *)
      iDestruct "Hloop_inv" as "(HKVS & Hridx_empty)".

      iDestruct (open_isKVS_not_alloc _ _ _ _ (Z.to_nat n) with "HKVS Halloc")
        as "(%opt_kwidx & %Hm_kwidx & HKVS & Halloc & Hfkey & %Hneq_fkey)" ; eauto; [lia|].

      iAssert (
          (cgp_b ^+ 3 * Z.to_nat n)%a ↦ₐ
            (match opt_kwidx with
             | Some (k,w) => WInt ASM_SOME
             | None => WInt ASM_NONE
             end)
          ∗
            (cgp_b ^+ (3 * Z.to_nat n + 1))%a ↦ₐ
              (match opt_kwidx with
               | Some (k,w) => WInt k
               | None => WInt EMPTY_SLOT
               end)
          ∗
            (cgp_b ^+ (3 * Z.to_nat n + 2))%a ↦ₐ
              (match opt_kwidx with
               | Some (k,w) => w
               | None => WInt DEFAULT_VAL
               end)
          ∗ (match opt_kwidx with | Some _ => True | None => (Z.to_nat n) ⤇(KVS) NONE end)
        )%I with "[Hfkey]" as "(Hn0 & Hn1 & Hn2 & Hfkey)".
      { destruct opt_kwidx as [ [kidx widx] | ]; iFrame.
        iDestruct "Hfkey" as "($&$&$)"; auto.
      }
      replace (cgp_b ^+ 3 * Z.to_nat n)%a  with (cgp_b ^+ (3 * n))%a by solve_addr+Hn.
      replace (cgp_b ^+ (3 * Z.to_nat n + 1))%a with (cgp_b ^+ (3 * n + 1))%a by solve_addr+Hn.
      replace (cgp_b ^+ (3 * Z.to_nat n + 2))%a with (cgp_b ^+ (3 * n + 2))%a by solve_addr+Hn.

      (* load rscratch cgp; *)
      iInstr "Hcode".
      { split; [done |solve_addr]. }
      iEval (cbn) in "Hrscratch".

      destruct opt_kwidx as [ [kidx widx] | ].
      + (* This is not an empty slot. Because we know that fkey ∉ s, the key will not match *)
        (* jnz (".some_index")%asm rscratch; *)
        iInstr "Hcode".

        (* lea cgp 1; *)
        iInstr "Hcode".
        { transitivity (Some ((cgp_b ^+ (3 * n + 1))%a)); solve_addr+Hn Hn' Hcgp_bound. }
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
        { transitivity (Some ((cgp_b ^+ (3 * n + 3))%a)); solve_addr+Hn Hn' Hcgp_bound. }
        (* add ridx ridx 1; *)
        iInstr "Hcode".
        (* jmp (".loop_start"); *)
        iInstr "Hcode".
        { transitivity (Some ( (pc_a ^+ 2)%a)); solve_addr. }

        iDestruct (close_isKVS with "[$HKVS Hn0 Hn1 Hn2 Hfkey]") as "HKVS";eauto.
        {
          replace (cgp_b ^+ (3 * n))%a with (cgp_b ^+ 3 * Z.to_nat n)%a by solve_addr+Hn.
          replace (cgp_b ^+ (3 * n + 1))%a  with (cgp_b ^+ (3 * Z.to_nat n + 1))%a by solve_addr+Hn.
          replace (cgp_b ^+ (3 * n + 2))%a  with (cgp_b ^+ (3 * Z.to_nat n + 2))%a by solve_addr+Hn.
          iFrame.
        }
        replace (cgp_b ^+ (3 * n + 3))%a with (cgp_b ^+ (3 * (n + 1)))%a by solve_addr+ Hn Hn' Hcgp_bound.

        iApply ("IH" with "[] [] [$Hcgp] [$Hrkey] [$Hrscratch] [$Halloc]
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
        (* lea cgp 3; *)
        iInstr "Hcode".
        { transitivity (Some ((cgp_b ^+ (3 * (n + 1)))%a)); solve_addr+Hn Hn' Hcgp_bound. }
        (* add ridx ridx 1; *)
        iInstr "Hcode".
        (* jmp (".loop_start"); *)
        iInstr "Hcode".
        { transitivity (Some ( (pc_a ^+ 2)%a)); solve_addr. }

        rewrite {6}(_ : n = (Z.of_nat (Z.to_nat n))); last lia.
        replace (cgp_b ^+ (3 * n))%a with (cgp_b ^+ 3 * Z.to_nat n)%a by solve_addr+Hn.
        replace (cgp_b ^+ (3 * n + 1))%a  with (cgp_b ^+ (3 * Z.to_nat n + 1))%a by solve_addr+Hn.
        replace (cgp_b ^+ (3 * n + 2))%a  with (cgp_b ^+ (3 * Z.to_nat n + 2))%a by solve_addr+Hn.
        iApply ("IH" with "[] [] [$Hcgp] [$Hrkey] [$Hrscratch] [$Halloc]
         [$Hpost] [$Hridx] [$Hcode] [$HPC] [HKVS Hridx_empty Hn0 Hn1 Hn2 Hfkey]").
        * iPureIntro; lia.
        * iPureIntro.
          intros idx0 Hidx0_bound k0 w0 Hidx0.
          destruct (decide (idx0 = Z.to_nat n)%Z) as [-> | Hidx']; eauto.
          { rewrite Hm_kwidx in Hidx0; simplify_map_eq; done. }
          { eapply Hfkey_notin_nfirst; eauto; lia. }
        * case_decide as Hnone'; iFrame; last (iPureIntro; lia).
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
        "(%idx_empty_found & %Hidx_empty_found & HKVS & Hn0 & Hn1 & Hn2 & Hfkey & Hridx_empty)".

      iDestruct (isKVS_open_valid_None with "HKVS Hfkey") as "%Hidx_empty_found'".

      iDestruct (close_isKVS with "[$HKVS Hn0 Hn1 Hn2 Hfkey]") as "HKVS";eauto.
      { iFrame. }


      iDestruct (open_isKVS_not_alloc _ _ _ _ (Z.to_nat n) with "HKVS Halloc")
        as "(%opt_kwidx & %Hm_kwidx & HKVS & Halloc & Hfkey & %Hneq_fkey)" ; eauto; [lia|].

      iAssert (
          (cgp_b ^+ 3 * Z.to_nat n)%a ↦ₐ
            (match opt_kwidx with
             | Some (k,w) => WInt ASM_SOME
             | None => WInt ASM_NONE
             end)
          ∗
            (cgp_b ^+ (3 * Z.to_nat n + 1))%a ↦ₐ
              (match opt_kwidx with
               | Some (k,w) => WInt k
               | None => WInt EMPTY_SLOT
               end)
          ∗
            (cgp_b ^+ (3 * Z.to_nat n + 2))%a ↦ₐ
              (match opt_kwidx with
               | Some (k,w) => w
               | None => WInt DEFAULT_VAL
               end)
          ∗ (match opt_kwidx with | Some _ => True | None => (Z.to_nat n) ⤇(KVS) NONE end)
        )%I with "[Hfkey]" as "(Hn0 & Hn1 & Hn2 & Hfkey)".
      { destruct opt_kwidx as [ [kidx widx] | ]; iFrame.
        iDestruct "Hfkey" as "($&$&$)"; auto.
      }
      replace (cgp_b ^+ 3 * Z.to_nat n)%a  with (cgp_b ^+ (3 * n))%a by solve_addr+Hn.
      replace (cgp_b ^+ (3 * Z.to_nat n + 1))%a with (cgp_b ^+ (3 * n + 1))%a by solve_addr+Hn.
      replace (cgp_b ^+ (3 * Z.to_nat n + 2))%a with (cgp_b ^+ (3 * n + 2))%a by solve_addr+Hn.

      (* load rscratch cgp; *)
      iInstr "Hcode".
      { split; [done |solve_addr]. }
      iEval (cbn) in "Hrscratch".


      destruct opt_kwidx as [ [kidx widx] | ].
      + (* This is not an empty slot. Because we know that fkey ∉ s, the key will not match *)
        (* jnz (".some_index")%asm rscratch; *)
        iInstr "Hcode".

        (* lea cgp 1; *)
        iInstr "Hcode".
        { transitivity (Some ((cgp_b ^+ (3 * n + 1))%a)); solve_addr+Hn Hn' Hcgp_bound. }
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
        { transitivity (Some ((cgp_b ^+ (3 * n + 3))%a)); solve_addr+Hn Hn' Hcgp_bound. }
        (* add ridx ridx 1; *)
        iInstr "Hcode".
        (* jmp (".loop_start"); *)
        iInstr "Hcode".
        { transitivity (Some ( (pc_a ^+ 2)%a)); solve_addr. }

        iDestruct (close_isKVS with "[$HKVS Hn0 Hn1 Hn2 Hfkey]") as "HKVS";eauto.
        {
          replace (cgp_b ^+ (3 * n))%a with (cgp_b ^+ 3 * Z.to_nat n)%a by solve_addr+Hn.
          replace (cgp_b ^+ (3 * n + 1))%a  with (cgp_b ^+ (3 * Z.to_nat n + 1))%a by solve_addr+Hn.
          replace (cgp_b ^+ (3 * n + 2))%a  with (cgp_b ^+ (3 * Z.to_nat n + 2))%a by solve_addr+Hn.
          iFrame.
        }
        replace (cgp_b ^+ (3 * n + 3))%a with (cgp_b ^+ (3 * (n + 1)))%a by solve_addr + Hn Hn' Hcgp_bound.

        iDestruct (open_isKVS_not_alloc _ _ _ _ idx_empty_found with "HKVS Halloc")
          as "(%opt_kwidx_empty & %Hm_kwidx_empty & HKVS & Halloc & Hfkey & %Hneq_fkey_empty)" ; eauto; [lia|].
        rewrite Hidx_empty_found' in Hm_kwidx_empty; simplify_eq.
        iDestruct "Hfkey" as "(Hn0 & Hn1 & Hn2 & Hfkey)".

        iApply ("IH" with "[] [] [$Hcgp] [$Hrkey] [$Hrscratch] [$Halloc]
         [$Hpost] [$Hridx] [$Hcode] [$HPC] [HKVS Hn0 Hn1 Hn2 Hfkey Hridx_empty]").
        * iPureIntro; lia.
        * iPureIntro.
          intros idx0 Hidx0_bound k0 w0 Hidx0.
          clear Hidx_empty_found.
          destruct (decide (idx0 = Z.to_nat n)%Z) as [-> | Hidx']; eauto.
          { rewrite Hm_kwidx in Hidx0; simplify_map_eq; done. }
          { eapply Hfkey_notin_nfirst; eauto; lia. }
        * case_decide as Hnone'; iFrame; last (iPureIntro; lia).
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
        (* lea cgp 3; *)
        iInstr "Hcode".
        { transitivity (Some ((cgp_b ^+ (3 * (n + 1)))%a)); solve_addr+Hn Hn' Hcgp_bound. }
        (* add ridx ridx 1; *)
        iInstr "Hcode".
        (* jmp (".loop_start"); *)
        iInstr "Hcode".
        { transitivity (Some ( (pc_a ^+ 2)%a)); solve_addr. }

        rewrite {6}(_ : n = (Z.of_nat (Z.to_nat n))); last lia.
        replace (cgp_b ^+ (3 * n))%a with (cgp_b ^+ 3 * Z.to_nat n)%a by solve_addr+Hn.
        replace (cgp_b ^+ (3 * n + 1))%a  with (cgp_b ^+ (3 * Z.to_nat n + 1))%a by solve_addr+Hn.
        replace (cgp_b ^+ (3 * n + 2))%a  with (cgp_b ^+ (3 * Z.to_nat n + 2))%a by solve_addr+Hn.
        iApply ("IH" with "[] [] [$Hcgp] [$Hrkey] [$Hrscratch] [$Halloc]
         [$Hpost] [$Hridx] [$Hcode] [$HPC] [HKVS Hridx_empty Hn0 Hn1 Hn2 Hfkey]").
        * iPureIntro; lia.
        * iPureIntro.
          intros idx0 Hidx0_bound k0 w0 Hidx0.
          clear Hidx_empty_found.
          destruct (decide (idx0 = Z.to_nat n)%Z) as [-> | Hidx']; eauto.
          { rewrite Hm_kwidx in Hidx0; simplify_map_eq; done. }
          { eapply Hfkey_notin_nfirst; eauto; lia. }
        * case_decide as Hnone'; iFrame; last (iPureIntro; lia).
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
