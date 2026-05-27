From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel rules.
From cap_machine Require Import switcher kvs.
From cap_machine Require Import proofmode.
From cap_machine Require Export kvs_preamble.

Section KVS_search.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {kvsg:kvsG Σ}
    {nainv: logrel_na_invs Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Lemma KVS_search_spec_in `{KVS : kvsLayout}
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (rkey ridx rscratch : RegName)
    (m : kvs_map) (s : kvs_alloc) (idx : nat) (fkey : Z) (w : Word)
    :
    let instrs := (kvs_search_instrs rkey ridx rscratch) in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->
    withinBounds cgp_b cgp_e cgp_b = true ->
    ((cgp_b + (1 + 2*SIZE_MAP)%Z)%a = Some cgp_e)%a ->
    fkey ≠ EMPTY_SLOT ->

    rscratch ≠ cnull ->
    ridx ≠ cnull ->
    rkey ≠ cnull ->

    (
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e (cgp_b ^+ 1 )%a ∗
      rkey ↦ᵣ WInt fkey ∗
      ridx ↦ᵣ - ∗
      rscratch ↦ᵣ - ∗

      isKVS (cgp_b ^+ 1)%a m s ∗
      fkey ⤇(KVS)[idx] w ∗

      codefrag pc_a instrs ∗
      ▷ (
          PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
          cgp ↦ᵣ WCap RW Global cgp_b cgp_e (cgp_b ^+ (1+2*idx) )%a ∗
          rkey ↦ᵣ WInt fkey ∗
          ridx ↦ᵣ WInt idx ∗
          rscratch ↦ᵣ - ∗

          isKVS_open (cgp_b ^+ 1)%a m s idx ∗
          (cgp_b ^+ (1+2*idx))%a ↦ₐ WInt fkey ∗
          (cgp_b ^+ (2+2*idx))%a ↦ₐ w ∗
          isKVS_entry_empty idx fkey ∗

          ⌜ withinBounds cgp_b cgp_e (cgp_b ^+ (2 + 2 * idx))%a = true ⌝ ∗

          fkey ⤇(KVS)[idx] w ∗
          codefrag pc_a instrs -∗

          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros instrs ; subst instrs.
    iIntros (HsubBounds Hbounds_cgp Hcgp_bound Hfkey_ne_empty Hrscratch Hridx Hkey)
      "(HPC & Hcgp & Hrkey & [%widx Hridx] & Hrscratch & HKVS & Hkvs_frag & Hcode & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* Mov ridx 0 *)
    iInstr "Hcode".

    remember 0%Z as n.
    iAssert (⌜ (0 <= n <= SIZE_MAP)%Z ⌝)%I as "%Hn"; first (iPureIntro ; lia).
    rewrite{1} (_ : (cgp_b ^+ 1)%a = (cgp_b ^+ (1 + 2 * n))%a); last by solve_addr.
    assert (forall i, (0 <= i < Z.to_nat n) -> ∃ (k : Z) (w : Word),  m !! i = Some (k,w) ∧ k ≠ fkey)
    as Hfkey_notin_nfirst.
    { rewrite Heqn; intros i Hi; lia. }
    clear Heqn.

    iLöb as "IH" forall (n Hn Hfkey_notin_nfirst).

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
      apply Hfkey_notin_nfirst in Hidx as (k' & w' & Hm_idx' & Hneq_keys).
      rewrite Hm_idx in Hm_idx'; simplify_eq.
    }
    assert (0 ≤ n < SIZE_MAP)%Z as Hn' by lia.
    (* jnz (".loop_body")%asm rscratch; *)
    iInstr "Hcode".
    { by injection. }

    destruct (decide (Z.of_nat idx = n)%Z) as [<- | Hneq'].
    - iDestruct (open_isKVS_kvs_frag_idx with "[$HKVS $Hkvs_frag]") as "(HKVS & (Hbk & Hbw & Hfkey) & Hkvs_frag)".
      replace ((cgp_b ^+ 1) ^+ 2 * idx)%a  with (cgp_b ^+ (1 + 2 * idx))%a by solve_addr+Hn.
      replace ((cgp_b ^+ 1) ^+ (2 * idx + 1))%a with (cgp_b ^+ (2 + 2 * idx))%a by solve_addr+Hn.
      (* load rscratch cgp; *)
      iInstr "Hcode".
      { split; [done |solve_addr]. }
      (* sub rscratch rkey rscratch; *)
      iInstr "Hcode".
      (* jnz (".not_same_key")%asm rscratch; *)
      replace (fkey - (fkey, w).1)%Z with 0%Z by (cbn;lia).
      iInstr "Hcode".
      (* jmp (".loop_end_found")%asm; *)
      iInstr "Hcode".

      cbn.
      iApply "Hpost"; iFrame.
      iPureIntro; rewrite /withinBounds; solve_addr.

    - iDestruct (open_isKVS_kvs_frag_idx_diff _ _ _ _ (Z.to_nat n) with "[$HKVS $Hkvs_frag]")
        as "(%k' & %w' & %Hkk' & %Hm_idx' & HKVS  & Hkvs_frag & (Hbk & Hbw & Hfkey))"
      ; auto; try lia.
      replace ((cgp_b ^+ 1) ^+ 2 * Z.to_nat n)%a  with (cgp_b ^+ (1 + 2 * n))%a by solve_addr+Hn.
      replace ((cgp_b ^+ 1) ^+ (2 * Z.to_nat n + 1))%a with (cgp_b ^+ (2 + 2 * n))%a by solve_addr+Hn.
      (* load rscratch cgp; *)
      iInstr "Hcode".
      { split; [done | solve_addr]. }
      (* sub rscratch rkey rscratch; *)
      iInstr "Hcode".
      (* jnz (".not_same_key")%asm rscratch; *)
      iInstr "Hcode".
      { injection; cbn; lia. }
      (* lea cgp 2; *)
      iInstr "Hcode".
      { transitivity (Some ( (cgp_b ^+ (1 + 2 * (n+1)))%a)); solve_addr. }
      (* add ridx ridx 1; *)
      iInstr "Hcode".
      (* jmp (".loop_start"); *)
      iInstr "Hcode".
      { transitivity (Some ( (pc_a ^+ 1)%a)); solve_addr. }

      iDestruct (close_isKVS with "[$HKVS Hbk Hbw Hfkey]") as "HKVS";eauto.
      {
        replace (cgp_b ^+ (1 + 2 * n))%a with ((cgp_b ^+ 1) ^+ 2 * Z.to_nat n)%a by solve_addr+Hn.
        replace (cgp_b ^+ (2 + 2 * n))%a  with ((cgp_b ^+ 1) ^+ (2 * Z.to_nat n + 1))%a by solve_addr+Hn.
        iFrame.
      }

      iApply ("IH" with "[] [] [$Hcgp] [$Hrkey] [$Hrscratch] [$HKVS] [$Hkvs_frag] [$Hpost] [$Hcode] [$HPC] [$Hridx]").
      + iPureIntro; lia.
      + iPureIntro.
        intros idx' Hidx'_bound.
        destruct (decide (idx' = Z.to_nat n)%Z) as [-> | Hidx']; eauto.
        apply Hfkey_notin_nfirst; lia.
  Qed.

  Lemma KVS_search_spec_notin `{KVS : kvsLayout}
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (rkey ridx rscratch : RegName)
    (m : kvs_map) (s : kvs_alloc) (s' : gset Z) (ku kn : Z)
    :
    let instrs := (kvs_search_instrs rkey ridx rscratch) in
    let fkey := kvs_full_key ku kn in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->
    withinBounds cgp_b cgp_e cgp_b = true ->
    ((cgp_b + (1 + 2*SIZE_MAP)%Z)%a = Some cgp_e)%a ->
    kn ∉ s' ->
    wf_kvs_full_key ku kn ->

    rscratch ≠ cnull ->
    ridx ≠ cnull ->
    rkey ≠ cnull ->

    (
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e (cgp_b ^+ 1 )%a ∗
      rkey ↦ᵣ WInt fkey ∗
      ridx ↦ᵣ - ∗
      rscratch ↦ᵣ - ∗

      isKVS (cgp_b ^+ 1)%a m s ∗
      ◯(ALLOC)[ku] s' ∗

      codefrag pc_a instrs ∗
      ▷ (
          PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
          cgp ↦ᵣ WCap RW Global cgp_b cgp_e (cgp_b ^+ 1)%a ∗
          rkey ↦ᵣ WInt fkey ∗
          ridx ↦ᵣ WInt (-1) ∗
          rscratch ↦ᵣ - ∗

          isKVS (cgp_b ^+ 1)%a m s ∗
          ◯(ALLOC)[ku] s' ∗

          codefrag pc_a instrs -∗

          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros instrs fkey ; subst instrs.
    iIntros (HsubBounds Hbounds_cgp Hcgp_bound Hs' Hwf_full_key Hrscratch Hridx Hkey)
      "(HPC & Hcgp & Hrkey & [%wridx Hridx] & Hrscratch & HKVS & Halloc & Hcode & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* Mov ridx 0 *)
    iInstr "Hcode".

    remember 0%Z as n.
    iAssert (⌜ (0 <= n <= SIZE_MAP)%Z ⌝)%I as "%Hn"; first (iPureIntro ; lia).
    rewrite{1} (_ : (cgp_b ^+ 1)%a = (cgp_b ^+ (1 + 2 * n))%a); last by solve_addr.
    assert (forall i, (0 <= i < Z.to_nat n) -> ∃ (k : Z) (w : Word),  m !! i = Some (k,w) ∧ k ≠ fkey)
    as Hfkey_notin_nfirst.
    { rewrite Heqn; intros i Hi; lia. }
    clear Heqn.

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

      (* lea cgp (-(2*SIZE_MAP))%Z; *)
      iInstr "Hcode".
      { transitivity (Some (cgp_b ^+ 1)%a); rewrite /SIZE_MAP in Hcgp_bound |- *; solve_addr. }
      (* mov ridx (-1)%Z; *)
      iInstr "Hcode".
      rewrite decide_False //=.
      iApply "Hpost"; iFrame.
    }
    assert (0 ≤ n < SIZE_MAP)%Z as Hn' by lia.
    (* jnz (".loop_body")%asm rscratch; *)
    iInstr "Hcode".
    { by injection. }

  iDestruct (open_isKVS_not_alloc _ _ _ _ (Z.to_nat n) with "HKVS Halloc")
    as "(%kidx' & %widx & %Hkidx_ne & %Hm_kidx & HKVS & Halloc & (Hbk & Hbw & Hfkey))" ; eauto; [lia|].
  replace ((cgp_b ^+ 1) ^+ 2 * Z.to_nat n)%a  with (cgp_b ^+ (1 + 2 * n))%a by solve_addr+Hn.
  replace ((cgp_b ^+ 1) ^+ (2 * Z.to_nat n + 1))%a with (cgp_b ^+ (2 + 2 * n))%a by solve_addr+Hn.

  (* load rscratch cgp; *)
  iInstr "Hcode".
  { split; [done | solve_addr]. }
  (* sub rscratch rkey rscratch; *)
  iInstr "Hcode".
  (* jnz (".not_same_key")%asm rscratch; *)
  iInstr "Hcode".
  { injection; cbn; lia. }
  (* lea cgp 2; *)
  iInstr "Hcode".
  { transitivity (Some ( (cgp_b ^+ (1 + 2 * (n+1)))%a)); solve_addr. }
  (* add ridx ridx 1; *)
  iInstr "Hcode".
  (* jmp (".loop_start"); *)
  iInstr "Hcode".
  { transitivity (Some ( (pc_a ^+ 1)%a)); solve_addr. }

  iDestruct (close_isKVS with "[$HKVS Hbk Hbw Hfkey]") as "HKVS";eauto.
  {
    replace (cgp_b ^+ (1 + 2 * n))%a with ((cgp_b ^+ 1) ^+ 2 * Z.to_nat n)%a by solve_addr+Hn.
    replace (cgp_b ^+ (2 + 2 * n))%a  with ((cgp_b ^+ 1) ^+ (2 * Z.to_nat n + 1))%a by solve_addr+Hn.
    iFrame.
  }

  iApply ("IH" with "[] [] [$Hcgp] [$Hrkey] [$Hrscratch] [$HKVS] [$Halloc] [$Hpost] [$Hcode] [$HPC] [$Hridx]").
    + iPureIntro; lia.
    + iPureIntro.
      intros idx' Hidx'_bound.
      destruct (decide (idx' = Z.to_nat n)%Z) as [-> | Hidx']; eauto.
      apply Hfkey_notin_nfirst; lia.
  Qed.

  Lemma KVS_search_spec_empty_slot `{KVS : kvsLayout}
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (rkey ridx rscratch : RegName)
    (m : kvs_map) (s : kvs_alloc)
    :
    let instrs := (kvs_search_instrs rkey ridx rscratch) in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->
    withinBounds cgp_b cgp_e cgp_b = true ->
    ((cgp_b + (1 + 2*SIZE_MAP)%Z)%a = Some cgp_e)%a ->

    rscratch ≠ cnull ->
    ridx ≠ cnull ->
    rkey ≠ cnull ->

    (
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e (cgp_b ^+ 1 )%a ∗
      rkey ↦ᵣ WInt EMPTY_SLOT ∗
      ridx ↦ᵣ - ∗
      rscratch ↦ᵣ - ∗

      isKVS (cgp_b ^+ 1)%a m s ∗

      codefrag pc_a instrs ∗
      ▷ ( (* An empty slot was found*)
          ( ∃ idx_empty_slot : nat,
            (
            PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
            cgp ↦ᵣ WCap RW Global cgp_b cgp_e (cgp_b ^+ (1+2*idx_empty_slot))%a ∗
            rkey ↦ᵣ WInt EMPTY_SLOT ∗
            ridx ↦ᵣ WInt idx_empty_slot ∗
            rscratch ↦ᵣ - ∗

            isKVS_open (cgp_b ^+ 1)%a m s idx_empty_slot ∗
            (cgp_b ^+ (1+2*idx_empty_slot))%a ↦ₐ WInt EMPTY_SLOT ∗
            (cgp_b ^+ (2+2*idx_empty_slot))%a ↦ₐ WInt DEFAULT_VAL ∗
            EMPTY_SLOT ⤇(KVS)[ idx_empty_slot ] WInt DEFAULT_VAL ∗

            ⌜ withinBounds cgp_b cgp_e (cgp_b ^+ (2 + 2 * idx_empty_slot))%a = true ⌝ ∗
            ⌜ 0 <= idx_empty_slot ⌝ ∗

            codefrag pc_a instrs
            )
          )
          ∨ (* No empty slot found*)
            (
              PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
              cgp ↦ᵣ WCap RW Global cgp_b cgp_e (cgp_b ^+ 1)%a ∗
              rkey ↦ᵣ WInt EMPTY_SLOT ∗
              ridx ↦ᵣ WInt (-1) ∗
              rscratch ↦ᵣ - ∗

              isKVS (cgp_b ^+ 1)%a m s ∗

              codefrag pc_a instrs
            ) -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros instrs ; subst instrs.
    iIntros (HsubBounds Hbounds_cgp Hcgp_bound Hrscratch Hridx Hkey)
      "(HPC & Hcgp & Hrkey & [%wridx Hridx] & Hrscratch & HKVS & Hcode & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* Mov ridx 0 *)
    iInstr "Hcode".

    remember 0%Z as n.
    iAssert (⌜ (0 <= n <= SIZE_MAP)%Z ⌝)%I as "%Hn"; first (iPureIntro ; lia).
    rewrite{1} (_ : (cgp_b ^+ 1)%a = (cgp_b ^+ (1 + 2 * n))%a); last by solve_addr.
    assert (forall i, (0 <= i < Z.to_nat n) -> ∃ (k : Z) (w : Word),  m !! i = Some (k,w) ∧ k ≠ EMPTY_SLOT)
    as Hfkey_notin_nfirst.
    { rewrite Heqn; intros i Hi; lia. }
    clear Heqn.

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

      (* lea cgp (-(2*SIZE_MAP))%Z; *)
      iInstr "Hcode".
      { transitivity (Some (cgp_b ^+ 1)%a); rewrite /SIZE_MAP in Hcgp_bound |- *; solve_addr. }
      (* mov ridx (-1)%Z; *)
      iInstr "Hcode".
      rewrite decide_False //=.
      iApply "Hpost"; iRight; iFrame.
    }
    assert (0 ≤ n < SIZE_MAP)%Z as Hn' by lia.
    (* jnz (".loop_body")%asm rscratch; *)
    iInstr "Hcode".
    { by injection. }

  iDestruct (open_isKVS _ _ _ (Z.to_nat n) with "HKVS") as "(%kidx' & %widx & %Hm_kidx & HKVS & (Hbk & Hbw & Hfkey))"
  ; eauto; [lia|].
  replace ((cgp_b ^+ 1) ^+ 2 * Z.to_nat n)%a  with (cgp_b ^+ (1 + 2 * n))%a by solve_addr+Hn.
  replace ((cgp_b ^+ 1) ^+ (2 * Z.to_nat n + 1))%a with (cgp_b ^+ (2 + 2 * n))%a by solve_addr+Hn.
  iEval (cbn) in "Hbk"; iEval (cbn) in "Hbw"; iEval (cbn) in "Hfkey".

  (* load rscratch cgp; *)
  iInstr "Hcode".
  { split; [done | solve_addr]. }
  (* sub rscratch rkey rscratch; *)
  iInstr "Hcode".

  rewrite /isKVS_entry_empty.
  destruct (decide (kidx' = EMPTY_SLOT)) as [Hkidx'_empty |  Hkidx'_empty]; simplify_eq.
  - (* Empty slot found *)
    replace (Z.sub EMPTY_SLOT EMPTY_SLOT) with 0%Z by lia.
    (* jnz (".not_same_key")%asm rscratch; *)
    iInstr "Hcode".
    (* jmp (".loop_end_found")%asm; *)
    iInstr "Hcode".

    iDestruct (isKVS_open_valid with "HKVS Hfkey") as "%Hm_kidx_eq"; simplify_map_eq.
    replace (cgp_b ^+ (1 + 2 * n))%a with (cgp_b ^+ (1 + 2 * Z.to_nat n))%a by solve_addr+Hn.
    replace (cgp_b ^+ (2 + 2 * n))%a  with (cgp_b ^+ (2 + 2 * Z.to_nat n))%a by solve_addr+Hn.


    assert (((Z.of_nat (Z.to_nat n))) = n) as Hn_eq by lia.
    rewrite -{1}Hn_eq.
    iApply "Hpost"; iLeft; iFrame.
    iPureIntro; rewrite /withinBounds; solve_addr.

  - (* Empty slot not found *)

    (* jnz (".not_same_key")%asm rscratch; *)
    iInstr "Hcode".
    { injection; cbn; lia. }
    (* lea cgp 2; *)
    iInstr "Hcode".
    { transitivity (Some ( (cgp_b ^+ (1 + 2 * (n+1)))%a)); solve_addr. }
    (* add ridx ridx 1; *)
    iInstr "Hcode".
    (* jmp (".loop_start"); *)
    iInstr "Hcode".
    { transitivity (Some ( (pc_a ^+ 1)%a)); solve_addr. }

    iDestruct (close_isKVS with "[$HKVS Hbk Hbw Hfkey]") as "HKVS";eauto.
    {
      replace (cgp_b ^+ (1 + 2 * n))%a with ((cgp_b ^+ 1) ^+ 2 * Z.to_nat n)%a by solve_addr+Hn.
      replace (cgp_b ^+ (2 + 2 * n))%a  with ((cgp_b ^+ 1) ^+ (2 * Z.to_nat n + 1))%a by solve_addr+Hn.
      rewrite /isKVS_entry /isKVS_entry_empty /= decide_False //.
      iFrame.
    }

    iApply ("IH" with "[] [] [$Hcgp] [$Hrkey] [$Hrscratch] [$HKVS] [$Hpost] [$Hcode] [$HPC] [$Hridx]").
    + iPureIntro; lia.
    + iPureIntro.
      intros idx' Hidx'_bound.
      destruct (decide (idx' = Z.to_nat n)%Z) as [-> | Hidx']; eauto.
      apply Hfkey_notin_nfirst; lia.
  Qed.

End KVS_search.
