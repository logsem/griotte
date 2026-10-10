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

  Definition kvs_search_found_resources `{KVS : kvsLayout}
    (pc_b pc_e pc_a cgp_b cgp_e : Addr)
    (rkey ridx ridx_empty rscratch : RegName)
    (pkvs : kvs_physical_map) (idx : nat) (fkey : full_key_t) (w : Word) : iProp Σ :=
    let instrs := kvs_search_instrs rkey ridx ridx_empty rscratch in
    (PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
     cgp ↦ᵣ WCap RW Global cgp_b cgp_e
       (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * idx))%a ∗
     rkey ↦ᵣ WInt fkey ∗ ridx ↦ᵣ WInt idx ∗ ridx_empty ↦ᵣ - ∗ rscratch ↦ᵣ - ∗
     (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * idx))%a ↦ₐ WInt ASM_SOME ∗
     (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * idx + 1))%a ↦ₐ WInt fkey ∗
     (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * idx + 2))%a ↦ₐ w ∗
     is_physical_kvs_open cgp_b pkvs idx ∗
     ⌜withinBounds cgp_b cgp_e
        (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * idx + 2))%a = true⌝ ∗
     codefrag pc_a instrs)%I.

  Definition kvs_search_missing_resources `{KVS : kvsLayout}
    (pc_b pc_e pc_a cgp_b cgp_e : Addr)
    (rkey ridx ridx_empty rscratch : RegName)
    (pkvs : kvs_physical_map) (fkey : full_key_t) : iProp Σ :=
    let instrs := kvs_search_instrs rkey ridx ridx_empty rscratch in
    ((∃ idx_empty_slot : nat,
       PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
       cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
       rkey ↦ᵣ WInt fkey ∗ ridx ↦ᵣ WInt (-1)%Z ∗
       ridx_empty ↦ᵣ WInt idx_empty_slot ∗ rscratch ↦ᵣ - ∗
       is_physical_kvs_open cgp_b pkvs idx_empty_slot ∗
       (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * idx_empty_slot))%a ↦ₐ WInt ASM_NONE ∗
       (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * idx_empty_slot + 1))%a ↦ₐ - ∗
       (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * idx_empty_slot + 2))%a ↦ₐ - ∗
       ⌜withinBounds cgp_b cgp_e
          (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * idx_empty_slot + 2))%a = true⌝ ∗
       ⌜0 <= idx_empty_slot⌝ ∗
       ⌜pkvs !! idx_empty_slot = Some None⌝ ∗ codefrag pc_a instrs) ∨
     (PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
      rkey ↦ᵣ WInt fkey ∗ ridx ↦ᵣ WInt (-1)%Z ∗
      ridx_empty ↦ᵣ WInt (-1)%Z ∗ rscratch ↦ᵣ - ∗
      is_physical_kvs cgp_b pkvs ∗ codefrag pc_a instrs))%I.

  Lemma kvs_physical_map_open_any
    (a : Addr) (pkvs : kvs_physical_map) (idx : nat) :
    0 <= idx < SIZE_MAP ->
    is_physical_kvs a pkvs -∗
    ∃ opt_kw,
      ⌜pkvs !! idx = Some opt_kw⌝ ∗
      is_physical_kvs_open a pkvs idx ∗
      physical_kvs_entry a idx opt_kw.
  Proof.
    iIntros (Hidx) "[%Hwf HKVS]".
    pose proof (wf_kvs_is_Some pkvs idx Hwf Hidx) as [opt_kw Hlookup].
    iExists opt_kw. iSplit; first done.
    rewrite -{1}(insert_id pkvs idx opt_kw); last done.
    iDestruct (big_sepM_insert_delete with "HKVS") as "[Hentry HKVS]".
    iFrame. iPureIntro; done.
  Qed.

  Lemma kvs_search_empty_iteration_spec `{KVS : kvsLayout}
    (pc_b pc_e pc_a cgp_b cgp_e : Addr)
    (rkey ridx ridx_empty rscratch : RegName) (n fkey : Z)
    (wempty wscratch w1 w2 : Word) :
    let instrs := kvs_search_instrs rkey ridx ridx_empty rscratch in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->
    ((cgp_b + (ASM_SIZEOF_KVS_ENTRY * SIZE_MAP)%Z)%a = Some cgp_e)%a ->
    (0 <= n < SIZE_MAP)%Z ->
    rscratch ≠ cnull ->
    ridx ≠ cnull ->
    ridx_empty ≠ cnull ->
    rkey ≠ cnull ->

    (PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ 2)%a ∗
     cgp ↦ᵣ WCap RW Global cgp_b cgp_e
       (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n))%a ∗
     rkey ↦ᵣ WInt fkey ∗
     ridx ↦ᵣ WInt n ∗
     ridx_empty ↦ᵣ wempty ∗
     rscratch ↦ᵣ wscratch ∗
     (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n))%a ↦ₐ WInt ASM_NONE ∗
     (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 1))%a ↦ₐ w1 ∗
     (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 2))%a ↦ₐ w2 ∗
     codefrag pc_a instrs ∗

     ▷ (PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ 2)%a ∗
        cgp ↦ᵣ WCap RW Global cgp_b cgp_e
          (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * (n + 1)))%a ∗
        rkey ↦ᵣ WInt fkey ∗
        ridx ↦ᵣ WInt (n + 1) ∗
        ridx_empty ↦ᵣ WInt n ∗
        rscratch ↦ᵣ WInt 0 ∗
        (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n))%a ↦ₐ WInt ASM_NONE ∗
        (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 1))%a ↦ₐ w1 ∗
        (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 2))%a ↦ₐ w2 ∗
        codefrag pc_a instrs -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
     ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros instrs HsubBounds Hcgp_bound Hn Hrscratch Hridx Hridx_empty Hkey.
    iIntros "(HPC & Hcgp & Hrkey & Hridx & Hempty & Hscratch & Hn0 & Hn1 & Hn2 & Hcode & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous; clear H0.
    (* sub rscratch SIZE_MAP ridx; *)
    iInstr "Hcode".
    assert (WInt (SIZE_MAP - n) ≠ WInt 0) by (injection; intro; lia).
    (* jnz (".loop_body")%asm rscratch; *)
    iInstr "Hcode".
    (* load rscratch cgp; *)
    iInstr "Hcode". { split; [done | solve_addr]. }
    (* jnz (".some_index")%asm rscratch; *)
    iInstr "Hcode".
    (* mov ridx_empty ridx; *)
    iInstr "Hcode".
    (* lea cgp ASM_SIZEOF_KVS_ENTRY; *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * (n + 1)))%a); solve_addr. }
    (* add ridx ridx 1; *)
    iInstr "Hcode".
    (* jmp (".loop_start")%asm; *)
    iInstr "Hcode". { transitivity (Some (pc_a ^+ 2)%a); solve_addr. }
    iApply "Hpost". iFrame.
  Qed.

  Lemma kvs_search_found_iteration_spec `{KVS : kvsLayout}
    (pc_b pc_e pc_a cgp_b cgp_e : Addr)
    (rkey ridx ridx_empty rscratch : RegName)
    (n fkey kidx : Z) (widx wempty wscratch : Word) :
    let instrs := kvs_search_instrs rkey ridx ridx_empty rscratch in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->
    ((cgp_b + (ASM_SIZEOF_KVS_ENTRY * SIZE_MAP)%Z)%a = Some cgp_e)%a ->
    (0 <= n < SIZE_MAP)%Z ->
    rscratch ≠ cnull ->
    ridx ≠ cnull ->
    ridx_empty ≠ cnull ->
    rkey ≠ cnull ->

    (PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ 2)%a ∗
     cgp ↦ᵣ WCap RW Global cgp_b cgp_e
       (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n))%a ∗
     rkey ↦ᵣ WInt fkey ∗
     ridx ↦ᵣ WInt n ∗
     ridx_empty ↦ᵣ wempty ∗
     rscratch ↦ᵣ wscratch ∗
     (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n))%a ↦ₐ WInt ASM_SOME ∗
     (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 1))%a ↦ₐ WInt kidx ∗
     (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 2))%a ↦ₐ widx ∗
     codefrag pc_a instrs ∗

     ▷ (((⌜fkey = kidx⌝ ∗
           PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
           cgp ↦ᵣ WCap RW Global cgp_b cgp_e
             (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n))%a ∗
           rkey ↦ᵣ WInt fkey ∗
           ridx ↦ᵣ WInt n ∗
           ridx_empty ↦ᵣ wempty ∗
           rscratch ↦ᵣ WInt 0 ∗
           (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n))%a ↦ₐ WInt ASM_SOME ∗
           (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 1))%a ↦ₐ WInt kidx ∗
           (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 2))%a ↦ₐ widx ∗
           codefrag pc_a instrs) ∨
          (⌜fkey ≠ kidx⌝ ∗
           PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ 2)%a ∗
           cgp ↦ᵣ WCap RW Global cgp_b cgp_e
             (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * (n + 1)))%a ∗
           rkey ↦ᵣ WInt fkey ∗
           ridx ↦ᵣ WInt (n + 1) ∗
           ridx_empty ↦ᵣ wempty ∗
           rscratch ↦ᵣ WInt (fkey - kidx) ∗
           (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n))%a ↦ₐ WInt ASM_SOME ∗
           (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 1))%a ↦ₐ WInt kidx ∗
           (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 2))%a ↦ₐ widx ∗
           codefrag pc_a instrs)) -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
     ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros instrs HsubBounds Hcgp_bound Hn Hrscratch Hridx Hridx_empty Hkey.
    iIntros "(HPC & Hcgp & Hrkey & Hridx & Hempty & Hscratch & Hn0 & Hn1 & Hn2 & Hcode & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous; clear H0.
    (* sub rscratch SIZE_MAP ridx; *)
    iInstr "Hcode".
    assert (WInt (SIZE_MAP - n) ≠ WInt 0) by (injection; intro; lia).
    (* jnz (".loop_body")%asm rscratch; *)
    iInstr "Hcode".
    (* load rscratch cgp; *)
    iInstr "Hcode".
    { split; [done | solve_addr]. }
    (* jnz (".some_index")%asm rscratch; *)
    iInstr "Hcode".
    (* lea cgp 1; *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 1))%a); [solve_addr | done]. }
    (* load rscratch cgp; *)
    iInstr "Hcode".
    { split; [done | solve_addr]. }
    (* sub rscratch rkey rscratch; *)
    iInstr "Hcode".
    destruct (decide (fkey = kidx)) as [-> | Hneq].
    - replace (kidx - kidx)%Z with 0%Z by lia.
      (* jnz (".not_same_key")%asm rscratch; *)
      iInstr "Hcode".
      (* lea cgp (-1)%Z; *)
      iInstr "Hcode"; first (transitivity (Some (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n))%a); solve_addr).
      (* jmp (".loop_end_found")%asm; *)
      iInstr "Hcode".
      iApply "Hpost". iLeft. iFrame. done.
    - assert (WInt (fkey - kidx)%Z ≠ WInt 0) by (injection; intro; simplify_eq; apply Hneq; lia).
      (* jnz (".not_same_key")%asm rscratch; *)
      iInstr "Hcode".
      (* lea cgp 2; *)
      iInstr "Hcode"; first (transitivity (Some (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * (n + 1)))%a); [solve_addr | done]).
      (* add ridx ridx 1; *)
      iInstr "Hcode".
      (* jmp (".loop_start")%asm; *)
      iInstr "Hcode"; first (transitivity (Some (pc_a ^+ 2)%a); solve_addr).
      iApply "Hpost". iRight. iFrame. done.
  Qed.

  Definition kvs_search_outcome_resources `{KVS : kvsLayout}
    (pc_b pc_e pc_a cgp_b cgp_e : Addr)
    (rkey ridx ridx_empty rscratch : RegName)
    (pkvs : kvs_physical_map) (fkey : full_key_t) : iProp Σ :=
    ((∃ (idx : nat) (w : Word),
       ⌜pkvs !! idx = Some (Some (fkey, w))⌝ ∗
       kvs_search_found_resources pc_b pc_e pc_a cgp_b cgp_e
         rkey ridx ridx_empty rscratch pkvs idx fkey w) ∨
     (⌜fkey ∉ kvs_keys pkvs⌝ ∗
      kvs_search_missing_resources pc_b pc_e pc_a cgp_b cgp_e
        rkey ridx ridx_empty rscratch pkvs fkey))%I.

  Lemma kvs_search_full_block_spec `{KVS : kvsLayout}
    (pc_b pc_e pc_a cgp_b cgp_e : Addr)
    (rkey ridx ridx_empty rscratch : RegName) (fkey : full_key_t)
    (wempty wscratch : Word) :
    let instrs := kvs_search_instrs rkey ridx ridx_empty rscratch in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->
    withinBounds cgp_b cgp_e cgp_b = true ->
    ((cgp_b + (ASM_SIZEOF_KVS_ENTRY * SIZE_MAP)%Z)%a = Some cgp_e)%a ->
    rscratch ≠ cnull ->
    ridx ≠ cnull ->
    ridx_empty ≠ cnull ->
    rkey ≠ cnull ->

    (PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ 2)%a ∗
     cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_e ∗
     rkey ↦ᵣ WInt fkey ∗
     ridx ↦ᵣ WInt SIZE_MAP ∗
     ridx_empty ↦ᵣ wempty ∗
     rscratch ↦ᵣ wscratch ∗
     codefrag pc_a instrs ∗

     ▷ (PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
        cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
        rkey ↦ᵣ WInt fkey ∗
        ridx ↦ᵣ WInt (-1)%Z ∗
        ridx_empty ↦ᵣ wempty ∗
        rscratch ↦ᵣ WInt 0 ∗
        codefrag pc_a instrs -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
     ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros instrs HsubBounds Hbounds_cgp Hcgp_bound Hrscratch Hridx Hridx_empty Hkey.
    iIntros "(HPC & Hcgp & Hrkey & Hridx & Hempty & Hscratch & Hcode & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous; clear H0.
    (* sub rscratch SIZE_MAP ridx; *)
    iInstr "Hcode".
    replace (SIZE_MAP - SIZE_MAP)%Z with 0%Z by lia.
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
    iApply "Hpost". iFrame.
  Qed.

  Lemma KVS_search_unified_spec `{KVS : kvsLayout}
    (pc_b pc_e pc_a cgp_b cgp_e : Addr)
    (rkey ridx ridx_empty rscratch : RegName)
    (pkvs : kvs_physical_map) (fkey : full_key_t) :
    let instrs := kvs_search_instrs rkey ridx ridx_empty rscratch in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->
    withinBounds cgp_b cgp_e cgp_b = true ->
    ((cgp_b + (ASM_SIZEOF_KVS_ENTRY * SIZE_MAP)%Z)%a = Some cgp_e)%a ->
    rscratch ≠ cnull -> ridx ≠ cnull -> ridx_empty ≠ cnull -> rkey ≠ cnull ->
    (PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
     cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
     rkey ↦ᵣ WInt fkey ∗ ridx ↦ᵣ - ∗ ridx_empty ↦ᵣ - ∗ rscratch ↦ᵣ - ∗
     is_physical_kvs cgp_b pkvs ∗ codefrag pc_a instrs ∗
     ▷ (kvs_search_outcome_resources pc_b pc_e pc_a cgp_b cgp_e
          rkey ridx ridx_empty rscratch pkvs fkey -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
     ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros instrs.
    iIntros (HsubBounds Hbounds_cgp Hcgp_bound Hrscratch Hridx Hridx_empty Hkey)
      "(HPC & Hcgp & Hrkey & [%wridx Hridx] & [%wridx_empty Hridx_empty] & Hrscratch
        & HKVS & Hcode & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous; clear H0.
    iDestruct (is_physical_kvs_wf with "HKVS") as %Hwf_pkvs.

    (* mov ridx 0%Z; *)
    iInstr "Hcode".
    (* mov ridx_empty (-1)%Z; *)
    iInstr "Hcode".
    destruct (decide (ridx_empty = cnull)) as [Hnull | Hnonnull]; first done.

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
      destruct ( decide (Forall (λ idx : nat, pkvs !! idx ≠ Some None) (seq 0 (Z.to_nat n))) ) as [|Hcontra]; iFrame.
      exfalso; apply Hcontra.
      rewrite Heqn /=; apply Forall_nil; done.
    }
    clear Heqn.

    iLöb as "IH" forall (n Hn Hfkey_notin_nfirst).

    iDestruct "Hrscratch" as "[%wrscratch Hrscratch]".
    destruct (decide ((SIZE_MAP - n) = 0)%Z) as [Hneq|Hneq].
    { (* End of the loop. *)
      assert (n = SIZE_MAP) as -> by lia.
      replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * SIZE_MAP))%a with cgp_e by
        (rewrite /SIZE_MAP in Hcgp_bound |- *; solve_addr).
      assert (fkey ∉ kvs_keys pkvs) as Hnotin.
      { intro Hin. apply elem_of_kvs_keys in Hin as (w0 & idx0 & Hlookup).
        eapply (Hfkey_notin_nfirst idx0); eauto.
        pose proof (wf_kvs_indom_idx pkvs idx0) as Hidx0.
        apply Hidx0; [by apply elem_of_dom | done]. }
      destruct ( decide ( (Forall (λ idx : nat, pkvs !! idx ≠ Some None) (seq 0 (Z.to_nat SIZE_MAP))) )) as [Hnone|Hnone].
      - iDestruct "Hloop_inv" as "(HKVS & Hridx_empty)".
        iApply (kvs_search_full_block_spec pc_b pc_e pc_a cgp_b cgp_e
          rkey ridx ridx_empty rscratch fkey (WInt (-1)) wrscratch
          HsubBounds Hbounds_cgp Hcgp_bound Hrscratch Hridx Hridx_empty Hkey
          with "[$HPC $Hcgp $Hrkey $Hridx $Hridx_empty $Hrscratch $Hcode HKVS Hpost]").
        iNext. iIntros "(HPC & Hcgp & Hrkey & Hridx & Hridx_empty & Hrscratch & Hcode)".
        iApply "Hpost".
        rewrite /kvs_search_outcome_resources /kvs_search_missing_resources.
        iRight. iSplit; first done. iRight. iFrame.

      - iDestruct "Hloop_inv" as
          "(%idx_empty_found & %Hidx_empty_found & HKVS & Hn0 & Hn1 & Hn2 & Hridx_empty & %Hpkvs_idx_empty)".
        iApply (kvs_search_full_block_spec pc_b pc_e pc_a cgp_b cgp_e
          rkey ridx ridx_empty rscratch fkey (WInt idx_empty_found) wrscratch
          HsubBounds Hbounds_cgp Hcgp_bound Hrscratch Hridx Hridx_empty Hkey
          with "[$HPC $Hcgp $Hrkey $Hridx $Hridx_empty $Hrscratch $Hcode HKVS Hn0 Hn1 Hn2 Hpost]").
        iNext. iIntros "(HPC & Hcgp & Hrkey & Hridx & Hridx_empty & Hrscratch & Hcode)".
        iApply "Hpost".
        rewrite /kvs_search_outcome_resources /kvs_search_missing_resources.
        iRight. iSplit; first done. iLeft. iFrame.
        iPureIntro; split.
        * solve_addr.
        * split; [lia | exact Hpkvs_idx_empty].
    }
    assert (0 ≤ n < SIZE_MAP)%Z as Hn' by lia.

    destruct ( decide (Forall (λ idx : nat, pkvs !! idx ≠ Some None) (seq 0 (Z.to_nat n))) ) as [Hnone | Hnone].
    - (* No empty slot have been found yet *)
      iDestruct "Hloop_inv" as "(HKVS & Hridx_empty)".

      iDestruct (kvs_physical_map_open_any _ _ (Z.to_nat n) with "HKVS")
        as "(%opt_kwidx & %Hm_kwidx & HKVS & Hfkey)"; first lia.
      iDestruct (destruct_physical_kvs_entry with "Hfkey") as "(Hn0 & Hn1 & Hn2)"; first solve_addr.
      replace (cgp_b ^+ ASM_SIZEOF_KVS_ENTRY * Z.to_nat n)%a  with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n))%a by solve_addr+Hn.
      replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * Z.to_nat n + 1))%a with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 1))%a by solve_addr+Hn.
      replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * Z.to_nat n + 2))%a with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 2))%a by solve_addr+Hn.

      destruct opt_kwidx as [ [kidx widx] | ].
      + (* This is not an empty slot. Because we mkow that fkey ∉ s, the key will not match *)
        iApply (kvs_search_found_iteration_spec pc_b pc_e pc_a cgp_b cgp_e
          rkey ridx ridx_empty rscratch n fkey kidx widx (WInt (-1)) wrscratch
          HsubBounds Hcgp_bound Hn' Hrscratch Hridx Hridx_empty Hkey
          with "[$HPC $Hcgp $Hrkey $Hridx $Hridx_empty $Hrscratch $Hn0 $Hn1 $Hn2 $Hcode HKVS Hpost]").
        iNext. iIntros "Hresult".
        iDestruct "Hresult" as "[(%Hsame & HPC & Hcgp & Hrkey & Hridx & Hridx_empty & Hrscratch & Hn0 & Hn1 & Hn2 & Hcode) |
          (%Hdifferent & HPC & Hcgp & Hrkey & Hridx & Hridx_empty & Hrscratch & Hn0 & Hn1 & Hn2 & Hcode)]".
        { subst kidx.
          iApply "Hpost".
          rewrite /kvs_search_outcome_resources /kvs_search_found_resources.
          iLeft. iExists (Z.to_nat n), widx. iSplit; first done.
          assert (Hnat : Z.of_nat (Z.to_nat n) = n) by lia.
          rewrite Hnat.
          iFrame. iPureIntro; solve_addr+Hn Hn' Hcgp_bound. }

        iDestruct (kvs_physical_map_close with "[$HKVS] [Hn0 Hn1 Hn2]") as "HKVS";eauto.
        {
          iApply destruct_physical_kvs_entry; first solve_addr.
          replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n))%a with (cgp_b ^+ ASM_SIZEOF_KVS_ENTRY * Z.to_nat n)%a by solve_addr+Hn.
          replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 1))%a  with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * Z.to_nat n + 1))%a by solve_addr+Hn.
          replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 2))%a  with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * Z.to_nat n + 2))%a by solve_addr+Hn.
          iFrame.
        }
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
        iDestruct "Hn1" as "[%wn1 Hn1]".
        iDestruct "Hn2" as "[%wn2 Hn2]".
        iApply (kvs_search_empty_iteration_spec pc_b pc_e pc_a cgp_b cgp_e
          rkey ridx ridx_empty rscratch n fkey (WInt (-1)) wrscratch wn1 wn2
          HsubBounds Hcgp_bound Hn' Hrscratch Hridx Hridx_empty Hkey
          with "[$HPC $Hcgp $Hrkey $Hridx $Hridx_empty $Hrscratch $Hn0 $Hn1 $Hn2 $Hcode HKVS Hpost]").
        iNext. iIntros "Hresult".
        iDestruct "Hresult" as "(HPC & Hcgp & Hrkey & Hridx & Hridx_empty & Hrscratch & Hn0 & Hn1 & Hn2 & Hcode)".

        replace n with (Z.of_nat (Z.to_nat n)) in Hridx_empty by lia.
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
        * case_decide as Hnone'.
          { iFrame. exfalso.
            replace ( (seq 0 (Z.to_nat (n + 1))) ) with ( (seq 0 (Z.to_nat n)) ++ [Z.to_nat n] ) in Hnone'.
            2: {
              replace [Z.to_nat n] with (seq (Z.to_nat n) 1) by done.
              rewrite -seq_app.
              replace (Z.to_nat n + 1) with (Z.to_nat (n + 1)) by lia.
              done.
            }
            apply Forall_app in Hnone' as [_ Hnone'].
            apply (Forall_singleton _ (Z.to_nat n)) in Hnone'; cbn in *.
            done. }
          iExists (Z.to_nat n). iSplit; first (iPureIntro; lia).
          iFrame.
          replace (Z.of_nat (Z.to_nat n)) with n by lia. iFrame.
          iPureIntro; exact Hm_kwidx.

    - (* An empty slot have already been found *)
      iDestruct "Hloop_inv" as
        "(%idx_empty_found & %Hidx_empty_found & HKVS & Hn0 & Hn1 & Hn2 & Hridx_empty
          & %Hpkvs_idx_empty)".

      iDestruct (kvs_physical_map_close _ _ _ None with "[$HKVS] [Hn0 Hn1 Hn2]") as "HKVS";eauto.
      { iApply destruct_physical_kvs_entry; first solve_addr; iFrame. }


      iDestruct (kvs_physical_map_open_any _ _ (Z.to_nat n) with "HKVS")
        as "(%opt_kwidx & %Hm_kwidx & HKVS & Hfkey)"; first lia.
      iDestruct (destruct_physical_kvs_entry with "Hfkey") as "(Hn0 & Hn1 & Hn2)"; first solve_addr.
      replace (cgp_b ^+ ASM_SIZEOF_KVS_ENTRY * Z.to_nat n)%a  with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n))%a by solve_addr+Hn.
      replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * Z.to_nat n + 1))%a with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 1))%a by solve_addr+Hn.
      replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * Z.to_nat n + 2))%a with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 2))%a by solve_addr+Hn.

      destruct opt_kwidx as [ [kidx widx] | ].
      + (* This is not an empty slot. Because we mkow that fkey ∉ s, the key will not match *)
        iApply (kvs_search_found_iteration_spec pc_b pc_e pc_a cgp_b cgp_e
          rkey ridx ridx_empty rscratch n fkey kidx widx (WInt idx_empty_found) wrscratch
          HsubBounds Hcgp_bound Hn' Hrscratch Hridx Hridx_empty Hkey
          with "[$HPC $Hcgp $Hrkey $Hridx $Hridx_empty $Hrscratch $Hn0 $Hn1 $Hn2 $Hcode HKVS Hpost]").
        iNext. iIntros "Hresult".
        iDestruct "Hresult" as "[(%Hsame & HPC & Hcgp & Hrkey & Hridx & Hridx_empty & Hrscratch & Hn0 & Hn1 & Hn2 & Hcode) |
          (%Hdifferent & HPC & Hcgp & Hrkey & Hridx & Hridx_empty & Hrscratch & Hn0 & Hn1 & Hn2 & Hcode)]".
        { subst kidx.
          iApply "Hpost".
          rewrite /kvs_search_outcome_resources /kvs_search_found_resources.
          iLeft. iExists (Z.to_nat n), widx. iSplit; first done.
          assert (Hnat : Z.of_nat (Z.to_nat n) = n) by lia.
          rewrite Hnat.
          iFrame. iPureIntro; solve_addr+Hn Hn' Hcgp_bound. }

        iDestruct (kvs_physical_map_close with "[$HKVS] [Hn0 Hn1 Hn2]") as "HKVS";eauto.
        {
          iApply destruct_physical_kvs_entry; first solve_addr.
          replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n))%a with (cgp_b ^+ ASM_SIZEOF_KVS_ENTRY * Z.to_nat n)%a by solve_addr+Hn.
          replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 1))%a  with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * Z.to_nat n + 1))%a by solve_addr+Hn.
          replace (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * n + 2))%a  with (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * Z.to_nat n + 2))%a by solve_addr+Hn.
          iFrame.
        }
        iDestruct (kvs_physical_map_open_any _ _ idx_empty_found with "HKVS")
          as "(%opt_kwidx_empty & %Hm_kwidx_empty & HKVS & Hfkey)"; first lia.
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
        iDestruct "Hn1" as "[%wn1 Hn1]".
        iDestruct "Hn2" as "[%wn2 Hn2]".
        iApply (kvs_search_empty_iteration_spec pc_b pc_e pc_a cgp_b cgp_e
          rkey ridx ridx_empty rscratch n fkey (WInt idx_empty_found) wrscratch wn1 wn2
          HsubBounds Hcgp_bound Hn' Hrscratch Hridx Hridx_empty Hkey
          with "[$HPC $Hcgp $Hrkey $Hridx $Hridx_empty $Hrscratch $Hn0 $Hn1 $Hn2 $Hcode HKVS Hpost]").
        iNext. iIntros "Hresult".
        iDestruct "Hresult" as "(HPC & Hcgp & Hrkey & Hridx & Hridx_empty & Hrscratch & Hn0 & Hn1 & Hn2 & Hcode)".
        replace n with (Z.of_nat (Z.to_nat n)) in Hridx_empty by lia.
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
        * case_decide as Hnone'.
          { iFrame. exfalso.
            replace ( (seq 0 (Z.to_nat (n + 1))) ) with ( (seq 0 (Z.to_nat n)) ++ [Z.to_nat n] ) in Hnone'.
            2: {
              replace [Z.to_nat n] with (seq (Z.to_nat n) 1) by done.
              rewrite -seq_app.
              replace (Z.to_nat n + 1) with (Z.to_nat (n + 1)) by lia.
              done.
            }
            apply Forall_app in Hnone' as [_ Hnone'].
            apply (Forall_singleton _ (Z.to_nat n)) in Hnone'; cbn in *.
            done. }
          iExists (Z.to_nat n). iSplit; first (iPureIntro; lia).
          iFrame.
          replace (Z.of_nat (Z.to_nat n)) with n by lia. iFrame.
          iPureIntro; exact Hm_kwidx.
  Qed.

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
    intros instrs HsubBounds Hbounds_cgp Hcgp_bound Hlookup Hrscratch Hridx_ne Hridx_empty_ne Hrkey_ne.
    iIntros "(HPC & HcgpReg & Hrkey & Hridx & Hridx_empty & HscratchReg & HKVS & Hcode & Hpost)".
    iDestruct (is_physical_kvs_wf with "HKVS") as %Hwf.
    iApply (KVS_search_unified_spec pc_b pc_e pc_a cgp_b cgp_e
      rkey ridx ridx_empty rscratch pkvs fkey
      HsubBounds Hbounds_cgp Hcgp_bound Hrscratch Hridx_ne Hridx_empty_ne Hrkey_ne
      with "[$HPC $HcgpReg $Hrkey $Hridx $Hridx_empty $HscratchReg $HKVS $Hcode Hpost]").
    iNext. iIntros "Houtcome".
    rewrite /kvs_search_outcome_resources.
    iDestruct "Houtcome" as "[Hfound | [%Hnotin Hmissing]]".
    - iDestruct "Hfound" as (idx' w') "(%Hlookup' & Hfound)".
      destruct (decide (idx = idx')) as [-> | Hidxneq].
      2: { exfalso.
           eapply (wf_kvs_neq pkvs idx idx' fkey fkey w w'); eauto. }
      rewrite Hlookup in Hlookup'; simplify_map_eq.
      iApply "Hpost".
      iEval (rewrite /kvs_search_found_resources) in "Hfound". iFrame.
    - exfalso. apply Hnotin. apply elem_of_kvs_keys.
      eexists w, idx; exact Hlookup.
  Qed.

  Lemma KVS_search_spec_empty_slot `{KVS : kvsLayout}
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (rkey ridx ridx_empty rscratch : RegName)
    (pkvs : kvs_physical_map) (uk : user_key_t) (mk : map_key_t)
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
    intros instrs fkey HsubBounds Hbounds_cgp Hcgp_bound Hnotin Huint16
      Hrscratch Hridx_ne Hridx_empty_ne Hrkey_ne.
    iIntros "(HPC & HcgpReg & Hrkey & Hridx & Hridx_empty & HscratchReg & HKVS & Hcode & Hpost)".
    iApply (KVS_search_unified_spec pc_b pc_e pc_a cgp_b cgp_e
      rkey ridx ridx_empty rscratch pkvs fkey
      HsubBounds Hbounds_cgp Hcgp_bound Hrscratch Hridx_ne Hridx_empty_ne Hrkey_ne
      with "[$HPC $HcgpReg $Hrkey $Hridx $Hridx_empty $HscratchReg $HKVS $Hcode Hpost]").
    iNext. iIntros "Houtcome".
    rewrite /kvs_search_outcome_resources.
    iDestruct "Houtcome" as "[Hfound | [_ Hmissing]]".
    - iDestruct "Hfound" as (idx' w') "(%Hlookup & _)".
      exfalso. apply Hnotin. apply elem_of_kvs_keys.
      eexists w', idx'; exact Hlookup.
    - iApply "Hpost".
      iEval (rewrite /kvs_search_missing_resources) in "Hmissing". iFrame.
  Qed.
End KVS_search.
