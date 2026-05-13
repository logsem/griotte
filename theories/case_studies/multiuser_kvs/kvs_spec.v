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

  Fixpoint isKVS_open
    (b e : Addr) (m : kvs_map) (idx : Z) : iProp Σ :=
    match m with
    | [] => ⌜ b = e ⌝
    | (k,w)::m' =>
        if (idx =? 0)%Z
        then isKVS_open (b^+2)%a e m' (-1)%Z
        else (b ↦ₐ WInt k ∗ (b^+1)%a ↦ₐ w ∗ isKVS_open (b^+2)%a e m' (idx-1)%Z)%I
    end
  .

  Definition kvs_frag_idx (idx : nat) (k : Z * Z) (w : Word) : iProp Σ. Admitted.
  Notation "k ⤇(KVS){ idx } w" := (kvs_frag_idx idx k w) (at level 20) : bi_scope.
  (* Global Instance persistent_kvs_frag k w : Persistent (k ⤇(KVS) w)%I. *)
  (* Admitted. *)

  Definition kvs_frag (k : Z * Z) (w : Word) : iProp Σ := ∃ idx, k ⤇(KVS){ idx } w.
  Notation "k ⤇(KVS) w" := (kvs_frag k w) (at level 20) : bi_scope.
  (* Global Instance persistent_kvs_frag k w : Persistent (k ⤇(KVS) w)%I. *)
  (* Admitted. *)

  Lemma kvs_frag_kvs_frag_idx (k : Z * Z) (w : Word) :
    k ⤇(KVS) w -∗ ∃ idx, k ⤇(KVS){idx} w.
  Proof. rewrite /kvs_frag; iIntros "?"; done. Qed.

  Lemma kvs_frag_idx_kvs_frag (k : Z * Z) (w : Word) (idx : nat) :
    k ⤇(KVS){idx} w -∗ k ⤇(KVS) w.
  Proof. rewrite /kvs_frag; iIntros "$".  Qed.

  Lemma open_isKVS_kvs_frag_idx
    (b e : Addr) (m : kvs_map)
    (idx : nat) (k : Z * Z) (w : Word) :
    isKVS b e m ∗
    k ⤇(KVS){ idx } w -∗
    isKVS_open b e m idx ∗
    (b ^+ (2*idx))%a ↦ₐ WInt (kvs_full_key k.1 k.2) ∗
    (b ^+ (1+2*idx))%a ↦ₐ w ∗
    k ⤇(KVS){ idx } w.
  Proof.
  Admitted.

  Lemma open_isKVS_kvs_frag
    (b e : Addr) (m : kvs_map)
    (k : Z * Z) (w : Word) :
    isKVS b e m ∗
    k ⤇(KVS) w -∗
    ∃ idx,
      isKVS_open b e m idx ∗
      (b ^+ (2*idx))%a ↦ₐ WInt (kvs_full_key k.1 k.2) ∗
      (b ^+ (1+2*idx))%a ↦ₐ w ∗
      k ⤇(KVS) w.
  Proof.
    iIntros "(HKVS & Hkvs_frag)".
    iDestruct (kvs_frag_kvs_frag_idx with "Hkvs_frag") as (idx) "Hkvs_frag".
    iExists idx.
    iDestruct (open_isKVS_kvs_frag_idx with "[$HKVS $Hkvs_frag]") as "($ & $ & $ & Hkvk_frag)".
    by iApply kvs_frag_idx_kvs_frag.
  Qed.

  Lemma close_isKVS_kvs_frag_idx
    (b e : Addr) (m : kvs_map)
    (idx : nat) (k : Z * Z) (w : Word) :
    isKVS_open b e m idx ∗
    (b ^+ (2*idx))%a ↦ₐ WInt (kvs_full_key k.1 k.2) ∗
    (b ^+ (1+2*idx))%a ↦ₐ w ∗
    k ⤇(KVS){ idx } w -∗
    isKVS b e m ∗
    k ⤇(KVS){ idx } w
  .
  Proof.
  Admitted.

  (* TODO move *)
  Notation "r ↦ᵣ -" := (∃ w, pointsto (L:=RegName) (V:=Word) r (DfracOwn 1) w)%I (at level 20) : bi_scope.
  Notation "a ↦ₐ -" := (∃ w, pointsto (L:=Addr) (V:=Word) a (DfracOwn 1) w)%I (at level 20) : bi_scope.

  Lemma KVS_getFullKey_spec `{KVS : kvsLayout}
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (rsealkey rkey rscratch : RegName)
    (user_key nkey : Z)
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
      rscratch ↦ᵣ - ∗

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
      "(HPC & Hcgp & Hrsealkey & Hrkey & [%wscratch Hrscratch] & Hcgp_b & Hcode & Hpost)".
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


  Lemma open_isKVS
    (b e : Addr) (m : kvs_map) (idx : Z):
    (0 ≤ idx < 16)%Z ->
    (* (e + 32)%a = Some b -> *)
    isKVS b e m -∗
    ∃ k w,
      isKVS_open b e m idx ∗
      (b ^+ (2*idx))%a ↦ₐ WInt (kvs_full_key k.1 k.2) ∗
      (b ^+ (1+2*idx))%a ↦ₐ w.
  Proof.
    (*         generalize dependent b. *)
    (*         induction idx; iIntros (b Hkvs_size Hidx) "HKVS"; cbn. *)
    (*         - iDestruct "HKVS" as "%HKVS". solve_addr. *)
    (*         - destruct a as [k w]; iDestruct "HKVS" as "(Hb & Hb' & HKVS)". *)
    (*           destruct ((idx =? 0)%Z). *)
    (*           + iExists (kvs_reverse_full_key k), w. *)
    (*             admit. *)
    (*           + iFrame. *)
    (*             iDestruct (IHm with "HKVS") as "HKVS"; auto. *)
    (* admit. *)
    (*           exists k, w. *)
  Admitted.

  Lemma close_isKVS
    (b e : Addr) (m : kvs_map) (idx : Z) (k : Z * Z) (w : Word):
    (0 ≤ idx < 16)%Z ->
    (* (e + 32)%a = Some b -> *)
    isKVS_open b e m idx ∗
    (b ^+ (2*idx))%a ↦ₐ WInt (kvs_full_key k.1 k.2) ∗
    (b ^+ (1+2*idx))%a ↦ₐ w -∗
    isKVS b e m.
  Proof.
    (*         generalize dependent b. *)
    (*         induction idx; iIntros (b Hkvs_size Hidx) "HKVS"; cbn. *)
    (*         - iDestruct "HKVS" as "%HKVS". solve_addr. *)
    (*         - destruct a as [k w]; iDestruct "HKVS" as "(Hb & Hb' & HKVS)". *)
    (*           destruct ((idx =? 0)%Z). *)
    (*           + iExists (kvs_reverse_full_key k), w. *)
    (*             admit. *)
    (*           + iFrame. *)
    (*             iDestruct (IHm with "HKVS") as "HKVS"; auto. *)
    (* admit. *)
    (*           exists k, w. *)
  Admitted.

  (* From cap_machine Require Import bitblast. *)
  Lemma kvs_full_key_inj (uk1 nk1 uk2 nk2 : Z) :
    (0 <= nk1 < 16)%Z ->
    (0 <= nk2 < 16)%Z ->
    (0 <= uk1)%Z ->
    (0 <= uk2)%Z ->
    (kvs_full_key uk1 nk1 = kvs_full_key uk2 nk2)%Z -> uk1 = uk2 ∧ nk1 = nk2.
  Proof.
    intros Hnk1 Hnk2 Huk1 Huk2 Heq.
    rewrite /kvs_full_key in Heq.
  Admitted.

  Lemma KVS_search_spec `{KVS : kvsLayout}
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (rkey ridx rscratch : RegName)
    (user_key nkey : Z)
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
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e (cgp_b ^+ 1 )%a ∗
      rkey ↦ᵣ WInt (kvs_full_key user_key nkey) ∗
      ridx ↦ᵣ - ∗
      rscratch ↦ᵣ - ∗

      isKVS (cgp_b ^+ 1)%a cgp_e m ∗
      (user_key, nkey) ⤇(KVS) w ∗

      codefrag pc_a instrs ∗
      ▷ ( ∀ idx,
            (
              ⌜ (0 <= idx)%Z ⌝ ∗
              PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
              cgp ↦ᵣ WCap RW Global cgp_b cgp_e (cgp_b ^+ (1+2*idx) )%a ∗
              rkey ↦ᵣ WInt (kvs_full_key user_key nkey) ∗
              ridx ↦ᵣ WInt idx ∗
              rscratch ↦ᵣ - ∗

              isKVS_open (cgp_b ^+ 1)%a cgp_e m idx ∗
              (cgp_b ^+ (1+2*idx))%a ↦ₐ WInt (kvs_full_key user_key nkey) ∗
              (cgp_b ^+ (2+2*idx))%a ↦ₐ w ∗

              ⌜ withinBounds cgp_b cgp_e (cgp_b ^+ (2 + 2 * idx))%a = true ⌝ ∗

              (user_key, nkey) ⤇(KVS) w ∗
              codefrag pc_a instrs -∗

              WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}
            )
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros instrs ; subst instrs.
    iIntros (HsubBounds Hbounds_cgp Hrscratch Hridx Hkey)
      "(HPC & Hcgp & Hrkey & [%widx Hridx] & Hrscratch & HKVS & Hkvs_frag & Hcode & Hpost)".
    assert ( (cgp_b ^+ 33)%a < cgp_e  )%a as Hcgp_bound by admit.
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* Mov ridx 0 *)
    iInstr "Hcode".

    remember 0%Z as n.
    rewrite{1} Heqn.
    iAssert (⌜ (0 <= n <= 16)%Z ⌝)%I as "%Hn"; first (iPureIntro ; lia).
    rewrite{1} (_ : (cgp_b ^+ 1)%a = (cgp_b ^+ (1 + 2 * n))%a); last by solve_addr.
    clear Heqn.
    (* remember (WCap RW Global cgp_b cgp_e (cgp_b ^+ (1 + 2 * n))%a) as gp. *)
    (* clear Heqgp. *)

    iLöb as "IH" forall (n Hn).
    (* sub rscratch SIZE_MAP ridx; *)
    iDestruct "Hrscratch" as "[%wrscratch Hrscratch]".
    iInstr "Hcode".
    destruct (decide ((16 - n) = 0)%Z) as [Hneq|Hneq].
    { (* End of the loop. It means that the key wasn't found in the KVS *)
      (* We know that it should be a contradiction, because `(user_key, nkey)⤇(KVS) w`
         witnesses that it exists
       *)
      rewrite Hneq.
      assert ( n = 16 ) as -> by lia.
      (* jnz (".loop_body")%asm rscratch; *)
      iInstr "Hcode".
      (* jmp (".loop_end_not_found")%asm; *)
      iInstr "Hcode".
      (* lea cgp (-(2*SIZE_MAP))%Z; *)
      iInstr "Hcode".
      { transitivity (Some (cgp_b^+ 1)%a) ; solve_addr. }
      (* mov ridx (-1)%Z; *)
      iInstr "Hcode".
      admit.
    }
    assert (0 ≤ n < 16)%Z as Hn' by lia.
    (* jnz (".loop_body")%asm rscratch; *)
    iInstr "Hcode".
    { by injection. }
    (* load rscratch cgp; *)
    iDestruct (open_isKVS _ _ _ n with "HKVS") as "(%k' & %w' & HKVS & Hbk' & Hbw')"; first done.
    replace ((cgp_b ^+ 1) ^+ 2 * n)%a  with (cgp_b ^+ (1 + 2 * n))%a by solve_addr+Hn.
    replace ((cgp_b ^+ 1) ^+ (1 + 2 * n))%a with (cgp_b ^+ (2 + 2 * n))%a by solve_addr+Hn.
    iInstr "Hcode".
    { split; [done | solve_addr]. }

    (* sub rscratch rkey rscratch; *)
    iInstr "Hcode".
    destruct (decide ( (kvs_full_key user_key nkey - kvs_full_key k'.1 k'.2) = 0)%Z) as [Heqfullkey | Heqfullkey].
    - (* keys are equal *)
      (* jnz (".not_same_key")%asm rscratch; *)
      rewrite Heqfullkey.
      iInstr "Hcode".
      (* jmp (".loop_end_found")%asm; *)
      iInstr "Hcode".

      assert ( (kvs_full_key user_key nkey = kvs_full_key k'.1 k'.2)%Z ) as Heqfullkey' by lia.
      destruct k' as [ku kn].
      apply kvs_full_key_inj in Heqfullkey' as [<- <-].
      {
        assert (w' = w) as -> by admit.
        iApply ("Hpost" $! n); iFrame.
        iPureIntro ; split ; first lia.
        admit.
      }
      all: admit.
    - (* keys are not equal *)
      (* jnz (".not_same_key")%asm rscratch; *)
      iInstr "Hcode".
      { by injection. }
      (* lea cgp 2; *)
      iInstr "Hcode".
      { transitivity (Some ( (cgp_b ^+ (1 + 2 * (n+1)))%a)); solve_addr. }
      (* add ridx ridx 1; *)
      iInstr "Hcode".
      (* jmp (".loop_start"); *)
      iInstr "Hcode".
      { transitivity (Some ( (pc_a ^+ 1)%a)); solve_addr. }
      replace (cgp_b ^+ (1 + 2 * n))%a with ((cgp_b ^+ 1) ^+ 2 * n)%a by solve_addr+Hn.
      replace (cgp_b ^+ (2 + 2 * n))%a with ((cgp_b ^+ 1) ^+ (1 + 2 * n))%a  by solve_addr+Hn.

      iDestruct (close_isKVS with "[$HKVS $Hbk' $Hbw']") as "HKVS"; first done.

      iApply ("IH" with "[] [$Hcgp] [$Hrkey] [$Hrscratch] [$HKVS] [$Hkvs_frag] [$Hpost] [$Hcode] [$HPC] [$Hridx]").
      iPureIntro; lia.
  Admitted.

  Lemma KVS_read `{KVS : kvsLayout}
    (pc_b pc_b' pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (wret : Word)
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
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      (* initial memory layout *)
      [[ pc_b , pc_b' ]] ↦ₐ [[ imports ]] ∗
      codefrag pc_a kvs_read_instrs ∗
      cgp_b ↦ₐ kvs_service_unsealing_key ∗

      isKVS (cgp_b ^+ 1)%a cgp_e m ∗
      (user_key, nkey) ⤇(KVS) w ∗

      ▷ (na_own logrel_nais ⊤ ∗
         PC ↦ᵣ updatePcPerm wret ∗
         cgp ↦ᵣ - ∗
         cra ↦ᵣ - ∗
         ca0 ↦ᵣ WInt ASM_TRUE ∗ (* TRUE: the key exists in the map *)
         ca1 ↦ᵣ w ∗ (* result of the read *)
         ct1 ↦ᵣ - ∗ (* scratch *)
         ct2 ↦ᵣ - ∗ (* scratch *)
         cnull ↦ᵣ -
         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros imports.
    iIntros (HsubBounds Hbounds_user_key Hcgp_contiguous Himports_contiguous)
      "(Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hct1 & Hct2 & [%wcnull Hcnull] & Himports & Hcode & Hcgp_b & HKVS & Hkvs_frag & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)
    rewrite /kvs_read_instrs /assembled_kvs_read.
    rewrite -/(kvs_getFullKey ca0 ca0 ca1 ct1).
    rewrite -/(kvs_search ca0 ct1 ct2).

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
    iNext; iIntros (idx)
             "(%Hidx & HPC & Hcgp & Hca0 & Hct1 & Hct2 & HKVS & Hcgp_key & Hcgp_val & %Hcgp_idx & Hkvs_frag & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 3 "Hcode" as a_read Ha_read "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_search.
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

    iApply "Hpost"; iFrame.
  Qed.

End KVS_spec.
