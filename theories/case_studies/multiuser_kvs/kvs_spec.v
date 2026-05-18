From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel rules.
From cap_machine Require Import switcher kvs.
From cap_machine Require Import proofmode.

Definition kvs_entry : Type := (Z * Word).
Definition kvs_map : Type := gmap nat kvs_entry.

(* CMRA for Cerise *)
Class kvsG Σ :=
  KvsG {
      kvs_genG :: gen_heapGS nat kvs_entry Σ; (* memory *)
    }.

Definition kvs_frag_idx_frac `{kvsG} (idx : nat) (k : Z) (w : Word) (q : dfrac) : iProp Σ :=
  (pointsto (L:=nat) (V:=kvs_entry) idx q (k,w)).
Notation "k '⤇(KVS){' q '}[' idx  ']' w" :=
  (kvs_frag_idx_frac idx k w q) (at level 20) : bi_scope.
Notation "k '⤇(KVS)[' idx  ']' w" :=
  (kvs_frag_idx_frac idx k w (DfracOwn 1)) (at level 20) : bi_scope.

Definition kvs_frag `{kvsG} (k : Z ) (w : Word) : iProp Σ := ∃ idx, k ⤇(KVS)[ idx ] w.
Notation "k '⤇(KVS)' w" := (kvs_frag k w) (at level 20) : bi_scope.

Notation "●(KVS) m" := (gen_heap_interp m) (at level 20) : bi_scope.

Section KVS_spec.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {kvsg:kvsG Σ}
    {nainv: logrel_na_invs Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .


  Definition isKVS_entry (a : Addr) (idx : nat) (kw : Z * Word) : iProp Σ :=
    (a ^+ (2*idx))%a ↦ₐ (WInt kw.1) ∗ (a ^+ (2*idx + 1))%a ↦ₐ kw.2.

  Definition kvs_dom : gset nat := set_seq 0 SIZE_MAP.

  Definition wf_kvs_map (m : kvs_map) : Prop :=
    dom m = kvs_dom ∧ NoDup (fst <$> (snd <$> (map_to_list m))).

  Definition isKVS
    (a : Addr) (m : kvs_map) : iProp Σ :=
    ⌜ wf_kvs_map m ⌝ ∗
    ●(KVS) m ∗
    [∗ map] idx ↦ kw ∈ m, isKVS_entry a idx kw.

  Definition isKVS_open
    (a : Addr) (m : kvs_map) (open_idx : nat) : iProp Σ :=
    ⌜ wf_kvs_map m ⌝ ∗
    ●(KVS) m ∗
    [∗ map] idx ↦ kw ∈ (delete open_idx m), isKVS_entry a idx kw.


  Lemma kvs_frag_kvs_frag_idx (k : Z) (w : Word) :
    k ⤇(KVS) w -∗ ∃ idx, k ⤇(KVS)[idx] w.
  Proof. rewrite /kvs_frag; iIntros "?"; done. Qed.

  Lemma kvs_frag_idx_kvs_frag (k : Z) (w : Word) (idx : nat) :
    k ⤇(KVS)[idx] w -∗ k ⤇(KVS) w.
  Proof. rewrite /kvs_frag; iIntros "$".  Qed.

  Lemma open_isKVS_kvs_frag_idx
    (b : Addr) (m : kvs_map)
    (idx : nat) (k : Z) (w : Word) :
    isKVS b m ∗
    k ⤇(KVS)[idx] w -∗
    isKVS_open b m idx ∗
    isKVS_entry b idx (k, w) ∗
    k ⤇(KVS)[idx] w.
  Proof.
    iIntros "( (%HdomKVS & Hkvs_auth & HKVS) & Hk)".
    iDestruct (gen_heap_valid with "Hkvs_auth Hk") as "%Hidx'".
    rewrite -{2}(insert_id m idx (k,w)); last done.
    iDestruct (big_sepM_insert_delete with "HKVS") as "[Hkvs_entry HKVS]".
    iFrame; eauto.
  Qed.

  Lemma close_isKVS_kvs_frag_idx
    (b : Addr) (m : kvs_map)
    (idx : nat) (k : Z) (w : Word) :
    isKVS_open b m idx ∗
    isKVS_entry b idx (k, w) ∗
    k ⤇(KVS)[ idx ] w -∗
    isKVS b m ∗
    k ⤇(KVS)[ idx ] w
  .
  Proof.
    iIntros "( (%HdomKVS & Hkvs_auth & HKVS) & Hkvs_entry & Hk)".
    iDestruct (gen_heap_valid with "Hkvs_auth Hk") as "%Hidx'".
    iDestruct (big_sepM_delete with "[$HKVS $Hkvs_entry]") as "HKVS"; eauto.
    iFrame; eauto.
  Qed.

  Lemma open_isKVS_kvs_frag_idx_diff
    (b : Addr) (m : kvs_map) (idx idx' : nat) (k : Z) (w : Word):
    0 <= idx' < SIZE_MAP ->
    idx ≠ idx' ->
    isKVS b m ∗
    k ⤇(KVS)[ idx ] w -∗
    ∃ k' w',
      ⌜ k ≠ k' ⌝ ∗ ⌜ m !! idx' = Some (k', w') ⌝ ∗
      isKVS_open b m idx' ∗
      k ⤇(KVS)[ idx ] w ∗
      isKVS_entry b idx' (k', w').
  Proof.
    iIntros (Hidx' Hidx) "( (%Hwf & Hkvs_auth & HKVS) & Hk)".
    destruct Hwf as [Hkvs_dom Hkvs_uniqueness].
    iDestruct (gen_heap_valid with "Hkvs_auth Hk") as "%Hm_idx".
    assert (is_Some (m !! idx')) as [ [k' w'] Hm_idx'].
    { apply elem_of_dom. rewrite Hkvs_dom /kvs_dom.
      by apply elem_of_set_seq.
    }
    assert (k ≠ k') as Hkk'.
    { rewrite -(insert_id m idx (k, w)) in Hkvs_uniqueness; last done.
      rewrite -insert_delete_eq in Hkvs_uniqueness.
      rewrite -(insert_id (<[idx:=(k, w)]> (delete idx m)) idx' (k', w')) in Hkvs_uniqueness; last by simplify_map_eq.
      rewrite -insert_delete_eq in Hkvs_uniqueness.
      rewrite -(insert_delete_ne _ idx idx') in Hkvs_uniqueness; auto.
      rewrite map_to_list_insert in Hkvs_uniqueness; last by simplify_map_eq.
      rewrite map_to_list_insert in Hkvs_uniqueness; last by simplify_map_eq.
      cbn in Hkvs_uniqueness.
      apply NoDup_cons_1_1 in Hkvs_uniqueness.
      set_solver+Hkvs_uniqueness.
    }
    iExists k',w'.
    rewrite -{2}(insert_id m idx' (k',w')); last done.
    iDestruct (big_sepM_insert_delete with "HKVS") as "[ [Hkb' Hkw'] HKVS]".
    iFrame; eauto.
  Qed.

  Lemma close_isKVS
    (b : Addr) (m : kvs_map) (idx : nat) (k : Z) (w : Word):
    m !! idx = Some (k, w) ->
    isKVS_open b m idx ∗
    isKVS_entry b idx (k, w) -∗
    isKVS b m.
  Proof.
    iIntros (Hidx) "[(%Hwf & Hkvs_auth & HKVS) Hkvs_entry]"; cbn.
    iDestruct (big_sepM_delete with "[$HKVS $Hkvs_entry]") as "HKVS"; eauto.
    iFrame; eauto.
  Qed.

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

  Lemma KVS_search_spec `{KVS : kvsLayout}
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (rkey ridx rscratch : RegName)
    (fkey : Z)
    (m : kvs_map) (w : Word)
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
      rkey ↦ᵣ WInt fkey ∗
      ridx ↦ᵣ - ∗
      rscratch ↦ᵣ - ∗

      isKVS (cgp_b ^+ 1)%a m ∗
      fkey ⤇(KVS) w ∗

      codefrag pc_a instrs ∗
      ▷ ( ∀ idx,
            (
              ⌜ (0 <= idx) ⌝ ∗
              PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
              cgp ↦ᵣ WCap RW Global cgp_b cgp_e (cgp_b ^+ (1+2*idx) )%a ∗
              rkey ↦ᵣ WInt fkey ∗
              ridx ↦ᵣ WInt idx ∗
              rscratch ↦ᵣ - ∗

              isKVS_open (cgp_b ^+ 1)%a m (idx) ∗
              (cgp_b ^+ (1+2*idx))%a ↦ₐ WInt fkey ∗
              (cgp_b ^+ (2+2*idx))%a ↦ₐ w ∗

              ⌜ withinBounds cgp_b cgp_e (cgp_b ^+ (2 + 2 * idx))%a = true ⌝ ∗

              fkey ⤇(KVS) w ∗
              codefrag pc_a instrs -∗

              WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}
            )
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros instrs ; subst instrs.
    iIntros (HsubBounds Hbounds_cgp Hcgp_bound Hrscratch Hridx Hkey)
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

      iDestruct "HKVS" as "( [%Hkvs_dom %Hkvs_uniqueness] & Hkvs_auth & HKVS)".
      iDestruct (kvs_frag_kvs_frag_idx with "Hkvs_frag") as "(%idx & Hkvs_frag)".
      iDestruct (gen_heap_valid with "Hkvs_auth Hkvs_frag") as "%Hm_idx".
      exfalso.

      assert (0 <= idx < SIZE_MAP) as Hidx.
      { apply elem_of_dom_2 in Hm_idx.
        rewrite Hkvs_dom /kvs_dom in Hm_idx.
        apply elem_of_set_seq in Hm_idx.
        lia.
      }
      apply Hfkey_notin_nfirst in Hidx as (k' & w' & Hm_idx' & Hneq_keys).
      rewrite Hm_idx in Hm_idx'; simplify_eq.
    }
    assert (0 ≤ n < SIZE_MAP)%Z as Hn' by lia.
    (* jnz (".loop_body")%asm rscratch; *)
    iInstr "Hcode".
    { by injection. }

    iDestruct (kvs_frag_kvs_frag_idx with "Hkvs_frag") as "(%idx & Hkvs_frag)".
    destruct (decide (Z.of_nat idx = n)%Z) as [<- | Hneq'].
    - iDestruct (open_isKVS_kvs_frag_idx with "[$HKVS $Hkvs_frag]") as "(HKVS & [Hbk Hbw] & Hkvs_frag)".
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
      iPureIntro; split; first lia.
      rewrite /withinBounds; solve_addr.

    - iDestruct (open_isKVS_kvs_frag_idx_diff _ _ _ (Z.to_nat n) with "[$HKVS $Hkvs_frag]")
        as "(%k' & %w' & %Hkk' & %Hm_idx' & HKVS  & Hkvs_frag & [Hbk Hbw])".
      { lia. }
      { lia. }
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

      iDestruct (close_isKVS with "[$HKVS Hbk Hbw]") as "HKVS";eauto.
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
    let fkey := (kvs_full_key user_key nkey) in

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

      isKVS (cgp_b ^+ 1)%a m ∗
      fkey ⤇(KVS) w ∗
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
    intros imports fkey.
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
