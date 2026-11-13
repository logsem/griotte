From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode.
From griotte Require Import logrel rules.
From griotte Require Import locks.
From griotte Require Import
  switcher_base_ktk kvs kvs_preamble kvs_spec_getFullKey kvs_spec_search kvs_spec_check_uint16
  kvs_spec_acquire map_simpl register_tactics.

(** The outcomes of [read] on the table [pkvs], with the full key [fkey]:
    the key is found with the stored word [w] ([Some w]), or it is missing
    ([None]). *)
Definition kvs_read_outcome (fkey : full_key_t) (pkvs : kvs_physical_map)
  (r : option LWord) : Prop :=
  match r with
  | Some w => ∃ idx, pkvs !! idx = Some (Some (fkey, w))
  | None => fkey ∉ kvs_keys pkvs
  end.

(** The word returned by [read] in [ca1] for the outcome [r]: the stored
    word or, for a heap capability, its tag-cleared form; [0] if the key is
    missing. *)
Definition kvs_read_result `{HeapRegion} (r : option LWord) (actual : LWord) : Prop :=
  match r with
  | Some w => lload_heap w actual
  | None => actual = lword_of_word (WInt 0)
  end.

Section KVS_spec_read.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {kvsg:kvsG Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
    {KVS_layout : kvsLayout} {KVS_layout_WF : kvsLayoutWf}
    {LK : locksLayout}
    (kvs_users : gmap user_key_t CmptName)
  .

  (** The critical section of [read] on the ghost state: the table is
      handed to the code and given back unchanged; the outcome of the
      search is the entry [o] of the user [uk] at [nkey]. *)
  Lemma kvs_read_ghost
    (uk : user_key_t) (nkey : map_key_t) (o : option LWord) :
    let fkey := kvs_full_key uk nkey in
    is_uint16 nkey ->
    physical_kvs_inv ∗
    logical_kvs_inv ∗
    user_kvs_inv uk ∗
    (uk, nkey) ↦(UKVS) o -∗
    ∃ pkvs,
      is_physical_kvs KVS_cgp_b pkvs ∗
      ∀ r,
        ⌜ kvs_read_outcome fkey pkvs r ⌝ -∗
        is_physical_kvs KVS_cgp_b pkvs -∗
        ⌜ r = o ⌝ ∗
        physical_kvs_inv ∗
        logical_kvs_inv ∗
        user_kvs_inv uk ∗
        (uk, nkey) ↦(UKVS) o.
  Proof.
    intros fkey Hnkey.
    iIntros "( (%pkvs & HPKVS & Hpf) & (%lkvs & Hlauth & %pkvs2 & %Hsync & Hpf2)
              & (%ukvs & Hua & %m & Hm & %Husync) & Hk)".
    iDestruct (kvs_physical_kvs_valid with "Hpf Hpf2") as %<-.
    iDestruct (kvs_logical_kvs_valid with "Hlauth Hm") as %Hlk.
    iDestruct (kvs_user_kvs_valid with "Hua Hk") as %Huk.
    iExists pkvs. iFrame "HPKVS".
    iIntros (r Hout) "HPKVS".
    iSplit.
    { iPureIntro.
      assert (o = m !! nkey) as ->.
      { destruct (Husync nkey) as [Hs _].
        pose proof (Hs (mk_is_Some _ _ Huk)) as Hs'. rewrite Hs' in Huk. by injection Huk. }
      destruct r as [w|]; cbn in Hout.
      - destruct Hout as [idx Hidx].
        destruct (proj2 (Hsync (uk, nkey) w Hnkey) (ex_intro _ idx Hidx)) as (m' & Hm' & Hw).
        cbn in Hm', Hw. rewrite Hlk in Hm'. injection Hm' as <-. by rewrite Hw.
      - destruct (m !! nkey) as [w|] eqn:Hmk; last done.
        exfalso. apply Hout. apply elem_of_kvs_keys_2. exists w.
        eapply kvs_synced_logical_lookup_Some; eauto. }
    iFrame "Hk HPKVS Hpf Hlauth Hpf2 Hua Hm". done.
  Qed.

  (*** KVS READ: the code *)

  (** The code of [read], from its entry with a uint16 map key and a sealed
      user key to its return. The critical section is the hook ["Hcs"]: from
      the resource of the lock, it gives the table to the code, and takes it
      back unchanged with the outcome [r] of the search, giving [Q r]. *)
  Lemma KVS_read_spec_layer_0
    (wret : LWord)
    (user_key : user_key_t) (nkey : map_key_t) (πnkey : option AId) (l_user_key : Locality) (user_key_addr : Addr)
    (dq : dfrac)
    (mie : InterruptStatus)
    (Q : option LWord -> iProp Σ)
    :
    let fkey := (kvs_full_key user_key nkey) in

    is_shadow_address (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET) = false ->
    is_shadow_address user_key_addr = false ->
    is_heap_address kvs_lock_addr = false ->
    is_heap_address b_locks = false ->

    withinBounds user_key_addr (user_key_addr ^+ 1) user_key_addr = true ->
    is_uint16 nkey ->

    jalr_target_ok cnull cra wret.(lw) = true ->
    th ≠ CtxSwitch ->
    route_pre th mie ->

    ( kvs_static ∗
      kvs_lock kvs_users ∗

      (* initial register file *)
      PC ↦ₚ[th] Cap RX Global KVS_pcc_b KVS_pcc_e kvs_read_pcc_addr ∗
      cgp ↦ᵣ[th] Cap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ[th] wret ∗
      MIE ↦ₜ[th] mie ∗
      held (th := th) mie ∗
      ca0 ↦ᵣ[th] kvs_user_seal_key l_user_key user_key_addr ∗ (* Sealed User Key *)
      ca1 ↦ᵣ[th] WInt nkey @@? πnkey ∗ (* Key to read *)
      cs0 ↦ᵣ[th] - ∗ (* scratch: the lock *)
      cs1 ↦ᵣ[th] - ∗ (* scratch *)
      ct0 ↦ᵣ[th] - ∗ (* scratch *)
      ctp ↦ᵣ[th] - ∗ (* scratch *)
      ct1 ↦ᵣ[th] - ∗ (* scratch *)
      ct2 ↦ᵣ[th] - ∗ (* scratch *)

      user_key_addr ↦ₐ{dq} WInt user_key ∗

      (* the critical section *)
      (kvs_R kvs_users ={⊤}=∗
       ∃ pkvs,
         is_physical_kvs KVS_cgp_b pkvs ∗
         ∀ r,
           ⌜ kvs_read_outcome fkey pkvs r ⌝ -∗
           is_physical_kvs KVS_cgp_b pkvs
           ={⊤}=∗
           kvs_R kvs_users ∗ Q r) ∗

      ▷ (∀ r,
          Q r ∗
          PC ↦ₚ[th] lupdatePcPerm wret ∗
          cgp ↦ᵣ[th] - ∗
          cra ↦ᵣ[th] - ∗
          MIE ↦ₜ[th] default mie (jalr_target_mie wret.(lw)) ∗
          held (th := th) (default mie (jalr_target_mie wret.(lw))) ∗
          ca0 ↦ᵣ[th] WInt (if r then ASM_TRUE else ASM_FALSE) ∗
          (∃ actual, ca1 ↦ᵣ[th] actual ∗ ⌜ kvs_read_result r actual ⌝) ∗
          cs0 ↦ᵣ[th] - ∗
          cs1 ↦ᵣ[th] - ∗
          ct0 ↦ᵣ[th] - ∗
          ctp ↦ᵣ[th] - ∗
          ct1 ↦ᵣ[th] - ∗
          ct2 ↦ᵣ[th] - ∗
          user_key_addr ↦ₐ{dq} WInt user_key
          -∗ safe[th])
      ⊢ safe[th])%I.
  Proof.
    pose proof KVS_cgp_disjoint_from_shadow as Hcgp_shadow.
    intros fkey.
    iIntros (Hunsealing_shadow Huser_key_shadow Hlock_heap Hlocks_heap Hbounds_a_user_key
      His_uint16_nkey Htgt Hth Hroute)
      "(#Hkvs_static & #Hlock & HPC & Hcgp & Hcra & Hmie & Hheld & Hca0 & Hca1
        & Hcs0 & Hcs1 & Hct0 & Hctp & Hct1 & Hct2 & Ha_user_key & Hcs & Hpost)".
    iDestruct (kvs_static_unsealing_key with "Hkvs_static") as "#Ha_unsealing".
    iDestruct (kvs_static_try_lock with "Hkvs_static") as "#Ha_try_lock".
    iDestruct "Hkvs_static" as "(_ & #Hcode_main & #Hlock_static)".
    pose proof (HKVS_pcc_b' := KVS_size_imports).
    pose proof (Hcode_continuous := KVS_size_code).
    pose proof (Hcgp_continuous := KVS_size_data).
    assert ((KVS_cgp_b + length kvs_data)%a = Some KVS_cgp_e) as Hbounds_cgp.
    { by rewrite /length_kvs_data in Hcgp_continuous. }

    (* The code of [read], out of the service *)
    rewrite /kvs_service_instrs.
    focus_block_nochangePC 1 "Hcode_main" as a_read Ha_read "Hcode" "Hcont".
    assert (a_read = kvs_read_pcc_addr) as ->
      by (rewrite /kvs_read_pcc_addr kvs_read_pcc_off_eq; cbn in *;
          solve_addr+Hcode_continuous HKVS_pcc_b' Ha_read).
    iClear "Hcont Hcode_main". clear H.
    assert (SubBounds KVS_pcc_b KVS_pcc_e kvs_read_pcc_addr
              (kvs_read_pcc_addr ^+ length kvs_read_instrs)) as Hbounds_pcc.
    { rewrite /kvs_service_instrs !length_app in Hcode_continuous.
      rewrite /kvs_read_pcc_addr kvs_read_pcc_off_eq.
      solve_addr+HKVS_pcc_b' Hcode_continuous. }
    iRename "Hcode" into "Hcode_main".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)
    iEval (rewrite /kvs_read_instrs /assembled_kvs_read) in "Hcode_main".
    iEval (rewrite -/(kvs_search ca0 ctp ct1 ct2) -/(kvs_check_uint16 ca1 ct1) -/kvs_table) in "Hcode_main".
    iEval (cbn [fmap list_fmap]) in "Hcode_main".
    iEval (cbn [concat]) in "Hcode_main".

    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcode_main" as hcode.
    iApply (KVS_check_uint16_spec_is_uint16 with "[- $HPC $Hca1 $Hct1 $Hcode]"); eauto; iNext.
    iIntros "(HPC & Hca1 & _ & Hct1)".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    focus_block 1 "Hcode_main" as a_check_uint Ha_check_uint "Hcode" "Hcont"; iHide "Hcode_main" as hcode.
    (* jnez (".read_not_uint16")%asm ct1; *)
    iInstr "Hcode".
    (* jmp (".read_uint16_check_pass")%asm; *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    focus_block 2 "Hcode_main" as a_get_full_key Ha_get_full_key "Hcode" "Hcont"; iHide "Hcode_main" as hcode
    ; clear dependent Ha_check_uint.
    iApply (KVS_getFullKey_spec with "[- $HPC $Hctp $Hca0 $Hca1 $Ha_unsealing $Ha_user_key $Hcode]") ; eauto.
    { kvs_getFullKey_offset. }
    iNext.
    iIntros "(HPC & Hctp & Hca0 & Hca1 & _ & Ha_user_key & _)".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    focus_block 3 "Hcode_main" as a_lea Ha_lea "Hcode" "Hcont"; iHide "Hcode_main" as hcode ; clear dependent Ha_get_full_key.
    (* mov ca0 ctp; *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    (* acquire(); *)
    focus_block 4 "Hcode_main" as a_acquire Ha_acquire "Hcode" "Hcont"; iHide "Hcode_main" as hcode ; clear dependent Ha_lea.
    iAssert (ct1 ↦ᵣ[th] -)%I with "[Hct1]" as "Hct1"; first by iExists _.
    iApply (kvs_acquire_spec kvs_users KVS_pcc_b KVS_pcc_e a_acquire kvs_read_acquire_off mie wret
             with "[- $HPC $Hcgp $Hcra $Hcs0 $Hcs1 $Hct0 $Hct1 $Hct2 $Hmie $Hheld $Hcode $Ha_try_lock
                     $Hlock_static $Hlock]").
    { assumption. }
    { rewrite !length_app in Ha_acquire. cbn in Ha_acquire.
      rewrite /kvs_read_acquire_off /kvs_acquire_fetch_at.
      rewrite /kvs_read_pcc_addr kvs_read_pcc_off_eq in Ha_acquire.
      rewrite /length_kvs_imports in HKVS_pcc_b' Ha_acquire. cbn in HKVS_pcc_b', Ha_acquire.
      rewrite /TRY_LOCK_OFFSET. solve_addr. }
    { eapply disjoint_from_shadow_not_in; first exact KVS_pcc_disjoint_from_shadow.
      apply withinBounds_true_iff.
      rewrite /kvs_service_instrs !length_app in Hcode_continuous.
      rewrite /TRY_LOCK_OFFSET. solve_addr. }
    all: try done.
    iNext. iIntros "(HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hct0 & Hct1 & Hct2 & Hmie & Hheld & HR)".
    iEval (rewrite (_ : length (kvs_acquire_instrs kvs_read_acquire_off) = 17%nat); last done) in "HPC".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    (* [cgp] restricted to the table *)
    focus_block 5 "Hcode_main" as a_table Ha_table "Hcode" "Hcont"; iHide "Hcode_main" as hcode ; clear dependent Ha_acquire.
    iApply (kvs_table_spec KVS_pcc_b KVS_pcc_e a_table with "[- $HPC $Hcgp $Hct0 $Hct1 $Hcode]"); try done.
    iNext. iIntros "(HPC & Hcgp & Hct0 & Hct1)".
    iEval (rewrite (_ : length kvs_table_instrs = 3%nat); last done) in "HPC".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    focus_block 6 "Hcode_main" as a_search Ha_search "Hcode" "Hcont"; iHide "Hcode_main" as hcode; clear dependent Ha_table.
    pose proof (eq_refl : length kvs_data = 49) as Hlen.
    rewrite Hlen in Hbounds_cgp.
    assert ((KVS_cgp_b + 48)%a = Some kvs_lock_addr) as Hlock_addr.
    { rewrite /kvs_lock_addr /KVS_LOCK_OFFSET. solve_addr. }
    assert (disjoint_from_shadow KVS_cgp_b kvs_lock_addr) as Htable_shadow.
    { rewrite /disjoint_from_shadow in Hcgp_shadow |- *.
      intros a Ha Hsh. apply (Hcgp_shadow a); last done.
      apply elem_of_finz_seq_between; apply elem_of_finz_seq_between in Ha. solve_addr. }
    (* The critical section: the table *)
    iMod ("Hcs" with "HR") as (pkvs) "[HPKVS Hclose]".
    iAssert (ctp ↦ᵣ[th] -)%I with "[Hctp]" as "Hctp"; first by iExists _.
    iAssert (ct2 ↦ᵣ[th] -)%I with "[Hct2]" as "Hct2"; first by iExists _.
    iApply (KVS_search_unified_spec KVS_pcc_b KVS_pcc_e a_search KVS_cgp_b kvs_lock_addr
              ca0 ctp ct1 ct2 pkvs fkey
             with "[- $HPC $Hcgp $Hca0 $Hctp $Hct1 $Hct2 $HPKVS $Hcode]");
      [exact Htable_shadow | assumption | rewrite /withinBounds; solve_addr | exact Hlock_addr
      | done | done | done | done |].
    iNext. iIntros "Hout".
    rewrite /kvs_search_outcome_resources /kvs_search_found_resources /kvs_search_missing_resources.
    iDestruct "Hout" as "[ (%idx & %w_old & %Hidx & HPC & Hcgp & Hca0 & Hctp & Hct1 & Hct2 & Hcgp_opt
                          & Hcgp_key & Hcgp_val & HPKVS & %Hcgp_idx & _)
                        | (%Hnot & [ (%idx_empty & HPC & Hcgp & Hca0 & Hctp & Hct1 & Hct2 & HPKVS
                                      & Hcgp_opt & [%wkey Hcgp_key] & [%wval Hcgp_val] & %Hcgp_bounds
                                      & %Hidx_empty & %Hpkvs_idx_empty & _)
                                   | (HPC & Hcgp & Hca0 & Hctp & Hct1 & Hct2 & HPKVS & _) ]) ]".
    all: unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
    all: focus_block 7 "Hcode_main" as a_found Ha_found "Hcode" "Hcont"; iHide "Hcode_main" as hcode; clear dependent Ha_search.

    - (* The key is found: its value is loaded *)
      (* sub ctp ctp (-1)%Z; *)
      iInstr "Hcode".
      (* jnez (".read_key_found")%asm ctp; *)
      iInstr "Hcode".
      { apply nonZero_WInt; injection; intros; lia. }
      (* lea cgp cgp 2; *)
      iInstr "Hcode".
      { transitivity ( Some (KVS_cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * idx + 2)) ); last done; solve_addr+Hcgp_idx. }
      (* load ca1 cgp: the heap shadow can clear the returned tag. *)
      iInstrApply "Hcode" (wp_load_preserve_or_clear_noid _ _ _ _ _ _ _ (a_found ^+ 7))
        with "[$HPC $Hca1 $Hcgp $Hcgp_val]"
        as (actual) "(%Hactual & HPC & Hca1 & Hcgp & Hcgp_val)".
      { eapply disjoint_from_shadow_not_in; first exact Htable_shadow. exact Hcgp_idx. }
      replace (lload_word RW w_old) with w_old in Hactual by (destruct w_old; done).
      (* mov ca0 ASM_TRUE; *)
      iInstr "Hcode".
      iDestruct (kvs_physical_map_close with "[$HPKVS] [Hcgp_opt Hcgp_key Hcgp_val]")
        as "HPKVS"; eauto.
      { iApply destruct_physical_kvs_entry; first (clear -Hcgp_idx Hlock_addr; solve_addr); iFrame. }
      unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
      iMod ("Hclose" $! (Some w_old) with "[%] HPKVS") as "[HR HQ]".
      { by exists idx. }
      focus_block 8 "Hcode_main" as a_release Ha_release "Hcode" "Hcont"; iHide "Hcode_main" as hcode; clear dependent Ha_found.
      iDestruct (codefrag_app_pers a_release kvs_release_instrs
                   (encodeInstrsW [Jalr cnull cra]) with "Hcode") as "[#Hrel _]".
      (* release(): store cs0 0; mov cs0 0; *)
      iApply (kvs_release_spec kvs_users KVS_pcc_b KVS_pcc_e a_release mie
               with "[- $HPC $Hcs0 $Hmie $Hheld $Hrel $Hlock $HR]"); [solve_addr | done |].
      iNext. iIntros "(HPC & Hcs0 & Hmie & Hheld)".
      clear Ha_release.
      (* jalr cnull cra; *)
      iInstr "Hcode".
      iApply ("Hpost" $! (Some w_old)). iFrame "HQ HPC Hmie Hheld Hca0 Ha_user_key".
      iSplitL "Hcgp"; first by iExists _.
      iSplitL "Hcra"; first by iExists _.
      iSplitL "Hca1"; first by iExists _; iFrame.
      iFrame.

    - (* The key is missing, an empty slot is found *)
      (* sub ctp ctp (-1)%Z; *)
      iInstr "Hcode".
      replace (-1 - -1)%Z with 0%Z by lia.
      (* jnez (".read_key_found")%asm ctp; *)
      iInstr "Hcode".
      (* mov ca0 ASM_FALSE; *)
      iInstr "Hcode".
      (* mov ca1 0; *)
      iInstr "Hcode".
      (* jmp (".read_key_ret")%asm; *)
      iInstr "Hcode".
      iDestruct (kvs_physical_map_close with "[$HPKVS] [Hcgp_opt Hcgp_key Hcgp_val]")
        as "HPKVS"; eauto.
      { iApply destruct_physical_kvs_entry; first (clear -Hcgp_bounds Hlock_addr; solve_addr); iFrame. }
      unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
      iMod ("Hclose" $! None with "[%] HPKVS") as "[HR HQ]".
      { exact Hnot. }
      focus_block 8 "Hcode_main" as a_release Ha_release "Hcode" "Hcont"; iHide "Hcode_main" as hcode; clear dependent Ha_found.
      iDestruct (codefrag_app_pers a_release kvs_release_instrs
                   (encodeInstrsW [Jalr cnull cra]) with "Hcode") as "[#Hrel _]".
      (* release(): store cs0 0; mov cs0 0; *)
      iApply (kvs_release_spec kvs_users KVS_pcc_b KVS_pcc_e a_release mie
               with "[- $HPC $Hcs0 $Hmie $Hheld $Hrel $Hlock $HR]"); [solve_addr | done |].
      iNext. iIntros "(HPC & Hcs0 & Hmie & Hheld)".
      clear Ha_release.
      (* jalr cnull cra; *)
      iInstr "Hcode".
      iApply ("Hpost" $! None). iFrame "HQ HPC Hmie Hheld Hca0 Ha_user_key".
      iSplitL "Hcgp"; first by iExists _.
      iSplitL "Hcra"; first by iExists _.
      iSplitL "Hca1"; first by iExists _; iFrame.
      iFrame.

    - (* The key is missing, no slot is empty *)
      (* sub ctp ctp (-1)%Z; *)
      iInstr "Hcode".
      replace (-1 - -1)%Z with 0%Z by lia.
      (* jnez (".read_key_found")%asm ctp; *)
      iInstr "Hcode".
      (* mov ca0 ASM_FALSE; *)
      iInstr "Hcode".
      (* mov ca1 0; *)
      iInstr "Hcode".
      (* jmp (".read_key_ret")%asm; *)
      iInstr "Hcode".
      unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
      iMod ("Hclose" $! None with "[%] HPKVS") as "[HR HQ]".
      { exact Hnot. }
      focus_block 8 "Hcode_main" as a_release Ha_release "Hcode" "Hcont"; iHide "Hcode_main" as hcode; clear dependent Ha_found.
      iDestruct (codefrag_app_pers a_release kvs_release_instrs
                   (encodeInstrsW [Jalr cnull cra]) with "Hcode") as "[#Hrel _]".
      (* release(): store cs0 0; mov cs0 0; *)
      iApply (kvs_release_spec kvs_users KVS_pcc_b KVS_pcc_e a_release mie
               with "[- $HPC $Hcs0 $Hmie $Hheld $Hrel $Hlock $HR]"); [solve_addr | done |].
      iNext. iIntros "(HPC & Hcs0 & Hmie & Hheld)".
      clear Ha_release.
      (* jalr cnull cra; *)
      iInstr "Hcode".
      iApply ("Hpost" $! None). iFrame "HQ HPC Hmie Hheld Hca0 Ha_user_key".
      iSplitL "Hcgp"; first by iExists _.
      iSplitL "Hcra"; first by iExists _.
      iSplitL "Hca1"; first by iExists _; iFrame.
      iFrame.
  Qed.

  (*** KVS READ: a known caller, which holds its own map *)

  (** [read] for a caller that holds the map of its user key: the result is
      its entry [o] at [nkey], which is unchanged. *)
  Lemma KVS_read_spec
    (wret : LWord)
    (user_key : user_key_t) (nkey : map_key_t) (πnkey : option AId) (l_user_key : Locality) (user_key_addr : Addr)
    (dq : dfrac)
    (o : option LWord)
    (F : coPset)
    (mie : InterruptStatus)
    :

    is_shadow_address (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET) = false ->
    is_shadow_address user_key_addr = false ->
    is_heap_address kvs_lock_addr = false ->
    is_heap_address b_locks = false ->

    is_uint16 nkey ->
    withinBounds user_key_addr (user_key_addr ^+ 1) user_key_addr = true ->

    jalr_target_ok cnull cra wret.(lw) = true ->
    th ≠ CtxSwitch ->
    route_pre th mie ->

    ( kvs_static ∗
      kvs_lock kvs_users ∗
      na_own (tpool th) F ∗

      (* initial register file *)
      PC ↦ₚ[th] Cap RX Global KVS_pcc_b KVS_pcc_e kvs_read_pcc_addr ∗
      cgp ↦ᵣ[th] Cap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ[th] wret ∗
      MIE ↦ₜ[th] mie ∗
      held (th := th) mie ∗
      ca0 ↦ᵣ[th] kvs_user_seal_key l_user_key user_key_addr ∗ (* Sealed User Key *)
      ca1 ↦ᵣ[th] WInt nkey @@? πnkey ∗ (* Key to read *)
      cs0 ↦ᵣ[th] - ∗ (* scratch: the lock *)
      cs1 ↦ᵣ[th] - ∗ (* scratch *)
      ct0 ↦ᵣ[th] - ∗ (* scratch *)
      ctp ↦ᵣ[th] - ∗ (* scratch *)
      ct1 ↦ᵣ[th] - ∗ (* scratch *)
      ct2 ↦ᵣ[th] - ∗ (* scratch *)

      user_key_addr ↦ₐ{dq} WInt user_key ∗

      user_kvs_inv user_key ∗
      (user_key, nkey) ↦(UKVS) o ∗

      ▷ (na_own (tpool th) F ∗
         PC ↦ₚ[th] lupdatePcPerm wret ∗
         cgp ↦ᵣ[th] - ∗
         cra ↦ᵣ[th] - ∗
         MIE ↦ₜ[th] default mie (jalr_target_mie wret.(lw)) ∗
         held (th := th) (default mie (jalr_target_mie wret.(lw))) ∗
         ca0 ↦ᵣ[th] WInt (if o then ASM_TRUE else ASM_FALSE) ∗
         (∃ actual, ca1 ↦ᵣ[th] actual ∗ ⌜ kvs_read_result o actual ⌝) ∗ (* result of the read *)
         cs0 ↦ᵣ[th] - ∗
         cs1 ↦ᵣ[th] - ∗
         ct0 ↦ᵣ[th] - ∗
         ctp ↦ᵣ[th] - ∗
         ct1 ↦ᵣ[th] - ∗
         ct2 ↦ᵣ[th] - ∗
         user_key_addr ↦ₐ{dq} WInt user_key ∗
         user_kvs_inv user_key ∗
         (user_key, nkey) ↦(UKVS) o
         -∗ safe[th])
      ⊢ safe[th])%I.
  Proof.
    iIntros (Hunsealing_shadow Huser_key_shadow Hlock_heap Hlocks_heap His_uint16_nkey
      Hbounds_a_user_key Htgt Hth Hroute)
      "(#Hkvs_static & #Hlock & Hna
      & HPC & Hcgp & Hcra & Hmie & Hheld & Hca0 & Hca1 & Hcs0 & Hcs1 & Hct0 & Hctp & Hct1 & Hct2
      & Ha_user_key & Huser & Hk & Hpost)".
    iApply (KVS_read_spec_layer_0 wret user_key nkey πnkey l_user_key user_key_addr dq mie
              (λ r, ⌜ r = o ⌝ ∗ user_kvs_inv user_key ∗ (user_key, nkey) ↦(UKVS) o)%I
             with "[- $Hkvs_static $Hlock $HPC $Hcgp $Hcra $Hmie $Hheld $Hca0 $Hca1
                     $Hcs0 $Hcs1 $Hct0 $Hctp $Hct1 $Hct2 $Ha_user_key]"); try done.
    iSplitL "Huser Hk".
    - (* the critical section *)
      iIntros "(Hphys & Hlog & Husers)".
      iDestruct (kvs_read_ghost user_key nkey o His_uint16_nkey
                  with "[$Hphys $Hlog $Huser $Hk]") as (pkvs) "[HPKVS Hclose]".
      iModIntro. iExists pkvs. iFrame "HPKVS".
      iIntros (r Hout) "HPKVS".
      iDestruct ("Hclose" $! r Hout with "HPKVS") as "(%Hr & Hphys & Hlog & Huser & Hk)".
      iModIntro. iFrame. done.
    - iNext. iIntros (r) "((%Hr & Huser & Hk) & HPC & Hcgp & Hcra & Hmie & Hheld & Hca0 & Hca1
                         & Hcs0 & Hcs1 & Hct0 & Hctp & Hct1 & Hct2 & Ha_user_key)".
      subst r.
      iApply "Hpost". iFrame.
  Qed.

  (*** KVS READ: Ill-formed inputs *)

  Lemma KVS_read_spec_not_uint16_map_key_pre
    (pc_b pc_e pc_a : Addr)
    (wret : LWord)
    (wca1 : LWord)
    (mie : InterruptStatus)
    :

    SubBounds pc_b pc_e pc_a (pc_a ^+ length kvs_read_instrs) ->
    ¬ word_is_uint16 wca1.(lw) ->

    jalr_target_ok cnull cra wret.(lw) = true ->
    th ≠ CtxSwitch ->
    route_pre th mie ->

    (
      (* initial register file *)
      PC ↦ₚ[th] Cap RX Global pc_b pc_e pc_a ∗
      cra ↦ᵣ[th] wret ∗
      MIE ↦ₜ[th] mie ∗
      held (th := th) mie ∗
      ca0 ↦ᵣ[th] - ∗
      ca1 ↦ᵣ[th] wca1 ∗ (* Key to read *)
      ct1 ↦ᵣ[th] - ∗ (* scratch *)

      (* initial memory layout *)
      codefrag_pers pc_a kvs_read_instrs ∗

      ( ▷ (PC ↦ₚ[th] lupdatePcPerm wret ∗
         cra ↦ᵣ[th] - ∗
         MIE ↦ₜ[th] default mie (jalr_target_mie wret.(lw)) ∗
         held (th := th) (default mie (jalr_target_mie wret.(lw))) ∗
         ca0 ↦ᵣ[th] WInt ASM_FALSE ∗ (* ERROR: map key is not a unint16  *)
         ca1 ↦ᵣ[th] WInt 0 ∗ (* Dummy value *)
         ct1 ↦ᵣ[th] - ∗ (* scratch *)
         codefrag_pers pc_a kvs_read_instrs
         -∗ safe[th]
        ) )
      ⊢ safe[th])%I.
  Proof.
    pose proof KVS_cgp_disjoint_from_shadow as Hcgp_shadow.
    iIntros (HsubBounds Hnkey_is_uint16 Htgt Hth Hroute)
      "(HPC & Hcra & Hmie & Hheld & [%wca0 Hca0] & Hca1 & Hct1 & #Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous ; clear H0.

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)
    iEval (rewrite /kvs_read_instrs /assembled_kvs_read) in "Hcode_main".
    iEval (rewrite -/(kvs_getFullKey kvs_read_getFullKey_off ctp ca0 ca1) -/(kvs_search ca0 ctp ct1 ct2)
      -/(kvs_check_uint16 ca1 ct1)) in "Hcode_main".
    iEval (cbn [fmap list_fmap]) in "Hcode_main".
    iEval (cbn [concat]) in "Hcode_main".

    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcode_main" as hcode.
    iApply (KVS_check_uint16_spec_not_uint16 with "[- $HPC $Hca1 $Hct1 $Hcode]"); eauto;iNext.
    iIntros "(HPC & Hca1 & _ & Hct1)".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    focus_block 1 "Hcode_main" as a_check_uint Ha_check_uint "Hcode" "Hcont". iHide "Hcode_main" as hcode.
    (* jnez (".read_not_uint16")%asm ct1; *)
    iInstr "Hcode".
    (* mov ca0 ASM_FALSE; *)
    iInstr "Hcode".
    (* mov ca1 0; *)
    iInstr "Hcode".
    (* Jalr cnull cra *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    iApply "Hpost"; iFrame "∗ Hcode_main".
  Qed.

  Lemma KVS_read_spec_not_uint16_map_key
    (wret : LWord)
    (wca1 : LWord)
    (F : coPset)
    (mie : InterruptStatus)
    :

    ¬ word_is_uint16 wca1.(lw) ->

    jalr_target_ok cnull cra wret.(lw) = true ->
    th ≠ CtxSwitch ->
    route_pre th mie ->

    ( kvs_static ∗
      na_own (tpool th) F ∗

      (* initial register file *)
      PC ↦ₚ[th] Cap RX Global KVS_pcc_b KVS_pcc_e kvs_read_pcc_addr ∗
      cra ↦ᵣ[th] wret ∗
      MIE ↦ₜ[th] mie ∗
      held (th := th) mie ∗
      ca0 ↦ᵣ[th] - ∗
      ca1 ↦ᵣ[th] wca1 ∗ (* Key to read *)
      ct1 ↦ᵣ[th] - ∗ (* scratch *)

      ( ▷ (na_own (tpool th) F ∗
         PC ↦ₚ[th] lupdatePcPerm wret ∗
         cra ↦ᵣ[th] - ∗
         MIE ↦ₜ[th] default mie (jalr_target_mie wret.(lw)) ∗
         held (th := th) (default mie (jalr_target_mie wret.(lw))) ∗
         ca0 ↦ᵣ[th] WInt ASM_FALSE ∗ (* ERROR: map key is not a unint16  *)
         ca1 ↦ᵣ[th] WInt 0 ∗ (* Dummy value *)
         ct1 ↦ᵣ[th] - (* scratch *)
         -∗ safe[th]
        ) )
      ⊢ safe[th])%I.
  Proof.
    pose proof KVS_cgp_disjoint_from_shadow as Hcgp_shadow.
    iIntros (Hnkey_is_uint16 Htgt Hth Hroute)
      "(#Hkvs_static & Hna & HPC & Hcra & Hmie & Hheld & Hca0 & Hca1 & Hct1 & Hpost)".
    iDestruct "Hkvs_static" as "(_ & #Hcode_main & _)".
    pose proof (Hcgp_continuous := KVS_size_data).
    pose proof (HKVS_pcc_b' := KVS_size_imports).
    pose proof (Hcode_continuous := KVS_size_code).
    assert (SubBounds KVS_pcc_b KVS_pcc_e KVS_pcc_b' (KVS_pcc_b' ^+ length kvs_service_instrs)) as HSubBounds.
    { solve_addr. }
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous ; clear H0.

    rewrite /kvs_service_instrs.
    focus_block_nochangePC 1 "Hcode_main" as a_read Ha_read "Hcode" "Hcont"; iHide "Hcode_main" as hcode.
    assert (a_read = kvs_read_pcc_addr) as -> by (rewrite /kvs_read_pcc_addr kvs_read_pcc_off_eq ; cbn in * ; solve_addr+Hcode_continuous HKVS_pcc_b' Ha_read).
    iApply (KVS_read_spec_not_uint16_map_key_pre with
              "[$HPC $Hcra $Hmie $Hheld $Hca0 $Hca1 $Hct1 $Hcode Hna Hpost]"); eauto.
    iNext; iIntros "(HPC & Hcra & Hmie & Hheld & Hca0 & Hca1 & Hct1 & _)".
    iApply "Hpost"; iFrame.
  Qed.

  Lemma KVS_read_spec_invalid_sealed_user_key_pre
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (wret : LWord)
    (wca0 : LWord)
    (nkey : Z) (πnkey : option AId)
    :

    is_shadow_address (pc_b ^+ UNSEALING_USER_KEY_OFFSET) = false ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length kvs_read_instrs) ->
    (pc_b + kvs_read_pcc_off)%a = Some pc_a ->
    is_uint16 nkey ->
    (is_sealed_with_o wca0.(lw) KVS_OTYPE = false \/ get_tag wca0.(lw) = false) ->

    (cgp_b + length kvs_data)%a = Some cgp_e ->

    (
      (* initial register file *)
      PC ↦ₚ[th] Cap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e cgp_b ∗
      cra ↦ᵣ[th] wret ∗
      ca0 ↦ᵣ[th] wca0 ∗ (* Sealed User Key *)
      ca1 ↦ᵣ[th] WInt nkey @@? πnkey ∗ (* Key to read *)
      ct1 ↦ᵣ[th] - ∗ (* scratch *)
      ct2 ↦ᵣ[th] - ∗ (* scratch *)
      ctp ↦ᵣ[th] - ∗ (* scratch *)

      (* initial memory layout *)
      codefrag_pers pc_a kvs_read_instrs ∗
      (pc_b ^+ UNSEALING_USER_KEY_OFFSET) ↦ₐ□ kvs_service_unsealing_key ∗

      (* The load after the failed unsealing of the user key faults *)
      ▷ ( ∀ a,
          cgp ↦ᵣ[th] - ∗
          cra ↦ᵣ[th] - ∗
          ca0 ↦ᵣ[th] - ∗
          ca1 ↦ᵣ[th] - ∗
          ct1 ↦ᵣ[th] - ∗
          ct2 ↦ᵣ[th] - ∗
          ctp ↦ᵣ[th] - -∗
          trap_safe (Cap RX Global pc_b pc_e a) ⊤
            (HO th) )

      ⊢ safe[th])%I.
  Proof.
    pose proof KVS_cgp_disjoint_from_shadow as Hcgp_shadow.
    iIntros (Hunsealing_shadow HsubBounds Hpc_a Hnkey_is_uint16 Hwca0 Hcgp_contiguous)
      "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hct1 & Hct2 & Hctp
      & #Hcode_main & #Ha_unsealing & Hfailed)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous ; clear H0.


    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)
    iEval (rewrite /kvs_read_instrs /assembled_kvs_read) in "Hcode_main".
    iEval (rewrite -/(kvs_getFullKey kvs_read_getFullKey_off ctp ca0 ca1) -/(kvs_search ca0 ctp ct1 ct2)
      -/(kvs_check_uint16 ca1 ct1)) in "Hcode_main".
    iEval (cbn [fmap list_fmap]) in "Hcode_main".
    iEval (cbn [concat]) in "Hcode_main".

    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcode_main" as hcode.
    iApply (KVS_check_uint16_spec_is_uint16 with "[- $HPC $Hca1 $Hct1 $Hcode]"); eauto;iNext.
    iIntros "(HPC & Hca1 & _ & Hct1)".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    focus_block 1 "Hcode_main" as a_check_uint Ha_check_uint "Hcode" "Hcont". iHide "Hcode_main" as hcode.
    (* jnez (".read_not_uint16")%asm ct1; *)
    iInstr "Hcode".
    (* jmp (".read_uint16_check_pass")%asm; *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    focus_block 2 "Hcode_main" as a_get_full_key Ha_get_full_key "Hcode" "Hcont"; iHide "Hcode_main" as hcode
    ; clear dependent Ha_check_uint.
    iApply (KVS_getFullKey_spec_invalid_sealed_user_key with "[- $HPC $Hctp $Hca0 $Ha_unsealing $Hcode]") ; eauto.
    { kvs_getFullKey_offset. }
    iIntros "[Hctp Hca0]".
    iApply ("Hfailed" with "[$Hcgp $Hcra $Hca0 $Hca1 $Hct1 $Hct2 $Hctp]").
  Qed.

  Lemma KVS_read_spec_invalid_sealed_user_key
    (wret : LWord)
    (wca0 : LWord)
    (nkey : Z) (πnkey : option AId)
    (F : coPset)
    :

    is_shadow_address (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET) = false ->

    is_uint16 nkey ->
    (is_sealed_with_o wca0.(lw) KVS_OTYPE = false \/ get_tag wca0.(lw) = false) ->

    ( kvs_static ∗
      na_own (tpool th) F ∗

      (* initial register file *)
      PC ↦ₚ[th] Cap RX Global KVS_pcc_b KVS_pcc_e kvs_read_pcc_addr ∗
      cgp ↦ᵣ[th] Cap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ[th] wret ∗
      ca0 ↦ᵣ[th] wca0 ∗ (* Sealed User Key *)
      ca1 ↦ᵣ[th] WInt nkey @@? πnkey ∗ (* Key to read *)
      ct1 ↦ᵣ[th] - ∗ (* scratch *)
      ct2 ↦ᵣ[th] - ∗ (* scratch *)
      ctp ↦ᵣ[th] - ∗ (* scratch *)

      (* The load after the failed unsealing of the user key faults *)
      ▷ ( ∀ a,
          na_own (tpool th) F ∗
          cgp ↦ᵣ[th] - ∗
          cra ↦ᵣ[th] - ∗
          ca0 ↦ᵣ[th] - ∗
          ca1 ↦ᵣ[th] - ∗
          ct1 ↦ᵣ[th] - ∗
          ct2 ↦ᵣ[th] - ∗
          ctp ↦ᵣ[th] - -∗
          trap_safe (Cap RX Global KVS_pcc_b KVS_pcc_e a) ⊤
            (HO th) )

      ⊢ safe[th])%I.
  Proof.
    pose proof KVS_cgp_disjoint_from_shadow as Hcgp_shadow.
    iIntros (Hunsealing_shadow Hnkey_is_uint16 Hwca0)
      "(#Hkvs_static & Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hct1 & Hct2 & Hctp & Hfailed)".

    iDestruct (kvs_static_unsealing_key with "Hkvs_static") as "#Ha_unsealing".
    iDestruct "Hkvs_static" as "(_ & #Hcode_main & _)".
    pose proof (Hcgp_continuous := KVS_size_data).
    pose proof (HKVS_pcc_b' := KVS_size_imports).
    pose proof (Hcode_continuous := KVS_size_code).
    assert (SubBounds KVS_pcc_b KVS_pcc_e KVS_pcc_b' (KVS_pcc_b' ^+ length kvs_service_instrs)) as HSubBounds.
    { solve_addr. }
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous ; clear H0.

    rewrite /kvs_service_instrs.
    focus_block_nochangePC 1 "Hcode_main" as a_read Ha_read "Hcode" "Hcont"; iHide "Hcode_main" as hcode.
    assert (a_read = kvs_read_pcc_addr) as -> by (rewrite /kvs_read_pcc_addr kvs_read_pcc_off_eq ; cbn in * ; solve_addr+Hcode_continuous HKVS_pcc_b' Ha_read).
    assert ((KVS_pcc_b + kvs_read_pcc_off)%a = Some kvs_read_pcc_addr) as Hread_off
      by (rewrite /kvs_read_pcc_addr kvs_read_pcc_off_eq; cbn in * ; solve_addr+Hcode_continuous HKVS_pcc_b').
    iApply (KVS_read_spec_invalid_sealed_user_key_pre
             with "[$HPC $Hcgp $Hcra $Hca0 $Hca1 $Hct1 $Hct2 $Hctp $Hcode $Ha_unsealing Hna Hfailed]");
      eauto.
    iNext; iIntros (a_fault) "Hregs".
    iApply ("Hfailed" with "[$Hna $Hregs]").
  Qed.


  Lemma KVS_read_spec_known_to_known
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : LWord)
    (b_stk e_stk a_stk : Addr)
    (arg_rmap : LReg) (cstk : CSTK) (F : coPset)
    (user_key : user_key_t) (nkey : map_key_t)
    (l_user_key : Locality) (user_key_addr : Addr) (w : LWord) :
    is_shadow_address (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET) = false ->
    is_shadow_address user_key_addr = false ->
    is_heap_cap w.(lw) = false ->
    is_heap_address kvs_lock_addr = false ->
    is_heap_address b_locks = false ->
    is_uint16 nkey ->
    withinBounds user_key_addr (user_key_addr ^+ 1) user_key_addr = true ->
    arg_rmap !! ca0 = Some (lword_of_word (kvs_user_seal_key l_user_key user_key_addr)) ->
    arg_rmap !! ca1 = Some (lword_of_word (WInt nkey)) ->
    kvs_static ∗
    kvs_lock kvs_users
    ⊢
    switcher_cc_specification_known_to_known_function false
      (user_key_addr ↦ₐ WInt user_key ∗
       user_kvs_inv user_key ∗
       (user_key, nkey) ↦(KVS) w)
      (λ wca0 wca1,
         user_key_addr ↦ₐ WInt user_key ∗
         user_kvs_inv user_key ∗
         (user_key, nkey) ↦(KVS) w ∗
         ⌜ wca0 = WInt ASM_TRUE ⌝ ∗
         ⌜ wca1 = w ⌝)
      wcgp_caller wcra_caller wcs0_caller wcs1_caller
      b_stk e_stk a_stk arg_rmap cstk kvs_read_nargs kvs_read_min_stack F
      KVS_pcc_b KVS_pcc_e KVS_cgp_b KVS_cgp_e kvs_read_pcc_off InterruptEnabled
      (Cap RO Global b_kvs_exp_tbl e_kvs_exp_tbl kvs_read_exp_tbl_addr).
  Proof.
    pose proof KVS_cgp_disjoint_from_shadow as Hcgp_shadow.
    iIntros (Hunsealing_shadow Huser_key_shadow Hw_nonheap Hlock_heap Hlocks_heap Hnkey Huser_key
      Hca0_arg Hca1_arg).
    rewrite /switcher_cc_specification_known_to_known_function.
    iIntros "(#Hkvs_static & #Hlock)" (arg_rmap' rmap')
      "(_ & %Harg_rmap' & %Hrmap' & Hna & HPC & Hcgp & Hcra & Hcsp
       & Hargs & Hrmap & Hstk & Hhwm & Hcstk & %Hroute & Hmie & Hheld
       & (Huser_key & Huser_kvs & Hkey)
       & Hpost)".
    iEval (cbn) in "HPC".
    iDestruct (stack_ints_region with "Hstk") as (stk_mem) "Hstk".

    iExtractList "Hargs" [ca0;ca1;ca2;ca3;ca4;ca5;ct0]
      as ["[Hca0 %Hwca0]";"[Hca1 %Hwca1]";"[Hca2 %Hwca2]";
          "[Hca3 %Hwca3]";"[Hca4 %Hwca4]";"[Hca5 %Hwca5]";
          "[Hct0 %Hwct0]"]
    ; iClear "Hargs".
    destruct (decide (ca0 ∈ dom_arg_rmap kvs_read_nargs)) as [_|]; last done.
    destruct (decide (ca1 ∈ dom_arg_rmap kvs_read_nargs)) as [_|]; last done.
    destruct (decide (ca2 ∈ dom_arg_rmap kvs_read_nargs)) as [|_]; first done.
    simplify_eq.

    assert (is_Some (rmap' !! ctp)) as [wctp Hwctp].
    { apply elem_of_dom. rewrite Hrmap' /dom_arg_rmap /=. set_solver+. }
    assert (is_Some (rmap' !! ct1)) as [wct1 Hwct1].
    { apply elem_of_dom. rewrite Hrmap' /dom_arg_rmap /=. set_solver+. }
    assert (is_Some (rmap' !! ct2)) as [wct2 Hwct2].
    { apply elem_of_dom. rewrite Hrmap' /dom_arg_rmap /=. set_solver+. }
    assert (is_Some (rmap' !! cnull)) as [wcnull Hwcnull].
    { apply elem_of_dom. rewrite Hrmap' /dom_arg_rmap /=. set_solver+. }
    iExtractList "Hrmap" [cs0;cs1;ctp;ct1;ct2;cnull]
      as ["[Hcs0 %Hcs0]";"[Hcs1 %Hcs1]";"[Hctp %Hctp]";
          "[Hct1 %Hct1]";"[Hct2 %Hct2]";"[Hcnull %Hcnull]"]
    ; simplify_eq.

    assert (th ≠ CtxSwitch) as Hth by (intros ->; by specialize (Hroute eq_refl)).
    iApply (KVS_read_spec with
      "[- $Hkvs_static $Hlock $Hna $HPC $Hcgp $Hcra $Hmie $Hheld
       $Hca0 $Hca1 $Hcs0 $Hcs1 $Hct0 $Hctp $Hct1 $Hct2
       $Huser_key $Huser_kvs $Hkey]"); auto.
    iNext.
    iIntros "(Hna & HPC & [%wcgp Hcgp] & [%wcra Hcra] & Hmie & Hheld
              & Hca0 & (%actual & Hca1 & %Hactual) & Hcs0 & Hcs1 & [%wct0' Hct0]
              & [%wctp Hctp] & [%wct1 Hct1] & [%wct2 Hct2]
              & Huser_key & Huser_kvs & Hkey)".
    destruct Hactual as [-> | Hcleared]; last (destruct Hcleared as [Hheap _]; congruence).
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iInsertList "Hrmap" [ctp;ct1;ct2;cnull;ca2;ca3;ca4;ca5;ct0].
    set (rmap_ret0 := delete cs1 (delete cs0 rmap')).
    set (rmap_ret1 := <[ctp := wctp]> rmap_ret0).
    set (rmap_ret2 := <[ct1 := wct1]> rmap_ret1).
    set (rmap_ret3 := <[ct2 := wct2]> rmap_ret2).
    set (rmap_ret4 := <[cnull := lword_of_word (WInt 0)]> rmap_ret3).
    set (rmap_ret5 := <[ca2 := lword_of_word (WInt 0)]> rmap_ret4).
    set (rmap_ret6 := <[ca3 := lword_of_word (WInt 0)]> rmap_ret5).
    set (rmap_ret7 := <[ca4 := lword_of_word (WInt 0)]> rmap_ret6).
    set (rmap_ret8 := <[ca5 := lword_of_word (WInt 0)]> rmap_ret7).
    set (rmap_ret := <[ct0 := wct0']> rmap_ret8).
    iEval (cbn) in "HPC".

    iApply ("Hpost" $! 0%Z (WInt ASM_TRUE) w rmap_ret stk_mem).
    iSplit.
    { iPureIntro.
      rewrite /rmap_ret /rmap_ret8 /rmap_ret7 /rmap_ret6 /rmap_ret5
        /rmap_ret4 /rmap_ret3 /rmap_ret2 /rmap_ret1 /rmap_ret0.
      repeat (rewrite dom_insert_L).
      repeat (rewrite dom_delete_L).
      rewrite Hrmap' /dom_arg_rmap /=. set_solver+. }
    iFrame.
    iFrame. iSplit; first done. done.
  Qed.

End KVS_spec_read.
