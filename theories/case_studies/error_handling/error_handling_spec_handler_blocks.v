From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import error_handling_spec_states.

(** * The blocks of the error handler of [stats]

    The stackful handler of [stats] is called with [ca0] pointing to the
    [ErrorState] of the faulting context (word 0 holds the saved PC, words
    1 to 15 the registers x1 to x15), mcause in [ca1] and mtval in [ca2].
    - Block 5 decodes the fault ([stats_handler_decode_spec]): a CHERI
      bounds violation on a register of the save area
      ([stats_repairable]) goes on to block 6 with the index of the
      register in [ct0]; any other fault to block 8.
    - Block 6 loads the saved word at that index, a capability, and checks
      it ([stats_handler_check_spec]): when its bounds are not empty and
      its base lies outside the [ErrorState] ([stats_base_outside]), it
      goes on to block 7; otherwise to block 8.
    - Block 7 stores back the capability with its address at its base
      ([stats_repair_word]), puts InstallContext in [ca0], and returns to
      [cra] ([stats_handler_fix_spec]).
    - Block 8 releases the lock, puts ForceUnwind in [ca0], and returns to
      [cra] ([stats_handler_unwind_spec]).

    The specifications are stated over plain points-to: they hold no
    invariant and no token. *)

Section Error_Handling_Handler_Blocks.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
  .

  (** The faults that the handler repairs, from mcause [c] and mtval [v]:
      a CHERI bounds violation on a register of the save area. *)
  Definition stats_repairable (c v : Z) : Prop :=
    c = MCAUSE_CHERI ∧
    mtval_code_field v = cause_code_num BoundsViolation ∧
    (TrustedStack_offset_cra <= mtval_reg_field v <= TrustedStack_offset_ca5)%Z.

  #[global] Instance stats_repairable_dec c v : Decision (stats_repairable c v).
  Proof. rewrite /stats_repairable. apply _. Qed.

  (** The repaired word: a capability with its address at its base. *)
  Definition stats_repair_word (w : LWord) : LWord :=
    match w with
    | MkLWord (WCap t p g b e _) π => MkLWord (WCap t p g b e b) π
    | _ => w
    end.

  (** The base [b] lies outside the [ErrorState] slot
      $[a16, a16 + ErrorState_size)$, as block 6 tests it. *)
  Definition stats_base_outside (a16 b : Addr) : Prop :=
    (b < a16)%Z ∨ (a16 + ErrorState_size <= b)%Z.

  #[global] Instance stats_base_outside_dec a16 b : Decision (stats_base_outside a16 b).
  Proof. rewrite /stats_base_outside. apply _. Qed.

  (** Block 5: decode the cause and the register. *)
  Lemma stats_handler_decode_spec
    (pc_b pc_e : Addr) (c v : Z) (wct0 : LWord) :
    stats_code_bounds pc_b pc_e ->
    PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_b ^+ stats_label ".Lstats_handler")%a ∗
    ca1 ↦ᵣ[th] WInt c ∗
    ca2 ↦ᵣ[th] WInt v ∗
    ct0 ↦ᵣ[th] wct0 ∗
    codefrag_pers pc_b stats_code ∗
    ▷ ( (⌜stats_repairable c v⌝ -∗
         PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_b ^+ stats_label ".Lstats_handler_check")%a ∗
         ca1 ↦ᵣ[th] WInt c ∗
         ca2 ↦ᵣ[th] WInt v ∗
         ct0 ↦ᵣ[th] WInt (mtval_reg_field v) ∗
         codefrag_pers pc_b stats_code
         -∗ safe[th]) ∧
        (⌜¬ stats_repairable c v⌝ -∗
         PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_b ^+ stats_label ".Lstats_handler_unwind")%a ∗
         ca1 ↦ᵣ[th] WInt c ∗
         ca2 ↦ᵣ[th] WInt v ∗
         ct0 ↦ᵣ[th] - ∗
         codefrag_pers pc_b stats_code
         -∗ safe[th]) )
    ⊢ safe[th].
  Proof.
    iIntros ((HsubBounds & Hpc_shadow & Hpc_nonheap))
      "(HPC & Hca1 & Hca2 & Hct0 & Hcode_stats & Hpost)".
    iDestruct (codefrag_contiguous_region_pers with "Hcode_stats") as %Hpc_contiguous;
    cbn [length map encodeInstrsW] in Hpc_contiguous.
    stats_unfold_code.
    focus_block (stats_block ".Lstats_handler") "Hcode_stats" of stats_blocks at pc_b
      as a_decode Ha_decode "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    destruct (decide (c = MCAUSE_CHERI)) as [-> | Hc].
    2: {
      assert (negb (c =? MCAUSE_CHERI)%Z = true) as Hjmp
        by (apply negb_true_iff, Z.eqb_neq; done).
      (* Jne .Lstats_handler_unwind ca1 MCAUSE_CHERI *)
      iInstr "Hcode".
      { jump_label ".Lstats_handler_unwind" of stats_asm at pc_b. }
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_stats".
      iDestruct "Hpost" as "[_ Hpost]".
      iApply ("Hpost" with "[%] [$HPC $Hca1 $Hca2 $Hcode_stats Hct0]"); last by iExists _.
      by intros (? & _). }
    (* Jne .Lstats_handler_unwind ca1 MCAUSE_CHERI *)
    iInstr "Hcode".
    (* LAnd ct0 ca2 MTVAL_CODE_MASK *)
    iInstr "Hcode".
    destruct (decide (mtval_code_field v = cause_code_num BoundsViolation)) as [Hcode | Hcode].
    2: {
      assert (negb (mtval_code_field v =? cause_code_num BoundsViolation)%Z = true) as Hjmp
        by (apply negb_true_iff, Z.eqb_neq; done).
      (* Jne .Lstats_handler_unwind ct0 (cause_code_num BoundsViolation) *)
      iInstr "Hcode".
      { jump_label ".Lstats_handler_unwind" of stats_asm at pc_b. }
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_stats".
      iDestruct "Hpost" as "[_ Hpost]".
      iApply ("Hpost" with "[%] [$HPC $Hca1 $Hca2 $Hcode_stats Hct0]"); last by iExists _.
      by intros (_ & ? & _). }
    assert (negb (mtval_code_field v =? cause_code_num BoundsViolation)%Z = false) as Hnext
      by (apply negb_false_iff, Z.eqb_eq; done).
    (* Jne .Lstats_handler_unwind ct0 (cause_code_num BoundsViolation) *)
    iInstr "Hcode".
    (* LShiftR ct0 ca2 MTVAL_REG_SHIFT *)
    iInstr "Hcode".
    (* LAnd ct0 ct0 MTVAL_REG_MASK *)
    iInstr "Hcode".
    destruct (Z.lt_dec (mtval_reg_field v) TrustedStack_offset_cra) as [Hlo | Hlo].
    { assert ((mtval_reg_field v <? TrustedStack_offset_cra)%Z = true) as Hjmp
        by (apply Z.ltb_lt; done).
      (* Jlt .Lstats_handler_unwind ct0 TrustedStack_offset_cra *)
      iInstr "Hcode".
      { jump_label ".Lstats_handler_unwind" of stats_asm at pc_b. }
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_stats".
      iDestruct "Hpost" as "[_ Hpost]".
      iApply ("Hpost" with "[%] [$HPC $Hca1 $Hca2 $Hcode_stats Hct0]"); last by iExists _.
      intros (_ & _ & Hrange). lia. }
    assert ((mtval_reg_field v <? TrustedStack_offset_cra)%Z = false) as Hnext_lo
      by (apply Z.ltb_ge; lia).
    (* Jlt .Lstats_handler_unwind ct0 TrustedStack_offset_cra *)
    iInstr "Hcode".
    destruct (Z.lt_dec TrustedStack_offset_ca5 (mtval_reg_field v)) as [Hhi | Hhi].
    { assert ((TrustedStack_offset_ca5 <? mtval_reg_field v)%Z = true) as Hjmp
        by (apply Z.ltb_lt; done).
      (* Jlt .Lstats_handler_unwind TrustedStack_offset_ca5 ct0 *)
      iInstr "Hcode".
      { jump_label ".Lstats_handler_unwind" of stats_asm at pc_b. }
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_stats".
      iDestruct "Hpost" as "[_ Hpost]".
      iApply ("Hpost" with "[%] [$HPC $Hca1 $Hca2 $Hcode_stats Hct0]"); last by iExists _.
      intros (_ & _ & Hrange). lia. }
    assert ((TrustedStack_offset_ca5 <? mtval_reg_field v)%Z = false) as Hnext_hi
      by (apply Z.ltb_ge; lia).
    (* Jlt .Lstats_handler_unwind TrustedStack_offset_ca5 ct0 *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_stats".
    iDestruct "Hpost" as "[Hpost _]".
    assert (a_decode ^+ 7 = (pc_b ^+ stats_label ".Lstats_handler_check")%a) as ->
      by (offsets_compute; solve_addr).
    iApply ("Hpost" with "[%] [$HPC $Hca1 $Hca2 $Hct0 $Hcode_stats]").
    split_and!; [done | done | lia ..].
  Qed.

  (** Block 6: load the saved word at index [n] of the [ErrorState], a
      capability, and check it. When its bounds are not empty and its base
      lies outside the [ErrorState], go on to block 7 with the loaded word
      in [ct2], its base in [ct0] and its cell in [ct1]; otherwise go on
      to block 8. The load may strip the tag of a heap capability
      ([lload_heap]). *)
  Lemma stats_handler_check_spec
    (pc_b pc_e : Addr) (g0 : Locality) (b0 e0 a16 : Addr) (ws : list LWord) (n : Z)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId) (wct1 wct2 wctp : LWord) :
    stats_code_bounds pc_b pc_e ->
    (b0 <= a16)%a ->
    (a16 + ErrorState_size <= e0)%Z ->
    disjoint_from_shadow a16 (a16 ^+ ErrorState_size) ->
    length ws = Z.to_nat ErrorState_size ->
    (TrustedStack_offset_cra <= n <= TrustedStack_offset_ca5)%Z ->
    ws !! Z.to_nat n = Some (MkLWord (Cap p g b e a) π) ->
    PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_b ^+ stats_label ".Lstats_handler_check")%a ∗
    ca0 ↦ᵣ[th] Cap RWL g0 b0 e0 a16 ∗
    ct0 ↦ᵣ[th] WInt n ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    ctp ↦ᵣ[th] wctp ∗
    [[ a16 , a16 ^+ ErrorState_size ]] ↦ₐ [[ ws ]] ∗
    codefrag_pers pc_b stats_code ∗
    ▷ ( (∀ t, ⌜(b < e)%a⌝ -∗
          ⌜stats_base_outside a16 b⌝ -∗
          ⌜lload_heap (MkLWord (Cap p g b e a) π) (MkLWord (WCap t p g b e a) π)⌝ -∗
          PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_b ^+ stats_label ".Lstats_handler_fix")%a ∗
          ca0 ↦ᵣ[th] Cap RWL g0 b0 e0 a16 ∗
          ct0 ↦ᵣ[th] WInt b ∗
          ct1 ↦ᵣ[th] Cap RWL g0 b0 e0 (a16 ^+ Z.to_nat n) ∗
          ct2 ↦ᵣ[th] MkLWord (WCap t p g b e a) π ∗
          ctp ↦ᵣ[th] - ∗
          [[ a16 , a16 ^+ ErrorState_size ]] ↦ₐ [[ ws ]] ∗
          codefrag_pers pc_b stats_code
          -∗ safe[th]) ∧
        (⌜¬ ((b < e)%a ∧ stats_base_outside a16 b)⌝ -∗
         PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_b ^+ stats_label ".Lstats_handler_unwind")%a ∗
         ca0 ↦ᵣ[th] Cap RWL g0 b0 e0 a16 ∗
         ct0 ↦ᵣ[th] - ∗
         ct1 ↦ᵣ[th] - ∗
         ct2 ↦ᵣ[th] - ∗
         ctp ↦ᵣ[th] - ∗
         [[ a16 , a16 ^+ ErrorState_size ]] ↦ₐ [[ ws ]] ∗
         codefrag_pers pc_b stats_code
         -∗ safe[th]) )
    ⊢ safe[th].
  Proof.
    iIntros ((HsubBounds & Hpc_shadow & Hpc_nonheap) Hb0_a16 Ha16_e0 Hes_shadow Hlen Hn Hws_n)
      "(HPC & Hca0 & Hct0 & Hct1 & Hct2 & Hctp & Hes & Hcode_stats & Hpost)".
    iDestruct (codefrag_contiguous_region_pers with "Hcode_stats") as %Hpc_contiguous;
    cbn [length map encodeInstrsW] in Hpc_contiguous.
    rewrite /ErrorState_size /TrustedStack_offset_cra /TrustedStack_offset_ca5
      in Ha16_e0 Hes_shadow Hlen Hn |- *.
    set (k := Z.to_nat n) in Hws_n |- *.
    assert ((a16 + n)%a = Some (a16 ^+ k)) as Ha16_k by (subst k; solve_addr).
    assert (is_shadow_address (a16 ^+ k) = false) as Hk_shadow.
    { eapply disjoint_from_shadow_not_in; first exact Hes_shadow.
      apply withinBounds_true_iff; subst k; solve_addr. }
    iEval (rewrite (region_pointsto_cells a16); last (rewrite Hlen; solve_addr)) in "Hes".
    iDestruct (big_sepL_insert_acc with "Hes") as "[Hes_k Hes]"; first exact Hws_n.
    stats_unfold_code.
    focus_block (stats_block ".Lstats_handler_check") "Hcode_stats" of stats_blocks at pc_b
      as a_check Ha_check "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Lea ct1 ca0 ct0 *)
    iInstr "Hcode".
    (* CLoad ct2 ct1 0 *)
    iInstrApply "Hcode" wp_load_preserve_or_clear_noid with "[$HPC $Hct2 $Hct1 $Hes_k]"
      as (wload) "(%Hwload & HPC & Hct2 & Hct1 & Hes_k)".
    { apply withinBounds_true_iff; subst k; solve_addr. }
    assert (∃ t, wload = MkLWord (WCap t p g b e a) π) as [t ->].
    { rewrite /lload_word /lift_word /= load_word_no_dl_dro // in Hwload.
      destruct Hwload as [-> | [_ ->] ]; by eexists. }
    assert (lload_heap (MkLWord (Cap p g b e a) π) (MkLWord (WCap t p g b e a) π))
      as Hlh by (rewrite /lload_word /lift_word /= load_word_no_dl_dro // in Hwload).
    (* The memory is unchanged: give the cell back now, for both exits *)
    iDestruct ("Hes" with "Hes_k") as "Hes".
    rewrite list_insert_id //.
    iEval (rewrite -(region_pointsto_cells a16 (a16 ^+ 16) ws); [|rewrite Hlen; solve_addr])
      in "Hes".
    (* GetLen ct0 ct2 *)
    iInstr "Hcode".
    destruct (decide (b < e)%a) as [Hbe | Hbe].
    2: {
      assert ((e - b <=? 0)%Z = true) as Hjmp by (apply Z.leb_le; solve_addr).
      (* Jle .Lstats_handler_unwind ct0 0 *)
      iInstr "Hcode".
      { jump_label ".Lstats_handler_unwind" of stats_asm at pc_b. }
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_stats".
      iDestruct "Hpost" as "[_ Hpost]".
      iApply ("Hpost" with "[%] [$HPC $Hca0 $Hcode_stats Hct0 Hct1 Hct2 Hctp Hes]");
        first by intros [? _].
      iSplitL "Hct0"; first by iExists _.
      iSplitL "Hct1"; first by iExists _.
      iSplitL "Hct2"; first by iExists _.
      iSplitL "Hctp"; first by iExists _.
      iFrame. }
    assert ((e - b <=? 0)%Z = false) as Hnext by (apply Z.leb_gt; solve_addr).
    (* Jle .Lstats_handler_unwind ct0 0 *)
    iInstr "Hcode".
    (* GetB ct0 ct2 *)
    iInstr "Hcode".
    (* GetA ctp ca0 *)
    iInstr "Hcode".
    destruct (Z.lt_dec b a16) as [Hlo | Hlo].
    { (* Below the slot: fix *)
      assert ((b <? a16)%Z = true) as Hjmp by (apply Z.ltb_lt; done).
      (* Jlt .Lstats_handler_fix ct0 ctp *)
      iInstr "Hcode".
      assert (a_check ^+ 9 = (pc_b ^+ stats_label ".Lstats_handler_fix")%a) as ->
        by (offsets_compute; solve_addr).
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_stats".
      iDestruct "Hpost" as "[Hpost _]".
      iApply ("Hpost" $! t with "[%] [%] [%] [$HPC $Hca0 $Hct0 $Hct1 $Hct2 $Hcode_stats Hctp Hes]");
        [done | by left | done |].
      iSplitL "Hctp"; first by iExists _.
      iFrame. }
    assert ((b <? a16)%Z = false) as Hnext_lo by (apply Z.ltb_ge; lia).
    (* Jlt .Lstats_handler_fix ct0 ctp *)
    iInstr "Hcode".
    (* Add ctp ctp 16 *)
    iInstr "Hcode".
    destruct (Z.lt_dec b (a16 + 16)%Z) as [Hin | Hhi].
    { (* In the slot: unwind *)
      assert ((b <? a16 + 16)%Z = true) as Hjmp by (apply Z.ltb_lt; done).
      (* Jlt .Lstats_handler_unwind ct0 ctp *)
      iInstr "Hcode".
      { jump_label ".Lstats_handler_unwind" of stats_asm at pc_b. }
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_stats".
      iDestruct "Hpost" as "[_ Hpost]".
      iApply ("Hpost" with "[%] [$HPC $Hca0 $Hcode_stats Hct0 Hct1 Hct2 Hctp Hes]").
      { rewrite /stats_base_outside /ErrorState_size. intros [_ [? | ?] ]; lia. }
      iSplitL "Hct0"; first by iExists _.
      iSplitL "Hct1"; first by iExists _.
      iSplitL "Hct2"; first by iExists _.
      iSplitL "Hctp"; first by iExists _.
      iFrame. }
    assert ((b <? a16 + 16)%Z = false) as Hnext_hi by (apply Z.ltb_ge; lia).
    (* Jlt .Lstats_handler_unwind ct0 ctp *)
    iInstr "Hcode".
    (* Above the slot: fall through to the fix *)
    assert (a_check ^+ 9 = (pc_b ^+ stats_label ".Lstats_handler_fix")%a) as ->
      by (offsets_compute; solve_addr).
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_stats".
    iDestruct "Hpost" as "[Hpost _]".
    iApply ("Hpost" $! t with "[%] [%] [%] [$HPC $Hca0 $Hct0 $Hct1 $Hct2 $Hcode_stats Hctp Hes]");
      [done | rewrite /stats_base_outside /ErrorState_size; right; lia | done |].
    iSplitL "Hctp"; first by iExists _.
    iFrame.
  Qed.

  (** Block 7: store the capability in [ct2] back at the cell in [ct1],
      with its address at its base [b], in [ct0], and return
      InstallContext. *)
  Lemma stats_handler_fix_spec
    (pc_b pc_e : Addr) (g0 : Locality) (b0 e0 a16 : Addr) (ws : list LWord) (n : Z)
    (t : bool) (p : Perm) (g : Locality) (b e a : Addr) (π : option AId) (wcra : LWord) :
    stats_code_bounds pc_b pc_e ->
    (b0 <= a16)%a ->
    (a16 + ErrorState_size <= e0)%Z ->
    disjoint_from_shadow a16 (a16 ^+ ErrorState_size) ->
    length ws = Z.to_nat ErrorState_size ->
    (TrustedStack_offset_cra <= n <= TrustedStack_offset_ca5)%Z ->
    jalr_target_ok cnull cra wcra.(lw) = true ->
    PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_b ^+ stats_label ".Lstats_handler_fix")%a ∗
    ca0 ↦ᵣ[th] Cap RWL g0 b0 e0 a16 ∗
    ct0 ↦ᵣ[th] WInt b ∗
    ct1 ↦ᵣ[th] Cap RWL g0 b0 e0 (a16 ^+ Z.to_nat n) ∗
    ct2 ↦ᵣ[th] MkLWord (WCap t p g b e a) π ∗
    cra ↦ᵣ[th] wcra ∗
    [[ a16 , a16 ^+ ErrorState_size ]] ↦ₐ [[ ws ]] ∗
    codefrag_pers pc_b stats_code ∗
    ▷ (PC ↦ₚ[th] lupdatePcPerm wcra ∗
       ca0 ↦ᵣ[th] WInt InstallContext ∗
       ct0 ↦ᵣ[th] - ∗
       ct1 ↦ᵣ[th] - ∗
       ct2 ↦ᵣ[th] - ∗
       cra ↦ᵣ[th] wcra ∗
       [[ a16 , a16 ^+ ErrorState_size ]] ↦ₐ
         [[ <[Z.to_nat n := stats_repair_word (MkLWord (WCap t p g b e a) π)]> ws ]] ∗
       codefrag_pers pc_b stats_code
       -∗ safe[th])
    ⊢ safe[th].
  Proof.
    iIntros ((HsubBounds & Hpc_shadow & Hpc_nonheap) Hb0_a16 Ha16_e0 Hes_shadow Hlen Hn Htgt)
      "(HPC & Hca0 & Hct0 & Hct1 & Hct2 & Hcra & Hes & Hcode_stats & Hpost)".
    iDestruct (codefrag_contiguous_region_pers with "Hcode_stats") as %Hpc_contiguous;
    cbn [length map encodeInstrsW] in Hpc_contiguous.
    rewrite /ErrorState_size /TrustedStack_offset_cra /TrustedStack_offset_ca5
      in Ha16_e0 Hes_shadow Hlen Hn |- *.
    set (k := Z.to_nat n).
    assert (is_shadow_address (a16 ^+ k) = false) as Hk_shadow.
    { eapply disjoint_from_shadow_not_in; first exact Hes_shadow.
      apply withinBounds_true_iff; subst k; solve_addr. }
    destruct (lookup_lt_is_Some_2 ws k) as [wk Hws_k]; first (rewrite Hlen; subst k; lia).
    iEval (rewrite (region_pointsto_cells a16); last (rewrite Hlen; solve_addr)) in "Hes".
    iDestruct (big_sepL_insert_acc with "Hes") as "[Hes_k Hes]"; first exact Hws_k.
    stats_unfold_code.
    focus_block (stats_block ".Lstats_handler_fix") "Hcode_stats" of stats_blocks at pc_b
      as a_fix Ha_fix "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* SetA ct2 ct2 ct0 *)
    iInstr "Hcode".
    (* Store ct1 ct2 0 *)
    iInstr "Hcode".
    { apply withinBounds_true_iff; subst k; solve_addr. }
    rewrite lstore_word_isWL //.
    (* Mov ca0 InstallContext *)
    iInstr "Hcode".
    (* Jalr cnull cra *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_stats".
    iDestruct ("Hes" with "Hes_k") as "Hes".
    iApply ("Hpost" with "[$HPC $Hca0 $Hcra $Hcode_stats Hct0 Hct1 Hct2 Hes]").
    iSplitL "Hct0"; first by iExists _.
    iSplitL "Hct1"; first by iExists _.
    iSplitL "Hct2"; first by iExists _.
    rewrite (region_pointsto_cells a16); last (rewrite length_insert Hlen; solve_addr).
    iFrame.
  Qed.

  (** Block 8: release the lock, and return ForceUnwind. *)
  Lemma stats_handler_unwind_spec
    (pc_b pc_e cgp_b cgp_e : Addr)
    (wlock wca0 wcra : LWord) :
    stats_code_bounds pc_b pc_e ->
    (cgp_b < cgp_e)%a ->
    is_shadow_address cgp_b = false ->
    jalr_target_ok cnull cra wcra.(lw) = true ->
    PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_b ^+ stats_label ".Lstats_handler_unwind")%a ∗
    cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e cgp_b ∗
    ca0 ↦ᵣ[th] wca0 ∗
    cra ↦ᵣ[th] wcra ∗
    cgp_b ↦ₐ wlock ∗
    codefrag_pers pc_b stats_code ∗
    ▷ (PC ↦ₚ[th] lupdatePcPerm wcra ∗
        cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e cgp_b ∗
        ca0 ↦ᵣ[th] WInt ForceUnwind ∗
        cra ↦ᵣ[th] wcra ∗
        cgp_b ↦ₐ WInt 0 ∗
        codefrag_pers pc_b stats_code
        -∗ safe[th])
    ⊢ safe[th].
  Proof.
    iIntros ((HsubBounds & Hpc_shadow & Hpc_nonheap) Hcgp_bounds Hcgp_shadow Htgt)
      "(HPC & Hcgp & Hca0 & Hcra & Hlock & Hcode_stats & Hpost)".
    iDestruct (codefrag_contiguous_region_pers with "Hcode_stats") as %Hpc_contiguous;
    cbn [length map encodeInstrsW] in Hpc_contiguous.
    stats_unfold_code.
    focus_block (stats_block ".Lstats_handler_unwind") "Hcode_stats" of stats_blocks at pc_b
      as a_unwind Ha_unwind "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Store cgp 0 0 *)
    iInstr "Hcode".
    { apply withinBounds_true_iff; solve_addr. }
    (* Mov ca0 ForceUnwind *)
    iInstr "Hcode".
    (* Jalr cnull cra *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_stats".
    iApply "Hpost"; iFrame "∗ Hcode_stats".
  Qed.

End Error_Handling_Handler_Blocks.
