From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import switcher_call_states.

(** * Call routine: spill of the callee-save registers

    [.Lswitch_entry_first_spill] spills the callee-save registers in the
    spill area below the cursor of the caller's stack: the first store goes
    to the cell furthest from the cursor, then the cursor moves down. When
    the first store fits, the stack is long enough for the others; a cursor
    above the top of the stack can still make a later store fault. The
    block falls through to [.Lswitcher_trusted_stack_push]. *)

Section Switch_Entry_First_Spill.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** The stack is not a shadow-table address. *)
  #[local] Ltac stk_not_shadow H :=
    eapply disjoint_from_shadow_not_in;
    [exact (disjoint_from_mmio_shadow _ _ H) | rewrite /withinBounds; solve_addr].

  (** Close the fault of a store of the spill after [k] stores, in the
      context of [switch_entry_first_spill_above_spec]: the faulting PC is
      not resumed. *)
  #[local] Ltac spill_fault_trap k :=
    switcher_merge_pc;
    lazymatch goal with
    | |- context [ environments.Esnoc _ _
                     (PC ↦ₚ (WCap _ _ _ _ _ (a_switcher_call ^+ ?o)%a) @@? _)%I ] =>
      iSpecialize ("Hfailed" $! k o with "[] []");
      [ iPureIntro; split; [solve_addr | lia]
      | iPureIntro; apply trap_no_resume_switcher_pc; by vm_compute
      | iTrap with "Hfailed" ]
    end.

  (** From [.Lswitch_entry_first_spill]: spill the callee-save registers in
      the spill area, below the cursor [a_stk], the furthest cell first,
      then move the cursor down. The cursor is not above the top of the
      stack: only the first store can fault, when the spill does not fit,
      and nothing is written. *)
  Lemma switch_entry_first_spill_spec
    (b_stk e_stk a_stk : Addr) (wcs0 wcs1 wcra wcgp : LWord) (stk_mem : list LWord) :
    disjoint_from_mmio b_stk e_stk ->
    stk_cursor_ok b_stk e_stk a_stk ->

    PC ↦ₚ switcher_label_pc ".Lswitch_entry_first_spill" ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    cra ↦ᵣ wcra ∗
    cgp ↦ᵣ wcgp ∗
    csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
    [[ stk_free_b b_stk a_stk , stk_free_e e_stk a_stk ]] ↦ₐ [[ stk_mem ]] ∗
    switcher_code ∗
    ( ▷ ( PC ↦ₚ switcher_label_pc ".Lswitcher_trusted_stack_push" ∗
          cs0 ↦ᵣ wcs0 ∗
          cs1 ↦ᵣ wcs1 ∗
          cra ↦ᵣ wcra ∗
          cgp ↦ᵣ wcgp ∗
          csp ↦ᵣ WCap true RWL Local b_stk e_stk (stk_saved_a a_stk) ∗
          switcher_stk_cells (stk_spill_a a_stk) wcs0 wcs1 wcgp wcra ∗
          [[ stk_callee_b b_stk a_stk , stk_callee_e e_stk a_stk ]] ↦ₐ
            [[ stk_mem_callee stk_mem ]] ∗
          ⌜ switcher_stk_bounds b_stk e_stk a_stk ⌝ -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) ∧
      ( ⌜ ¬ stk_spill_fits b_stk e_stk a_stk ⌝ -∗
        cs0 ↦ᵣ wcs0 ∗
        cs1 ↦ᵣ wcs1 ∗
        cra ↦ᵣ wcra ∗
        cgp ↦ᵣ wcgp ∗
        csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
        [[ stk_free_b b_stk a_stk , stk_free_e e_stk a_stk ]] ↦ₐ [[ stk_mem ]] -∗
        trap_safe (switcher_label_pc ".Lswitch_entry_first_spill") ⊤
          (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hstk_mmio Hcursor)
      "(HPC & Hcs0 & Hcs1 & Hcra & Hcgp & Hcsp & Hstk & #Hswitcher & Hpost)".
    switcher_open_label ".Lswitch_entry_first_spill" "Hswitcher" as "Hcode".
    (* The first store faults: nothing is written *)
    destruct (decide (b_stk + SpillSlot_size <= a_stk)%Z) as [Hfits | Hnfits]; cycle 1.
    { iDestruct "Hpost" as "[_ Hfailed]".
      iSpecialize ("Hfailed" $! Hnfits).
      revert Hnfits Hcursor; stk_unfold; intros Hnfits Hcursor.
      destruct (a_stk + (SpillSlot_cs0 - SpillSlot_size))%a as [a_stk4|] eqn:Ha_stk4.
      - (* Store csp cs0 (SpillSlot_cs0 - SpillSlot_size) *)
        iInstrApply "Hcode" wp_store_fail_reg_imm with "[$HPC $Hcs0 $Hcsp]"
          as "(HPC & Hcs0 & Hcsp)".
        { rewrite /withinBounds; revert Ha_stk4; stk_unfold; intros Ha_stk4; solve_addr. }
        switcher_change_pc_label ".Lswitch_entry_first_spill".
        iTrap with "Hfailed".
      - (* Store csp cs0 (SpillSlot_cs0 - SpillSlot_size) *)
        iInstrApply "Hcode" wp_store_fail_reg_overflow_imm with "[$HPC $Hcs0 $Hcsp]"
          as "(HPC & Hcs0 & Hcsp)".
        switcher_change_pc_label ".Lswitch_entry_first_spill".
        iTrap with "Hfailed". }

    switcher_hide "Hpost" as hpost.
    (* Split the spill area off the free part *)
    assert (switcher_stk_bounds b_stk e_stk a_stk) as Hbounds.
    { rewrite /switcher_stk_bounds; revert Hfits Hcursor; stk_unfold; intros Hfits Hcursor.
      split_and!; solve_addr. }
    iDestruct (big_sepL2_length with "Hstk") as %Hstklen.
    rewrite (stk_free_split _ _ _ stk_mem Hbounds (eq_sym Hstklen)).
    iDestruct "Hstk" as "[Hspill Hstk]".
    iDestruct (big_sepL2_length with "Hspill") as %Hspill_len.
    pose proof Hbounds as (Hb & Hb3 & Ha4).
    revert Hb Hb3 Ha4 Hspill_len; stk_unfold; intros Hb Hb3 Ha4 Hspill_len.
    destruct (drop (length stk_mem - 4) stk_mem) as [|w0 [|w1 [|w2 [|w3 [|w4 ws] ] ] ] ];
      try (exfalso; rewrite finz_seq_between_length /finz.dist /= in Hspill_len; solve_addr).
    iRegionSplit "Hspill" as "(Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3)".

    (* Store csp cs0 (SpillSlot_cs0 - SpillSlot_size) *)
    iInstr "Hcode".
    { stk_not_shadow Hstk_mmio. }
    { rewrite /withinBounds. solve_addr. }
    (* Lea csp csp (- SpillSlot_size) *)
    iInstr "Hcode".
    assert (((a_stk ^+ - (4)) + 1)%a = Some ((a_stk ^+ - (4)) ^+ 1)%a) as Ha1 by solve_addr.
    assert (((a_stk ^+ - (4)) + 2)%a = Some ((a_stk ^+ - (4)) ^+ 2)%a) as Ha2 by solve_addr.
    assert (((a_stk ^+ - (4)) + 3)%a = Some ((a_stk ^+ - (4)) ^+ 3)%a) as Ha3 by solve_addr.
    (* Store csp cs1 SpillSlot_cs1 *)
    iInstr "Hcode".
    { stk_not_shadow Hstk_mmio. }
    { rewrite /withinBounds. solve_addr. }
    (* Store csp cgp SpillSlot_cgp *)
    iInstr "Hcode".
    { stk_not_shadow Hstk_mmio. }
    { rewrite /withinBounds. solve_addr. }
    (* Store csp cra SpillSlot_pcc *)
    iInstr "Hcode".
    { stk_not_shadow Hstk_mmio. }
    { rewrite /withinBounds. solve_addr. }
    repeat rewrite lstore_word_isWL; try reflexivity.
    switcher_change_pc_label ".Lswitcher_trusted_stack_push".
    subst hpost.
    iDestruct "Hpost" as "[Hpost _]".
    iApply "Hpost".
    iFrame "HPC Hcs0 Hcs1 Hcra Hcgp Hcsp Ha_stk Ha_stk1 Ha_stk2 Ha_stk3 Hstk".
    iPureIntro; exact Hbounds.
  Qed.

  (** From [.Lswitch_entry_first_spill]: the first store faults when the
      furthest cell of the spill is not within the bounds of the stack
      pointer: nothing is written. *)
  Lemma switch_entry_first_spill_fail_spec (wcsp wcs0 : LWord) :
    switcher_csp_checked wcsp ->
    (∀ b e a a4, wcsp.(lw) = WCap true RWL Local b e a ->
                 (a + (SpillSlot_cs0 - SpillSlot_size))%a = Some a4 ->
                 (a4 < b)%a ∨ (e <= a4)%a) ->

    PC ↦ₚ switcher_label_pc ".Lswitch_entry_first_spill" ∗
    csp ↦ᵣ wcsp ∗
    cs0 ↦ᵣ wcs0 ∗
    switcher_code ∗
    ( csp ↦ᵣ wcsp ∗
      cs0 ↦ᵣ wcs0 -∗
      trap_safe (switcher_label_pc ".Lswitch_entry_first_spill") ⊤
        (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hchecked Hnot_stk) "(HPC & Hcsp & Hcs0 & #Hswitcher & Hfailed)".
    switcher_open_label ".Lswitch_entry_first_spill" "Hswitcher" as "Hcode" a_spill Ha_spill.
    (* The faults are at the start of the block. The label would be unfolded by
       the simplifications of [iInstr_fail] *)
    rewrite -Ha_spill.
    clear Ha_spill.
    destruct (is_cap wcsp.(lw)) eqn:Hcap; cycle 1.
    { (* Store csp cs0 (SpillSlot_cs0 - SpillSlot_size) *)
      iInstrApply "Hcode" wp_store_fail_reg_not_cap_lword_imm with "[$HPC $Hcs0 $Hcsp]"
        as "(HPC & Hcs0 & Hcsp)".
      iTrap with "Hfailed". }
    destruct wcsp as [ [| [t p g b e a|] | | ] π]; cbn in Hcap; try discriminate.
    destruct t.
    2: { (* Store csp cs0 (SpillSlot_cs0 - SpillSlot_size) *)
         iInstr_fail "Hcode".
         iTrap with "Hfailed". }
    destruct (switcher_csp_checked_cap _ _ _ _ _ _ Hchecked) as [-> ->].
    destruct (a + (SpillSlot_cs0 - SpillSlot_size))%a as [a4|] eqn:Ha4.
    - specialize (Hnot_stk b e a a4 eq_refl Ha4).
      (* Store csp cs0 (SpillSlot_cs0 - SpillSlot_size) *)
      iInstrApply "Hcode" wp_store_fail_reg_imm with "[$HPC $Hcs0 $Hcsp]"
        as "(HPC & Hcs0 & Hcsp)".
      { destruct Hnot_stk; rewrite /withinBounds; solve_addr. }
      iTrap with "Hfailed".
    - (* Store csp cs0 (SpillSlot_cs0 - SpillSlot_size) *)
      iInstrApply "Hcode" wp_store_fail_reg_overflow_imm with "[$HPC $Hcs0 $Hcsp]"
        as "(HPC & Hcs0 & Hcsp)".
      iTrap with "Hfailed".
  Qed.

  (** From [.Lswitch_entry_first_spill]: a later store faults when the
      cursor [a] is above the top [e] of the stack and the furthest cell of
      the spill is within its bounds: the cells of the spill area below [e],
      the first [k] ones, are written, the cursor is moved down, and the
      store of the cell at [e] faults, at a PC that is not resumed. *)
  Lemma switch_entry_first_spill_above_spec (b e a : Addr) (ws : list LWord)
    (wcs0 wcs1 wcgp wcra : LWord) :
    disjoint_from_mmio b e ->
    (e < a)%a ->
    (b <= stk_spill_a a < e)%a ->
    stk_spill_ok a ->

    PC ↦ₚ switcher_label_pc ".Lswitch_entry_first_spill" ∗
    csp ↦ᵣ WCap true RWL Local b e a ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    cgp ↦ᵣ wcgp ∗
    cra ↦ᵣ wcra ∗
    [[ stk_spill_a a , e ]] ↦ₐ [[ ws ]] ∗
    switcher_code ∗
    ( ∀ (k : nat) (off : Z),
      ⌜ (stk_spill_a a + k)%a = Some e ∧ (1 <= k <= 3)%nat ⌝ -∗
      ⌜ trap_no_resume (switcher_pc off) ⌝ -∗
      csp ↦ᵣ WCap true RWL Local b e (stk_saved_a a) ∗
      cs0 ↦ᵣ wcs0 ∗
      cs1 ↦ᵣ wcs1 ∗
      cgp ↦ᵣ wcgp ∗
      cra ↦ᵣ wcra ∗
      [[ stk_spill_a a , e ]] ↦ₐ [[ take k [wcs0; wcs1; wcgp] ]] -∗
      trap_safe (switcher_pc off) ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hstk_mmio Hea Hspill Ha4)
      "(HPC & Hcsp & Hcs0 & Hcs1 & Hcgp & Hcra & Hstk & #Hswitcher & Hfailed)".
    revert Hspill Ha4; stk_unfold; intros Hspill Ha4.
    switcher_open_label ".Lswitch_entry_first_spill" "Hswitcher" as "Hcode".
    iDestruct (big_sepL2_length with "Hstk") as %Hlen.
    rewrite finz_seq_between_length /finz.dist in Hlen.
    destruct ws as [|w0 ws]; first (exfalso; cbn in Hlen; solve_addr).
    iDestruct (region_pointsto_cons _ ((a ^+ - (4)) ^+ 1)%a with "Hstk") as "[Ha0 Hstk]";
      [solve_addr..|].
    (* Store csp cs0 (SpillSlot_cs0 - SpillSlot_size) *)
    iInstr "Hcode".
    { stk_not_shadow Hstk_mmio. }
    { rewrite /withinBounds. solve_addr. }
    rewrite lstore_word_isWL; last reflexivity.
    (* Lea csp csp (- SpillSlot_size) *)
    iInstr "Hcode".
    destruct (decide (e = (a ^+ - (4)) ^+ 1)%a) as [He1 | He1].
    { assert (((a ^+ - (4)) + 1)%a = Some e) as Ha_e by solve_addr.
      (* Store csp cs1 SpillSlot_cs1 *)
      iInstrApply "Hcode" wp_store_fail_reg_imm with "[$HPC $Hcs1 $Hcsp]"
        as "(HPC & Hcs1 & Hcsp)".
      { rewrite /withinBounds; solve_addr. }
      destruct ws; last (exfalso; cbn in Hlen; solve_addr).
      iDestruct (region_pointsto_cons with "[$Ha0 $Hstk]") as "Hstk"; [solve_addr..|].
      spill_fault_trap 1%nat. }
    destruct ws as [|w1 ws]; first (exfalso; cbn in Hlen; solve_addr).
    iDestruct (region_pointsto_cons _ ((a ^+ - (4)) ^+ 2)%a with "Hstk") as "[Ha1 Hstk]";
      [solve_addr..|].
    assert (((a ^+ - (4)) + 1)%a = Some ((a ^+ - (4)) ^+ 1)%a) as Ha1 by solve_addr.
    (* Store csp cs1 SpillSlot_cs1 *)
    iInstr "Hcode".
    { stk_not_shadow Hstk_mmio. }
    { rewrite /withinBounds. solve_addr. }
    rewrite lstore_word_isWL; last reflexivity.
    destruct (decide (e = (a ^+ - (4)) ^+ 2)%a) as [He2 | He2].
    { assert (((a ^+ - (4)) + 2)%a = Some e) as Ha_e by solve_addr.
      (* Store csp cgp SpillSlot_cgp *)
      iInstrApply "Hcode" wp_store_fail_reg_imm with "[$HPC $Hcgp $Hcsp]"
        as "(HPC & Hcgp & Hcsp)".
      { rewrite /withinBounds; solve_addr. }
      destruct ws; last (exfalso; cbn in Hlen; solve_addr).
      iDestruct (region_pointsto_cons with "[$Ha1 $Hstk]") as "Hstk"; [solve_addr..|].
      iDestruct (region_pointsto_cons with "[$Ha0 $Hstk]") as "Hstk"; [solve_addr..|].
      spill_fault_trap 2%nat. }
    destruct ws as [|w2 ws]; first (exfalso; cbn in Hlen; solve_addr).
    destruct ws; last (exfalso; cbn in Hlen; solve_addr).
    iDestruct (region_pointsto_cons _ ((a ^+ - (4)) ^+ 3)%a with "Hstk") as "[Ha2 Hstk]";
      [solve_addr..|].
    assert (((a ^+ - (4)) + 2)%a = Some ((a ^+ - (4)) ^+ 2)%a) as Ha2 by solve_addr.
    assert (((a ^+ - (4)) + 3)%a = Some e) as Ha_e by solve_addr.
    (* Store csp cgp SpillSlot_cgp *)
    iInstr "Hcode".
    { stk_not_shadow Hstk_mmio. }
    { rewrite /withinBounds. solve_addr. }
    rewrite lstore_word_isWL; last reflexivity.
    (* Store csp cra SpillSlot_pcc *)
    iInstrApply "Hcode" wp_store_fail_reg_imm with "[$HPC $Hcra $Hcsp]"
      as "(HPC & Hcra & Hcsp)".
    { rewrite /withinBounds; solve_addr. }
    iDestruct (region_pointsto_cons with "[$Ha2 $Hstk]") as "Hstk"; [solve_addr..|].
    iDestruct (region_pointsto_cons with "[$Ha1 $Hstk]") as "Hstk"; [solve_addr..|].
    iDestruct (region_pointsto_cons with "[$Ha0 $Hstk]") as "Hstk"; [solve_addr..|].
    spill_fault_trap 3%nat.
  Qed.

End Switch_Entry_First_Spill.
