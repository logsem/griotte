From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import switcher_call_states.

(** * Call routine: spill of the callee-save registers

    [.Lswitch_entry_first_spill] spills the callee-save registers in the
    spill area below the cursor of the caller's stack: the first store goes
    to the cell furthest from the cursor, then the cursor moves down. When
    the first store fits, the stack is long enough for the others; a cursor
    above the top of the stack can still make a later store fault. The
    block falls through to [.Lswitch_trusted_stack_load]. *)

Section Switch_Entry_First_Spill.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** The stack is not a shadow-table address. *)
  #[local] Ltac stk_not_shadow H :=
    eapply disjoint_from_shadow_not_in;
    [exact (disjoint_from_mmio_shadow _ _ H) | rewrite /withinBounds; solve_addr].

  (** A store of the spill to a stack cell at [x], in [[s, u)]: the logical
      MSHWM stays at its value [h] before the spill, or is lowered between
      MSHWMB and [h], to one of the cells of [[s, u)]. *)
  #[local] Lemma hwm_spill_bound_step (s u hb h h0 h1 : Z) (x : Addr) :
    (s <= x < u)%Z →
    (h0 = h ∨ (hb <= h0 < h ∧ s <= h0 < u))%Z →
    h1 = h0 ∨ h1 = hwm_after x hb h0 →
    (h1 = h ∨ (hb <= h1 < h ∧ s <= h1 < u))%Z.
  Proof.
    intros Hx Hb [-> | ->]; first done.
    destruct (hwm_after_cases x hb h0) as [-> | [-> Hx'] ]; first done.
    lia.
  Qed.

  (* TODO: move to common/switcher_preamble.v *)
  (** The cells of the free part of a caller's stack split into those of
      its spill area and those of the callee's stack. *)
  Lemma stk_free_split_cells b e a (l : list LWord) :
    switcher_stk_bounds b e a →
    length l = length (stk_free b e a) →
    stack_region (stk_free_b b a) (stk_free_e e a) l ⊣⊢
    stack_region (stk_spill_a a) (stk_spill_a a ^+ SpillSlot_size) (stk_mem_spill l) ∗
    stack_region (stk_callee_b b a) (stk_callee_e e a) (stk_mem_callee l).
  Proof.
    intros Hbounds Hl.
    pose proof Hbounds as (Hb & Hb3 & Ha4).
    rewrite /stk_free finz_seq_between_length in Hl.
    rewrite stk_spill_a_end //.
    revert Hb Hb3 Ha4 Hl; stk_unfold; intros Hb Hb3 Ha4 Hl.
    rewrite (stack_region_split b (a ^+ - (4)) a); [|solve_addr|solve_addr].
    rewrite bi.sep_comm.
    rewrite (_ : finz.dist b (a ^+ - (4)) = (length l - Z.to_nat 4)%nat);
      last (rewrite Hl /finz.dist; solve_addr).
    done.
  Qed.

  (** Close the fault of a store of the spill after [k] stores, in the
      context of [switch_entry_first_spill_above_spec]: the faulting PC is
      not resumed. *)
  #[local] Ltac spill_fault_trap k vh :=
    switcher_merge_pc;
    lazymatch goal with
    | |- context [ environments.Esnoc _ _
                     (PC ↦ₚ (WCap _ _ _ _ _ (a_switcher_call ^+ ?o)) @@? _)%I ] =>
      iSpecialize ("Hfailed" $! k o vh with "[] [] []");
      [ iPureIntro; split; [solve_addr | lia]
      | iPureIntro; apply trap_no_resume_switcher_pc; by vm_compute
      | iPureIntro;
        repeat (eapply hwm_spill_bound_step; last eassumption; first solve_addr); by left
      | iTrap with "Hfailed" ]
    end.

  (** From [.Lswitch_entry_first_spill]: spill the callee-save registers in
      the spill area, below the cursor [a_stk], the furthest cell first,
      then move the cursor down. The cursor is not above the top of the
      stack: only the first store can fault, when the spill does not fit,
      and nothing is written. *)
  Lemma switch_entry_first_spill_spec
    (b_stk e_stk a_stk : Addr) (wcs0 wcs1 wcra wcgp : LWord) (stk_mem : list LWord)
    (hb h : Z) :
    disjoint_from_mmio b_stk e_stk ->
    stk_cursor_ok b_stk e_stk a_stk ->

    PC ↦ₚ[th] switcher_label_pc ".Lswitch_entry_first_spill" ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    cra ↦ᵣ[th] wcra ∗
    cgp ↦ᵣ[th] wcgp ∗
    csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk ∗
    stack_region (stk_free_b b_stk a_stk) (stk_free_e e_stk a_stk) stk_mem ∗
    hwm_regs hb h ∗
    switcher_code ∗
    ( ▷ ( ∀ h' : Z,
          (* MSHWM is unchanged, or lowered to one of the spilled cells *)
          ⌜(h' = h ∨
            (hb <= h' < h ∧ stk_spill_a a_stk <= h' < a_stk))%Z⌝ -∗
          PC ↦ₚ[th] switcher_label_pc ".Lswitch_trusted_stack_load" ∗
          cs0 ↦ᵣ[th] wcs0 ∗
          cs1 ↦ᵣ[th] wcs1 ∗
          cra ↦ᵣ[th] wcra ∗
          cgp ↦ᵣ[th] wcgp ∗
          csp ↦ᵣ[th] Cap RWL Local b_stk e_stk (stk_saved_a a_stk) ∗
          switcher_stk_cells (stk_spill_a a_stk) wcs0 wcs1 wcgp wcra ∗
          stack_region (stk_callee_b b_stk a_stk) (stk_callee_e e_stk a_stk)
            (stk_mem_callee stk_mem) ∗
          hwm_regs hb h' ∗
          ⌜ switcher_stk_bounds b_stk e_stk a_stk ⌝ -∗
          safe[th] ) ∧
      ( ⌜ ¬ stk_spill_fits b_stk e_stk a_stk ⌝ -∗
        cs0 ↦ᵣ[th] wcs0 ∗
        cs1 ↦ᵣ[th] wcs1 ∗
        cra ↦ᵣ[th] wcra ∗
        cgp ↦ᵣ[th] wcgp ∗
        csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk ∗
        stack_region (stk_free_b b_stk a_stk) (stk_free_e e_stk a_stk) stk_mem ∗
        hwm_regs hb h -∗
        trap_safe (switcher_label_pc ".Lswitch_entry_first_spill") ⊤
          (HO th) ) )
    ⊢ safe[th].
  Proof.
    iIntros (Hstk_mmio Hcursor)
      "(HPC & Hcs0 & Hcs1 & Hcra & Hcgp & Hcsp & Hstk & Hhwm & #Hswitcher & Hpost)".
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
    rewrite (stk_free_split_cells _ _ _ stk_mem Hbounds (eq_sym Hstklen)).
    iDestruct "Hstk" as "[Hspill Hstk]".
    iDestruct (big_sepL2_length with "Hspill") as %Hspill_len.
    pose proof Hbounds as (Hb & Hb3 & Ha4).
    revert Hb Hb3 Ha4 Hspill_len; stk_unfold; intros Hb Hb3 Ha4 Hspill_len.
    destruct (drop (length stk_mem - 4) stk_mem) as [|w0 [|w1 [|w2 [|w3 [|w4 ws] ] ] ] ];
      try (exfalso; rewrite finz_seq_between_length /finz.dist /= in Hspill_len; solve_addr).
    rewrite (stack_region_cons _ ((a_stk ^+ - (4)) ^+ 1)); [|solve_addr|solve_addr].
    rewrite (stack_region_cons _ ((a_stk ^+ - (4)) ^+ 2)); [|solve_addr|solve_addr].
    rewrite (stack_region_cons _ ((a_stk ^+ - (4)) ^+ 3)); [|solve_addr|solve_addr].
    rewrite (stack_region_cons _ ((a_stk ^+ - (4)) ^+ 4)); [|solve_addr|solve_addr].
    iDestruct "Hspill" as "(Hc0 & Hc1 & Hc2 & Hc3 & _)".
    iPoseProof deref_res_none as "Hderef".

    (* Store csp cs0 (SpillSlot_cs0 - SpillSlot_size) *)
    iInstrApply "Hcode" wp_store_stack_cell_reg_imm
      with "[$HPC $Hcs0 $Hcsp $Hc0 $Hhwm $Hderef]"
      as (h1) "(%Hh1 & HPC & Hcs0 & Hcsp & Ha_stk & Hhwm & _)".
    { stk_not_shadow Hstk_mmio. }
    { rewrite /withinBounds. solve_addr. }
    (* Lea csp csp (- SpillSlot_size) *)
    iInstr "Hcode".
    assert (((a_stk ^+ - (4)) + 1)%a = Some ((a_stk ^+ - (4)) ^+ 1)) as Ha1 by solve_addr.
    assert (((a_stk ^+ - (4)) + 2)%a = Some ((a_stk ^+ - (4)) ^+ 2)) as Ha2 by solve_addr.
    assert (((a_stk ^+ - (4)) + 3)%a = Some ((a_stk ^+ - (4)) ^+ 3)) as Ha3 by solve_addr.
    (* Store csp cs1 SpillSlot_cs1 *)
    iInstrApply "Hcode" wp_store_stack_cell_reg_imm
      with "[$HPC $Hcs1 $Hcsp $Hc1 $Hhwm $Hderef]"
      as (h2) "(%Hh2 & HPC & Hcs1 & Hcsp & Ha_stk1 & Hhwm & _)".
    { stk_not_shadow Hstk_mmio. }
    { rewrite /withinBounds. solve_addr. }
    (* Store csp cgp SpillSlot_cgp *)
    iInstrApply "Hcode" wp_store_stack_cell_reg_imm
      with "[$HPC $Hcgp $Hcsp $Hc2 $Hhwm $Hderef]"
      as (h3) "(%Hh3 & HPC & Hcgp & Hcsp & Ha_stk2 & Hhwm & _)".
    { stk_not_shadow Hstk_mmio. }
    { rewrite /withinBounds. solve_addr. }
    (* Store csp cra SpillSlot_pcc *)
    iInstrApply "Hcode" wp_store_stack_cell_reg_imm
      with "[$HPC $Hcra $Hcsp $Hc3 $Hhwm $Hderef]"
      as (h4) "(%Hh4 & HPC & Hcra & Hcsp & Ha_stk3 & Hhwm & _)".
    { stk_not_shadow Hstk_mmio. }
    { rewrite /withinBounds. solve_addr. }
    switcher_change_pc_label ".Lswitch_trusted_stack_load".
    subst hpost.
    iDestruct "Hpost" as "[Hpost _]".
    iApply ("Hpost" $! h4 with "[%]").
    { eapply hwm_spill_bound_step; last exact Hh4; first solve_addr.
      eapply hwm_spill_bound_step; last exact Hh3; first solve_addr.
      eapply hwm_spill_bound_step; last exact Hh2; first solve_addr.
      eapply hwm_spill_bound_step; last exact Hh1; first solve_addr.
      by left. }
    iFrame "HPC Hcs0 Hcs1 Hcra Hcgp Hcsp Ha_stk Ha_stk1 Ha_stk2 Ha_stk3 Hstk Hhwm".
    iPureIntro; exact Hbounds.
    Unshelve. all: exact 1%Qp.
  Qed.

  (** From [.Lswitch_entry_first_spill]: the first store faults when the
      furthest cell of the spill is not within the bounds of the stack
      pointer: nothing is written. *)
  Lemma switch_entry_first_spill_fail_spec (wcsp wcs0 : LWord) :
    switcher_csp_checked wcsp ->
    (∀ b e a a4, wcsp.(lw) = Cap RWL Local b e a ->
                 (a + (SpillSlot_cs0 - SpillSlot_size))%a = Some a4 ->
                 (a4 < b)%a ∨ (e <= a4)%a) ->

    PC ↦ₚ[th] switcher_label_pc ".Lswitch_entry_first_spill" ∗
    csp ↦ᵣ[th] wcsp ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    switcher_code ∗
    ( csp ↦ᵣ[th] wcsp ∗
      cs0 ↦ᵣ[th] wcs0 -∗
      trap_safe (switcher_label_pc ".Lswitch_entry_first_spill") ⊤
        (HO th) )
    ⊢ safe[th].
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
    (wcs0 wcs1 wcgp wcra : LWord) (hb h : Z) :
    disjoint_from_mmio b e ->
    (e < a)%a ->
    stk_spill_a a ∈ₐ [b, e) ->
    stk_spill_ok a ->

    PC ↦ₚ[th] switcher_label_pc ".Lswitch_entry_first_spill" ∗
    csp ↦ᵣ[th] Cap RWL Local b e a ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    cgp ↦ᵣ[th] wcgp ∗
    cra ↦ᵣ[th] wcra ∗
    stack_region (stk_spill_a a) e ws ∗
    hwm_regs hb h ∗
    switcher_code ∗
    ( ∀ (k : nat) (off : Z) (h' : Z),
      ⌜ (stk_spill_a a + k)%a = Some e ∧ (1 <= k <= 3)%nat ⌝ -∗
      ⌜ trap_no_resume (switcher_pc off) ⌝ -∗
      (* MSHWM is unchanged, or lowered to one of the spilled cells below [e] *)
      ⌜(h' = h ∨
        (hb <= h' < h ∧ stk_spill_a a <= h' < e))%Z⌝ -∗
      csp ↦ᵣ[th] Cap RWL Local b e (stk_saved_a a) ∗
      cs0 ↦ᵣ[th] wcs0 ∗
      cs1 ↦ᵣ[th] wcs1 ∗
      cgp ↦ᵣ[th] wcgp ∗
      cra ↦ᵣ[th] wcra ∗
      [[ stk_spill_a a , e ]] ↦ₐ [[ take k [wcs0; wcs1; wcgp] ]] ∗
      hwm_regs hb h' -∗
      trap_safe (switcher_pc off) ⊤ (HO th) )
    ⊢ safe[th].
  Proof.
    iIntros (Hstk_mmio Hea Hspill Ha4)
      "(HPC & Hcsp & Hcs0 & Hcs1 & Hcgp & Hcra & Hstk & Hhwm & #Hswitcher & Hfailed)".
    revert Hspill Ha4; stk_unfold; intros Hspill Ha4.
    switcher_open_label ".Lswitch_entry_first_spill" "Hswitcher" as "Hcode".
    iPoseProof deref_res_none as "Hderef".
    iDestruct (big_sepL2_length with "Hstk") as %Hlen.
    rewrite finz_seq_between_length /finz.dist in Hlen.
    iAssert ([[ e , e ]] ↦ₐ [[ [] ]])%I as "Hnil".
    { rewrite /region_pointsto finz_seq_between_empty; last solve_addr. done. }
    destruct ws as [|w0 ws]; first (exfalso; cbn in Hlen; solve_addr).
    rewrite (stack_region_cons _ ((a ^+ - (4)) ^+ 1)); [|solve_addr|solve_addr].
    iDestruct "Hstk" as "[Hc0 Hstk]".
    (* Store csp cs0 (SpillSlot_cs0 - SpillSlot_size) *)
    iInstrApply "Hcode" wp_store_stack_cell_reg_imm
      with "[$HPC $Hcs0 $Hcsp $Hc0 $Hhwm $Hderef]"
      as (h1) "(%Hh1 & HPC & Hcs0 & Hcsp & Ha0 & Hhwm & _)".
    { stk_not_shadow Hstk_mmio. }
    { rewrite /withinBounds. solve_addr. }
    (* Lea csp csp (- SpillSlot_size) *)
    iInstr "Hcode".
    destruct (decide (e = (a ^+ - (4)) ^+ 1)%a) as [He1 | He1].
    { assert (((a ^+ - (4)) + 1)%a = Some e) as Ha_e by solve_addr.
      (* Store csp cs1 SpillSlot_cs1 *)
      iInstrApply "Hcode" wp_store_fail_reg_imm with "[$HPC $Hcs1 $Hcsp]"
        as "(HPC & Hcs1 & Hcsp)".
      { rewrite /withinBounds; solve_addr. }
      destruct ws; last (exfalso; cbn in Hlen; solve_addr).
      iDestruct (region_pointsto_cons with "[$Ha0 $Hnil]") as "Hstk'"; [solve_addr..|].
      spill_fault_trap 1%nat h1. }
    destruct ws as [|w1 ws]; first (exfalso; cbn in Hlen; solve_addr).
    rewrite (stack_region_cons _ ((a ^+ - (4)) ^+ 2)); [|solve_addr|solve_addr].
    iDestruct "Hstk" as "[Hc1 Hstk]".
    assert (((a ^+ - (4)) + 1)%a = Some ((a ^+ - (4)) ^+ 1)) as Ha1 by solve_addr.
    (* Store csp cs1 SpillSlot_cs1 *)
    iInstrApply "Hcode" wp_store_stack_cell_reg_imm
      with "[$HPC $Hcs1 $Hcsp $Hc1 $Hhwm $Hderef]"
      as (h2) "(%Hh2 & HPC & Hcs1 & Hcsp & Ha1 & Hhwm & _)".
    { stk_not_shadow Hstk_mmio. }
    { rewrite /withinBounds. solve_addr. }
    destruct (decide (e = (a ^+ - (4)) ^+ 2)%a) as [He2 | He2].
    { assert (((a ^+ - (4)) + 2)%a = Some e) as Ha_e by solve_addr.
      (* Store csp cgp SpillSlot_cgp *)
      iInstrApply "Hcode" wp_store_fail_reg_imm with "[$HPC $Hcgp $Hcsp]"
        as "(HPC & Hcgp & Hcsp)".
      { rewrite /withinBounds; solve_addr. }
      destruct ws; last (exfalso; cbn in Hlen; solve_addr).
      iDestruct (region_pointsto_cons with "[$Ha1 $Hnil]") as "Hstk'"; [solve_addr..|].
      iDestruct (region_pointsto_cons with "[$Ha0 $Hstk']") as "Hstk'"; [solve_addr..|].
      spill_fault_trap 2%nat h2. }
    destruct ws as [|w2 ws]; first (exfalso; cbn in Hlen; solve_addr).
    destruct ws; last (exfalso; cbn in Hlen; solve_addr).
    rewrite (stack_region_cons _ ((a ^+ - (4)) ^+ 3)); [|solve_addr|solve_addr].
    iDestruct "Hstk" as "[Hc2 Hstk]".
    assert (((a ^+ - (4)) + 2)%a = Some ((a ^+ - (4)) ^+ 2)) as Ha2 by solve_addr.
    assert (((a ^+ - (4)) + 3)%a = Some e) as Ha_e by solve_addr.
    (* Store csp cgp SpillSlot_cgp *)
    iInstrApply "Hcode" wp_store_stack_cell_reg_imm
      with "[$HPC $Hcgp $Hcsp $Hc2 $Hhwm $Hderef]"
      as (h3) "(%Hh3 & HPC & Hcgp & Hcsp & Ha2 & Hhwm & _)".
    { stk_not_shadow Hstk_mmio. }
    { rewrite /withinBounds. solve_addr. }
    (* Store csp cra SpillSlot_pcc *)
    iInstrApply "Hcode" wp_store_fail_reg_imm with "[$HPC $Hcra $Hcsp]"
      as "(HPC & Hcra & Hcsp)".
    { rewrite /withinBounds; solve_addr. }
    iDestruct (region_pointsto_cons with "[$Ha2 $Hnil]") as "Hstk'"; [solve_addr..|].
    iDestruct (region_pointsto_cons with "[$Ha1 $Hstk']") as "Hstk'"; [solve_addr..|].
    iDestruct (region_pointsto_cons with "[$Ha0 $Hstk']") as "Hstk'"; [solve_addr..|].
    spill_fault_trap 3%nat h3.
    Unshelve. all: exact 1%Qp.
  Qed.

End Switch_Entry_First_Spill.
