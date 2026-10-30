From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import call_stack switcher_preamble clear_stack_spec clear_registers_spec.

(** * Callback: clear the callee's frame and return to the caller

    [.Lswitch_callee_stack_zero], at the end of the block
    [switcher_after_compartment_call], clears the stack from its base to
    the cursor ([clear_stack_asm]),
    [.Lswitch_callee_dead_zeros] clears the
    registers that do not hold return values or the caller's restored state
    ([clear_registers_post_call_asm]), and [.Lswitch_just_return]
    returns to [cra]. [.Lswitch_callee_dead_zeros] is also the target of
    [.Lswitch_trusted_stack_exhausted]. *)

(* TODO: move to program_logic/stack_cells.v *)
Section stack_cells_zero.
  Context {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}.

  Lemma stack_zeroed_from_app (b b' : Addr) (v : Z) (l1 l2 : list LWord) :
    (b + length l1 = b')%Z →
    stack_zeroed_from b v (l1 ++ l2) =
    stack_zeroed_from b v l1 ++ stack_zeroed_from b' v l2.
  Proof.
    intros Hb'. rewrite /stack_zeroed_from length_app take_app.
    destruct (decide (Z.to_nat (v - b) <= length l1)%nat) as [Hle | Hgt].
    - rewrite (_ : (Z.to_nat (v - b) - length l1)%nat = 0); last lia.
      rewrite (_ : Z.to_nat (v - b') = 0); last lia.
      rewrite take_0 app_nil_r /= Nat.sub_0_r -app_assoc -replicate_add.
      do 2 f_equal. lia.
    - rewrite take_ge; last lia.
      rewrite (_ : (Z.to_nat (v - b) - length l1)%nat = Z.to_nat (v - b')); last lia.
      rewrite (_ : (length l1 - Z.to_nat (v - b))%nat = 0); last lia.
      rewrite /= app_nil_r -!app_assoc. do 3 f_equal. lia.
  Qed.

  (** Zeroed cells from [lo] on join the zone. *)
  Lemma region_zeroes_zone_from E (v lo e : Addr) :
    (v <= lo)%a → (lo <= e)%a →
    [[ v , e ]] ↦ₐ [[ 0…0 ]] ⊢
    |~{E}~> stack_region v lo (region_addrs_zeroes v lo) ∗
            [∗ list] a ∈ finz.seq_between lo e, zone_cell a.
  Proof.
    iIntros (Hvlo Hloe) "Hz".
    rewrite (region_addrs_zeroes_split v lo e); last solve_addr.
    iDestruct (region_pointsto_split v e lo with "Hz") as "[Hlo Hhi]";
      [solve_addr | by rewrite /region_addrs_zeroes length_replicate |].
    iDestruct (stack_region_of_pointsto with "Hlo") as "Hlo".
    iMod (zone_deposit_list _ (finz.seq_between lo e) with "[Hhi]") as "Hhi".
    { rewrite /region_pointsto /region_addrs_zeroes -(finz_seq_between_length lo e).
      by rewrite big_sepL2_replicate_r. }
    iModIntro. iFrame.
  Qed.

  Lemma stack_region_zeroes_join (v lo e : Addr) :
    (v <= lo)%a → (lo <= e)%a →
    stack_region v lo (region_addrs_zeroes v lo) ∗
    ([∗ list] a ∈ finz.seq_between lo e, zone_cell a) ⊢
    stack_region v e (region_addrs_zeroes v e).
  Proof.
    iIntros (Hvlo Hloe) "[Hlo Hhi]".
    rewrite /stack_region (finz_seq_between_split v lo e); last solve_addr.
    rewrite (region_addrs_zeroes_split v lo e); last solve_addr.
    iApply (big_sepL2_app with "Hlo").
    rewrite /region_addrs_zeroes -(finz_seq_between_length lo e) big_sepL2_replicate_r;
      last done.
    iApply (big_sepL_mono with "Hhi"). iIntros (k a _) "Ha".
    by iApply stack_cell_of_zone.
  Qed.

  (** The cells of [[b, e)] once those of [[v, e)] are zeroed, with the
      zeroed cells as stack cells. *)
  Lemma stack_region_zeroed_from_cells (b v e : Addr) (ws : list LWord) :
    (b <= v)%a → (v <= e)%a →
    length ws = finz.dist b e →
    stack_region b v (take (finz.dist b v) ws) ∗
    stack_region v e (region_addrs_zeroes v e) ⊢
    stack_region b e (stack_zeroed_from b v ws).
  Proof.
    iIntros (Hbv Hve Hlen) "[Hlo Hhi]".
    rewrite (stack_region_split b v e); [|solve_addr|solve_addr].
    rewrite /stack_zeroed_from (_ : Z.to_nat (v - b) = finz.dist b v);
      last (rewrite /finz.dist; solve_addr).
    assert (finz.dist b v <= length ws)%nat as Hle.
    { rewrite Hlen /finz.dist. solve_addr. }
    rewrite take_app_le; last (rewrite length_take; lia).
    rewrite take_idemp.
    rewrite drop_app_le; last (rewrite length_take; lia).
    rewrite drop_ge; last (rewrite length_take; lia).
    iFrame "Hlo".
    rewrite /region_addrs_zeroes Hlen /=.
    rewrite (_ : (finz.dist b e - finz.dist b v)%nat = finz.dist v e);
      last (rewrite /finz.dist; solve_addr).
    iFrame.
  Qed.

  Lemma stack_zeroed_from_length (b : Addr) (v : Z) (ws : list LWord) :
    length (stack_zeroed_from b v ws) = length ws.
  Proof. rewrite /stack_zeroed_from length_app length_take length_replicate. lia. Qed.

  (** Two adjacent stack regions make one. *)
  Lemma stack_region_app (b m e : Addr) (l1 l2 : list LWord) :
    (b <= m)%a → (m <= e)%a →
    length l1 = finz.dist b m →
    stack_region b m l1 ∗ stack_region m e l2 ⊣⊢ stack_region b e (l1 ++ l2).
  Proof.
    intros Hbm Hme Hl1.
    rewrite /stack_region (finz_seq_between_split b m e); last solve_addr.
    rewrite big_sepL2_app_same_length; first done.
    left. by rewrite finz_seq_between_length.
  Qed.

  Lemma stack_region_app_inv (b m e : Addr) (l1 l2 : list LWord) :
    (b <= m)%a → (m <= e)%a →
    length l1 = finz.dist b m →
    stack_region b e (l1 ++ l2) ⊢ stack_region b m l1 ∗ stack_region m e l2.
  Proof. intros. by rewrite stack_region_app. Qed.

End stack_cells_zero.

(* TODO: move to program_logic/stack_cells.v *)
Section csrw_zeroed.
  Context {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}.

  (** [csrw mshwm, src] with [src] at [a], after the zeroing of [[z, a)]
      from the logical MSHWM [v]: [z] is [v], or [a] when [v] is at or above
      it. The zeroed cells that the new value covers join the zone. *)
  Lemma wp_csrw_mshwm_zeroed E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src vsrc
      (hb v : Z) (z a : Addr) dq :
    decodeInstrW w.(lw) = SpecialRW cnull mshwm (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    get_a vsrc.(lw) = a →
    (z <= a)%a →
    (v = z ∨ (z = a ∧ a <= v))%Z →
    (0 <= hb)%Z →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ vsrc ∗
        ▷ hwm_regs hb v ∗
        [[ z , a ]] ↦ₐ [[ 0…0 ]] }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        src ↦ᵣ vsrc ∗
        hwm_regs hb a ∗
        stack_region z a (region_addrs_zeroes z a) }}}.
  Proof.
    iIntros (Hdecode Hvpc Hsr Hpca' Hsrc Hx Hza Hzv Hb0 φ)
      "(HPC & Hi & Hsrc & Hhwm & Hzero) Hφ".
    destruct (decide (Z.max hb v <= a)%Z) as [Hlo | Hlo].
    - destruct (finz_of_z_spec MemNum (Z.max hb v))
        as [ (lo & _ & Hlo_eq) | [_ Hlo_none] ]; last (exfalso; solve_addr).
      iMod (region_zeroes_zone_from _ z lo a with "Hzero") as "[Hzero Hcells]";
        [solve_addr | solve_addr |].
      iApply (wp_csrw_mshwm_gen _ _ _ _ _ _ _ _ _ _ _ _ _ lo a
               with "[$HPC $Hi $Hsrc $Hhwm $Hcells]"); try done.
      iIntros "!> (HPC & Hi & Hsrc & Hhwm & Hcells)".
      iApply "Hφ". iFrame.
      iApply (stack_region_zeroes_join with "[$Hzero $Hcells]"); solve_addr.
    - iDestruct "Hhwm" as "[Hb Hh]".
      iDestruct (stack_region_of_pointsto with "Hzero") as "Hzero".
      destruct (decide (a < hb)%Z) as [Hbelow | Hge].
      + iApply (wp_csrw_mshwm_below with "[$HPC $Hi $Hsrc $Hb $Hh]"); try done; first lia.
        iIntros "!> (HPC & Hi & Hsrc & Hb & Hh)".
        iApply "Hφ". rewrite Hx. iFrame.
      + iApply (wp_csrw_mshwm with "[$HPC $Hi $Hsrc $Hb $Hh]"); try done; first (cbn; lia).
        iIntros "!> (HPC & Hi & Hsrc & Hb & Hh)".
        iApply "Hφ". rewrite Hx. iFrame.
  Qed.

End csrw_zeroed.

Section Switcher_Zero_Callee_Frame.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** From [.Lswitch_just_return]: the jump to [wret], which faults
      when [wret] is not a valid target. *)
  Lemma switcher_return_to_caller_spec (wret : LWord) :
    PC ↦ₚ[th] switcher_label_pc ".Lswitch_just_return" ∗
    cra ↦ᵣ[th] wret ∗
    switcher_code ∗
    ( ▷ ( PC ↦ₚ[th] lupdatePcPerm wret ∗
          cra ↦ᵣ[th] wret ∗
          £ 1 -∗
          safe[th] ) ∧
      ( ⌜jalr_target_ok cnull cra wret.(lw) = false⌝ ∗
        cra ↦ᵣ[th] wret -∗
        trap_safe (switcher_label_pc ".Lswitch_just_return") ⊤
          (HO th) ) )
    ⊢ safe[th].
  Proof.
    iIntros "(HPC & Hcra & #Hswitcher & Hpost)".
    switcher_open_label ".Lswitch_just_return" "Hswitcher" as "Hcode" a_ret Ha_ret.
    destruct (jalr_target_ok cnull cra wret.(lw)) eqn:Htgt; cycle 1.
    { (* The fault is at the start of the block. The label would be unfolded
         by the simplifications of [iInstr_fail] *)
      rewrite -Ha_ret.
      clear Ha_ret.
      (* Jalr cnull cra *)
      iInstr_fail "Hcode".
      iDestruct "Hpost" as "[_ Hfailed]".
      iTrap with "Hfailed".
      done. }
    (* Jalr cnull cra *)
    iInstr "Hcode" with "Hlc".
    iDestruct "Hpost" as "[Hpost _]".
    iApply "Hpost". iFrame "HPC Hcra Hlc".
  Qed.

  (** From [.Lswitch_callee_dead_zeros]: clear the registers of [rmap] and
      jump to [wcra]. The jump faults when [wcra] is not a valid target. *)
  Lemma switch_callee_dead_zeros_spec (wcra : LWord) (rmap : LReg) :
    dom rmap = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ->

    PC ↦ₚ[th] switcher_label_pc ".Lswitch_callee_dead_zeros" ∗
    cra ↦ᵣ[th] wcra ∗
    regs[th] rmap ∗
    switcher_code ∗
    ▷ ( ∀ (rmap' : LReg),
        ⌜ dom rmap' = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
        cra ↦ᵣ[th] wcra ∗
        regs₀[th] rmap' -∗
        ( PC ↦ₚ[th] lupdatePcPerm wcra ∗
          £ 1 -∗
          safe[th] ) ∧
        ( ⌜ jalr_target_ok cnull cra wcra.(lw) = false ⌝ -∗
          trap_safe (switcher_label_pc ".Lswitch_just_return") ⊤
            (HO th) ) )
    ⊢ safe[th].
  Proof.
    iIntros (Hdom) "(HPC & Hcra & Hrmap & #Hswitcher & Hpost)".
    iAssert switcher_code as "Hswitcher_ret"; first iFrame "Hswitcher".
    switcher_open_label ".Lswitch_callee_dead_zeros" "Hswitcher" as "Hcode".
    iApply (clear_registers_post_call_spec with "[- $HPC $Hrmap $Hcode]");
      try solve_pure.
    iNext; iIntros "(%rmap' & %Hrmap' & HPC & Hrmap & _)".
    switcher_change_pc_label ".Lswitch_just_return".
    iApply (switcher_return_to_caller_spec with "[- $HPC $Hcra $Hswitcher_ret]").
    iSplit.
    - iNext; iIntros "(HPC & Hcra & Hlc)".
      iDestruct ("Hpost" $! rmap' with "[$Hcra $Hrmap //]") as "[Hpost _]".
      iApply "Hpost"; iFrame "HPC Hlc".
    - iIntros "(%Htgt & Hcra)".
      iDestruct ("Hpost" $! rmap' with "[$Hcra $Hrmap //]") as "[_ Hfailed]".
      by iApply "Hfailed".
  Qed.

  (** From [.Lswitch_callee_dead_zeros], in [switcher_zero_callee_frame_spec]:
      clear the registers, and go to the continuation. *)
  #[local] Ltac zero_frame_dead_zeros Hdom :=
    iDestruct (big_sepM_insert_2 with "[Hct2] Hrmap") as "Hrmap"; [iFrame "Hct2"|];
    iDestruct (big_sepM_insert_2 with "[Hct1] Hrmap") as "Hrmap"; [iFrame "Hct1"|];
    iDestruct (big_sepM_insert_2 with "[Hct0] Hrmap") as "Hrmap"; [iFrame "Hct0"|];
    iDestruct (big_sepM_insert_2 with "[Hca2] Hrmap") as "Hrmap"; [iFrame "Hca2"|];
    iDestruct (big_sepM_insert_2 with "[Hctp] Hrmap") as "Hrmap"; [iFrame "Hctp"|];
    switcher_change_pc_label ".Lswitch_callee_dead_zeros";
    iApply (switch_callee_dead_zeros_spec with "[- $HPC $Hcra $Hrmap $Hswitcher_dz]");
    [ rewrite !dom_insert_L Hdom; clear; set_solver | ];
    iNext; iIntros (rmap') "(%Hrmap' & Hcra & Hrmap)";
    iDestruct "Hpost" as "[Hpost _]".

  (** In [switcher_zero_callee_frame_spec], when MSHWM is at or above the
      cursor: the zeroing stores nothing, and the cells are unchanged. *)
  #[local] Ltac zero_frame_skip v a hb Hdom :=
    (* Jle 4 ct1 ct2 *)
    iInstrApply "Hcode_zero" wp_jcond_success_jmp_r_r with "[$HPC $Hct1 $Hct2]"
      as "(HPC & Hct1 & Hct2)";
    [ cbn; apply Z.leb_le; solve_addr | ];
    iAssert ([[ a , a ]] ↦ₐ [[ 0…0 ]])%I as "Hnil";
    [ rewrite /region_pointsto /region_addrs_zeroes finz_seq_between_empty; [|solve_addr];
      rewrite finz_dist_0; [done | solve_addr] | ];
    iAssert (hwm_regs hb v) with "[$Hmshwmb $Hmshwm]" as "Hhwm";
    (* SpecialRW cnull MSHWM (inr csp) *)
    iInstrApply "Hcode_csrw" (wp_csrw_mshwm_zeroed _ _ _ _ _ _ _ _ _ _ _ hb v a a)
      with "[$HPC $Hcsp $Hhwm $Hnil]" as "Hres";
    [ done | solve_addr | right; split; [done | lia] | lia | ];
    iDestruct "Hres" as "(HPC & Hcsp & Hhwm & _)";
    zero_frame_dead_zeros Hdom;
    iDestruct (switcher_stk_cells_region_4 with "Hcells") as "Hcells";
    [ rewrite /SpillSlot_size; solve_addr | ];
    iDestruct (stack_region_of_pointsto with "Hcells") as "Hcells".

  (** From [.Lswitch_callee_stack_zero]: clear the caller's free part, the
      spill area and the callee's stack, from the value [h] of MSHWM to the
      cursor [a], write [a] to MSHWM, clear the registers and jump back to
      the caller [wcra']. The cells below [h] are left. When [h] is below
      the base of the stack, the first store of the zeroing faults. *)
  Lemma switcher_zero_callee_frame_spec
    (b e a : Addr) (stk_mem : list LWord)
    (wcs0 wcs1 wcra wcgp : LWord)
    (wcgp' wcra' wcs1' wcs0' wca2 wctp wct0 wct1 wct2 : LWord)
    (rmap : LReg) (hb h : Z) :
    switcher_stk_bounds b e a ->
    disjoint_from_mmio b e ->
    dom rmap = all_registers_s ∖
                 {[ csp ; ca0 ; ca1 ; cra ; cgp ; ctp ; ca2 ; cs1 ; cs0 ; ct0 ; ct1 ; ct2 ]} ->
    (0 <= hb <= h)%Z ->

    PC ↦ₚ[th] switcher_label_pc ".Lswitch_callee_stack_zero" ∗
    cgp ↦ᵣ[th] wcgp' ∗
    cra ↦ᵣ[th] wcra' ∗
    cs1 ↦ᵣ[th] wcs1' ∗
    cs0 ↦ᵣ[th] wcs0' ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    ca2 ↦ᵣ[th] wca2 ∗
    ctp ↦ᵣ[th] wctp ∗
    csp ↦ᵣ[th] Cap RWL Local b e a ∗
    switcher_stk_cells (stk_spill_a a) wcs0 wcs1 wcgp wcra ∗
    stack_region (stk_callee_b b a) (stk_callee_e e a) stk_mem ∗
    hwm_regs hb h ∗
    regs[th] rmap ∗
    switcher_code ∗
    ( ▷ ( ∀ rmap' : LReg,
          (* the zeroing, from the value [h] read from MSHWM, did not fault *)
          ⌜(b <= h)%Z⌝ -∗
          ⌜ dom rmap' = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
          cra ↦ᵣ[th] wcra' ∗
          cgp ↦ᵣ[th] wcgp' ∗
          cs0 ↦ᵣ[th] wcs0' ∗
          cs1 ↦ᵣ[th] wcs1' ∗
          csp ↦ᵣ[th] Cap RWL Local b e a ∗
          stack_region (stk_spill_a a) (stk_spill_a a ^+ SpillSlot_size)
            (stack_zeroed_from (stk_spill_a a) h [wcs0; wcs1; wcgp; wcra]) ∗
          stack_region (stk_callee_b b a) (stk_callee_e e a)
            (stack_zeroed_from (stk_callee_b b a) h stk_mem) ∗
          hwm_regs hb a ∗
          regs₀[th] rmap' -∗
          ( PC ↦ₚ[th] lupdatePcPerm wcra' ∗
            £ 1 -∗
            safe[th] ) ∧
          ( ⌜ jalr_target_ok cnull cra wcra'.(lw) = false ⌝ -∗
            trap_safe (switcher_label_pc ".Lswitch_just_return") ⊤
              (HO th) ) ) ∧
      (* the first store of the zeroing faults: [h] is below the base *)
      ( ∀ off : Z,
          ⌜(h < b)%Z⌝ -∗
          ⌜ trap_no_resume (switcher_pc off) ⌝ -∗
          cgp ↦ᵣ[th] wcgp' ∗
          cra ↦ᵣ[th] wcra' ∗
          cs1 ↦ᵣ[th] wcs1' ∗
          cs0 ↦ᵣ[th] wcs0' ∗
          ct0 ↦ᵣ[th] wct0 ∗
          ct1 ↦ᵣ[th] WInt a ∗
          (∃ wct2', ct2 ↦ᵣ[th] wct2') ∗
          ca2 ↦ᵣ[th] wca2 ∗
          ctp ↦ᵣ[th] WInt h ∗
          csp ↦ᵣ[th] Cap RWL Local b e a ∗
          switcher_stk_cells (stk_spill_a a) wcs0 wcs1 wcgp wcra ∗
          stack_region (stk_callee_b b a) (stk_callee_e e a) stk_mem ∗
          hwm_regs hb h ∗
          regs[th] rmap -∗
          trap_safe (switcher_pc off) ⊤ (HO th) ) )
    ⊢ safe[th].
  Proof.
    iIntros (Hbounds Hstk_mmio Hdom Hhwm_ok)
      "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hct0 & Hct1 & Hct2 & Hca2 & Hctp & Hcsp
      & Hcells & Hstk & [Hmshwmb Hmshwm] & Hrmap & #Hswitcher & Hpost)".
    iAssert switcher_code as "Hswitcher_dz"; first iFrame "Hswitcher".
    pose proof Hbounds as (Hba & Hba3 & Ha4).
    revert Hba Hba3 Ha4; stk_unfold; intros Hba Hba3 Ha4.
    pose proof (disjoint_from_mmio_shadow _ _ Hstk_mmio) as Hstk_shadow.
    switcher_open_label "switcher_after_compartment_call" "Hswitcher" as "Hcode" a_block Heq_block.
    switcher_pc_in_block "switcher_after_compartment_call" ".Lswitch_callee_stack_zero" "HPC".
    (* SpecialRW ctp MSHWM (inr cnull) *)
    iInstrApply "Hcode" wp_csrr_mshwm with "[$HPC $Hctp $Hmshwm]"
      as "(HPC & Hctp & Hmshwm)".
    (* GetA ct1 csp *)
    iInstr "Hcode".
    iAssert (codefrag_pers (a_block ^+ 19%nat) (clear_stack_instrs ct2 ct1)) as "Hcode_zero".
    { iEval (rewrite -(take_drop 19 (encodeInstrsW _))) in "Hcode".
      iDestruct (codefrag_app_pers with "Hcode") as "[_ Hcode']".
      rewrite length_take_le; last (cbn; lia).
      iEval (rewrite -(take_drop 4 (drop 19 _))) in "Hcode'".
      iDestruct (codefrag_app_pers with "Hcode'") as "[Hcode'' _]".
      iExact "Hcode''". }
    iAssert (codefrag_pers (a_block ^+ 23%nat)
               (encodeInstrsW [SpecialRW cnull mshwm (inr csp)])) as "Hcode_csrw".
    { iEval (rewrite -(take_drop 23 (encodeInstrsW _))) in "Hcode".
      iDestruct (codefrag_app_pers with "Hcode") as "[_ Hcode']".
      rewrite length_take_le; last (cbn; lia).
      iExact "Hcode'". }
    assert (0 <= h)%Z as Hv0 by lia.
    iDestruct (big_sepL2_length with "Hstk") as %Hlen_stk.
    rewrite finz_seq_between_length in Hlen_stk.
    destruct (decide (a <= h)%Z) as [Hav | Hva].
    { (* MSHWM is at or above the cursor: nothing is stored *)
      destruct (finz_of_z_spec MemNum h) as [ (va & Hva_some & Hvaeq) | [Hnone _] ].
      - (* SetA ct2 csp ctp *)
        iInstr "Hcode".
        { exact Hva_some. }
        zero_frame_skip h a hb Hdom.
        iApply ("Hpost" $! rmap' with "[%] [-]"); [solve_addr |].
        rewrite (stack_zeroed_from_above (a ^- 4)); last (cbn; solve_addr).
        rewrite (stack_zeroed_from_above b); last (rewrite -Hlen_stk /finz.dist; solve_addr).
        iFrame "∗ %".
      - (* SetA ct2 csp ctp *)
        iInstr_invalidate "Hcode".
        zero_frame_skip h a hb Hdom.
        iApply ("Hpost" $! rmap' with "[%] [-]"); [solve_addr |].
        rewrite (stack_zeroed_from_above (a ^- 4)); last (cbn; solve_addr).
        rewrite (stack_zeroed_from_above b); last (rewrite -Hlen_stk /finz.dist; solve_addr).
        iFrame "∗ %". }
    destruct (finz_of_z_spec MemNum h) as [ (va & Hva_some & Hvaeq) | [_ Hnone] ];
      last (exfalso; solve_addr).
    subst h.
    (* SetA ct2 csp ctp *)
    iInstr "Hcode".
    destruct (decide (b <= va)%a) as [Hbva | Hvab]; cycle 1.
    { (* The first store of the zeroing faults *)
      iApply (clear_stack_below_base_spec with "[- $HPC $Hcode_zero $Hct2 $Hct1]");
        try solve_pure.
      { cbn [length clear_stack_instrs]; solve_addr. }
      all: try solve_addr.
      iIntros "[Hct2 Hct1]".
      iDestruct "Hpost" as "[_ Hfailed]".
      rewrite (_ : (a_block ^+ 19%nat) ^+ 1
                   = a_switcher_call
                      ^+ (switcher_label_offset "switcher_after_compartment_call" + 20));
        last (subst a_block; switcher_addr_eq).
      iApply ("Hfailed" with "[%] [%] [$Hcgp $Hcra $Hcs1 $Hcs0 $Hct0 $Hct1 $Hct2 $Hca2
                $Hctp $Hcsp $Hcells $Hstk $Hmshwmb $Hmshwm $Hrmap]").
      { solve_addr. }
      { apply trap_no_resume_switcher_pc; by vm_compute. } }
    (* The free part, from [va] to the cursor, is zeroed *)
    iDestruct (switcher_stk_cells_region_4 with "Hcells") as "Hcells";
      first (rewrite /SpillSlot_size; solve_addr).
    iDestruct (stack_region_of_pointsto with "Hcells") as "Hcells".
    iEval (rewrite (_ : (a ^- 4) ^+ SpillSlot_size = a);
           last (rewrite /SpillSlot_size; solve_addr)) in "Hcells".
    iAssert (stack_region b a (stk_mem ++ [wcs0; wcs1; wcgp; wcra])) with "[Hstk Hcells]"
      as "Hfree".
    { erewrite <- (stack_region_app b _ a); [iFrame | solve_addr | solve_addr | by rewrite Hlen_stk]. }
    iDestruct (stack_region_split b va with "Hfree") as "[Hlo Hhi]"; [solve_addr | solve_addr |].
    iApply (clear_stack_spec _ _ _ _ _ _ b e va a ct2 ct1 _ hb va
             with "[- $HPC $Hct2 $Hct1 $Hcode_zero $Hhi $Hmshwmb $Hmshwm]");
      try solve_pure.
    { cbn [length clear_stack_instrs]; solve_addr. }
    { solve_addr. }
    { cbn. lia. }
    iIntros "!> (HPC & Hct2 & Hct1 & Hhwm & _ & Hzero)".
    assert ((a_block ^+ 19%nat) ^+ length (clear_stack_instrs ct2 ct1)
            = a_block ^+ 23%nat) as Hpc_csrw by (cbn; solve_addr).
    iEval (rewrite Hpc_csrw) in "HPC".
    (* SpecialRW cnull MSHWM (inr csp) *)
    iInstrApply "Hcode_csrw" (wp_csrw_mshwm_zeroed _ _ _ _ _ _ _ _ _ _ _ hb va va a)
      with "[$HPC $Hcsp $Hhwm $Hzero]" as "Hres".
    { done. }
    { solve_addr. }
    { by left. }
    { lia. }
    iDestruct "Hres" as "(HPC & Hcsp & Hhwm & Hzero)".
    zero_frame_dead_zeros Hdom.
    iDestruct (stack_region_zeroed_from_cells b va a with "[$Hlo $Hzero]") as "Hfree";
      [solve_addr | solve_addr | rewrite length_app /= -Hlen_stk /finz.dist; solve_addr |].
    rewrite (stack_zeroed_from_app b (a ^- 4)); last (rewrite -Hlen_stk /finz.dist; solve_addr).
    iDestruct (stack_region_app_inv b (a ^- 4) a with "Hfree") as "[Hstk Hcells]";
      [solve_addr | solve_addr | by rewrite stack_zeroed_from_length -Hlen_stk |].
    iApply ("Hpost" $! rmap' with "[%] [-]"); [solve_addr |].
    rewrite (_ : (a ^- 4) ^+ 4 = a); last solve_addr.
    iFrame "∗ %".
  Qed.

End Switcher_Zero_Callee_Frame.
