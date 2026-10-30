From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import wp_rules_interp.
From griotte Require Export stack_cells clear_stack.

(* TODO: move to program_logic/stack_cells.v *)
Section stack_cells_extra.
  Context {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}.

  (** The words [ws] of the stack cells from [b], with those at or above the
      address [v] zeroed: the cells below [v] keep their content. *)
  Definition stack_zeroed_from (b : Addr) (v : Z) (ws : list LWord) : list LWord :=
    take (Z.to_nat (v - b)) ws ++
    replicate (length ws - Z.to_nat (v - b)) (lword_of_word (WInt 0)).

  (** Nothing is zeroed from an address above the cells. *)
  Lemma stack_zeroed_from_above (b : Addr) (v : Z) (ws : list LWord) :
    (b + length ws <= v)%Z →
    stack_zeroed_from b v ws = ws.
  Proof.
    intros Hv. rewrite /stack_zeroed_from take_ge; last lia.
    rewrite (_ : length ws - Z.to_nat (v - b) = 0)%nat; last lia.
    by rewrite app_nil_r.
  Qed.

  Lemma stack_region_split (b a e : Addr) (ws : list LWord) :
    (b <= a)%a → (a <= e)%a →
    stack_region b e ws ⊣⊢
    stack_region b a (take (finz.dist b a) ws) ∗ stack_region a e (drop (finz.dist b a) ws).
  Proof.
    intros Hba Hae. rewrite /stack_region (finz_seq_between_split b a e); last solve_addr.
    rewrite -{1}(take_drop (finz.dist b a) ws).
    iSplit.
    - iIntros "H". iDestruct (big_sepL2_length with "H") as %Hlen.
      iDestruct (big_sepL2_app_inv with "H") as "[$ $]".
      left. rewrite finz_seq_between_length length_take.
      rewrite !length_app !finz_seq_between_length length_take length_drop in Hlen. lia.
    - iIntros "[H1 H2]". iApply (big_sepL2_app with "H1 H2").
  Qed.

  (** The cells of [[b, e)] once those of [[v, e)] are zeroed. *)
  Lemma stack_region_zeroed_from (b v e : Addr) (ws : list LWord) :
    (b <= v)%a → (v <= e)%a →
    length ws = finz.dist b e →
    stack_region b v (take (finz.dist b v) ws) ∗
    [[ v , e ]] ↦ₐ [[ 0…0 ]] ⊢
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
    iFrame "Hlo". iApply stack_region_of_pointsto.
    rewrite /region_addrs_zeroes Hlen /=.
    rewrite (_ : (finz.dist b e - finz.dist b v)%nat = finz.dist v e);
      last (rewrite /finz.dist; solve_addr).
    iFrame.
  Qed.

  (** A stack cell holding 0 joins the zone. *)
  Lemma stack_cell_zero_zone E (a : Addr) :
    stack_cell a (lword_of_word (WInt 0)) ⊢ |~{E}~> zone_cell a.
  Proof.
    iIntros "[Ha | [Hcell _]]"; last by iModIntro.
    by iApply zone_deposit.
  Qed.

  (** Zeroed stack cells join the zone. *)
  Lemma stack_region_zeroes_zone E (b e : Addr) :
    stack_region b e (region_addrs_zeroes b e) ⊢
    |~{E}~> [∗ list] a ∈ finz.seq_between b e, zone_cell a.
  Proof.
    rewrite /stack_region /region_addrs_zeroes.
    rewrite -(finz_seq_between_length b e).
    generalize (finz.seq_between b e) as l.
    intros l. induction l as [|a l IH]; cbn.
    { iIntros "_". by iModIntro. }
    iIntros "[Ha Hl]".
    iApply (si_upd_bind _ (zone_cell a) with "[Ha]"); first by iApply stack_cell_zero_zone.
    iIntros "Ha". iApply (si_upd_bind with "[Hl]"); first by iApply IH.
    iIntros "Hl". iModIntro. iFrame.
  Qed.

  (** The locked cells of [[hb, f)]: cells of the zone, between MSHWMB [hb]
      and the floor [f]. *)
  Definition hwm_locked (hb f : Addr) : iProp Σ :=
    [∗ list] a ∈ finz.seq_between hb f, zone_cell a.

  #[global] Instance hwm_locked_timeless hb f : Timeless (hwm_locked hb f).
  Proof. apply _. Qed.

  (** A stack cell excludes a zone cell at the same address. *)
  Lemma stack_cell_zone_cell_false (x : Addr) (w : LWord) :
    stack_cell x w -∗ zone_cell x -∗ False.
  Proof.
    iIntros "[Hx | [Hcell _]] Hzone".
    - iApply (zone_cell_pointsto_false with "Hzone Hx").
    - iApply (zone_cell_excl with "Hcell Hzone").
  Qed.

  (** A stack cell is not one of the locked cells. *)
  Lemma hwm_locked_not_stack_cell (hb f x : Addr) (w : LWord) :
    hwm_locked hb f -∗ stack_cell x w -∗ ⌜¬ (hb <= x < f)%a⌝.
  Proof.
    iIntros "Hlocked Hx %Hx".
    iDestruct (big_sepL_elem_of _ _ x with "Hlocked") as "Hcell".
    { apply elem_of_finz_seq_between. solve_addr. }
    iApply (stack_cell_zone_cell_false with "Hx Hcell").
  Qed.

  (** The logical MSHWM after a store at [x] to a cell of the zone is the old
      one, or [x] between MSHWMB and the old one. *)
  Lemma hwm_after_cases (x : Addr) (hb h : Z) :
    hwm_after x hb h = h ∨
    (hwm_after x hb h = x ∧ hb <= x < h)%Z.
  Proof. rewrite /hwm_after. case_decide; [by right | by left]. Qed.

  (** A store of the integer [z] to a cell of a stack at or above the logical
      MSHWM: a points-to by the ordinary store, a zone cell by the zone store.
      The logical MSHWM is unchanged. *)
  Lemma wp_store_stack_cell_z_imm E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst z
      p g b e a ea (imm : Z) (wa : LWord) (hb h : Z) dq q :
    is_shadow_address ea = false →
    decodeInstrW w.(lw) = Store dst (inl z) imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    writeAllowed p = true → withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    dst ≠ cnull →
    (h <= ea)%Z →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ Cap p g b e a @@? π ∗
        stack_cell ea wa ∗
        ▷ hwm_regs hb h ∗
        deref_res π q }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        dst ↦ᵣ Cap p g b e a @@? π ∗
        ea ↦ₐ WInt z ∗
        hwm_regs hb h ∗
        deref_res π q }}}.
  Proof.
    iIntros (Hsh Hdecode Hvpc Hpca' Hwa Hwb Hadd Hdst Hhwm φ)
      "(HPC & Hi & Hdst & Hcell & [Hb Hh] & Hdw) Hφ".
    iDestruct "Hcell" as "[Ha | [Hcell _]]".
    - iApply (wp_store_success_z_imm with "[$HPC $Hi $Hdst $Ha $Hdw]"); try done.
      iIntros "!> (HPC & Hi & Hdst & Ha & Hdw)".
      iApply "Hφ". iFrame.
    - iApply (wp_store_zone_z_imm with "[$HPC $Hi $Hdst $Hcell $Hb $Hh $Hdw]"); try done.
      iIntros "!> (HPC & Hi & Hdst & Ha & Hb & Hh & Hdw)".
      rewrite /hwm_after decide_False; last lia.
      iApply "Hφ". iFrame.
  Qed.

  (** A store of the register [src] to a stack cell. The logical MSHWM is
      lowered to [ea] when [ea] is in [[MSHWMB, MSHWM)], as by the zone
      store. *)
  Lemma wp_store_stack_cell_reg_imm E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst src wsrc
      p g b e a ea (imm : Z) (wa : LWord) (hb h : Z) dq q :
    is_shadow_address ea = false →
    decodeInstrW w.(lw) = Store dst (inr src) imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    writeAllowed p = true → withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    canStore p wsrc.(lw) = true →
    src ≠ cnull → dst ≠ cnull →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ wsrc ∗
        ▷ dst ↦ᵣ Cap p g b e a @@? π ∗
        stack_cell ea wa ∗
        ▷ hwm_regs hb h ∗
        deref_res π q }}}
      Instr Executable @ E
    {{{ (h' : Z), RET NextIV;
        ⌜h' = h ∨ h' = hwm_after ea hb h⌝ ∗
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        src ↦ᵣ wsrc ∗
        dst ↦ᵣ Cap p g b e a @@? π ∗
        ea ↦ₐ wsrc ∗
        hwm_regs hb h' ∗
        deref_res π q }}}.
  Proof.
    iIntros (Hsh Hdecode Hvpc Hpca' Hwa Hwb Hadd Hcan Hsrc Hdst φ)
      "(HPC & Hi & Hsrc & Hdst & Hcell & [Hb Hh] & Hdw) Hφ".
    iDestruct "Hcell" as "[Ha | [Hcell _]]".
    - iApply (wp_store_success_reg_imm with "[$HPC $Hi $Hsrc $Hdst $Ha $Hdw]"); try done.
      iIntros "!> (HPC & Hi & Hsrc & Hdst & Ha & Hdw)".
      iApply "Hφ". iFrame. by iLeft.
    - iApply (wp_store_zone_reg_imm with "[$HPC $Hi $Hsrc $Hdst $Hcell $Hb $Hh $Hdw]");
        try done.
      iIntros "!> (HPC & Hi & Hsrc & Hdst & Ha & Hb & Hh & Hdw)".
      rewrite lstore_word_canStore //.
      iApply "Hφ". iFrame. by iRight.
  Qed.

  (** [csrw mshwm, src], with the zone cells between [lo], the larger of
      MSHWMB and the logical MSHWM, and the new value [x]: none to lower or
      to go below MSHWMB, the cells of the raise otherwise. The cells stay in
      the zone. *)
  Lemma wp_csrw_mshwm_gen E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src vsrc
      (hb h : Z) (lo x : Addr) dq :
    decodeInstrW w.(lw) = SpecialRW cnull mshwm (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    get_a vsrc.(lw) = x →
    (Z.max hb h = lo)%Z →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ vsrc ∗
        ▷ hwm_regs hb h ∗
        ([∗ list] a ∈ finz.seq_between lo x, zone_cell a) }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        src ↦ᵣ vsrc ∗
        hwm_regs hb x ∗
        ([∗ list] a ∈ finz.seq_between lo x, zone_cell a) }}}.
  Proof.
    iIntros (Hdecode Hvpc Hsr Hpca' Hsrc Hx Hlo φ)
      "(HPC & Hi & Hsrc & [>Hb >Hh] & Hcells) Hφ".
    destruct (decide (x < hb)%Z) as [Hbelow | Hge_b].
    { iApply (wp_csrw_mshwm_below with "[$HPC $Hi $Hsrc $Hb $Hh]"); try done; first lia.
      iIntros "!> (HPC & Hi & Hsrc & Hb & Hh)".
      iApply "Hφ". rewrite Hx. iFrame. }
    destruct (decide (x <= h)%Z) as [Hle_h | Hgt_h].
    { iApply (wp_csrw_mshwm with "[$HPC $Hi $Hsrc $Hb $Hh]"); try done; first lia.
      iIntros "!> (HPC & Hi & Hsrc & Hb & Hh)".
      iApply "Hφ". rewrite Hx. iFrame. }
    iApply (wp_csrw_mshwm_raise _ _ _ _ _ _ _ _ _ _ _ hb h lo x
             with "[$HPC $Hi $Hsrc $Hb $Hh $Hcells]"); try done; first lia.
    iIntros "!> (HPC & Hi & Hsrc & Hb & Hh & Hcells)".
    iApply "Hφ". iFrame.
  Qed.

End stack_cells_extra.

Section ClearStackMacro.
  Context {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}.

  (** Zero the cells [[a_lo, a_hi)] of a stack through the capability in
      [rbase], whose cursor is at [a_lo], up to the address [a_hi] in [rtop].
      Each cell is a points-to or a zone cell; zone cells are at or above the
      logical MSHWM, which is unchanged. When [a_hi <= a_lo], nothing is
      stored. *)
  Lemma clear_stack_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (g : Locality) (b e a_lo a_hi : Addr)
    (rbase rtop : RegName) (ws : list LWord) (hb h : Z)
    φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (clear_stack_instrs rbase rtop)) ->
    (b <= a_lo)%a -> (a_hi <= e)%a ->
    (h <= a_lo)%Z ->
    disjoint_from_shadow b e →
    rbase ≠ cnull ->
    rtop ≠ cnull ->

    ( PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a
      ∗ rbase ↦ᵣ Cap RWL g b e a_lo
      ∗ rtop ↦ᵣ WInt a_hi
      ∗ hwm_regs hb h
      ∗ codefrag_pers pc_a (clear_stack_instrs rbase rtop)
      ∗ stack_region a_lo a_hi ws
      ∗ ▷ ( (PC ↦ₚ Cap pc_p pc_g pc_b pc_e (pc_a ^+ length (clear_stack_instrs rbase rtop))
             ∗ rbase ↦ᵣ Cap RWL g b e (if decide (a_lo < a_hi)%a then a_hi else a_lo)
             ∗ rtop ↦ᵣ WInt a_hi
             ∗ hwm_regs hb h
             ∗ codefrag_pers pc_a (clear_stack_instrs rbase rtop)
             ∗ ([[ a_lo , a_hi ]] ↦ₐ [[ 0…0 ]]))
        -∗ WP Exec {{ φ }})
    )
      ⊢ WP Exec {{ φ }}%I.
  Proof.
    iIntros (Hpc_exec Hbounds Hb Hhi Hhwm Hdisjoint Hrbase_cnull Hrtop_cnull)
      "(HPC & Hrbase & Hrtop & Hhwm_regs & #Hcode & Hstack & Hφ)".
    codefrag_facts "Hcode".
    destruct (decide (a_lo < a_hi)%a) as [Hlt | Hge]; cycle 1.
    { (* Jle 4 rtop rbase *)
      iInstrApply "Hcode" wp_jcond_success_jmp_r_r with "[$HPC $Hrtop $Hrbase]"
        as "(HPC & Hrtop & Hrbase)".
      { cbn; apply Z.leb_le; solve_addr. }
      iApply "Hφ". iFrame "∗ #".
      rewrite /region_pointsto finz_seq_between_empty; last solve_addr+Hge.
      rewrite /region_addrs_zeroes finz_dist_0; last solve_addr+Hge.
      done. }
    (* Jle 4 rtop rbase *)
    iInstrApply "Hcode" wp_jcond_success_next_r_r with "[$HPC $Hrtop $Hrbase]"
      as "(HPC & Hrtop & Hrbase)".
    { cbn; apply Z.leb_gt; solve_addr. }
    iAssert (⌜(b <= a_lo)%a ⌝)%I as "-#Hb"; first done.
    iAssert (⌜(a_lo < a_hi)%a ⌝)%I as "-#Hlo"; first done.
    iAssert (⌜(h <= a_lo)%Z ⌝)%I as "-#Hhwm"; first done.
    clear Hb Hlt Hhwm.
    iLöb as "IH" forall (a_lo ws).
    iDestruct "Hb" as "%Hb".
    iDestruct "Hlo" as "%Hlo".
    iDestruct "Hhwm" as "%Hhwm".
    iDestruct (big_sepL2_length with "Hstack") as "%Hlen_stk".
    rewrite finz_seq_between_cons in Hlen_stk; last solve_addr.
    destruct ws as [|wa ws]; simplify_eq.
    rewrite (stack_region_cons _ (a_lo ^+ 1)); [| solve_addr | solve_addr].
    iDestruct "Hstack" as "[Ha Hstack]".
    iPoseProof deref_res_none as "Hderef".
    (* Store rbase 0 0 *)
    iInstrApply "Hcode" wp_store_stack_cell_z_imm
      with "[$HPC $Hrbase $Ha $Hhwm_regs $Hderef]" as "(HPC & Hrbase & Ha & Hhwm_regs & _)".
    { eapply disjoint_from_shadow_not_in; first exact Hdisjoint.
      apply withinBounds_true_iff; solve_addr. }
    { apply withinBounds_true_iff; solve_addr. }
    { solve_addr. }
    (* Lea rbase rbase 1 *)
    iInstr "Hcode".
    { instantiate (1 := a_lo ^+ 1); solve_addr. }
    destruct (decide (a_lo ^+ 1 = a_hi)) as [Hend | Hne].
    - (* Jlt -2 rbase rtop *)
      iInstrApply "Hcode" wp_jcond_success_next_r_r with "[$HPC $Hrbase $Hrtop]"
        as "(HPC & Hrbase & Hrtop)".
      { cbn; apply Z.ltb_ge; solve_addr. }
      rewrite Hend finz_seq_between_empty in Hlen_stk; last solve_addr.
      destruct ws; last done.
      iApply "Hφ".
      iAssert ([[ a_lo ^+ 1 , a_hi ]] ↦ₐ [[ [] ]])%I as "Hnil".
      { rewrite /region_pointsto finz_seq_between_empty; last solve_addr. done. }
      iDestruct (region_pointsto_cons with "[$Ha $Hnil]") as "Hstk"; [solve_addr|solve_addr|].
      rewrite Hend.
      iFrame "∗ #".
      rewrite /region_addrs_zeroes (finz_dist_S a_lo); last solve_addr.
      rewrite -Hend finz_dist_0; last solve_addr.
      done.
    - (* Jlt -2 rbase rtop *)
      iInstrApply "Hcode" wp_jcond_success_jmp_r_r with "[$HPC $Hrbase $Hrtop]"
        as "(HPC & Hrbase & Hrtop)".
      { cbn; apply Z.ltb_lt; solve_addr. }
      { instantiate (1 := pc_a ^+ 1). solve_addr. }
      iApply ("IH" $! (a_lo ^+ 1) ws with
               "[$Hhwm_regs] [$Hstack] [Ha Hφ] [$HPC] [$Hrtop] [$Hrbase] [] [] []").
      { iIntros "(HPC & Hrbase & Hrtop & Hhwm_regs & _ & Hstk)".
        iApply "Hφ"; iFrame "∗ #".
        iDestruct (region_pointsto_cons with "[$Ha $Hstk]") as "Hstk"; [solve_addr|solve_addr|].
        rewrite /region_addrs_zeroes (finz_dist_S a_lo); last solve_addr.
        by cbn. }
      { iPureIntro; solve_addr. }
      { iPureIntro; solve_addr. }
      { iPureIntro; solve_addr. }
  Qed.

  (** When the cursor [a_lo] of [rbase] is below its base and below [a_hi],
      the first store faults, at [pc_a ^+ 1], and nothing is written. *)
  Lemma clear_stack_below_base_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (g : Locality) (b e a_lo a_hi : Addr)
    (rbase rtop : RegName)
    φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (clear_stack_instrs rbase rtop)) ->
    (a_lo < b)%a -> (a_lo < a_hi)%a ->
    rbase ≠ cnull ->
    rtop ≠ cnull ->

    ( PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a
      ∗ rbase ↦ᵣ Cap RWL g b e a_lo
      ∗ rtop ↦ᵣ WInt a_hi
      ∗ codefrag_pers pc_a (clear_stack_instrs rbase rtop)
      ∗ ( rbase ↦ᵣ Cap RWL g b e a_lo
          ∗ rtop ↦ᵣ WInt a_hi
          -∗ trap_safe (Cap pc_p pc_g pc_b pc_e (pc_a ^+ 1)) ⊤ φ )
    )
      ⊢ WP Exec {{ φ }}%I.
  Proof.
    iIntros (Hpc_exec Hbounds Hlo_b Hlo_hi Hrbase_cnull Hrtop_cnull)
      "(HPC & Hrbase & Hrtop & #Hcode & Hfailed)".
    codefrag_facts "Hcode".
    (* Jle 4 rtop rbase *)
    iInstrApply "Hcode" wp_jcond_success_next_r_r with "[$HPC $Hrtop $Hrbase]"
      as "(HPC & Hrtop & Hrbase)".
    { cbn; apply Z.leb_gt; solve_addr. }
    (* Store rbase 0 0 *)
    iInstrApply "Hcode" wp_store_fail_z_imm with "[$HPC $Hrbase]" as "(HPC & Hrbase)".
    { instantiate (1 := a_lo). solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    iTrap with "Hfailed".
  Qed.

End ClearStackMacro.
