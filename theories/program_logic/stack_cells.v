From iris.proofmode Require Import proofmode.
From griotte Require Export memory_region rules_hwm.

(** * Stack cells

    A cell of a stack is either a full points-to or a cell of the zone of the
    stack high-water mark, which holds an integer. *)

(** A word that is an integer. *)
Definition lword_int (w : LWord) : Prop := ∃ z : Z, w = lword_of_word (WInt z).

Section stack_cells.
  Context `{MP: MachineParameters} `{ceriseg: ceriseG Σ}.

  (** A cell of a stack at [a] holding [w]. *)
  Definition stack_cell (a : Addr) (w : LWord) : iProp Σ :=
    (a ↦ₐ w ∨ (∃ z, zone_cell_v a z ∗ ⌜w = lword_of_word (WInt z)⌝))%I.

  (** The cells of the stack region [b, e), holding [ws]. *)
  Definition stack_region (b e : Addr) (ws : list LWord) : iProp Σ :=
    [∗ list] a; w ∈ finz.seq_between b e; ws, stack_cell a w.

  (** The two high-water-mark registers, with their values. *)
  Definition hwm_regs (mshwmb_v mshwm_v : Z) : iProp Σ :=
    mshwmb ↦ₜ mshwmb_v ∗ mshwm ↦ₜ mshwm_v.

  #[global] Instance stack_cell_timeless a w : Timeless (stack_cell a w).
  Proof. apply _. Qed.

  #[global] Instance stack_region_timeless b e ws : Timeless (stack_region b e ws).
  Proof. apply _. Qed.

  Lemma stack_cell_of_pointsto a w : a ↦ₐ w -∗ stack_cell a w.
  Proof. iIntros "Ha". by iLeft. Qed.

  Lemma stack_cell_of_zone a z : zone_cell_v a z -∗ stack_cell a (lword_of_word (WInt z)).
  Proof. iIntros "Ha". iRight. by iFrame. Qed.

  (** A stack cell gives half of the points-to of its address, enough to load
      from it, and gets it back. *)
  Lemma stack_cell_half a w :
    stack_cell a w -∗
    a ↦ₐ{DfracOwn (1/2)} w ∗ (a ↦ₐ{DfracOwn (1/2)} w -∗ stack_cell a w).
  Proof.
    iIntros "[ [Ha1 Ha2] | (%z & Hcell & ->) ]".
    - iFrame "Ha1". iIntros "Ha1". iLeft. by iCombine "Ha1 Ha2" as "Ha".
    - iDestruct (zone_cell_v_unfold with "Hcell") as "[Htok $]".
      iIntros "Hhalf". iRight. iExists z. iSplit; last done.
      rewrite zone_cell_v_unfold. iFrame.
  Qed.

  Lemma stack_region_of_pointsto b e ws :
    [[ b , e ]] ↦ₐ [[ ws ]] ⊢ stack_region b e ws.
  Proof.
    rewrite /region_pointsto /stack_region.
    iIntros "H". iApply (big_sepL2_mono with "H").
    iIntros (k a w _ _) "Ha". by iApply stack_cell_of_pointsto.
  Qed.

  Lemma stack_region_length b e ws :
    stack_region b e ws -∗ ⌜length (finz.seq_between b e) = length ws⌝.
  Proof. iIntros "H". iApply (big_sepL2_length with "H"). Qed.

  Lemma stack_region_nil b : stack_region b b [] ⊣⊢ emp.
  Proof. rewrite /stack_region finz_seq_between_empty; last solve_addr. done. Qed.

  Lemma stack_region_cons (b b' e : Addr) (w : LWord) (ws : list LWord) :
    (b + 1)%a = Some b' → (b < e)%a →
    stack_region b e (w :: ws) ⊣⊢ stack_cell b w ∗ stack_region b' e ws.
  Proof.
    intros Hb' Hbe. rewrite /stack_region (finz_seq_between_cons b e); last solve_addr.
    rewrite big_sepL2_cons. by rewrite (_ : b ^+ 1 = b'); last solve_addr.
  Qed.

  (** The stores of [ws] from [a] through a capability of permission [p],
      end [e] and identifier [π], to stack cells. [D i] holds once the
      first [i] cells are written. Each store of a cell below [e] gets
      cell [i], a stack cell outside the shadow table, with the liveness
      of [π], and gives it back as a points-to of the stored word. Or cell
      [i] is an exposed device, reached without identifier: [D i] is kept,
      for a store that faults, and a store that succeeds gives [D (S i)]
      back from it. *)
  Definition cells_store_acc_cell (D : nat → iProp Σ) (p : Perm) (e a : Addr)
    (π : option AId) (ws : list LWord) : iProp Σ :=
    □ ∀ i : nat,
      ⌜(i < length ws)%nat⌝ -∗
      ⌜(a + i < e)%Z⌝ -∗
      D i
      ={⊤}=∗
      (∃ (v : LWord) (q : Qp),
        ⌜is_shadow_address (a ^+ i) = false⌝ ∗
        stack_cell (a ^+ i) v ∗
        deref_res π q ∗
        ▷ ((a ^+ i) ↦ₐ lstore_word p (ws !!! i) -∗
           deref_res π q
           ={⊤}=∗
           D (S i))) ∨
      (⌜is_exposed_mmio_address (a ^+ i) = true⌝ ∗
       ⌜π = None⌝ ∗
       D i ∗
       ▷ (D i ={⊤}=∗ D (S i))).

  #[global] Instance cells_store_acc_cell_persistent D p e a π ws :
    Persistent (cells_store_acc_cell D p e a π ws).
  Proof. apply _. Qed.

  (** The stores of [w :: ws] from [a], without the first: those of [ws]
      from [a ^+ 1]. *)
  Lemma cells_store_acc_cell_tail (D : nat → iProp Σ) (p : Perm) (e a : Addr)
    (π : option AId) (w : LWord) (ws : list LWord) :
    cells_store_acc_cell D p e a π (w :: ws) -∗
    cells_store_acc_cell (λ i, D (S i)) p e (a ^+ 1) π ws.
  Proof.
    iIntros "#Hacc !>" (i Hi Hie) "HD".
    rewrite (_ : (a ^+ 1) ^+ i = a ^+ S i); last solve_addr.
    iApply ("Hacc" $! (S i) with "[%] [%] HD"); [cbn; lia | solve_addr].
  Qed.

  (** Two cells of a stack at the same address exclude each other. *)
  Lemma stack_cell_excl (a : Addr) (v w : LWord) :
    stack_cell a v -∗ stack_cell a w -∗ False.
  Proof.
    iIntros "[Ha | (%za & Ha & _) ] [Hb | (%zb & Hb & _) ]".
    - iDestruct (pointsto_valid_2 with "Ha Hb") as %[Hv _].
      by rewrite dfrac_op_own dfrac_valid_own in Hv.
    - iApply (zone_cell_v_pointsto_false with "Hb Ha").
    - iApply (zone_cell_v_pointsto_false with "Ha Hb").
    - iApply (zone_cell_v_excl with "Ha Hb").
  Qed.

  (** A points-to is outside a stack region: each stack cell holds at least
      half of the points-to of its address. *)
  Lemma stack_region_disjoint_pointsto (b e a : Addr) (ws : list LWord) (w : LWord) :
    ⊢ stack_region b e ws ∗ a ↦ₐ w -∗ ⌜a ∉ finz.seq_between b e⌝.
  Proof.
    rewrite /stack_region. generalize (finz.seq_between b e) as la. intros la.
    revert ws. induction la as [|a1 la IH]; iIntros (ws) "[Hla Ha]".
    - iPureIntro. set_solver.
    - destruct ws as [|w1 ws]; first done.
      rewrite big_sepL2_cons. iDestruct "Hla" as "[Ha1 Hla]".
      iDestruct (stack_cell_half with "Ha1") as "[Ha1 _]".
      iDestruct (pointsto_ne with "Ha Ha1") as %Hne.
      iDestruct (IH with "[$Hla $Ha]") as %Hnin.
      iPureIntro. rewrite not_elem_of_cons. by split.
  Qed.

End stack_cells.

Section stack_cells_extra.
  Context {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {th : Thread} {CL : CritLink Σ th}
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

  (** The cells of [b, e) once those of [v, e) are zeroed. *)
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
    iIntros "[Ha | (%z & Hcell & _) ]"; last (iModIntro; by iExists z).
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

  (** The logical MSHWM after a store at [x] to a cell of the zone is the old
      one, or [x] between MSHWMB and the old one. *)
  Lemma hwm_after_cases (x : Addr) (mshwmb_v mshwm_v : Z) :
    hwm_after x mshwmb_v mshwm_v = mshwm_v ∨
    (hwm_after x mshwmb_v mshwm_v = x ∧ mshwmb_v <= x < mshwm_v)%Z.
  Proof. rewrite /hwm_after. case_decide; [by right | by left]. Qed.

  (** A store of the integer [z] to a cell of a stack at or above the logical
      MSHWM: a points-to by the ordinary store, a zone cell by the zone store.
      The logical MSHWM is unchanged. *)
  Lemma wp_store_stack_cell_z_imm E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst z
      p g b e a ea (imm : Z) (wa : LWord) (mshwmb_v mshwm_v : Z) dq q :
    is_shadow_address ea = false →
    decodeInstrW w.(lw) = Store dst (inl z) imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    writeAllowed p = true → withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    dst ≠ cnull →
    (mshwm_v <= ea)%Z →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ Cap p g b e a @@? π ∗
        stack_cell ea wa ∗
        ▷ hwm_regs mshwmb_v mshwm_v ∗
        deref_res π q }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        dst ↦ᵣ Cap p g b e a @@? π ∗
        ea ↦ₐ WInt z ∗
        hwm_regs mshwmb_v mshwm_v ∗
        deref_res π q }}}.
  Proof.
    iIntros (Hsh Hdecode Hvpc Hpca' Hwa Hwb Hadd Hdst Hhwm φ)
      "(HPC & Hi & Hdst & Hcell & [Hb Hh] & Hdw) Hφ".
    iDestruct "Hcell" as "[Ha | (%zc & Hcell & _) ]".
    - iApply (wp_store_success_z_imm with "[$HPC $Hi $Hdst $Ha $Hdw]"); try done.
      iIntros "!> (HPC & Hi & Hdst & Ha & Hdw)".
      iApply "Hφ". iFrame.
    - iApply (wp_store_zone_z_imm with "[$HPC $Hi $Hdst $Hcell $Hb $Hh $Hdw]"); try done.
      iIntros "!> (HPC & Hi & Hdst & Ha & Hb & Hh & Hdw)".
      rewrite /hwm_after decide_False; last lia.
      iApply "Hφ". iFrame.
  Qed.

  (** A store of the integer [z] to a cell of a stack, below or above the
      logical MSHWM: a points-to by the ordinary store, a zone cell by the zone
      store. The logical MSHWM is lowered to [ea] when [ea] is in
      [MSHWMB, MSHWM). *)
  Lemma wp_store_stack_cell_z_imm_gen E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst z
      p g b e a ea (imm : Z) (wa : LWord) (mshwmb_v mshwm_v : Z) dq q :
    is_shadow_address ea = false →
    decodeInstrW w.(lw) = Store dst (inl z) imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    writeAllowed p = true → withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    dst ≠ cnull →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ Cap p g b e a @@? π ∗
        stack_cell ea wa ∗
        ▷ hwm_regs mshwmb_v mshwm_v ∗
        deref_res π q }}}
      Instr Executable @ E
    {{{ (mshwm_v' : Z), RET NextIV;
        ⌜mshwm_v' = mshwm_v ∨ mshwm_v' = hwm_after ea mshwmb_v mshwm_v⌝ ∗
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        dst ↦ᵣ Cap p g b e a @@? π ∗
        ea ↦ₐ WInt z ∗
        hwm_regs mshwmb_v mshwm_v' ∗
        deref_res π q }}}.
  Proof.
    iIntros (Hsh Hdecode Hvpc Hpca' Hwa Hwb Hadd Hdst φ)
      "(HPC & Hi & Hdst & Hcell & [Hb Hh] & Hdw) Hφ".
    iDestruct "Hcell" as "[Ha | (%zc & Hcell & _) ]".
    - iApply (wp_store_success_z_imm with "[$HPC $Hi $Hdst $Ha $Hdw]"); try done.
      iIntros "!> (HPC & Hi & Hdst & Ha & Hdw)".
      iApply "Hφ". iFrame. by iLeft.
    - iApply (wp_store_zone_z_imm with "[$HPC $Hi $Hdst $Hcell $Hb $Hh $Hdw]"); try done.
      iIntros "!> (HPC & Hi & Hdst & Ha & Hb & Hh & Hdw)".
      iApply "Hφ". iFrame. by iRight.
  Qed.

  (** A store of the register [src] to a stack cell. The logical MSHWM is
      lowered to [ea] when [ea] is in [MSHWMB, MSHWM), as by the zone
      store. *)
  Lemma wp_store_stack_cell_reg_imm E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst src wsrc
      p g b e a ea (imm : Z) (wa : LWord) (mshwmb_v mshwm_v : Z) dq q :
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
        ▷ hwm_regs mshwmb_v mshwm_v ∗
        deref_res π q }}}
      Instr Executable @ E
    {{{ (mshwm_v' : Z), RET NextIV;
        ⌜mshwm_v' = mshwm_v ∨ mshwm_v' = hwm_after ea mshwmb_v mshwm_v⌝ ∗
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        src ↦ᵣ wsrc ∗
        dst ↦ᵣ Cap p g b e a @@? π ∗
        ea ↦ₐ wsrc ∗
        hwm_regs mshwmb_v mshwm_v' ∗
        deref_res π q }}}.
  Proof.
    iIntros (Hsh Hdecode Hvpc Hpca' Hwa Hwb Hadd Hcan Hsrc Hdst φ)
      "(HPC & Hi & Hsrc & Hdst & Hcell & [Hb Hh] & Hdw) Hφ".
    iDestruct "Hcell" as "[Ha | (%zc & Hcell & _) ]".
    - iApply (wp_store_success_reg_store_word_imm with "[$HPC $Hi $Hsrc $Hdst $Ha $Hdw]");
        try done.
      iIntros "!> (HPC & Hi & Hsrc & Hdst & Ha & Hdw)".
      rewrite lstore_word_canStore //.
      iApply "Hφ". iFrame. by iLeft.
    - iApply (wp_store_zone_reg_imm with "[$HPC $Hi $Hsrc $Hdst $Hcell $Hb $Hh $Hdw]");
        try done.
      iIntros "!> (HPC & Hi & Hsrc & Hdst & Ha & Hb & Hh & Hdw)".
      rewrite lstore_word_canStore //.
      iApply "Hφ". iFrame. by iRight.
  Qed.

  (** A store of the register [src] to a stack cell, of the word as the
      capability [p] stores it. The logical MSHWM is lowered to [ea] when
      [ea] is in [MSHWMB, MSHWM), as by the zone store. *)
  Lemma wp_store_stack_cell_reg_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w
      dst src wsrc p g b e a ea (imm : Z) (wa : LWord) (mshwmb_v mshwm_v : Z) dq q :
    is_shadow_address ea = false →
    decodeInstrW w.(lw) = Store dst (inr src) imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    writeAllowed p = true → withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    src ≠ cnull → dst ≠ cnull →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ wsrc ∗
        ▷ dst ↦ᵣ Cap p g b e a @@? π ∗
        stack_cell ea wa ∗
        ▷ hwm_regs mshwmb_v mshwm_v ∗
        deref_res π q }}}
      Instr Executable @ E
    {{{ (mshwm_v' : Z), RET NextIV;
        ⌜mshwm_v' = mshwm_v ∨ mshwm_v' = hwm_after ea mshwmb_v mshwm_v⌝ ∗
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        src ↦ᵣ wsrc ∗
        dst ↦ᵣ Cap p g b e a @@? π ∗
        ea ↦ₐ lstore_word p wsrc ∗
        hwm_regs mshwmb_v mshwm_v' ∗
        deref_res π q }}}.
  Proof.
    iIntros (Hsh Hdecode Hvpc Hpca' Hwa Hwb Hadd Hsrc Hdst φ)
      "(HPC & Hi & Hsrc & Hdst & Hcell & [Hb Hh] & Hdw) Hφ".
    iDestruct "Hcell" as "[Ha | (%zc & Hcell & _) ]".
    - iApply (wp_store_success_reg_store_word_imm with "[$HPC $Hi $Hsrc $Hdst $Ha $Hdw]");
        try done.
      iIntros "!> (HPC & Hi & Hsrc & Hdst & Ha & Hdw)".
      iApply "Hφ". iFrame. by iLeft.
    - iApply (wp_store_zone_reg_imm with "[$HPC $Hi $Hsrc $Hdst $Hcell $Hb $Hh $Hdw]");
        try done.
      iIntros "!> (HPC & Hi & Hsrc & Hdst & Ha & Hb & Hh & Hdw)".
      iApply "Hφ". iFrame. by iRight.
  Qed.

  (** [csrw mshwm, src], with the zone cells between [lo], the larger of
      MSHWMB and the logical MSHWM, and the new value [x]: none to lower or
      to go below MSHWMB, the cells of the raise otherwise. The cells stay in
      the zone. *)
  Lemma wp_csrw_mshwm_gen E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src vsrc
      (mshwmb_v mshwm_v : Z) (lo x : Addr) (zs : list Z) dq :
    decodeInstrW w.(lw) = SpecialRW cnull mshwm (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    get_a vsrc.(lw) = x →
    (Z.max mshwmb_v mshwm_v = lo)%Z →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ vsrc ∗
        ▷ hwm_regs mshwmb_v mshwm_v ∗
        ([∗ list] a; z ∈ finz.seq_between lo x; zs, zone_cell_v a z) }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        src ↦ᵣ vsrc ∗
        hwm_regs mshwmb_v x ∗
        ([∗ list] a; z ∈ finz.seq_between lo x; zs, zone_cell_v a z) }}}.
  Proof.
    iIntros (Hdecode Hvpc Hsr Hpca' Hsrc Hx Hlo φ)
      "(HPC & Hi & Hsrc & [>Hb >Hh] & Hcells) Hφ".
    destruct (decide (x < mshwmb_v)%Z) as [Hbelow | Hge_b].
    { iApply (wp_csrw_mshwm_below with "[$HPC $Hi $Hsrc $Hb $Hh]"); try done; first lia.
      iIntros "!> (HPC & Hi & Hsrc & Hb & Hh)".
      iApply "Hφ". rewrite Hx. iFrame. }
    destruct (decide (x <= mshwm_v)%Z) as [Hle_h | Hgt_h].
    { iApply (wp_csrw_mshwm with "[$HPC $Hi $Hsrc $Hb $Hh]"); try done; first lia.
      iIntros "!> (HPC & Hi & Hsrc & Hb & Hh)".
      iApply "Hφ". rewrite Hx. iFrame. }
    iApply (wp_csrw_mshwm_raise _ _ _ _ _ _ _ _ _ _ _ mshwmb_v mshwm_v lo x zs
             with "[$HPC $Hi $Hsrc $Hb $Hh $Hcells]"); try done; first lia.
    iIntros "!> (HPC & Hi & Hsrc & Hb & Hh & Hcells)".
    iApply "Hφ". iFrame.
  Qed.

  (** [csrw mshwm, src] with a value at most the logical MSHWM, or below
      MSHWMB. *)
  Lemma wp_csrw_mshwm_lower E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src vsrc (mshwmb_v mshwm_v : Z) dq :
    decodeInstrW w.(lw) = SpecialRW cnull mshwm (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    (mshwmb_v ≤ get_a vsrc.(lw) ≤ mshwm_v ∨ get_a vsrc.(lw) < mshwmb_v)%Z →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ vsrc ∗
        ▷ hwm_regs mshwmb_v mshwm_v }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        src ↦ᵣ vsrc ∗
        hwm_regs mshwmb_v (get_a vsrc.(lw)) }}}.
  Proof.
    iIntros (Hdecode Hvpc Hsr Hpca' Hsrc Hx φ) "(HPC & Hi & Hsrc & [>Hb >Hh]) Hφ".
    destruct Hx as [Hx | Hx].
    - iApply (wp_csrw_mshwm with "[$HPC $Hi $Hsrc $Hb $Hh]"); try done.
    - iApply (wp_csrw_mshwm_below with "[$HPC $Hi $Hsrc $Hb $Hh]"); try done.
  Qed.

End stack_cells_extra.

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
            [∗ list] a ∈ finz.seq_between lo e, zone_cell_v a 0.
  Proof.
    iIntros (Hvlo Hloe) "Hz".
    rewrite (region_addrs_zeroes_split v lo e); last solve_addr.
    iDestruct (region_pointsto_split v e lo with "Hz") as "[Hlo Hhi]";
      [solve_addr | by rewrite /region_addrs_zeroes length_replicate |].
    iDestruct (stack_region_of_pointsto with "Hlo") as "Hlo".
    iMod (zone_deposit_list_v _ (finz.seq_between lo e) with "[Hhi]") as "Hhi".
    { rewrite /region_pointsto /region_addrs_zeroes -(finz_seq_between_length lo e).
      by rewrite big_sepL2_replicate_r. }
    iModIntro. iFrame.
  Qed.

  Lemma stack_region_zeroes_join (v lo e : Addr) :
    (v <= lo)%a → (lo <= e)%a →
    stack_region v lo (region_addrs_zeroes v lo) ∗
    ([∗ list] a ∈ finz.seq_between lo e, zone_cell_v a 0) ⊢
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

  (** The cells of [b, e) once those of [v, e) are zeroed, with the
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

  (** Two adjacent stack regions make one, without a length premise. *)
  Lemma stack_region_join (b a e : Addr) (ws1 ws2 : list LWord) :
    (b <= a)%a → (a <= e)%a →
    stack_region b a ws1 ∗ stack_region a e ws2 ⊢ stack_region b e (ws1 ++ ws2).
  Proof.
    intros Hba Hae. rewrite /stack_region (finz_seq_between_split b a e); last solve_addr.
    iIntros "[H1 H2]". iApply (big_sepL2_app with "H1 H2").
  Qed.

  (** A stack region split around one of its cells, joined back. *)
  Lemma stack_region_join_cell (b a a' e : Addr) (ws1 ws2 : list LWord) (w : LWord) :
    (b <= a)%a → (a + 1)%a = Some a' → (a < e)%a →
    stack_region b a ws1 -∗ stack_cell a w -∗ stack_region a' e ws2 -∗
    stack_region b e (ws1 ++ w :: ws2).
  Proof.
    iIntros (Hba Ha' Hae) "H1 Hw H2".
    rewrite /stack_region (finz_seq_between_split b a e); last solve_addr.
    rewrite (finz_seq_between_cons a e); last solve_addr.
    rewrite (_ : a ^+ 1 = a'); last solve_addr.
    iApply (big_sepL2_app with "H1"). rewrite big_sepL2_cons. iFrame.
  Qed.

End stack_cells_zero.

(** * Stacks of integers

    A stack region whose cells hold some integers: what the zone of a stack
    gives, and what a callee gets of its stack. *)
Section stack_ints.
  Context {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}.

  (** The cells of the stack region [b, e), holding some integers. *)
  Definition stack_ints (b e : Addr) : iProp Σ :=
    ∃ ws : list LWord, ⌜Forall lword_int ws⌝ ∗ stack_region b e ws.

  #[global] Instance stack_ints_timeless b e : Timeless (stack_ints b e).
  Proof. apply _. Qed.

  Lemma stack_ints_of_region b e ws :
    Forall lword_int ws →
    stack_region b e ws ⊢ stack_ints b e.
  Proof. iIntros (Hws) "Hws". iExists ws. by iFrame. Qed.

  Lemma stack_ints_of_zeroes b e :
    stack_region b e (region_addrs_zeroes b e) ⊢ stack_ints b e.
  Proof.
    apply stack_ints_of_region. rewrite /region_addrs_zeroes.
    apply Forall_replicate. by exists 0%Z.
  Qed.

  Lemma stack_ints_region b e :
    stack_ints b e ⊢ ∃ ws, stack_region b e ws.
  Proof. iIntros "(%ws & _ & Hws)". by iExists ws. Qed.

  Lemma stack_ints_split (b m e : Addr) :
    (b <= m)%a → (m <= e)%a →
    stack_ints b e ⊣⊢ stack_ints b m ∗ stack_ints m e.
  Proof.
    intros Hbm Hme. iSplit.
    - iIntros "(%ws & %Hws & Hws)".
      iDestruct (stack_region_split b m e with "Hws") as "[H1 H2]"; [done | done |].
      iSplitL "H1".
      + iExists _. iFrame "H1". iPureIntro. by apply Forall_take.
      + iExists _. iFrame "H2". iPureIntro. by apply Forall_drop.
    - iIntros "[(%ws1 & %Hws1 & H1) (%ws2 & %Hws2 & H2)]".
      iExists (ws1 ++ ws2). iSplit; first (iPureIntro; by apply Forall_app).
      iApply (stack_region_join with "[$H1 $H2]"); done.
  Qed.

  (** Cells of the zone make a stack of integers. *)
  Lemma stack_ints_of_zone (b e : Addr) :
    ([∗ list] a ∈ finz.seq_between b e, zone_cell a) ⊢ stack_ints b e.
  Proof.
    rewrite zone_cells_exist. iIntros "(%zs & Hcells)".
    iExists ((λ z, lword_of_word (WInt z)) <$> zs). iSplit.
    { iPureIntro. apply Forall_fmap, Forall_forall. intros z _. by exists z. }
    rewrite /stack_region big_sepL2_fmap_r.
    iApply (big_sepL2_mono with "Hcells"). iIntros (k a z _ _) "Hcell".
    by iApply stack_cell_of_zone.
  Qed.
End stack_ints.

Section stack_ints_zone.
  Context {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {th : Thread} {CL : CritLink Σ th}
    `{MP: MachineParameters}.

  (** The cells of a stack of integers join the zone. *)
  Lemma stack_ints_zone E (b e : Addr) :
    stack_ints b e ⊢ |~{E}~> [∗ list] a ∈ finz.seq_between b e, zone_cell a.
  Proof.
    rewrite /stack_ints /stack_region.
    iIntros "(%ws & %Hws & Hstk)".
    iStopProof. revert ws Hws.
    generalize (finz.seq_between b e) as l. intros l.
    induction l as [|a l IH]; iIntros (ws Hws) "Hstk".
    { iClear "Hstk". by iModIntro. }
    iDestruct (big_sepL2_length with "Hstk") as %Hlen.
    destruct ws as [|w ws]; first done.
    apply Forall_cons in Hws as [ [z ->] Hws].
    iDestruct "Hstk" as "[Ha Hstk]".
    iMod (IH ws Hws with "Hstk") as "Hl".
    iDestruct "Ha" as "[Ha | (%z' & Ha & _)]".
    - iMod (zone_deposit_v with "Ha") as "Ha".
      iModIntro. iFrame "Hl". by iExists z.
    - iModIntro. iFrame "Hl". by iExists z'.
  Qed.
End stack_ints_zone.
