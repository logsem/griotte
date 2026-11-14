From iris.proofmode Require Import proofmode.
From griotte Require Import rules context_switch_layout switcher_link.

(** * The context-switch layout of the switcher

    The save area of a user thread is the register save area of its
    trusted stack, without its word [hazardPointers], and its saved MIE is
    InterruptDisabled. A thread parked with a save area resumes with the
    registers and the MIE it holds. *)

(** The word [k] of a save area. *)
Definition save_area_word (ws : list LWord) (k : Z) : LWord := default lnull (ws !! Z.to_nat k).

(** The registers that a thread parked with the save area [ws] resumes
    with: x1–x15 from the words 1 to 15; [cnull] holds [lnull]. *)
Definition resume_regs_of (ws : list LWord) : LReg :=
  list_to_map
    ((λ r, (r, if decide (r = cnull) then lnull
               else save_area_word ws (TrustedStack_offset_reg r))) <$> all_registers).

Lemma resume_regs_of_dom ws : dom (resume_regs_of ws) = all_registers_s.
Proof.
  rewrite /resume_regs_of dom_list_to_map_L -list_fmap_compose /all_registers_s.
  f_equal.
Qed.

(** The word of the PC that the resume path installs for the save area
    [ws]: the saved mepcc, one word further after an [ecall], legalised by
    the write to mepcc. *)
Definition resume_pc_word (ws : list LWord) : Word :=
  let pc := (save_area_word ws TrustedStack_offset_mepcc).(lw) in
  legalise_pc
    (if decide (get_a (save_area_word ws TrustedStack_offset_mcause).(lw) = MCAUSE_ECALL_MACHINE)
     then lea_word pc 1 else pc).

(** The resume PC: its word is the save area's resume-PC word; a tagged one
    has no identifier. *)
Definition resume_pc_ok (ws : list LWord) (pc : LWord) : Prop :=
  pc.(lw) = resume_pc_word ws ∧
  (get_tag pc.(lw) = true → pc.(lprov) = None).

(** The values that a thread parked with the save area [ws] resumes with:
    its registers as [resume_regs_of], its MIE the saved MPIE of the word
    [mstatus], its PC as [resume_pc_ok], and its MSHWMB and MSHWM the
    addresses of the words [mshwmb] and [mshwm]. *)
Definition resume_ok_full (ws : list LWord) (v : resume_vals) : Prop :=
  v.(rv_regs) = resume_regs_of ws ∧
  v.(rv_mie) = mpie_of (get_a (save_area_word ws TrustedStack_offset_mstatus).(lw)) ∧
  resume_pc_ok ws v.(rv_pc) ∧
  v.(rv_hwmb) = get_a (save_area_word ws TrustedStack_offset_mshwmb).(lw) ∧
  v.(rv_hwm) = get_a (save_area_word ws TrustedStack_offset_mshwm).(lw).

Lemma resume_ok_full_dom ws v :
  resume_ok_full ws v → dom v.(rv_regs) = all_registers_s.
Proof. intros [-> _]. apply resume_regs_of_dom. Qed.

Section context_switch_layout_instance.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}
    {swlayout : switcherLayout}.

  Lemma csl_full_posture_part t :
    @posture_part Σ MP (ceriseG_of (UserThread t)) (UserThread t)
      (crit_link_full (UserThread t)) (crit_route_full (UserThread t)) ⊣⊢
    (∃ ws, ⌜saved_mie_ok ws⌝ ∗
       (∃ mshwmb_v : Z, ⌜ws !! 20%nat = Some (lword_of_word (WInt mshwmb_v))⌝ ∗ hwm_base[u t] mshwmb_v) ∗
       save_area_holed (UserThread t) ws) ∗
    mtdc_lent_at (th := UserThread t).
  Proof.
    by rewrite (posture_part_user (UserThread t)) // /save_area_part /mtdc_lent_at /ceriseG_of.
  Qed.

  Lemma csl_full_link_disabled th σ :
    mie_st σ = InterruptDisabled →
    ⊢ @crit_link Σ th (crit_link_full th) σ.
  Proof. intros Hdis. rewrite crit_link_full_unfold /crit_link_def Hdis. done. Qed.

  Lemma csl_full_link_user_enabled t σ :
    mie_st σ = InterruptEnabled →
    @crit_link Σ (UserThread t) (crit_link_full (UserThread t)) σ ⊣⊢
    handover_res (ceriseg := ceriseG_of (UserThread t)) ∗
    @posture_part Σ MP (ceriseG_of (UserThread t)) (UserThread t)
      (crit_link_full (UserThread t)) (crit_route_full (UserThread t)).
  Proof.
    intros Hen. rewrite crit_link_full_unfold /crit_link_def Hen.
    rewrite (posture_part_user (UserThread t)) //.
  Qed.

  Lemma csl_full_link_ctx_enabled σ :
    mie_st σ = InterruptEnabled →
    @crit_link Σ CtxSwitch (crit_link_full CtxSwitch) σ ⊢
    handover_res (ceriseg := ceriseG_of CtxSwitch).
  Proof.
    intros Hen. rewrite crit_link_full_unfold /crit_link_def Hen.
    case_decide; [by iIntros "[$ _]" | done].
  Qed.

  (** The save area of user thread [t] holds its saved-MIE fact, and its
      word [mshwmb] is the thread's stack base. *)
  #[global] Instance context_switch_layout_full :
    ContextSwitchLayout Σ crit_link_full crit_route_full := {|
    save_area_at t ws :=
      (⌜saved_mie_ok ws⌝ ∗
       (∃ mshwmb_v : Z, ⌜ws !! 20%nat = Some (lword_of_word (WInt mshwmb_v))⌝ ∗ hwm_base[u t] mshwmb_v) ∗
       save_area_holed (UserThread t) ws)%I;
    resume_ok := resume_ok_full;
    csl_posture_part := csl_full_posture_part;
    csl_link_disabled := csl_full_link_disabled;
    csl_link_user_enabled := csl_full_link_user_enabled;
    csl_link_ctx_enabled := csl_full_link_ctx_enabled;
  |}.

  (** The registers of the save area [ws], [cnull] apart, are the
      registers that a thread parked with [ws] resumes with. *)
  Lemma regs_resume_regs_of (th : Thread) (ws : list LWord) :
    length ws = 21%nat →
    cnull ↦ᵣ[th] lnull ∗
    ([∗ list] r ∈ exception_spill_regs ++ [csp],
       r ↦ᵣ[th] save_area_word ws (TrustedStack_offset_reg r)) ⊣⊢
    regs[th] (resume_regs_of ws).
  Proof.
    intros _. rewrite /resume_regs_of.
    rewrite big_sepM_list_to_map; last first.
    { rewrite -list_fmap_compose. apply all_registers_NoDup. }
    rewrite big_sepL_fmap.
    rewrite (big_opL_permutation _ all_registers (cnull :: exception_spill_regs ++ [csp]));
      last by apply (bool_decide_unpack _).
    rewrite big_sepL_cons.
    assert (cnull ∉ exception_spill_regs ++ [csp]) as Hnull by (by apply (bool_decide_unpack _)).
    f_equiv.
    - cbn. by case_decide.
    - apply big_sepL_proper. intros k r Hr. cbn.
      case_decide as Heq; last done.
      subst r. exfalso. apply Hnull. by eapply list_elem_of_lookup_2.
  Qed.

  (** The save area of user thread [t] in the context-switch layout of the
      switcher. *)
  Lemma save_area_at_full (t : nat) (ws : list LWord) :
    @save_area_at Σ MP ceriseb crit_link_full crit_route_full context_switch_layout_full t ws ⊣⊢
    ⌜saved_mie_ok ws⌝ ∗
    (∃ mshwmb_v : Z, ⌜ws !! 20%nat = Some (lword_of_word (WInt mshwmb_v))⌝ ∗ hwm_base[u t] mshwmb_v) ∗
    save_area_holed (UserThread t) ws.
  Proof. reflexivity. Qed.

  (** The resume values of the context-switch layout of the switcher. *)
  Lemma resume_ok_full_eq (ws : list LWord) (v : resume_vals) :
    @resume_ok Σ MP ceriseb crit_link_full crit_route_full context_switch_layout_full ws v ↔
    resume_ok_full ws v.
  Proof. reflexivity. Qed.
End context_switch_layout_instance.

(** The word a Lea writes is [lea_word] of its source. *)
Lemma lea_result_lw (w w' : LWord) (z : Z) :
  lea_result w z = Some w' → w'.(lw) = lea_word w.(lw) z.
Proof.
  destruct w as [w π]. rewrite /lea_result /lea_word /=.
  intros Hres. destruct w as [| [ ] | | ]; repeat case_match; by simplify_eq.
Qed.

(** The resume PC of the save area [ws]: the saved mepcc, one word further
    after an [ecall], legalised. *)
Lemma resume_pc_word_install (ws : list LWord) :
  length ws = 21%nat →
  (get_a (save_area_word ws TrustedStack_offset_mcause).(lw) = MCAUSE_ECALL_MACHINE →
   legalise_pc (lea_word (save_area_word ws TrustedStack_offset_mepcc).(lw) 1) =
   resume_pc_word ws) ∧
  (get_a (save_area_word ws TrustedStack_offset_mcause).(lw) ≠ MCAUSE_ECALL_MACHINE →
   legalise_pc (save_area_word ws TrustedStack_offset_mepcc).(lw) = resume_pc_word ws).
Proof.
  intros _. rewrite /resume_pc_word. split; intros Hc.
  - by rewrite decide_True.
  - by rewrite decide_False.
Qed.

(** The save area of a thread, cell by cell. *)
Section save_area_cells.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}.

  (** A cell of the register save area of [o], other than its word
      [hazardPointers], read and given back. *)
  Lemma save_area_holed_cell (o : Thread) (ws : list LWord) (k : Z) :
    (0 ≤ k < TSTACK_REGFRAME_SZ)%Z →
    k ≠ TrustedStack_offset_hazardPointers →
    save_area_holed o ws ⊢
    (@b_trusted_stack (tlayout_of o) ^+ k)%a ↦ₐ save_area_word ws k ∗
    ((@b_trusted_stack (tlayout_of o) ^+ k)%a ↦ₐ save_area_word ws k -∗
     save_area_holed o ws).
  Proof.
    iIntros (Hk Hhaz) "Hsave".
    pose proof (trusted_stack_frames_fit (tlayout := tlayout_of o)) as [n Hfit].
    iDestruct (big_sepL2_length with "Hsave") as %Hlen.
    rewrite finz_seq_between_length /finz.dist in Hlen.
    rewrite /TSTACK_REGFRAME_SZ in Hk.
    assert (is_Some (ws !! Z.to_nat k)) as [w Hw].
    { apply lookup_lt_is_Some. rewrite -Hlen. tstack_unfold. solve_addr. }
    rewrite /save_area_word Hw /=.
    rewrite /save_area_holed.
    iDestruct (big_sepL2_lookup_acc _ _ _ (Z.to_nat k) with "Hsave") as "[Hw Hclose]";
      [|exact Hw|].
    { eapply finz_seq_between_lookup with (n := 21%nat); [lia | tstack_unfold; solve_addr]. }
    rewrite decide_False; last (rewrite /TrustedStack_offset_hazardPointers in Hhaz |- *; lia).
    rewrite (_ : (@b_trusted_stack (tlayout_of o) ^+ Z.to_nat k)%a =
                 (@b_trusted_stack (tlayout_of o) ^+ k)%a); last (f_equal; lia).
    iFrame "Hw". iExact "Hclose".
  Qed.

  (** The save area of [th], of a list of 21 words, cell by cell. *)
  Lemma save_area_holed_explicit (th : Thread)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : LWord) :
    save_area_holed th
      [w0; w1; w2; w3; w4; w5; w6; w7; w8; w9; w10; w11; w12; w13; w14; w15; w16; w17; w18;
       w19; w20] ⊣⊢
    @b_trusted_stack (tlayout_of th) ↦ₐ w0 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 1)%a ↦ₐ w1 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 2)%a ↦ₐ w2 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 3)%a ↦ₐ w3 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 4)%a ↦ₐ w4 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 5)%a ↦ₐ w5 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 6)%a ↦ₐ w6 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 7)%a ↦ₐ w7 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 8)%a ↦ₐ w8 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 9)%a ↦ₐ w9 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 10)%a ↦ₐ w10 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 11)%a ↦ₐ w11 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 12)%a ↦ₐ w12 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 13)%a ↦ₐ w13 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 14)%a ↦ₐ w14 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 15)%a ↦ₐ w15 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 17)%a ↦ₐ w17 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 18)%a ↦ₐ w18 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 19)%a ↦ₐ w19 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 20)%a ↦ₐ w20.
  Proof.
    pose proof (trusted_stack_frames_fit (tlayout := tlayout_of th)) as [n Hfit].
    rewrite /save_area_holed.
    etrans.
    { apply (big_sepL2_proper _
               (λ k _ w, if decide (k = Z.to_nat TrustedStack_offset_hazardPointers) then emp
                         else (@b_trusted_stack (tlayout_of th) ^+ (k : Z))%a ↦ₐ w)%I).
      intros k a w Ha Hw.
      pose proof (lookup_lt_Some _ _ _ Hw) as Hk. cbn [length] in Hk.
      rewrite (finz_seq_between_lookup _ _ k 21) in Ha; [|lia|tstack_unfold; solve_addr].
      by simplify_eq. }
    rewrite big_sepL2_const_sepL_r finz_seq_between_length /finz.dist.
    rewrite (_ : Z.to_nat TrustedStack_offset_hazardPointers = 16%nat); last done.
    cbn [length big_opL]. rewrite finz_add_0_default.
    repeat (case_decide; try (exfalso; lia)).
    iSplit.
    - iIntros "[_ ($ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & _ & $ & $ & $
                   & $ & _)]".
    - iIntros "($ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $)".
      iPureIntro. tstack_unfold. solve_addr.
  Qed.
End save_area_cells.
