From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte Require Import switcher_preamble handoff switcher_link.
From griotte Require Import context_switching_support.

(** * The tail of the exit path

    The exit path of the context-switch thread installs, in the MEPCC of an
    exited thread, the PCC of the last two words of the switcher, a loop
    that waits for interrupts. [exited_set_spec] is the setter of that
    MEPCC, [exited_safe] the safety of the exited thread from that PCC. *)

Section ctx_exit_tail.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}.

  (** The PCC of an exited thread: execute and load over the two words of
      its body. *)
  Definition exited_thread_pcc : Word := Cap RX Local a_tail (a_tail ^+ 2)%a a_tail.

  (** The setter, at the context-switch thread with interrupts disabled:
      MEPCC receives the PCC of an exited thread; only [csp] and [ca0]
      change. *)
  Definition exited_set_spec : iProp Σ :=
    ∀ (wcsp wca0 wm : LWord) (Φ : tval CtxK → iProp Σ),
      PC ↦ₚ[CtxSwitch] lword_of_word (Cap XSRW_ Local b_switcher e_switcher a_exit_set) -∗
      switcher_code_at CtxSwitch -∗
      MIE ↦ₜ[CtxSwitch] InterruptDisabled -∗
      csp ↦ᵣ[CtxSwitch] wcsp -∗
      ca0 ↦ᵣ[CtxSwitch] wca0 -∗
      mepcc ↦ₓ wm -∗
      ▷ (∀ wcsp' wca0' : LWord,
           PC ↦ₚ[CtxSwitch] switcher_label_pc ".Lcommon_thread_exit_clear" -∗
           MIE ↦ₜ[CtxSwitch] InterruptDisabled -∗
           csp ↦ᵣ[CtxSwitch] wcsp' -∗
           ca0 ↦ᵣ[CtxSwitch] wca0' -∗
           mepcc ↦ₓ lword_of_word exited_thread_pcc -∗
           WP Exec @[CtxSwitch] {{ Φ }}) -∗
      WP Exec @[CtxSwitch] {{ Φ }}.

  (** An exited thread resumed at its PCC runs safely from the fragments
      its park sets, and its posture when it resumes with interrupts
      disabled: no mtdc fragment, no pool token, no world. *)
  Definition exited_safe (t : nat) : iProp Σ :=
    ∀ (b : InterruptStatus) (lreg : LReg),
      ⌜dom lreg = all_registers_s⌝ -∗
      PC ↦ₚ[u t] lword_of_word exited_thread_pcc -∗
      MIE ↦ₜ[u t] b -∗
      regs[u t] lreg -∗
      (if b is InterruptEnabled then True
       else posture_res_gen (ceriseg := ceriseG_of (UserThread t)) (th := UserThread t)
              None None None None) -∗
      safe[u t].

  (** The body of an exited thread is the last two words of the switcher. *)
  Lemma a_tail_last : (a_tail + 2)%a = Some e_switcher.
  Proof.
    pose proof a_tail_label as Hlabel.
    pose proof switcher_size as Hsize.
    rewrite switcher_offset_tail_eq in Hlabel.
    (* The length of the code, without encoding its instructions. *)
    assert (length switcher_instrs = sum_list (length <$> assembled_switcher)) as Hlen.
    { rewrite /switcher_instrs length_concat.
      change (encodeInstrsW <$> assembled_switcher) with (map encodeInstrsW assembled_switcher).
      rewrite map_map (map_ext _ length); last (intros l; by rewrite /encodeInstrsW length_fmap).
      reflexivity. }
    assert (sum_list (length <$> assembled_switcher) = Z.to_nat (switcher_offset_tail + 2))
      as Hn by (vm_compute; reflexivity).
    rewrite Hlen Hn in Hsize.
    clear - Hsize Hlabel.
    rewrite /switcher_offset_tail in Hlabel Hsize |- *.
    solve_addr.
  Qed.

  (** The PCC of an exited thread is a legal PC. *)
  Lemma exited_thread_pcc_legal : legalise_pc exited_thread_pcc = exited_thread_pcc.
  Proof. apply legalise_pc_ok_id. done. Qed.

  (** The writes of the exit path to mtval and MEPCC keep their values. *)
  Lemma legalise_mtval_exit : legalise mtval (WInt MCAUSE_THREAD_EXIT) = WInt MCAUSE_THREAD_EXIT.
  Proof. reflexivity. Qed.

  (** The body of an exited thread, [wfi; jmp], runs safely from either of
      its two instructions, at any MIE and from any registers: no mtdc
      fragment, no pool token, no world. *)
  Lemma exited_tail_safe (t : nat) :
    switcher_code_at (UserThread t) ⊢
    ∀ (a : Addr) (b : InterruptStatus) (lreg : LReg),
      ⌜a = a_tail ∨ a = (a_tail ^+ 1)%a⌝ -∗
      ⌜dom lreg = all_registers_s⌝ -∗
      PC ↦ₚ[u t] lword_of_word (Cap RX Local a_tail (a_tail ^+ 2)%a a) -∗
      MIE ↦ₜ[u t] b -∗
      regs[u t] lreg -∗
      (if b is InterruptEnabled then True
       else posture_res_gen (ceriseg := ceriseG_of (UserThread t)) (th := UserThread t)
              None None None None) -∗
      safe[u t].
  Proof.
    pin_thread_instances (UserThread t).
    pose proof a_tail_last as Hlast.
    iIntros "#Hswitcher".
    iLöb as "IH".
    iIntros (a b lreg Ha Hdom) "HPC HMIE Hregs Hpost".
    switcher_open_label ".Lexited_thread" "Hswitcher" as "Hcode" a_block Heq_block.
    assert (a_block = a_tail) as ->.
    { pose proof a_tail_label as Hlabel. subst a_block. clear - Hlabel.
      offsets_compute. solve_addr. }
    destruct Ha as [-> | ->].
    - assert (is_Some (lreg !! cnull)) as [wnull Hnull].
      { apply elem_of_dom. rewrite Hdom. apply all_registers_s_correct. }
      iDestruct (big_sepM_delete with "Hregs") as "[Hnull Hregs]"; first exact Hnull.
      (* Mov cnull 0. *)
      iInstr "Hcode".
      iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[u t] y)%I with "[$Hnull $Hregs]") as "Hregs";
        first exact Hnull.
      iApply ("IH" $! (a_tail ^+ 1)%a with "[] [] HPC HMIE Hregs Hpost").
      { iPureIntro. by right. }
      { done. }
    - (* Jmp -1. *)
      iInstr "Hcode".
      { transitivity (Some a_tail); [solve_addr | reflexivity]. }
      iApply ("IH" $! a_tail with "[] [] HPC HMIE Hregs Hpost").
      { iPureIntro. by left. }
      { done. }
  Qed.

  Lemma exited_safe_holds (t : nat) : switcher_code_at (UserThread t) ⊢ exited_safe t.
  Proof.
    iIntros "#Hswitcher" (b lreg Hdom) "HPC HMIE Hregs Hpost".
    iApply (exited_tail_safe t with "Hswitcher [] [//] HPC HMIE Hregs Hpost").
    by iLeft.
  Qed.

  (** The bound [a2] of [Subseg], by name. *)
  #[local] Arguments subseg_next_ok_cap_base {MP pl lpc regs dst ρ2 t p g b e a π n2 a2}
    _ _ _ _ _ _%_function_scope.

  Lemma exited_set_spec_holds : switcher_code_at CtxSwitch ⊢ exited_set_spec.
  Proof.
    pin_thread_instances CtxSwitch.
    pose proof a_tail_last as Hlast.
    assert ((b_switcher <= a_tail)%a) as Hb_tail.
    { pose proof a_tail_label as Hlabel. pose proof switcher_call_entry_point as Hcall.
      pose proof switcher_size as Hsize. clear - Hlabel Hcall Hsize.
      offsets_compute. solve_addr. }
    iIntros "_" (wcsp wca0 wm Φ) "HPC #Hswitcher HMIE Hcsp Hca0 Hmepcc Hpost".
    switcher_open_label ".Lcommon_thread_exit_set_mepcc" "Hswitcher" as "Hcode"
      a_block Heq_block.
    assert (a_exit_set = a_block) as Hset.
    { pose proof a_exit_set_label as Hlabel. subst a_block. clear - Hlabel.
      offsets_compute. solve_addr. }
    iEval (rewrite Hset) in "HPC".
    (* Auipcc csp .Lexited_thread. *)
    iInstr "Hcode".
    { transitivity (Some a_tail); [| reflexivity].
      pose proof a_tail_label as Hlabel. subst a_block. clear - Hlabel.
      offsets_compute. solve_addr. }
    (* GetA ca0 csp. *)
    iInstr "Hcode".
    (* Add ca0 ca0 2. *)
    iInstr "Hcode".
    (* Subseg csp csp csp ca0. *)
    iInstr "Hcode" using (subseg_next_ok_cap_base (a2 := (a_tail ^+ 2)%a)).
    { solve_addr. }
    { rewrite /isWithin. apply andb_true_iff; split; apply Z.leb_le; solve_addr. }
    { solve_addr. }
    { intros _ _. apply (disjoint_from_heap_not_in b_switcher e_switcher).
      - exact (proj2 switcher_not_heap_range).
      - apply withinBounds_true_iff. solve_addr. }
    (* Mov ca0 EXITED_THREAD_PERMISSIONS. *)
    iInstr "Hcode".
    (* Restrict csp csp ca0. *)
    iInstr "Hcode".
    { rewrite decode_encode_permPair_inv. reflexivity. }
    { reflexivity. }
    { reflexivity. }
    (* SpecialRW cnull mepcc csp. *)
    iInstr "Hcode".
    iEval (fold exited_thread_pcc; rewrite /legalise exited_thread_pcc_legal) in "Hmepcc".
    switcher_change_pc_label ".Lcommon_thread_exit_clear".
    iApply ("Hpost" with "HPC HMIE Hcsp Hca0 Hmepcc").
  Qed.

End ctx_exit_tail.
