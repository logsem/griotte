From iris.proofmode Require Import proofmode.
From griotte Require Export memory_region rules_hwm.

(** * Stack cells

    A cell of a stack is either a full points-to or a cell of the zone of the
    stack high-water mark, which holds 0. *)

Section stack_cells.
  Context `{MP: MachineParameters} `{ceriseg: ceriseG Σ}.

  (** A cell of a stack at [a] holding [w]. *)
  Definition stack_cell (a : Addr) (w : LWord) : iProp Σ :=
    (a ↦ₐ w ∨ (zone_cell a ∗ ⌜w = lword_of_word (WInt 0)⌝))%I.

  (** The cells of the stack region [[b, e)], holding [ws]. *)
  Definition stack_region (b e : Addr) (ws : list LWord) : iProp Σ :=
    [∗ list] a; w ∈ finz.seq_between b e; ws, stack_cell a w.

  (** The two high-water-mark registers, with their values. *)
  Definition hwm_regs (hb h : Z) : iProp Σ :=
    mshwmb ↦ₜ hb ∗ mshwm ↦ₜ h.

  #[global] Instance stack_cell_timeless a w : Timeless (stack_cell a w).
  Proof. apply _. Qed.

  #[global] Instance stack_region_timeless b e ws : Timeless (stack_region b e ws).
  Proof. apply _. Qed.

  Lemma stack_cell_of_pointsto a w : a ↦ₐ w -∗ stack_cell a w.
  Proof. iIntros "Ha". by iLeft. Qed.

  Lemma stack_cell_of_zone a : zone_cell a -∗ stack_cell a (lword_of_word (WInt 0)).
  Proof. iIntros "Ha". iRight. by iFrame. Qed.

  (** A stack cell gives half of the points-to of its address, enough to load
      from it, and gets it back. *)
  Lemma stack_cell_half a w :
    stack_cell a w -∗
    a ↦ₐ{DfracOwn (1/2)} w ∗ (a ↦ₐ{DfracOwn (1/2)} w -∗ stack_cell a w).
  Proof.
    iIntros "[[Ha1 Ha2] | [Hcell ->]]".
    - iFrame "Ha1". iIntros "Ha1". iLeft. by iCombine "Ha1 Ha2" as "Ha".
    - iDestruct (zone_cell_unfold with "Hcell") as "[Htok $]".
      iIntros "Hhalf". iRight. iSplit; last done.
      rewrite zone_cell_unfold. iFrame.
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

End stack_cells.
