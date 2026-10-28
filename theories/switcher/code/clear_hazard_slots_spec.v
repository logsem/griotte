From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Export switcher.

(** * Specification of [clear_hazard_slots_asm]

    The specification of the macro [clear_hazard_slots_asm] (CHERIoT's
    [clear_hazard_slots]), for any trusted stack: [ts] holds a capability to
    it, whose word [hazardPointers] holds the store-only capability to the
    two hazard slots. Both slots end up cleared, and [scratch] holds the
    capability to them. *)

Section ClearHazardSlots.
  Context {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}.

  Lemma clear_hazard_slots_instrs_length ts scratch :
    length (clear_hazard_slots_instrs ts scratch) = 3%nat.
  Proof. done. Qed.

  Lemma clear_hazard_slots_spec (E : coPset)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (ts scratch : RegName) (g : Locality) (b e a : Addr) (b_hz e_hz : Addr)
    (wscratch : LWord) (ws : list LWord) φ :
    let a_hz := (a ^+ TrustedStack_offset_hazardPointers) in
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (clear_hazard_slots_instrs ts scratch)) ->
    (a + TrustedStack_offset_hazardPointers)%a = Some a_hz ->
    withinBounds b e a_hz = true ->
    is_shadow_address a_hz = false ->
    (b_hz + 2)%a = Some e_hz ->
    disjoint_from_shadow b_hz e_hz ->
    not_heap_range b_hz e_hz ->
    ts ≠ scratch ->
    ts ≠ cnull ->
    scratch ≠ cnull ->

    PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a ∗
    ts ↦ᵣ Cap RWL g b e a ∗
    scratch ↦ᵣ wscratch ∗
    a_hz ↦ₐ Cap WO Global b_hz e_hz b_hz ∗
    [[ b_hz, e_hz ]] ↦ₐ [[ ws ]] ∗
    codefrag_pers pc_a (clear_hazard_slots_instrs ts scratch) ∗
    ▷ ( PC ↦ₚ Cap pc_p pc_g pc_b pc_e
            (pc_a ^+ length (clear_hazard_slots_instrs ts scratch)) ∗
        ts ↦ᵣ Cap RWL g b e a ∗
        scratch ↦ᵣ Cap WO Global b_hz e_hz b_hz ∗
        a_hz ↦ₐ Cap WO Global b_hz e_hz b_hz ∗
        [[ b_hz , e_hz ]] ↦ₐ [[ 0…0 ]] -∗
        WP Exec @ E {{ φ }} )
    ⊢ WP Exec @ E {{ φ }}.
  Proof.
    intros a_hz; subst a_hz.
    iIntros (Hx Hbounds Ha_hz Hhz_bounds Hhz_shadow Hhz_size Hhz_slots_shadow Hhz_heap
             Hts_scratch Hts_cnull Hscratch_cnull)
      "(HPC & Hts & Hscratch & Hcell & Hslots & #Hcode & Hpost)".
    codefrag_facts "Hcode".
    iEval (rewrite /clear_hazard_slots_instrs /clear_hazard_slots) in "Hcode".
    (* CLoad scratch ts TrustedStack_offset_hazardPointers *)
    iInstr "Hcode".
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= (proj1 Hhz_heap) //. }
    { split; auto. }
    rewrite lload_word_RWL.
    iDestruct (big_sepL2_length with "Hslots") as %Hlen.
    rewrite finz_seq_between_length /finz.dist in Hlen.
    destruct ws as [|w0 [|w1 [|w2 ws] ] ]; cbn in Hlen; try (exfalso; solve_addr).
    iRegionSplit "Hslots" as "Hslots".
    iDestruct "Hslots" as "[Hw0 Hw1]".
    (* Store scratch 0 0 *)
    iInstr "Hcode".
    { eapply disjoint_from_shadow_not_in; [exact Hhz_slots_shadow | rewrite /withinBounds; solve_addr]. }
    { rewrite /withinBounds; solve_addr. }
    assert ((b_hz + 1)%a = Some (b_hz ^+ 1)) as Hhz_1 by solve_addr.
    (* Store scratch 0 1 *)
    iInstr "Hcode".
    { eapply disjoint_from_shadow_not_in; [exact Hhz_slots_shadow | rewrite /withinBounds; solve_addr]. }
    { rewrite /withinBounds; solve_addr. }
    iApply "Hpost".
    iFrame "HPC Hts Hscratch Hcell".
    rewrite /region_addrs_zeroes /finz.dist Hlen /=.
    iRegionMerge.
    iFrame "Hw0 Hw1".
  Qed.

  (** The code of the macro, at [i] in the code [l] of a block. *)
  Lemma codefrag_pers_clear_hazard_slots (a : Addr) (l : list Word) (i : nat) ts scratch :
    take 3 (drop i l) = clear_hazard_slots_instrs ts scratch →
    (i + 3 <= length l)%nat →
    codefrag_pers a l -∗ codefrag_pers (a ^+ i) (clear_hazard_slots_instrs ts scratch).
  Proof.
    iIntros (Hl Hlen) "Hcode".
    rewrite -{1}(take_drop i l) -{1}(take_drop 3 (drop i l)) Hl.
    iDestruct (codefrag_app_pers with "Hcode") as "[_ Hcode]".
    iDestruct (codefrag_app_pers with "Hcode") as "[Hcode _]".
    rewrite length_take_le; last lia.
    iExact "Hcode".
  Qed.

End ClearHazardSlots.
