From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte Require Export setbounds.

(** Specifications of the [setbounds_asm] macro: the destination gets the
    bounds [[a, a + n)] of its source's address [a]. *)

Section Setbounds_spec.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ}
      {MP: MachineParameters}
      {th : Thread} {CL : CritLink Σ th} {CR : CritRoute Σ th CL}
  .

  (** [setbounds_asm r r n t1 t2] (the destination is the source, as in
      the compiled code): [r] gets the bounds [[a, a + n)], when they are
      within its bounds. A source without identifier must not have a heap
      address (a sufficient condition for [Subseg]'s new tag; heap roots
      are not covered). *)
  Lemma setbounds_same_spec
    (r t1 t2 : RegName) (n : Z)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (p : Perm) (g : Locality) (b e a a_n : Addr) (π : option AId)
    (w1 w2 : LWord)
    (φ : tval (kind_of th) → iPropI Σ) :

    let setbounds := (setbounds_instrs r r n t1 t2) in
    let a_last := (pc_a ^+ length setbounds) in
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a a_last →
    (a + n)%a = Some a_n →
    (b <= a)%a →
    (0 ≤ n)%Z →
    (a_n <= e)%a →
    (π = None → is_heap_address a = false) →
    r ≠ cnull → t1 ≠ cnull → t2 ≠ cnull →

    ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a ∗
    ▷ r ↦ᵣ (Cap p g b e a @@? π) ∗
    ▷ t1 ↦ᵣ w1 ∗
    ▷ t2 ↦ᵣ w2 ∗
    ▷ codefrag_pers pc_a setbounds ∗
    ▷ (PC ↦ₚ Cap pc_p pc_g pc_b pc_e a_last ∗
       r ↦ᵣ (Cap p g a a_n a @@? π) ∗
       t1 ↦ᵣ WInt (finz.to_z a) ∗
       t2 ↦ᵣ WInt (finz.to_z a_n) ∗
       codefrag_pers pc_a setbounds -∗
       WP Exec {{ φ }})
    ⊢ WP Exec {{ φ }}.
  Proof.
    intros setbounds a_last; subst setbounds a_last.
    iIntros (Hvpc Hcont Ha_n Hb Hn He Hroot Hr Ht1 Ht2)
      "(>HPC & >Hr & >Ht1 & >Ht2 & >#Hprog & Hφ)".
    codefrag_facts "Hprog".
    (* GetA t1 r. *)
    iInstr "Hprog".
    (* Add t2 t1 n. *)
    iInstr "Hprog".
    (* Subseg r r t1 t2. *)
    iInstr "Hprog".
    1: { instantiate (1 := a_n); solve_addr. }
    1: { rewrite /isWithin; solve_addr. }
    1: { solve_addr. }
    1: { intros Hπ _; exact (Hroot Hπ). }
    replace (a + n)%Z with (finz.to_z a_n) by solve_addr.
    iApply "Hφ"; iFrame "∗ Hprog".
  Qed.

  (** [setbounds_asm r s n t1 t2], with a destination [r] other than the
      source [s] and than the scratch registers: [r] gets [s] with the
      bounds [[a, a + n)], and [s] is unchanged. *)
  Lemma setbounds_spec
    (r s t1 t2 : RegName) (n : Z)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (p : Perm) (g : Locality) (b e a a_n : Addr) (π : option AId)
    (wr w1 w2 : LWord)
    (φ : tval (kind_of th) → iPropI Σ) :

    let setbounds := (setbounds_instrs r s n t1 t2) in
    let a_last := (pc_a ^+ length setbounds) in
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a a_last →
    (a + n)%a = Some a_n →
    (b <= a)%a →
    (0 ≤ n)%Z →
    (a_n <= e)%a →
    (π = None → is_heap_address a = false) →
    r ≠ cnull → s ≠ cnull → t1 ≠ cnull → t2 ≠ cnull →

    ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a ∗
    ▷ s ↦ᵣ (Cap p g b e a @@? π) ∗
    ▷ r ↦ᵣ wr ∗
    ▷ t1 ↦ᵣ w1 ∗
    ▷ t2 ↦ᵣ w2 ∗
    ▷ codefrag_pers pc_a setbounds ∗
    ▷ (PC ↦ₚ Cap pc_p pc_g pc_b pc_e a_last ∗
       s ↦ᵣ (Cap p g b e a @@? π) ∗
       r ↦ᵣ (Cap p g a a_n a @@? π) ∗
       t1 ↦ᵣ WInt (finz.to_z a) ∗
       t2 ↦ᵣ WInt (finz.to_z a_n) ∗
       codefrag_pers pc_a setbounds -∗
       WP Exec {{ φ }})
    ⊢ WP Exec {{ φ }}.
  Proof.
    intros setbounds a_last; subst setbounds a_last.
    iIntros (Hvpc Hcont Ha_n Hb Hn He Hroot Hr Hs Ht1 Ht2)
      "(>HPC & >Hs & >Hr & >Ht1 & >Ht2 & >#Hprog & Hφ)".
    codefrag_facts "Hprog".
    (* GetA t1 s. *)
    iInstr "Hprog".
    (* Add t2 t1 n. *)
    iInstr "Hprog".
    (* Subseg r s t1 t2. *)
    iInstr "Hprog".
    1: { instantiate (1 := a_n); solve_addr. }
    1: { rewrite /isWithin; solve_addr. }
    1: { solve_addr. }
    1: { intros Hπ _; exact (Hroot Hπ). }
    replace (a + n)%Z with (finz.to_z a_n) by solve_addr.
    iApply "Hφ"; iFrame "∗ Hprog".
  Qed.

End Setbounds_spec.
