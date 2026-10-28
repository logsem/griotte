From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode assembler.

Section Lea_To_Base.
  Import Asm_Griotte.
  Context
      {MP: MachineParameters}
  .

  Definition lea_to_base_asm (r r1 r2 : RegName) : list asm_code :=
    [
      getb r1 r;
      geta r2 r;
      sub r1 r1 r2;
      lea r r r1;
      mov r1 0;
      mov r2 0
    ].

  Definition lea_to_base (r r1 r2 : RegName) : list instr :=
    Eval compute in assemble (lea_to_base_asm r r1 r2).
  Lemma lea_to_base_assembles (r r1 r2 : RegName) :
    asm_ok (assemble_check (lea_to_base_asm r r1 r2)).
  Proof. asm_check. Qed.

  Definition lea_to_base_instrs (r r1 r2 : RegName) : list Word :=
    encodeInstrsW (lea_to_base r r1 r2).
End Lea_To_Base.

Section Lea_To_Base_spec.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ}
      {MP: MachineParameters}
  .

  Lemma lea_to_base_spec
    (r r1 r2 : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (w1 w2 : LWord)
    (t : bool) (p : Perm) (g : Locality) (b e a : Addr) (π : option AId)
    (φ : language.val griotte_lang → iPropI Σ) :

    let lea_to_base := (lea_to_base_instrs r r1 r2) in
    let a_last := (pc_a ^+ length lea_to_base) in
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a a_last →
    r ≠ cnull ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a
    ∗ ▷ r ↦ᵣ WCap t p g b e a @@? π
    ∗ ▷ r1 ↦ᵣ w1
    ∗ ▷ r2 ↦ᵣ w2
    ∗ ▷ codefrag_pers pc_a lea_to_base
    ∗ ▷ ( PC ↦ₚ Cap pc_p pc_g pc_b pc_e a_last
         ∗ r ↦ᵣ WCap t p g b e b @@? π
         ∗ r1 ↦ᵣ WInt 0%Z
         ∗ r2 ↦ᵣ WInt 0%Z
         ∗ codefrag_pers pc_a lea_to_base
         -∗ WP Exec {{ φ }}
        )
    ⊢ WP Exec {{ φ }}.
  Proof.
    intros lea_to_base a_last ; subst lea_to_base a_last.
    iIntros (Hvpc Hcont Hrcnull Hr1cnull Hr2cnull)
      "(>HPC & >Hr & >Hr1 & >Hr2 & >#Hprog & Hφ)".
    codefrag_facts "Hprog".
    rename H into HcontRegion; clear H0.
    assert ((a + (b - a))%a = Some b) as Hlea;[solve_addr|].
    iGo "Hprog".
    iApply "Hφ"; iFrame "∗ Hprog".
  Qed.

End Lea_To_Base_spec.
