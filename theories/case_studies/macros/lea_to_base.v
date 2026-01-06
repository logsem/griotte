From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules proofmode.

Section Lea_To_Base.
  Context
      {MP: MachineParameters}
  .

  Definition lea_to_base_instrs (r r1 r2 : RegName) : list Word :=
    encodeInstrsW [
        GetB r1 r;
        GetA r2 r;
        Sub r1 r1 r2;
        Lea r r1;
        Mov r1 0;
        Mov r2 0
      ].

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
    (w1 w2 : Word)
    (p : Perm) (g : Locality) (b e a : Addr)
    (φ : language.val cap_lang → iPropI Σ) :

    let lea_to_base := (lea_to_base_instrs r r1 r2) in
    let a_last := (pc_a ^+ length lea_to_base)%a in
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a a_last →
    r ≠ cnull ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    ▷ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
    ∗ ▷ r ↦ᵣ WCap p g b e a
    ∗ ▷ r1 ↦ᵣ w1
    ∗ ▷ r2 ↦ᵣ w2
    ∗ ▷ codefrag pc_a lea_to_base
    ∗ ▷ ( PC ↦ᵣ WCap pc_p pc_g pc_b pc_e a_last
         ∗ r ↦ᵣ WCap p g b e b
         ∗ r1 ↦ᵣ WInt 0%Z
         ∗ r2 ↦ᵣ WInt 0%Z
         ∗ codefrag pc_a lea_to_base
         -∗ WP Seq (Instr Executable) {{ φ }}
        )
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    intros lea_to_base a_last ; subst lea_to_base a_last.
    iIntros (Hvpc Hcont Hrcnull Hr1cnull Hr2cnull)
      "(>HPC & >Hr & >Hr1 & >Hr2 & >Hprog & Hφ)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    codefrag_facts "Hprog".
    rename H into HcontRegion; clear H0.
    assert ((a + (b - a))%a = Some b) as Hlea;[solve_addr|].
    iGo "Hprog".
    iApply "Hφ"; iFrame.
  Qed.

End Lea_To_Base_spec.
