From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules proofmode.
From cap_machine Require Export fetch.

Section Fetch.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ}
      {MP: MachineParameters}
  .
  Lemma fetch_spec
    (n : Z) (rdst rscratch1 rscratch2 : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (wentry wdst w1 w2 : Word)
    (φ : language.val cap_lang → iPropI Σ) :

    let fetch_ := (fetch_instrs n rdst rscratch1 rscratch2) in
    let a_last := (pc_a ^+ length fetch_)%a in
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a a_last →
    withinBounds pc_b pc_e (pc_b ^+ n)%a = true ->

    ▷ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
    ∗ ▷ rdst ↦ᵣ wdst
    ∗ ▷ rscratch1 ↦ᵣ w1
    ∗ ▷ rscratch2 ↦ᵣ w2
    ∗ ▷ codefrag pc_a fetch_
    ∗ ▷ (pc_b ^+ n)%a ↦ₐ wentry
    ∗ ▷ (PC ↦ᵣ WCap pc_p pc_g pc_b pc_e a_last
         ∗ rdst ↦ᵣ load_word pc_p wentry
         ∗ rscratch1 ↦ᵣ WInt 0%Z
         ∗ rscratch2 ↦ᵣ WInt 0%Z
         ∗ codefrag pc_a fetch_
         ∗ (pc_b ^+ n)%a ↦ₐ wentry
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    intros fetch a_last ; subst fetch a_last.
    iIntros (Hvpc Hcont Hpc_n)
      "(>HPC & >Hrdst & >Hrscratch1 & >Hrscratch2 & >Hprog & >Hpc_bn & Hφ)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    codefrag_facts "Hprog".
    rename H into HcontRegion; clear H0.
    assert ((pc_a + (pc_b - pc_a))%a = Some pc_b) as Hlea;[solve_addr|].
    assert ((pc_b + n)%a = Some (pc_b ^+ n)%a) as Hpc_bn;[solve_addr|].
    iGo "Hprog".
    iApply "Hφ"; iFrame.
  Qed.

End Fetch.
