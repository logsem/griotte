From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte Require Export fetch.

Section Fetch.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ}
      {MP: MachineParameters}
  .
  Lemma fetch_spec
    (n off : Z) (rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (wentry : Word) (wdst : LWord) (dq : dfrac)
    (φ : language.val griotte_lang → iPropI Σ) :

    let fetch_ := (fetch_instrs off rdst) in
    let a_last := (pc_a ^+ length fetch_)%a in
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a a_last →
    (pc_a + off)%a = Some (pc_b ^+ n)%a ->
    withinBounds pc_b pc_e (pc_b ^+ n)%a = true ->
    disjoint_from_shadow pc_b pc_e →
    is_heap_cap wentry = false →
    rdst ≠ cnull ->

    ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a
    ∗ ▷ rdst ↦ᵣ wdst
    ∗ ▷ codefrag_pers pc_a fetch_
    ∗ ▷ (pc_b ^+ n)%a ↦ₐ{dq} wentry
    ∗ ▷ (PC ↦ₚ WCap true pc_p pc_g pc_b pc_e a_last
         ∗ rdst ↦ᵣ load_word pc_p wentry
         ∗ codefrag_pers pc_a fetch_
         ∗ (pc_b ^+ n)%a ↦ₐ{dq} wentry
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    intros fetch a_last ; subst fetch a_last.
    iIntros (Hvpc Hcont Hoff Hpc_n Hdisjoint Hnonheap Hrdst)
      "(>HPC & >Hrdst & >#Hprog & >Hpc_bn & Hφ)".
    codefrag_facts "Hprog".
    assert (is_shadow_address (pc_b ^+ n)%a = false) as Hshadow.
    { eapply disjoint_from_shadow_not_in; eauto. }
    (* Auipcc rdst off. *)
    iInstr "Hprog".
    (* CLoad rdst rdst 0. *)
    iInstr "Hprog".
    iApply "Hφ"; iFrame "∗ Hprog".
  Qed.

End Fetch.
