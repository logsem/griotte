From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules proofmode.

Section Is_WordType.
  Context
      {MP: MachineParameters}
  .

  Definition is_word_type_instrs (r r1 : RegName) (wtype : Word) : list Word :=
    encodeInstrsW [
        GetWType r1 r;
        Sub r1 r1 (encodeWordType wtype);
        (* if getwtype(r) == wtype
           then r1 = 0
           then r1 != 0
         *)
        Jnz 2 r1; (* r2 is zero, then continue, else jump to fail *)
        (* getwtype(r) == wtype *)
        Jmp 2;
        (* getwtype(r) != wtype *)
        Fail
      ].

  Definition is_int_instrs (r r1 : RegName) : list Word :=
   is_word_type_instrs r r1 wt_int.
  Definition is_memory_cap_instrs (r r1 : RegName) : list Word :=
   is_word_type_instrs r r1 wt_cap.
End Is_WordType.

Section Is_WordType_spec.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ}
      {MP: MachineParameters}
  .

  Lemma is_int_spec
    (r r1 : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (w w1 wtype : Word)
    (φ : language.val cap_lang → iPropI Σ) :

    let is_int := (is_int_instrs r r1) in
    let a_last := (pc_a ^+ length is_int)%a in
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a a_last →
    r ≠ cnull ->
    r1 ≠ cnull ->

    ▷ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
    ∗ ▷ r ↦ᵣ w
    ∗ ▷ r1 ↦ᵣ w1
    ∗ ▷ codefrag pc_a is_int
    ∗ ▷ ( ( PC ↦ᵣ WCap pc_p pc_g pc_b pc_e a_last
            ∗ r ↦ᵣ w ∗ ⌜ ∃ z, w = WInt z ⌝
            ∗ r1 ↦ᵣ WInt 0%Z
            ∗ codefrag pc_a is_int)
              -∗ WP Seq (Instr Executable) {{ φ }}
        )
    ∗ ▷ φ FailedV
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    intros is_int a_last ; subst is_int a_last.
    iIntros (Hvpc Hcont Hrcnull Hr1cnull)
      "(>HPC & >Hr & >Hr1 & >Hprog & Hφ & Hfailed)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    codefrag_facts "Hprog".
    rename H into HcontRegion; clear H0.
    destruct (is_z w) eqn:Hw_z.
    - destruct w; cbn in *; try done.
      iInstr "Hprog".
      iInstr "Hprog".
      replace (encodeWordType (WInt z) - encodeWordType wt_int)%Z with 0%Z.
      2: { rewrite (encodeWordType_correct_int z 0) /wt_int; lia. }
      iGo "Hprog".
      iApply "Hφ"; iFrame.
      iPureIntro; eexists; done.
    - iGo "Hprog".
      { apply getwtype_denote. }
      assert (WInt (encodeWordType w - encodeWordType wt_int) ≠ WInt 0).
      { pose proof (encodeWordType_correct w wt_int) as Hencode ; cbn in Hencode.
        intro H; injection H; intro Hcontra.
        destruct w as [| [] | |]; cbn in *; try done; try lia.
      }
      iGo "Hprog".
      wp_end; iApply "Hfailed".
  Qed.

  Lemma is_memory_cap_spec
    (r r1 : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (w w1 wtype : Word)
    (φ : language.val cap_lang → iPropI Σ) :

    let is_memory_cap := (is_memory_cap_instrs r r1) in
    let a_last := (pc_a ^+ length is_memory_cap)%a in
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a a_last →
    r ≠ cnull ->
    r1 ≠ cnull ->

    ▷ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
    ∗ ▷ r ↦ᵣ w
    ∗ ▷ r1 ↦ᵣ w1
    ∗ ▷ codefrag pc_a is_memory_cap
    ∗ ▷ ( (∃ p g b e a,
            PC ↦ᵣ WCap pc_p pc_g pc_b pc_e a_last
            ∗ r ↦ᵣ WCap p g b e a
            ∗ r1 ↦ᵣ WInt 0%Z
            ∗ codefrag pc_a is_memory_cap)
              -∗ WP Seq (Instr Executable) {{ φ }}
        )
    ∗ ▷ φ FailedV
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    intros is_int a_last ; subst is_int a_last.
    iIntros (Hvpc Hcont Hrcnull Hr1cnull)
      "(>HPC & >Hr & >Hr1 & >Hprog & Hφ & Hfailed)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    codefrag_facts "Hprog".
    rename H into HcontRegion; clear H0.
    destruct (is_cap w) eqn:Hw_cap.
    - destruct_word w; cbn in *; try done.
      iInstr "Hprog".
      iInstr "Hprog".
      replace (encodeWordType (WCap c g b e a) - encodeWordType wt_cap)%Z with 0%Z.
      2: { rewrite (encodeWordType_correct_cap c g b e a (O LG LM) Global 0%a 0%a 0%a) /wt_cap; lia. }
      iGo "Hprog".
      iApply "Hφ"; iFrame.
    - iGo "Hprog".
      { apply getwtype_denote. }
      assert (WInt (encodeWordType w - encodeWordType wt_cap) ≠ WInt 0).
      { pose proof (encodeWordType_correct w wt_cap) as Hencode ; cbn in Hencode.
        intro H; injection H; intro Hcontra.
        destruct w as [| [] | |]; cbn in *; try done; try lia.
      }
      iGo "Hprog".
      wp_end; iApply "Hfailed".
  Qed.

End Is_WordType_spec.
