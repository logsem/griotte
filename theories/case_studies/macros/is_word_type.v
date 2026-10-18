From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode assembler.

Section Is_WordType_Asm.
  Import Asm_Griotte.
  Context
      {MP: MachineParameters}
  .

  Definition is_word_type_asm (r r1 : RegName) (wtype : Word) : list asm_code :=
    [
      getwtype r1 r;
      sub r1 r1 (encodeWordType wtype);
      (* if getwtype(r) == wtype
         then r1 = 0
         then r1 != 0
       *)
      jnz 2 r1; (* r2 is zero, then continue, else jump to fail *)
      (* getwtype(r) == wtype *)
      jmp 2;
      (* getwtype(r) != wtype *)
      fail
    ].

  (** [encodeWordType] stays folded in the assembled code. *)
  Definition is_word_type (r r1 : RegName) (wtype : Word) : list instr :=
    Eval cbv -[encodeWordType word_encoding_mixin] in assemble (is_word_type_asm r r1 wtype).
  Lemma is_word_type_assembles (r r1 : RegName) (wtype : Word) :
    asm_ok (assemble_check (is_word_type_asm r r1 wtype)).
  Proof. asm_check. Qed.

  Definition is_int_asm (r r1 : RegName) : list asm_code :=
    is_word_type_asm r r1 wt_int.

  Definition is_memory_cap_asm (r r1 : RegName) : list asm_code :=
    is_word_type_asm r r1 wt_cap ++
    [gettag r1 r; sub r1 r1 1; jnz 2 r1; jmp 2; fail].
End Is_WordType_Asm.

Section Is_WordType.
  Context
      {MP: MachineParameters}
  .

  Definition is_word_type_instrs (r r1 : RegName) (wtype : Word) : list Word :=
    encodeInstrsW (is_word_type r r1 wtype).

  Definition is_int_instrs (r r1 : RegName) : list Word :=
   is_word_type_instrs r r1 wt_int.
  Definition is_memory_cap_instrs (r r1 : RegName) : list Word :=
   is_word_type_instrs r r1 wt_cap ++
   encodeInstrsW [GetTag r1 r; Sub r1 r1 1; Jnz 2 r1; Jmp 2; Fail].

  (** The code of [is_memory_cap_instrs], split for its proof, is its
      assembly. *)
  Lemma is_memory_cap_instrs_asm (r r1 : RegName) :
    is_memory_cap_instrs r r1 =
      encodeInstrsW (Asm_Griotte.assemble (is_memory_cap_asm r r1)).
  Proof. reflexivity. Qed.
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
    (w w1 : LWord) (wtype : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let is_int := (is_int_instrs r r1) in
    let a_last := (pc_a ^+ length is_int)%a in
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a a_last →
    r ≠ cnull ->
    r1 ≠ cnull ->

    ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a
    ∗ ▷ r ↦ᵣ w
    ∗ ▷ r1 ↦ᵣ w1
    ∗ ▷ codefrag_pers pc_a is_int
    ∗ ( ▷ ( ( PC ↦ₚ WCap true pc_p pc_g pc_b pc_e a_last
              ∗ r ↦ᵣ w ∗ ⌜ ∃ z, w.(lw) = WInt z ⌝
              ∗ r1 ↦ᵣ WInt 0%Z
              ∗ codefrag_pers pc_a is_int)
                -∗ WP Seq (Instr Executable) {{ φ }}
          ) ∧
        trap_ok ⊤ φ )
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    intros is_int a_last ; subst is_int a_last.
    iIntros (Hvpc Hcont Hrcnull Hr1cnull)
      "(>HPC & >Hr & >Hr1 & >#Hprog & Hk)".
    codefrag_facts "Hprog".
    rename H into HcontRegion; clear H0.
    destruct w as [w π].
    destruct (is_z w) eqn:Hw_z.
    - iDestruct "Hk" as "[Hφ _]".
      destruct w; cbn in *; try done.
      iInstr "Hprog".
      iInstr "Hprog".
      replace (encodeWordType (WInt z) - encodeWordType wt_int)%Z with 0%Z.
      2: { rewrite (encodeWordType_correct_int z 0) /wt_int; lia. }
      iGo "Hprog".
      iApply "Hφ"; iFrame "∗ Hprog".
      iPureIntro; eexists; done.
    - iDestruct "Hk" as "[_ Hfailed]".
      iGo "Hprog".
      { apply nonZero_WInt.
        pose proof (encodeWordType_correct w wt_int) as Hencode ; cbn in Hencode.
        intro H; injection H; intro Hcontra.
        destruct w as [| [] | |]; cbn in *; try done; try lia.
      }
      iGo "Hprog".
      iTrap.
  Qed.

  Lemma is_memory_cap_spec
    (r r1 : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (w w1 wtype : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let is_memory_cap := (is_memory_cap_instrs r r1) in
    let a_last := (pc_a ^+ length is_memory_cap)%a in
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a a_last →
    r ≠ cnull ->
    r1 ≠ cnull ->

    ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a
    ∗ ▷ r ↦ᵣ w
    ∗ ▷ r1 ↦ᵣ w1
    ∗ ▷ codefrag_pers pc_a is_memory_cap
    ∗ ▷ ( (∃ p g b e a,
            PC ↦ₚ WCap true pc_p pc_g pc_b pc_e a_last
            ∗ r ↦ᵣ WCap true p g b e a
            ∗ r1 ↦ᵣ WInt 0%Z
            ∗ codefrag_pers pc_a is_memory_cap)
              -∗ WP Seq (Instr Executable) {{ φ }}
        )
    ∗ trap_ok ⊤ φ
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    intros is_int a_last ; subst is_int a_last.
    iIntros (Hvpc Hcont Hrcnull Hr1cnull)
      "(>HPC & >Hr & >Hr1 & >#Hprog & Hφ & Hfailed)".
    codefrag_facts "Hprog".
    rename H into HcontRegion; clear H0.
    destruct (is_cap w) eqn:Hw_cap.
    - destruct_word w; cbn in *; try done.
      iInstr "Hprog".
      iInstr "Hprog".
      replace (encodeWordType (WCap t c g b e a) - encodeWordType wt_cap)%Z with 0%Z.
      2: { rewrite (encodeWordType_correct_cap t c g b e a true (O LG LM) Global 0%a 0%a 0%a) /wt_cap; lia. }
      destruct t; cbn.
      + (* Jnz 2 r1. *)
        iInstr "Hprog".
        (* Jmp 2. *)
        iInstr "Hprog".
        (* GetTag r1 r: the tag of the word may read as 0. *)
        iInstrApply "Hprog" wp_gettag_lax with "[$HPC $Hr $Hr1]"
          as (z) "(HPC & Hr & Hr1 & %Hz)".
        destruct Hz; destruct_and?; simplify_eq.
        * cbn. iGo "Hprog". iApply "Hφ"; iFrame "∗ Hprog".
        * iGo "Hprog". iTrap.
      + iGo "Hprog". iTrap.
    - iGo "Hprog".
      { apply nonZero_WInt.
        pose proof (encodeWordType_correct w wt_cap) as Hencode ; cbn in Hencode.
        intro H; injection H; intro Hcontra.
        destruct w as [| [] | |]; cbn in *; try done; try lia.
      }
      iGo "Hprog".
      iTrap.
  Qed.

End Is_WordType_spec.
