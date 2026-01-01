From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules proofmode.
From cap_machine Require Import is_word_type lea_to_base.

Section Checkints.
  Context
      {MP: MachineParameters}
  .


  Definition checkints_loop_instrs (r r1 r2 : RegName) : list Word :=
    encodeInstrsW [Load r1 r]
      ++ is_int_instrs r1 r2
      ++ encodeInstrsW
      [ (* is an integer *)
        GetA r1 r;
        machine_base.Add r1 r1 1;
        GetE r2 r;
        Lt r1 r1 r2;
        (* if r1 -> 0 then a + 1 >= e, and we continue,
        otherwise we jump back to the beginning of the loop *)
        Jnz (- ((length (is_int_instrs r1 r2))+5))%Z r1
      ].

  Definition checkints_instrs (r r1 r2 : RegName) : list Word :=
      lea_to_base_instrs r r1 r2
      ++ encodeInstrsW [
        GetB r1 r;
        GetE r2 r;
        Lt r1 r1 r2;
        Sub r1 r1 1; (* invert result for the jump *)
        Jnz (length (checkints_loop_instrs r r1 r2)) r1]
      ++ checkints_loop_instrs r r1 r2
      ++ encodeInstrsW [
        Mov r1 0;
        Mov r2 0].
End Checkints.

Section Checkints_spec.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ}
      {MP: MachineParameters}
  .

  Lemma checkints_spec_alt
    (r r1 r2 : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (w1 w2 : Word) (l : list Addr) (ws : list Word)
    (p : Perm) (g : Locality) (b e a : Addr)
    (φ : language.val cap_lang → iPropI Σ) :

    let checkints := (checkints_instrs r r1 r2) in
    let a_last := (pc_a ^+ length checkints)%a in
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a a_last →
    l ≡ₚ (finz.seq_between b e) ->

    ▷ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
    ∗ ▷ r ↦ᵣ (WCap p g b e a)
    ∗ ▷ r1 ↦ᵣ w1
    ∗ ▷ r2 ↦ᵣ w2
    ∗ ▷ codefrag pc_a checkints
    ∗ ▷ ( [∗ list] a;v ∈ l;ws, a ↦ₐ v )
    ∗ ▷ ( PC ↦ᵣ WCap pc_p pc_g pc_b pc_e a_last
         ∗ r ↦ᵣ WCap p g b e (finz.max b e)
         ∗ r1 ↦ᵣ WInt 0%Z
         ∗ r2 ↦ᵣ WInt 0%Z
         ∗ ( [∗ list] a;v ∈ l;ws, a ↦ₐ v )
         ∗ ⌜ Forall (λ w, ∃ z, w = WInt z) ws ⌝
         ∗ codefrag pc_a checkints
         ∗ £ 2
         -∗ WP Seq (Instr Executable) {{ φ }}
        )
    ∗ ▷ φ FailedV
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    intros checkints a_last ; subst checkints a_last.
    iIntros (Hvpc Hcont Hl)
      "(>HPC & >Hr & >Hr1 & >Hr2 & >Hprog & Hmem & Hφ & Hfailed)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    codefrag_facts "Hprog".
    rename H into HcontRegion; clear H0.
  Admitted.

  Lemma checkints_spec
    (r r1 r2 : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (w1 w2 : Word) (ws : list Word)
    (p : Perm) (g : Locality) (b e a : Addr)
    (φ : language.val cap_lang → iPropI Σ) :

    let checkints := (checkints_instrs r r1 r2) in
    let a_last := (pc_a ^+ length checkints)%a in
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a a_last →

    ▷ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
    ∗ ▷ r ↦ᵣ (WCap p g b e a)
    ∗ ▷ r1 ↦ᵣ w1
    ∗ ▷ r2 ↦ᵣ w2
    ∗ ▷ codefrag pc_a checkints
    ∗ ▷ ([[ b , e ]] ↦ₐ [[ ws ]])
    ∗ ▷ ( PC ↦ᵣ WCap pc_p pc_g pc_b pc_e a_last
         ∗ r ↦ᵣ WCap p g b e (finz.max b e)
         ∗ r1 ↦ᵣ WInt 0%Z
         ∗ r2 ↦ᵣ WInt 0%Z
         ∗ ([[ b , e ]] ↦ₐ [[ ws ]])
         ∗ ⌜ Forall (λ w, ∃ z, w = WInt z) ws ⌝
         ∗ codefrag pc_a checkints
         -∗ WP Seq (Instr Executable) {{ φ }}
        )
    ∗ ▷ φ FailedV
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    intros checkints a_last ; subst checkints a_last.
    iIntros (Hvpc Hcont)
      "(>HPC & >Hr & >Hr1 & >Hr2 & >Hprog & Hmem & Hφ & Hfailed)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    codefrag_facts "Hprog".
    rename H into HcontRegion; clear H0.
  Admitted.

End Checkints_spec.
