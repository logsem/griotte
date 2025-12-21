From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules proofmode.
From cap_machine Require Import is_word_type lea_to_base.

Section Checkra.
  Context
      {MP: MachineParameters}
  .


  Definition checkra_instrs (r r1 r2 : RegName) : list Word :=
    encodeInstrsW [ Mov r1 0%Z; Mov r2 0%Z ].
  (* TODO: it's actually quite annoying to check...
     In CHERIoT, I would do something like:
     ```
     GetP r1 r;
     LAnd r1 (R, Ow, DL, DRO);
     ```

     Maybe I should have another instruction in the machine
     for checking this easily?
   *)


End Checkra.

Section Checkra_spec.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ}
      {MP: MachineParameters}
  .

  Lemma checkra_spec
    (rsrc r1 r2 : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (wsrc w1 w2 : Word)
    (φ : language.val cap_lang → iPropI Σ) :

    let checkra_ := (checkra_instrs rsrc r1 r2) in
    let a_last := (pc_a ^+ length checkra_)%a in
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a a_last →

    ▷ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
    ∗ ▷ rsrc ↦ᵣ wsrc
    ∗ ▷ r1 ↦ᵣ w1
    ∗ ▷ r2 ↦ᵣ w2
    ∗ ▷ codefrag pc_a checkra_
    ∗ ▷ ( (∃ p g b e a,
          ⌜ readAllowed p = true ∧ wsrc = WCap p g b e a⌝
          ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e a_last
          ∗ rsrc ↦ᵣ WCap p g b e a
          ∗ r1 ↦ᵣ WInt 0%Z
          ∗ r2 ↦ᵣ WInt 0%Z
          ∗ codefrag pc_a checkra_ )
            -∗ WP Seq (Instr Executable) {{ φ }}
        )
    ∗ ▷ φ FailedV
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
  Admitted.

End Checkra_spec.
