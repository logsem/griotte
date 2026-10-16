From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode assembler.
From griotte Require Import is_word_type lea_to_base.

Section Checkra.
  Import Asm_Griotte.
  Context
      {MP: MachineParameters}
  .

  Definition checkra_asm (r r1 r2 : RegName) : list asm_code :=
    [
      getwtype r1 r;
      sub r2 r1 (encodeWordType wt_cap);
      jnz 4 r2;
      getp r1 r;
      sub r2 r1 (encodePerm (O LG LM));
      jnz 2 r2;
      fail;
      sub r2 r1 (encodePerm (O DL LM));
      jnz 2 r2;
      fail;
      sub r2 r1 (encodePerm (O LG DRO));
      jnz 2 r2;
      fail;
      sub r2 r1 (encodePerm (O DL DRO));
      jnz 2 r2;
      fail;
      sub r2 r1 (encodePerm WO);
      jnz 2 r2;
      fail;
      sub r2 r1 (encodePerm WO_DL);
      jnz 2 r2;
      fail;
      sub r2 r1 (encodePerm WO_DRO);
      jnz 2 r2;
      fail;
      sub r2 r1 (encodePerm WO_DL_DRO);
      jnz 2 r2;
      fail;
      sub r2 r1 (encodePerm WLO);
      jnz 2 r2;
      fail;
      sub r2 r1 (encodePerm WLO_DL);
      jnz 2 r2;
      fail;
      sub r2 r1 (encodePerm WLO_DRO);
      jnz 2 r2;
      fail;
      sub r2 r1 (encodePerm WLO_DL_DRO);
      jnz 2 r2;
      fail;
      mov r1 0;
      mov r2 0
    ].

  (** [encodeWordType], [wt_cap] and [encodePerm] stay folded in the
      assembled code. *)
  Definition checkra (r r1 r2 : RegName) : list instr :=
    Eval cbv -[encodeWordType word_encoding_mixin wt_cap
               encodePerm permission_encoding_mixin] in
      assemble (checkra_asm r r1 r2).
  Lemma checkra_assembles (r r1 r2 : RegName) :
    asm_ok (assemble_check (checkra_asm r r1 r2)).
  Proof. asm_check. Qed.

  Definition checkra_instrs (r r1 r2 : RegName) : list Word :=
    encodeInstrsW (checkra r r1 r2).
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

  #[local] Ltac fail_check_ra :=
    match goal with
    | _ : _ |- context [ WInt (encodePerm ?p - encodePerm ?p') ] =>
        replace (encodePerm p' - encodePerm p')%Z with 0%Z by lia
    end
    ; iInstr "Hcode"
    ; iInstr "Hcode"
    ; by wp_end.
  #[local] Ltac pass_check_ra :=
    match goal with
    | _ : _ |- context [ WInt (encodePerm ?p - encodePerm ?p') ] =>
        let Heq := fresh "Heq" in
        let Hneq := fresh "Hneq" in
        assert ( (WInt (encodePerm p - encodePerm p') ≠ WInt 0 )) as Hneq
        ; [
            intro; simplify_eq
            ; assert (encodePerm p = encodePerm p' ) as Heq by lia
            ; apply encodePerm_inj in Heq
            ; done
          |]
        ; iInstr "Hcode"
        ; iInstr "Hcode"
        ; clear Hneq
    end.
  #[local] Ltac check_ra :=
    match goal with
    | _ : _ |- context [ WInt (encodePerm ?p - encodePerm ?p') ] =>
        let Hp := fresh "Hp" in
        destruct (decide (p = p')) as [-> | Hp]; [fail_check_ra|pass_check_ra]
    end.

  Lemma checkra_spec
    (rsrc r1 r2 : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (wsrc w1 w2 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    let checkra_ := (checkra_instrs rsrc r1 r2) in
    let a_last := (pc_a ^+ length checkra_)%a in
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a a_last →
    rsrc ≠ cnull ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a
    ∗ ▷ rsrc ↦ᵣ wsrc
    ∗ ▷ r1 ↦ᵣ w1
    ∗ ▷ r2 ↦ᵣ w2
    ∗ ▷ codefrag_pers pc_a checkra_
    ∗ ▷ ( (∃ t p g b e a π,
          ⌜ readAllowed p = true ∧ wsrc = WCap t p g b e a @@? π⌝
          ∗ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e a_last
          ∗ rsrc ↦ᵣ WCap t p g b e a @@? π
          ∗ r1 ↦ᵣ WInt 0%Z
          ∗ r2 ↦ᵣ WInt 0%Z
          ∗ codefrag_pers pc_a checkra_ )
            -∗ WP Seq (Instr Executable) {{ φ }}
        )
    ∗ □ (▷ φ FailedV)
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    intros checkra a_last ; subst checkra a_last.
    iIntros (Hra Hbounds Hsrc_cnull Hr1_cnull Hr2_cnull) "(>HPC & >Hsrc & >Hr1 & >Hr2 & >#Hcode & Hpost & #Hfailed)".
    codefrag_facts "Hcode".
    rename H into HcontRegion; clear H0.
    destruct wsrc as [wsrc πsrc].

    iInstr "Hcode".
    iInstr "Hcode".

    destruct (is_cap wsrc) eqn:His_cap_wsrc; cycle 1.
    { assert (WInt (encodeWordType wsrc - encodeWordType wt_cap)%Z ≠ WInt 0).
      { intro; simplify_eq.
        destruct_word wsrc; cbn in *; try done.
        all: match goal with
             | _ : ((encodeWordType ?w - encodeWordType wt_cap)%Z = 0%Z) |- _ =>
                 pose proof (encodeWordType_correct w wt_cap) as Hwtype ; cbn in Hwtype; lia
             end.
      }
      iInstr "Hcode".
      iInstr "Hcode".
      by wp_end.
    }
    destruct_word wsrc; cbn in His_cap_wsrc; try done.
    pose proof (encodeWordType_correct (WCap t c g b e a) wt_cap) as Hwtype ; cbn in Hwtype.
    rewrite Hwtype.
    replace (encodeWordType wt_cap - encodeWordType wt_cap)%Z with 0%Z by lia.
    iInstr "Hcode".
    iInstr "Hcode".
    iInstr "Hcode".
    do 12 check_ra.
    iInstr "Hcode".
    iApply "Hpost"; iFrame "∗ Hcode".
    iPureIntro; split; last done.
    destruct_perm c; auto.
  Qed.

End Checkra_spec.
