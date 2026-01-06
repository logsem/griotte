From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules proofmode.
From cap_machine Require Import is_word_type lea_to_base.

Section Checkra.
  Context
      {MP: MachineParameters}
  .


  Definition checkra_instrs (r r1 r2 : RegName) : list Word :=
    encodeInstrsW [
        GetWType r1 r;
        Sub r2 r1 (encodeWordType wt_cap);
        Jnz 4 r2;
        GetP r1 r;
        Sub r2 r1 (encodePerm (O LG LM));
        Jnz 2 r2;
        Fail;
        Sub r2 r1 (encodePerm (O DL LM));
        Jnz 2 r2;
        Fail;
        Sub r2 r1 (encodePerm (O LG DRO));
        Jnz 2 r2;
        Fail;
        Sub r2 r1 (encodePerm (O DL DRO));
        Jnz 2 r2;
        Fail;
        Sub r2 r1 (encodePerm WO);
        Jnz 2 r2;
        Fail;
        Sub r2 r1 (encodePerm WO_DL);
        Jnz 2 r2;
        Fail;
        Sub r2 r1 (encodePerm WO_DRO);
        Jnz 2 r2;
        Fail;
        Sub r2 r1 (encodePerm WO_DL_DRO);
        Jnz 2 r2;
        Fail;
        Sub r2 r1 (encodePerm WLO);
        Jnz 2 r2;
        Fail;
        Sub r2 r1 (encodePerm WLO_DL);
        Jnz 2 r2;
        Fail;
        Sub r2 r1 (encodePerm WLO_DRO);
        Jnz 2 r2;
        Fail;
        Sub r2 r1 (encodePerm WLO_DL_DRO);
        Jnz 2 r2;
        Fail;
        Mov r1 0%Z;
        Mov r2 0%Z ].
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

  Local Ltac fail_check_ra :=
    match goal with
    | _ : _ |- context [ WInt (encodePerm ?p - encodePerm ?p') ] =>
        replace (encodePerm p' - encodePerm p')%Z with 0%Z by lia
    end
    ; iInstr "Hcode"
    ; iInstr "Hcode"
    ; by wp_end.
  Local Ltac pass_check_ra :=
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
  Local Ltac check_ra :=
    match goal with
    | _ : _ |- context [ WInt (encodePerm ?p - encodePerm ?p') ] =>
        let Hp := fresh "Hp" in
        destruct (decide (p = p')) as [-> | Hp]; [fail_check_ra|pass_check_ra]
    end.

  Lemma checkra_spec
    (rsrc r1 r2 : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (wsrc w1 w2 : Word)
    (φ : language.val cap_lang → iPropI Σ) :

    let checkra_ := (checkra_instrs rsrc r1 r2) in
    let a_last := (pc_a ^+ length checkra_)%a in
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a a_last →
    rsrc ≠ cnull ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->

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
    ∗ □ (▷ φ FailedV)
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    intros checkra a_last ; subst checkra a_last.
    iIntros (Hra Hbounds Hsrc_cnull Hr1_cnull Hr2_cnull) "(>HPC & >Hsrc & >Hr1 & >Hr2 & >Hcode & Hpost & #Hfailed)".
    codefrag_facts "Hcode".
    rename H into HcontRegion; clear H0.

    iInstr "Hcode".
    { rewrite /rules_Get.denote.
      destruct_word wsrc;done.
    }
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
    pose proof (encodeWordType_correct (WCap c g b e a) wt_cap) as Hwtype ; cbn in Hwtype.
    rewrite Hwtype.
    replace (encodeWordType wt_cap - encodeWordType wt_cap)%Z with 0%Z by lia.
    iInstr "Hcode".
    iInstr "Hcode".
    iInstr "Hcode".
    do 12 check_ra.
    iInstr "Hcode".
    iApply "Hpost"; iFrame.
    iPureIntro; split; last done.
    destruct_perm c; auto.
  Qed.

End Checkra_spec.
