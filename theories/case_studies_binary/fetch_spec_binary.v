From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode proofmode_binary.
From griotte Require Export fetch.

(** * Lockstep specification of the [fetch] macro

    Both runs execute the same [fetch] code, at the same address, and fetch
    the same word. *)

Section Fetch_binary.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ}
      {specg: specG Σ}
      {MP: MachineParameters}
  .

  Lemma fetch_spec_lockstep
    (n : Z) (rdst rscratch1 rscratch2 : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (wentry wdst w1 w2 swdst sw1 sw2 : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let fetch_ := (fetch_instrs n rdst rscratch1 rscratch2) in
    let a_last := (pc_a ^+ length fetch_)%a in
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a a_last →
    withinBounds pc_b pc_e (pc_b ^+ n)%a = true ->
    rdst ≠ cnull ->
    rscratch1 ≠ cnull ->
    rscratch2 ≠ cnull ->

    spec_ctx
    ∗ ⤇ Seq (Instr Executable)
    ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
    ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a
    ∗ rdst ↦ᵣ wdst
    ∗ rdst ↣ᵣ swdst
    ∗ rscratch1 ↦ᵣ w1
    ∗ rscratch1 ↣ᵣ sw1
    ∗ rscratch2 ↦ᵣ w2
    ∗ rscratch2 ↣ᵣ sw2
    ∗ codefrag pc_a fetch_
    ∗ spec_codefrag pc_a fetch_
    ∗ (pc_b ^+ n)%a ↦ₐ wentry
    ∗ (pc_b ^+ n)%a ↣ₐ wentry
    ∗ ▷ (⤇ Seq (Instr Executable)
         ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e a_last
         ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e a_last
         ∗ rdst ↦ᵣ load_word pc_p wentry
         ∗ rdst ↣ᵣ load_word pc_p wentry
         ∗ rscratch1 ↦ᵣ WInt 0%Z
         ∗ rscratch1 ↣ᵣ WInt 0%Z
         ∗ rscratch2 ↦ᵣ WInt 0%Z
         ∗ rscratch2 ↣ᵣ WInt 0%Z
         ∗ codefrag pc_a fetch_
         ∗ spec_codefrag pc_a fetch_
         ∗ (pc_b ^+ n)%a ↦ₐ wentry
         ∗ (pc_b ^+ n)%a ↣ₐ wentry
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    intros fetch a_last ; subst fetch a_last.
    iIntros (Hvpc Hcont Hpc_n Hrdst Hr1 Hr2)
      "(#Hspec & Hj & HPC & HsPC & Hrdst & Hsrdst & Hrscratch1 & Hsrscratch1
       & Hrscratch2 & Hsrscratch2 & Hprog & Hsprog & Hpc_bn & Hspc_bn & Hφ)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    codefrag_facts "Hprog".
    rename H into HcontRegion; clear H0.
    assert ((pc_a + (pc_b - pc_a))%a = Some pc_b) as Hlea;[solve_addr|].
    assert ((pc_b + n)%a = Some (pc_b ^+ n)%a) as Hpc_bn';[solve_addr|].

    (* Mov rdst PC *)
    iInstr_lockstep "Hsprog" "Hprog".

    (* GetB rscratch1 rdst *)
    iInstr_lockstep "Hsprog" "Hprog".

    (* GetA rscratch2 rdst *)
    iInstr_lockstep "Hsprog" "Hprog".

    (* Sub rscratch1 rscratch1 rscratch2 *)
    iInstr_lockstep "Hsprog" "Hprog".

    (* Lea rdst rscratch1 *)
    iInstr_spec_lookup "Hsprog" as "Hsi" "Hsprog".
    iMod (step_lea_success_reg with "[$Hspec $Hj $HsPC $Hsi $Hsrdst $Hsrscratch1]")
      as "(Hj & HsPC & Hsi & Hsrscratch1 & Hsrdst)";
      [solve_ndisj|solve_pure|solve_pure|solve_pure|exact Hlea|solve_pure|solve_pure|].
    iSpecSeq.
    iSpecialize ("Hsprog" with "[$]").
    (* Lea rdst rscratch1 *)
    iInstr_lookup "Hprog" as "Hi" "Hprog".
    wp_instr.
    iApply (wp_lea_success_reg with "[$HPC $Hi $Hrdst $Hrscratch1]"); auto; [solve_pure..|exact Hlea|].
    iIntros "!> (HPC & Hi & Hrscratch1 & Hrdst)".
    wp_pure.
    iSpecialize ("Hprog" with "[$]").

    (* Lea rdst n *)
    iInstr_lockstep "Hsprog" "Hprog".

    (* Load rdst rdst *)
    iInstr_lockstep "Hsprog" "Hprog".

    (* Mov rscratch1 0 *)
    iInstr_lockstep "Hsprog" "Hprog".

    (* Mov rscratch2 0 *)
    iInstr_lockstep "Hsprog" "Hprog".

    iApply "Hφ"; iFrame.
  Qed.

End Fetch_binary.
