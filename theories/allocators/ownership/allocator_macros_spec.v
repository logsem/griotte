From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode memory_region fetch.
From griotte.allocators.ownership Require Import allocator_preamble.
From griotte.allocators.common Require Export allocator_common_macros_spec.

(** The macros and the layout facts shared by the allocators are in
    [allocator_common_macros_spec]. *)

(** Facts on the layout of the allocator that depend on its code. *)
Section AllocatorLayoutFacts.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}
    {MP : MachineParameters} {layout : allocatorLayout} {layout_wf : allocatorLayoutWf}.

  Lemma allocator_code_free :
    (allocator_code_b + length allocator_malloc_instrs)%a = Some allocator_free_pcc_addr.
  Proof.
    pose proof allocator_size_imports as Himports.
    pose proof allocator_size_code as Hcode.
    rewrite /allocator_code length_app in Hcode.
    rewrite allocator_imports_length in Himports.
    unfold allocator_free_pcc_addr, allocator_free_pcc_off, allocator_malloc_pcc_off in *.
    solve_addr.
  Qed.

  Lemma allocator_malloc_pcc_bounds :
    SubBounds allocator_pcc_b allocator_pcc_e allocator_malloc_pcc_addr
      (allocator_malloc_pcc_addr ^+ length allocator_malloc_instrs)%a.
  Proof.
    pose proof allocator_size_code as Hsize_code.
    pose proof allocator_size_imports as Himports_size.
    rewrite /allocator_code length_app in Hsize_code.
    rewrite allocator_imports_length in Himports_size.
    unfold allocator_malloc_pcc_addr, allocator_malloc_pcc_off in *.
    solve_addr.
  Qed.

  Lemma allocator_free_pcc_bounds :
    SubBounds allocator_pcc_b allocator_pcc_e allocator_free_pcc_addr
      (allocator_free_pcc_addr ^+ length allocator_free_instrs)%a.
  Proof.
    pose proof allocator_size_code as Hsize_code.
    pose proof allocator_size_imports as Himports_size.
    rewrite /allocator_code length_app in Hsize_code.
    rewrite allocator_imports_length in Himports_size.
    unfold allocator_free_pcc_addr, allocator_free_pcc_off, allocator_malloc_pcc_off in *.
    solve_addr.
  Qed.

End AllocatorLayoutFacts.

Section AllocatorOwnerMacro.
  Context
    {Σ : gFunctors}
    {ceriseg : ceriseG Σ}
    {MP : MachineParameters}
    {layout : allocatorLayout} {layout_wf : allocatorLayoutWf}
  .

  Definition allocator_unsealing_key : Word :=
    WSealRange true (false, true) Global AllocOtype (AllocOtype ^+ 1)%ot AllocOtype.

  (** Load the owner identifier of an allocator capability. The physical owner
      word is only read. Block 0 of both allocator entries is this macro. *)

  Lemma allocator_owner_spec
    (E : coPset) (pc_b pc_e pc_a : Addr)
    (g : Locality) (a : Addr) (o : Z) (wtp w3 w4 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    let code := allocator_owner_instrs ctp ca0 ct3 ct4 in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length code)%a ->
    disjoint_from_shadow pc_b pc_e ->
    withinBounds pc_b pc_e (pc_b ^+ allocator_unsealing_key_import_off)%a = true ->
    is_shadow_address a = false ->
    (a < a ^+ 1)%a ->

    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a ∗
    ctp ↦ᵣ wtp ∗
    ct3 ↦ᵣ w3 ∗
    ct4 ↦ᵣ w4 ∗
    ca0 ↦ᵣ allocator_capability g a ∗
    (pc_b ^+ allocator_unsealing_key_import_off)%a ↦ₐ allocator_unsealing_key ∗
    a ↦ₐ WInt o ∗
    codefrag pc_a code ∗
    ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ length code)%a ∗
         ctp ↦ᵣ WInt o ∗
         ct3 ↦ᵣ WInt 0 ∗
         ct4 ↦ᵣ WInt 0 ∗
         ca0 ↦ᵣ allocator_capability g a ∗
         (pc_b ^+ allocator_unsealing_key_import_off)%a ↦ₐ allocator_unsealing_key ∗
         a ↦ₐ WInt o ∗
         codefrag pc_a code
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros code; subst code.
    iIntros (Hpc Hdisjoint Hkey Hshadow_a Ha)
      "(HPC & Hctp & Hct3 & Hct4 & Hca0 & Hkey & Ha & Hcode & Hφ)".
    codefrag_facts "Hcode".
    pose proof allocator_otype_size as Hotype.
    assert ((pc_a + (pc_b - pc_a))%a = Some pc_b) as Hlea by solve_addr.
    assert ((pc_b + allocator_unsealing_key_import_off)%a =
      Some (pc_b ^+ allocator_unsealing_key_import_off)%a) as Hpc_bn
      by (apply withinBounds_true_iff in Hkey; solve_addr).
    assert (is_shadow_address (pc_b ^+ allocator_unsealing_key_import_off)%a = false)
      as Hshadow_key by (eapply disjoint_from_shadow_not_in; eauto).
    rewrite /allocator_unsealing_key /allocator_capability /allocator_capability_scap.
    (* Mov ctp PC. *)
    iInstr "Hcode".
    (* GetB ct3 ctp. *)
    iInstr "Hcode".
    (* GetA ct4 ctp. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 ct4. *)
    iInstr "Hcode".
    (* Lea ctp ct3. *)
    iInstr "Hcode".
    (* Lea ctp allocator_unsealing_key_import_off. *)
    iInstr "Hcode".
    (* Load ctp ctp. *)
    iInstr "Hcode".
    { done. }
    iEval (rewrite /lload_word /lift_word /=) in "Hctp".
    (* Mov ct3 0. *)
    iInstr "Hcode".
    (* Mov ct4 0. *)
    iInstr "Hcode".
    (* UnSeal ctp ctp ca0. *)
    iInstr "Hcode".
    { done. }
    { apply withinBounds_true_iff; solve_addr. }
    (* Load ctp ctp. *)
    iInstr "Hcode".
    { done. }
    { apply withinBounds_true_iff; solve_addr. }
    iEval (rewrite /lload_word /lift_word /=) in "Hctp".
    iApply "Hφ". iFrame.
  Qed.

  (** A malformed allocator capability traps: either [unseal] fails, or it
      clears the tag of the result and the following [load] fails. *)

  Lemma allocator_owner_invalid_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wsealed wtp w3 w4 : LWord)
    (P : iProp Σ) :

    let code := allocator_owner_instrs ctp ca0 ct3 ct4 in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length code)%a ->
    disjoint_from_shadow pc_b pc_e ->
    withinBounds pc_b pc_e (pc_b ^+ allocator_unsealing_key_import_off)%a = true ->
    (is_sealed_with_o wsealed.(lw) AllocOtype = false \/ get_tag wsealed.(lw) = false) ->

    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a ∗
    ctp ↦ᵣ wtp ∗
    ct3 ↦ᵣ w3 ∗
    ct4 ↦ᵣ w4 ∗
    ca0 ↦ᵣ wsealed ∗
    (pc_b ^+ allocator_unsealing_key_import_off)%a ↦ₐ allocator_unsealing_key ∗
    codefrag pc_a code
    ⊢ WP Seq (Instr Executable) @ E {{ v, ⌜v = HaltedV⌝ → P }}.
  Proof.
    intros code; subst code.
    iIntros (Hpc Hdisjoint Hkey Hwsealed)
      "(HPC & Hctp & Hct3 & Hct4 & Hca0 & Hkey & Hcode)".
    codefrag_facts "Hcode".
    pose proof allocator_otype_size as Hotype.
    assert ((pc_a + (pc_b - pc_a))%a = Some pc_b) as Hlea by solve_addr.
    assert ((pc_b + allocator_unsealing_key_import_off)%a =
      Some (pc_b ^+ allocator_unsealing_key_import_off)%a) as Hpc_bn
      by (apply withinBounds_true_iff in Hkey; solve_addr).
    assert (is_shadow_address (pc_b ^+ allocator_unsealing_key_import_off)%a = false)
      as Hshadow_key by (eapply disjoint_from_shadow_not_in; eauto).
    rewrite /allocator_unsealing_key.
    (* Mov ctp PC. *)
    iInstr "Hcode".
    (* GetB ct3 ctp. *)
    iInstr "Hcode".
    (* GetA ct4 ctp. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 ct4. *)
    iInstr "Hcode".
    (* Lea ctp ct3. *)
    iInstr "Hcode".
    (* Lea ctp allocator_unsealing_key_import_off. *)
    iInstr "Hcode".
    (* Load ctp ctp. *)
    iInstr "Hcode".
    { done. }
    iEval (rewrite /lload_word /lift_word /=) in "Hctp".
    (* Mov ct3 0. *)
    iInstr "Hcode".
    (* Mov ct4 0. *)
    iInstr "Hcode".
    (* UnSeal ctp ctp ca0. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iDestruct (map_of_regs_3 with "HPC Hctp Hca0") as "[Hmap %Hne]".
    destruct Hne as (HPCctp & HPCca0 & Hctpca0).
    iApply (wp_UnSeal _ RX Global pc_b pc_e (pc_a ^+ 9)%a None _ ctp ctp ca0
      with "[$Hi $Hmap]").
    { by rewrite decode_encode_instrW_inv. }
    { solve_pure. }
    { by rewrite lookup_insert_eq. }
    { rewrite /regs_of !dom_insert_L. set_solver+. }
    iNext. iIntros (regs' retv) "(%Hspec & Hi & Hmap)".
    inversion Hspec as
      [ p g b e a πs o sb π Hsrc1 Hsrc2 Htag Hperm Hwb HincrPC
      | t p g b e a πs o sb π Hsrc1 Hsrc2 Hfalse HincrPC
      | Hfail ]; subst.
    - (* A well-formed allocator capability: excluded. *)
      exfalso. simplify_map_eq.
      apply withinBounds_le_addr in Hwb.
      destruct Hwsealed as [Hne|Hne]; [apply Z.eqb_neq in Hne; solve_addr|congruence].
    - (* The unsealed word is untagged, and the load traps. *)
      simplify_map_eq.
      apply incrementPC_Some_inv in HincrPC as (?&?&?&?&?&?&a10&?&HPC'&Ha10&->).
      simplify_map_eq.
      iEval (rewrite (insert_insert_ne _ ctp PC) // !insert_insert_eq) in "Hmap".
      iEval (rewrite !insert_insert_eq) in "Hmap".
      iDestruct (regs_of_map_3 with "Hmap") as "(HPC & Hctp & Hca0)"; [done..|].
      assert (a10 = (pc_a ^+ 10)%a) as -> by solve_addr.
      wp_pure.
      iSpecialize ("Hcode" with "Hi").
      (* Load ctp ctp. *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iDestruct (map_of_regs_2 with "HPC Hctp") as "[Hmap %Hne']".
      iApply (wp_load_fail_tag with "[$Hi $Hmap]").
      { by rewrite decode_encode_instrW_inv. }
      2: { by rewrite lookup_insert_eq. }
      { apply isCorrectPC_intro; [solve_addr|auto]. }
      { by simplify_map_eq. }
      { by destruct sb. }
      iNext. iIntros "_".
      wp_pure; wp_end; iIntros "%Hcontr"; done.
    - wp_pure; wp_end; iIntros "%Hcontr"; done.
  Qed.

End AllocatorOwnerMacro.
