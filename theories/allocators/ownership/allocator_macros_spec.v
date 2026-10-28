From iris.proofmode Require Import proofmode.
From griotte Require Import switcher_namespace rules proofmode memory_region fetch.
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
    unfold allocator_free_pcc_addr in *; rewrite allocator_free_pcc_off_eq;
    unfold allocator_malloc_pcc_off in *.
    solve_addr.
  Qed.

  Lemma allocator_malloc_pcc_bounds :
    SubBounds allocator_pcc_b allocator_pcc_e allocator_malloc_pcc_addr
      (allocator_malloc_pcc_addr ^+ length allocator_malloc_instrs).
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
      (allocator_free_pcc_addr ^+ length allocator_free_instrs).
  Proof.
    pose proof allocator_size_code as Hsize_code.
    pose proof allocator_size_imports as Himports_size.
    rewrite /allocator_code length_app in Hsize_code.
    rewrite allocator_imports_length in Himports_size.
    unfold allocator_free_pcc_addr in *; rewrite allocator_free_pcc_off_eq;
    unfold allocator_malloc_pcc_off in *.
    solve_addr.
  Qed.

  (** The code of each entry is at its offset in the PCC: the fetches load the
      imports relative to the PC. *)
  Lemma allocator_malloc_pcc_addr_off :
    (allocator_pcc_b + allocator_malloc_pcc_off)%a = Some allocator_malloc_pcc_addr.
  Proof.
    pose proof allocator_size_code as Hsize_code.
    pose proof allocator_size_imports as Himports_size.
    rewrite /allocator_code length_app in Hsize_code.
    rewrite allocator_imports_length in Himports_size.
    unfold allocator_malloc_pcc_addr, allocator_malloc_pcc_off in *.
    solve_addr.
  Qed.

  Lemma allocator_free_pcc_addr_off :
    (allocator_pcc_b + allocator_free_pcc_off)%a = Some allocator_free_pcc_addr.
  Proof.
    pose proof allocator_size_code as Hsize_code.
    pose proof allocator_size_imports as Himports_size.
    rewrite /allocator_code length_app in Hsize_code.
    rewrite allocator_imports_length in Himports_size.
    unfold allocator_free_pcc_addr in *; rewrite allocator_free_pcc_off_eq;
    unfold allocator_malloc_pcc_off in *.
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
    SealRange (false, true) Global AllocOtype (AllocOtype ^+ 1) AllocOtype.

  (** Load the owner identifier of an allocator capability. The physical owner
      word is only read. Block 0 of both allocator entries is this macro. *)

  Lemma allocator_owner_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (off : Z)
    (g : Locality) (a : Addr) (o : Z) (wtp : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    let code := allocator_owner_instrs off ctp ca0 in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length code) ->
    (pc_a + off)%a = Some (pc_b ^+ allocator_unsealing_key_import_off) ->
    disjoint_from_shadow pc_b pc_e ->
    withinBounds pc_b pc_e (pc_b ^+ allocator_unsealing_key_import_off) = true ->
    is_shadow_address a = false ->
    (a < a ^+ 1)%a ->

    PC ↦ₚ Cap RX Global pc_b pc_e pc_a ∗
    ctp ↦ᵣ wtp ∗
    ca0 ↦ᵣ allocator_capability g a ∗
    (pc_b ^+ allocator_unsealing_key_import_off) ↦ₐ□ allocator_unsealing_key ∗
    a ↦ₐ WInt o ∗
    codefrag_pers pc_a code ∗
    ▷ (PC ↦ₚ Cap RX Global pc_b pc_e (pc_a ^+ length code) ∗
         ctp ↦ᵣ WInt o ∗
         ca0 ↦ᵣ allocator_capability g a ∗
         (pc_b ^+ allocator_unsealing_key_import_off) ↦ₐ□ allocator_unsealing_key ∗
         a ↦ₐ WInt o ∗
         codefrag_pers pc_a code
         -∗ WP Exec @ E {{ φ }})
    ⊢ WP Exec @ E {{ φ }}.
  Proof.
    intros code; subst code.
    iIntros (Hpc Hoff Hdisjoint Hkey Hshadow_a Ha)
      "(HPC & Hctp & Hca0 & #Hkey & Ha & #Hcode & Hφ)".
    codefrag_facts "Hcode".
    pose proof allocator_otype_size as Hotype.
    assert (is_shadow_address (pc_b ^+ allocator_unsealing_key_import_off) = false)
      as Hshadow_key by (eapply disjoint_from_shadow_not_in; eauto).
    rewrite /allocator_unsealing_key /allocator_capability /allocator_capability_scap.
    (* Auipcc ctp off. *)
    iInstr "Hcode".
    (* CLoad ctp ctp 0. *)
    iInstr "Hcode".
    { done. }
    iEval (rewrite /lload_word /lift_word /=) in "Hctp".
    (* UnSeal ctp ctp ca0. *)
    iInstr "Hcode".
    { done. }
    { apply withinBounds_true_iff; solve_addr. }
    (* CLoad ctp ctp 0. *)
    iInstr "Hcode".
    { done. }
    { apply withinBounds_true_iff; solve_addr. }
    iEval (rewrite /lload_word /lift_word /=) in "Hctp".
    iApply "Hφ". iFrame "∗ Hkey Hcode".
  Qed.

  (** A malformed allocator capability traps: either [unseal] fails, or it
      clears the tag of the result and the following [load] fails. *)

  Lemma allocator_owner_invalid_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (off : Z) (wsealed wtp : LWord)
    (P : iProp Σ) :

    let code := allocator_owner_instrs off ctp ca0 in
    ↑Ntstack ⊆ E ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length code) ->
    (pc_a + off)%a = Some (pc_b ^+ allocator_unsealing_key_import_off) ->
    disjoint_from_shadow pc_b pc_e ->
    withinBounds pc_b pc_e (pc_b ^+ allocator_unsealing_key_import_off) = true ->
    (is_sealed_with_o wsealed.(lw) AllocOtype = false \/ get_tag wsealed.(lw) = false) ->

    PC ↦ₚ Cap RX Global pc_b pc_e pc_a ∗
    ctp ↦ᵣ wtp ∗
    ca0 ↦ᵣ wsealed ∗
    (pc_b ^+ allocator_unsealing_key_import_off) ↦ₐ□ allocator_unsealing_key ∗
    codefrag_pers pc_a code ∗
    (∀ a, ⌜a ∈ₐ [pc_a, pc_a ^+ length code)⌝ -∗
      ctp ↦ᵣ - ∗
      ca0 ↦ᵣ wsealed -∗
      trap_safe (Cap RX Global pc_b pc_e a) E (λ v, ⌜v = HaltedV⌝ → P)%I)
    ⊢ WP Exec @ E {{ v, ⌜v = HaltedV⌝ → P }}.
  Proof.
    intros code; subst code.
    iIntros (HEswitcher Hpc Hoff Hdisjoint Hkey Hwsealed)
      "(HPC & Hctp & Hca0 & #Hkey & #Hcode & Hfailed)".
    codefrag_facts "Hcode".
    pose proof allocator_otype_size as Hotype.
    assert (is_shadow_address (pc_b ^+ allocator_unsealing_key_import_off) = false)
      as Hshadow_key by (eapply disjoint_from_shadow_not_in; eauto).
    rewrite /allocator_unsealing_key.
    (* Auipcc ctp off. *)
    iInstr "Hcode".
    (* CLoad ctp ctp 0. *)
    iInstr "Hcode".
    { done. }
    iEval (rewrite /lload_word /lift_word /=) in "Hctp".
    iDestruct (map_of_regs_2 with "Hctp Hca0") as "[Hmap %Hctpca0]".
    (* UnSeal ctp ctp ca0. *)
    iInstrApply "Hcode" (wp_UnSeal _ RX Global pc_b pc_e (pc_a ^+ 2) None _ ctp ctp ca0)
      with "[$HPC $Hmap]"
      as (lpc' regs' retv) "(%Hspec & HPC & Hmap)".
    { rewrite /regs_of /operands_of !dom_insert_L. set_solver+. }
    inversion Hspec as
      [ p g b e a πs o sb π Hsrc1 Hsrc2 Htag Hperm Hwb HincrPC
      | t p g b e a πs o sb π Hsrc1 Hsrc2 Hfalse HincrPC
      | w1 w2 Hsrc1 Hsrc2 Hnot_sealed HincrPC
      | Hfail ]; subst.
    - (* A well-formed allocator capability: excluded. *)
      exfalso. simplify_map_eq.
      apply withinBounds_le_addr in Hwb.
      destruct Hwsealed as [Hne|Hne]; [apply Z.eqb_neq in Hne; solve_addr|congruence].
    - (* The unsealed word is untagged, and the load traps. *)
      simplify_map_eq.
      assert ((pc_a ^+ 2 + 1)%a = Some (pc_a ^+ 3)) as Ha3 by solve_addr.
      rewrite Ha3 in HincrPC; simplify_eq.
      iEval (rewrite !insert_insert_eq) in "Hmap".
      iDestruct (regs_of_map_2 with "Hmap") as "(Hctp & Hca0)"; first done.
      wp_pure.
      iDestruct (map_of_regs_1 with "Hctp") as "Hmap".
      (* CLoad ctp ctp 0. *)
      iInstrApply "Hcode" wp_load_fail_tag with "[$HPC $Hmap]" as "(HPC & Hmap)".
      { by simplify_map_eq. }
      { by destruct sb. }
      iDestruct (regs_of_map_1 with "Hmap") as "Hctp".
      iTrap with "Hfailed".
    - (* The word is not sealed: it loses its tag, and the load traps. *)
      simplify_map_eq.
      assert ((pc_a ^+ 2 + 1)%a = Some (pc_a ^+ 3)) as Ha3 by solve_addr.
      rewrite Ha3 in HincrPC; simplify_eq.
      iEval (rewrite !insert_insert_eq) in "Hmap".
      iDestruct (regs_of_map_2 with "Hmap") as "(Hctp & Hca0)"; first done.
      wp_pure.
      iDestruct (map_of_regs_1 with "Hctp") as "Hmap".
      (* CLoad ctp ctp 0. *)
      iInstrApply "Hcode" wp_load_fail_tag with "[$HPC $Hmap]" as "(HPC & Hmap)".
      { by simplify_map_eq. }
      { apply get_tag_clear_tag. }
      iDestruct (regs_of_map_1 with "Hmap") as "Hctp".
      iTrap with "Hfailed".
    - (* UnSeal ctp ctp ca0 fails: the registers are unchanged. *)
      inversion Hfail; subst;
        (iDestruct (regs_of_map_2 with "Hmap") as "(Hctp & Hca0)"; first done);
        iTrap with "Hfailed".
  Qed.

End AllocatorOwnerMacro.
