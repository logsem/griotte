From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode memory_region fetch.
From griotte.allocators.no_ownership Require Import allocator_preamble.
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
