From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte.allocators.ownership Require Import allocator_free_spec_states.

(** * Free, blocks 1 and 2: the checks of the request

    Block 1 moves the owner identifier from [ctp] to [ca0] and checks that
    [ca1] holds a capability, and block 2 that it is tagged and that its
    bounds lie in the allocated prefix of the heap, ignoring its cursor;
    block 2 reloads the heap root from the bump slot.
    On success, the group ends at block 3; otherwise at the rejection in
    the tail (block 5). *)

Section AllocatorFreeCheckBlocks2.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}
    {MP : MachineParameters} {layout : allocatorLayout} {layout_wf : allocatorLayoutWf}.

  Lemma allocator_free_check_valid_spec
    (E : coPset) (pc_b pc_e pc_a next : Addr) (o : Z) (wa0 wreq w0 w1 w2 w3 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_free_code_bounds pc_b pc_e pc_a ->
    allocator_free_in_prefix next wreq.(lw) ->
    allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
    PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_free_block_offset 1)%a ∗
    cgp ↦ᵣ WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
    ca0 ↦ᵣ wa0 ∗
    ca1 ↦ᵣ wreq ∗
    ctp ↦ᵣ WInt o ∗
    ct0 ↦ᵣ w0 ∗
    ct1 ↦ᵣ w1 ∗
    ct2 ↦ᵣ w2 ∗
    ct3 ↦ᵣ w3 ∗
    codefrag pc_a allocator_free_code ∗
    ▷ (allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
       cgp ↦ᵣ WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       ca0 ↦ᵣ WInt o ∗
       ca1 ↦ᵣ wreq ∗
       ctp ↦ᵣ WInt o ∗
       codefrag pc_a allocator_free_code ∗
       (∃ (p : Perm) (g : Locality) (b e a : Addr),
          ⌜wreq.(lw) = WCap true p g b e a ∧ (heap_b < b /\ b < e /\ e <= next)%a⌝ ∗
          PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_free_block_offset 3)%a ∗
          ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
          ct1 ↦ᵣ WInt b ∗
          ct2 ↦ᵣ WInt e ∗
          ct3 ↦ᵣ WInt 0)
       -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros (Hpc & Hpc_shadow & Hcgp_pc) (p & g & b & e & a & Hreq & Hbounds).
    destruct wreq as [wreq π]; cbn in Hreq; subst wreq.
    iIntros "(Hslot & HPC & Hcgp & Hca0 & Hca1 & Hctp & Hct0 & Hct1 & Hct2 & Hct3 & Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_free_unfold_code "Hcode_main".
    pose proof allocator_cgp_size.

    (* Block 1: the request is a capability *)
    focus_block 1 "Hcode_main" of allocator_free_blocks at pc_a as a_req Ha_req
      "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Mov ca0 ctp. *)
    iInstr "Hcode".
    (* GetWType ct3 ca1. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 (encodeWordType wt_cap). *)
    iInstr "Hcode".
    rewrite (encodeWordType_correct_cap true p g b e a true (O LG LM) Global 0%a 0%a 0%a)
      /wt_cap Z.sub_diag.
    (* Jnz .free_invalid ct3. *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 2: the tag and the bounds *)
    focus_block 2 "Hcode_main" of allocator_free_blocks at pc_a as a_check Ha_check
      "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* GetTag ct3 ca1. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 1. *)
    iInstr "Hcode".
    rewrite /Z.b2z Z.sub_diag.
    (* Jnz .free_invalid ct3. *)
    iInstr "Hcode".
    (* Load ct0 cgp. *)
    unfold lword_of_word.
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_load_success_exact with "[$HPC $Hi $Hct0 $Hcgp $Hslot]"); try solve_pure.
    { apply allocator_cgp_not_shadow. }
    { done. }
    { intros _. left. apply allocator_heap_root_authority. }
    { apply withinBounds_true_iff. solve_addr. }
    { intros Heq. apply Hcgp_pc. rewrite Heq elem_of_finz_seq_between. solve_addr. }
    iIntros "!> (HPC & Hi & Hct0 & Hcgp & Hslot)". wp_pure.
    iSpecialize ("Hcode" with "Hi").
    iEval (rewrite /lload_word /lift_word /=) in "Hct0".
    iEval (cbn [load_word]) in "Hct0".
    (* GetB ct1 ca1. *)
    iInstr "Hcode".
    (* GetE ct2 ca1. *)
    iInstr "Hcode".
    (* GetB ct3 ct0. *)
    iInstr "Hcode".
    (* Lt ct3 ct3 ct1. *)
    iInstr "Hcode".
    replace (heap_b <? b)%Z with true by (symmetry; apply Z.ltb_lt; solve_addr).
    (* Jnz .free_base_ok ct3. *)
    iInstr "Hcode".
    (* Lt ct3 ct1 ct2. *)
    iInstr "Hcode".
    replace (b <? e)%Z with true by (symmetry; apply Z.ltb_lt; solve_addr).
    (* Jnz .free_nonempty ct3. *)
    iInstr "Hcode".
    (* GetA ct3 ct0. *)
    iInstr "Hcode".
    (* Lt ct3 ct3 ct2. *)
    iInstr "Hcode".
    replace (next <? e)%Z with false by (symmetry; apply Z.ltb_ge; solve_addr).
    (* Jnz .free_invalid ct3. *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    change_pc_to (pc_a ^+ allocator_free_block_offset 3)%a.
    iApply "Hφ". iFrame "Hslot Hcgp Hca0 Hca1 Hctp Hcode_main".
    iExists p, g, b, e, a. iFrame. done.
  Qed.

  Lemma allocator_free_check_invalid_spec
    (E : coPset) (pc_b pc_e pc_a next : Addr) (o : Z) (wa0 wreq w0 w1 w2 w3 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_free_code_bounds pc_b pc_e pc_a ->
    ¬ allocator_free_in_prefix next wreq.(lw) ->
    allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
    PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_free_block_offset 1)%a ∗
    cgp ↦ᵣ WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
    ca0 ↦ᵣ wa0 ∗
    ca1 ↦ᵣ wreq ∗
    ctp ↦ᵣ WInt o ∗
    ct0 ↦ᵣ w0 ∗
    ct1 ↦ᵣ w1 ∗
    ct2 ↦ᵣ w2 ∗
    ct3 ↦ᵣ w3 ∗
    codefrag pc_a allocator_free_code ∗
    ▷ (allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
       cgp ↦ᵣ WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       ca0 ↦ᵣ WInt o ∗
       ca1 ↦ᵣ wreq ∗
       ctp ↦ᵣ WInt o ∗
       codefrag pc_a allocator_free_code ∗
       PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_free_invalid_offset)%a ∗
       ct0 ↦ᵣ - ∗
       ct1 ↦ᵣ - ∗
       ct2 ↦ᵣ - ∗
       ct3 ↦ᵣ -
       -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros (Hpc & Hpc_shadow & Hcgp_pc) Hrequest.
    destruct wreq as [wreq π]; cbn in Hrequest.
    iIntros "(Hslot & HPC & Hcgp & Hca0 & Hca1 & Hctp & Hct0 & Hct1 & Hct2 & Hct3 & Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_free_unfold_code "Hcode_main".
    pose proof allocator_cgp_size.

    (* Block 1: the request is a capability *)
    focus_block 1 "Hcode_main" of allocator_free_blocks at pc_a as a_req Ha_req
      "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Mov ca0 ctp. *)
    iInstr "Hcode".
    (* GetWType ct3 ca1. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 (encodeWordType wt_cap). *)
    iInstr "Hcode".
    destruct (is_cap wreq) eqn:Hreq_cap; last first.
    { assert (Hnoncap : WInt (encodeWordType wreq - encodeWordType wt_cap) ≠ WInt 0).
      { pose proof (encodeWordType_correct wreq wt_cap) as Hencode.
        intro Hzero. injection Hzero as Hzero.
        assert (Heq : encodeWordType wreq = encodeWordType wt_cap) by lia.
        destruct wreq; cbn in Hreq_cap, Hencode; try discriminate.
        all: try (destruct sb; cbn in Hreq_cap, Hencode; try discriminate); contradiction. }
      (* Jnz .free_invalid ct3. *)
      iInstr "Hcode".
      { transitivity (Some (pc_a ^+ allocator_free_invalid_offset)%a);
          offsets_compute; solve_addr. }
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
      change_pc_to (pc_a ^+ allocator_free_invalid_offset)%a.
      iApply "Hφ". iFrame. }
    destruct wreq; cbn in Hreq_cap; try done.
    destruct sb; cbn in Hreq_cap; try done.
    rewrite (encodeWordType_correct_cap tag p g b e a true (O LG LM) Global 0%a 0%a 0%a)
      /wt_cap Z.sub_diag.
    (* Jnz .free_invalid ct3. *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 2: the tag and the bounds *)
    focus_block 2 "Hcode_main" of allocator_free_blocks at pc_a as a_check Ha_check
      "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* GetTag ct3 ca1. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 1. *)
    iInstr "Hcode".
    destruct tag; last first.
    { cbn.
      (* Jnz .free_invalid ct3. *)
      iInstr "Hcode".
      { transitivity (Some (pc_a ^+ allocator_free_invalid_offset)%a);
          offsets_compute; solve_addr. }
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
      change_pc_to (pc_a ^+ allocator_free_invalid_offset)%a.
      iApply "Hφ". iFrame. }
    rewrite /Z.b2z Z.sub_diag.
    (* Jnz .free_invalid ct3. *)
    iInstr "Hcode".
    (* Load ct0 cgp. *)
    unfold lword_of_word.
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_load_success_exact with "[$HPC $Hi $Hct0 $Hcgp $Hslot]"); try solve_pure.
    { apply allocator_cgp_not_shadow. }
    { done. }
    { intros _. left. apply allocator_heap_root_authority. }
    { apply withinBounds_true_iff. solve_addr. }
    { intros Heq. apply Hcgp_pc. rewrite Heq elem_of_finz_seq_between. solve_addr. }
    iIntros "!> (HPC & Hi & Hct0 & Hcgp & Hslot)". wp_pure.
    iSpecialize ("Hcode" with "Hi").
    iEval (rewrite /lload_word /lift_word /=) in "Hct0".
    iEval (cbn [load_word]) in "Hct0".
    (* GetB ct1 ca1. *)
    iInstr "Hcode".
    (* GetE ct2 ca1. *)
    iInstr "Hcode".
    (* GetB ct3 ct0. *)
    iInstr "Hcode".
    (* Lt ct3 ct3 ct1. *)
    iInstr "Hcode".
    destruct (decide (heap_b < b)%a) as [Hbase|Hbase]; last first.
    { replace (heap_b <? b)%Z with false by (symmetry; apply Z.ltb_ge; solve_addr).
      (* Jnz .free_base_ok ct3. *)
      iInstr "Hcode".
      (* Jmp .free_invalid. *)
      iInstr "Hcode".
      { transitivity (Some (pc_a ^+ allocator_free_invalid_offset)%a);
          offsets_compute; solve_addr. }
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
      change_pc_to (pc_a ^+ allocator_free_invalid_offset)%a.
      iApply "Hφ". iFrame. }
    replace (heap_b <? b)%Z with true by (symmetry; apply Z.ltb_lt; solve_addr).
    (* Jnz .free_base_ok ct3. *)
    iInstr "Hcode".
    (* Lt ct3 ct1 ct2. *)
    iInstr "Hcode".
    destruct (decide (b < e)%a) as [Hnonempty|Hempty]; last first.
    { replace (b <? e)%Z with false by (symmetry; apply Z.ltb_ge; solve_addr).
      (* Jnz .free_nonempty ct3. *)
      iInstr "Hcode".
      (* Jmp .free_invalid. *)
      iInstr "Hcode".
      { transitivity (Some (pc_a ^+ allocator_free_invalid_offset)%a);
          offsets_compute; solve_addr. }
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
      change_pc_to (pc_a ^+ allocator_free_invalid_offset)%a.
      iApply "Hφ". iFrame. }
    replace (b <? e)%Z with true by (symmetry; apply Z.ltb_lt; solve_addr).
    (* Jnz .free_nonempty ct3. *)
    iInstr "Hcode".
    (* GetA ct3 ct0. *)
    iInstr "Hcode".
    (* Lt ct3 ct3 ct2. *)
    iInstr "Hcode".
    destruct (decide (next < e)%a) as [Hpast|Hwithin]; last first.
    { exfalso. apply Hrequest. exists p, g, b, e, a. split; first reflexivity. solve_addr. }
    replace (next <? e)%Z with true by (symmetry; apply Z.ltb_lt; solve_addr).
    (* Jnz .free_invalid ct3. *)
    iInstr "Hcode".
    { transitivity (Some (pc_a ^+ allocator_free_invalid_offset)%a);
        offsets_compute; solve_addr. }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    change_pc_to (pc_a ^+ allocator_free_invalid_offset)%a.
    iApply "Hφ". iFrame.
  Qed.

End AllocatorFreeCheckBlocks2.
