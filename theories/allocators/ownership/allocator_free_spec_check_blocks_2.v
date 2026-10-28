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

  (** On a request in the allocated prefix, the GetTag of block 2 returns
      1 and the checks pass, or it returns 0 on a request whose tag may be
      cleared. A result of 1 observes the claim of the base of the request,
      read from [P] by [Φc]; a result of 0 is impossible under a dereference
      witness for the identifier of the request. *)
  Lemma allocator_free_check_prefix_spec
    (E : coPset) (pc_b pc_e pc_a next : Addr) (o : Z) (wa0 wreq w0 w1 w2 w3 : LWord)
    (dw : deref_witness) (P : iProp Σ) (Φc : gmap Addr AddrClaim → Prop)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_free_code_bounds pc_b pc_e pc_a ->
    (next <= heap_e)%a ->
    allocator_free_in_prefix next wreq.(lw) ->
    (∀ C, addr_alloc_auth C -∗ P -∗ ⌜Φc C⌝) ->
    allocator_cgp_b ↦ₐ Cap RW Global heap_b heap_e next ∗
    PC ↦ₚ Cap RX Global pc_b pc_e (pc_a ^+ allocator_free_block_offset 1) ∗
    cgp ↦ᵣ Cap RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
    ca0 ↦ᵣ wa0 ∗
    ca1 ↦ᵣ wreq ∗
    ctp ↦ᵣ WInt o ∗
    ct0 ↦ᵣ w0 ∗
    ct1 ↦ᵣ w1 ∗
    ct2 ↦ᵣ w2 ∗
    ca3 ↦ᵣ w3 ∗
    deref_witness_res dw ∗
    P ∗
    codefrag_pers pc_a allocator_free_code ∗
    ▷ (allocator_cgp_b ↦ₐ Cap RW Global heap_b heap_e next ∗
       cgp ↦ᵣ Cap RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       ca0 ↦ᵣ WInt o ∗
       ca1 ↦ᵣ wreq ∗
       ctp ↦ᵣ WInt o ∗
       deref_witness_res dw ∗
       P ∗
       codefrag_pers pc_a allocator_free_code ∗
       ((∃ (p : Perm) (g : Locality) (b e a : Addr),
          ⌜wreq.(lw) = Cap p g b e a ∧ (heap_b < b /\ b < e /\ e <= next)%a⌝ ∗
          ⌜gettag_result dw Φc wreq 1⌝ ∗
          PC ↦ₚ Cap RX Global pc_b pc_e (pc_a ^+ allocator_free_block_offset 3) ∗
          ct0 ↦ᵣ Cap RW Global heap_b heap_e next ∗
          ct1 ↦ᵣ WInt b ∗
          ct2 ↦ᵣ WInt e ∗
          ca3 ↦ᵣ WInt 0) ∨
        (⌜wreq.(lprov) ≠ deref_id dw⌝ ∗
          PC ↦ₚ Cap RX Global pc_b pc_e (pc_a ^+ allocator_free_invalid_offset) ∗
          ct0 ↦ᵣ - ∗
          ct1 ↦ᵣ - ∗
          ct2 ↦ᵣ - ∗
          ca3 ↦ᵣ -))
       -∗ WP Exec @ E {{ φ }})
    ⊢ WP Exec @ E {{ φ }}.
  Proof.
    intros (Hpc & Hpc_shadow & Hcgp_pc) Hnext (p & g & b & e & a & Hreq & Hbounds) HP.
    destruct wreq as [wreq π]; cbn in Hreq; subst wreq.
    iIntros "(Hslot & HPC & Hcgp & Hca0 & Hca1 & Hctp & Hct0 & Hct1 & Hct2 & Hct3 & Hdw & HPr &
      #Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_free_unfold_code "Hcode_main".
    pose proof allocator_cgp_size.

    (* Block 1: the request is a capability *)
    focus_block 1 "Hcode_main" of allocator_free_blocks at pc_a as a_req Ha_req
      "Hcode" "Hcont".
    iHide "Hcode_main" as hcode.
    (* Mov ca0 ctp. *)
    iInstr "Hcode".
    (* GetWType ca3 ca1. *)
    iInstr "Hcode".
    (* Sub ca3 ca3 (encodeWordType wt_cap). *)
    iInstr "Hcode".
    rewrite (encodeWordType_correct_cap true p g b e a true (O LG LM) Global 0%a 0%a 0%a)
      /wt_cap Z.sub_diag.
    (* Jne .free_invalid ca3 0. *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    (* Block 2: the tag and the bounds *)
    focus_block 2 "Hcode_main" of allocator_free_blocks at pc_a as a_check Ha_check
      "Hcode" "Hcont".
    iHide "Hcode_main" as hcode.
    (* GetTag ca3 ca1. *)
    iInstrApply "Hcode" (wp_gettag_obs _ _ _ _ _ _ _ _ _ _ _ _ _ _ dw P Φc)
      with "[$HPC $Hca1 $Hct3 $Hdw $HPr]"
      as (z) "(HPC & Hca1 & Hct3 & Hdw & HPr & %Hres)".
    (* Sub ca3 ca3 1. *)
    iInstr "Hcode".
    destruct (decide (z = 1%Z)) as [->|Hz1]; last first.
    { assert (z = 0%Z) as -> by (destruct Hres as [ [-> | [-> _] ] _]; cbn in *; lia).
      assert (π ≠ deref_id dw) as Hπ.
      { intros Hπ. destruct Hres as (_ & Hexact & _).
        enough (0%Z = Z.b2z true) by done. apply Hexact; first done.
        intros _. left. split; first done. exists b.
        rewrite /heap_authority_base /heap_cap_base /= decide_True; last solve_addr.
        assert (is_heap_address b = true) as -> by (apply withinBounds_true_iff; solve_addr).
        done. }
      cbn.
      (* Jne .free_invalid ca3 0. *)
      iInstr "Hcode".
      { transitivity (Some (pc_a ^+ allocator_free_invalid_offset));
          offsets_compute; solve_addr. }
      unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
      change_pc_to (pc_a ^+ allocator_free_invalid_offset).
      iApply "Hφ". iFrame "∗ Hcode_main". iRight. iFrame. done. }
    rewrite Z.sub_diag.
    (* Jne .free_invalid ca3 0. *)
    iInstr "Hcode".
    unfold lword_of_word.
    iPoseProof deref_res_none as "-#Hderef".
    (* CLoad ct0 cgp. *)
    iInstrApply "Hcode" wp_load_success_exact
      with "[$HPC $Hct0 $Hcgp $Hslot $Hderef]"
      as "(HPC & Hct0 & Hcgp & Hslot & _)".
    { apply allocator_cgp_not_shadow. }
    { intros _. left. apply allocator_heap_root_authority. }
    { apply withinBounds_true_iff. solve_addr. }
    { intros Heq. apply Hcgp_pc. rewrite Heq elem_of_finz_seq_between. solve_addr. }
    iEval (rewrite /lload_word /lift_word /=) in "Hct0".
    iEval (cbn [load_word]) in "Hct0".
    (* GetB ct1 ca1. *)
    iInstr "Hcode".
    (* GetE ct2 ca1. *)
    iInstr "Hcode".
    (* GetB ca3 ct0. *)
    iInstr "Hcode".
    (* Lt ca3 ca3 ct1. *)
    iInstr "Hcode".
    replace (heap_b <? b)%Z with true by (symmetry; apply Z.ltb_lt; solve_addr).
    (* Jne .free_base_ok ca3 0. *)
    iInstr "Hcode".
    (* Lt ca3 ct1 ct2. *)
    iInstr "Hcode".
    replace (b <? e)%Z with true by (symmetry; apply Z.ltb_lt; solve_addr).
    (* Jne .free_nonempty ca3 0. *)
    iInstr "Hcode".
    (* GetA ca3 ct0. *)
    iInstr "Hcode".
    (* Lt ca3 ca3 ct2. *)
    iInstr "Hcode".
    replace (next <? e)%Z with false by (symmetry; apply Z.ltb_ge; solve_addr).
    (* Jne .free_invalid ca3 0. *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
    change_pc_to (pc_a ^+ allocator_free_block_offset 3).
    iApply "Hφ". iFrame "Hslot Hcgp Hca0 Hca1 Hctp Hdw HPr Hcode_main".
    iLeft. iExists p, g, b, e, a. iFrame "∗". done.
  Qed.


  (** Under a dereference witness for the identifier of the request, the
      checks pass on a request in the allocated prefix. *)
  Lemma allocator_free_check_valid_spec
    (E : coPset) (pc_b pc_e pc_a next : Addr) (o : Z) (wa0 wreq w0 w1 w2 w3 : LWord)
    (dw : deref_witness)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_free_code_bounds pc_b pc_e pc_a ->
    (next <= heap_e)%a ->
    allocator_free_in_prefix next wreq.(lw) ->
    wreq.(lprov) = deref_id dw ->
    allocator_cgp_b ↦ₐ Cap RW Global heap_b heap_e next ∗
    PC ↦ₚ Cap RX Global pc_b pc_e (pc_a ^+ allocator_free_block_offset 1) ∗
    cgp ↦ᵣ Cap RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
    ca0 ↦ᵣ wa0 ∗
    ca1 ↦ᵣ wreq ∗
    ctp ↦ᵣ WInt o ∗
    ct0 ↦ᵣ w0 ∗
    ct1 ↦ᵣ w1 ∗
    ct2 ↦ᵣ w2 ∗
    ca3 ↦ᵣ w3 ∗
    deref_witness_res dw ∗
    codefrag_pers pc_a allocator_free_code ∗
    ▷ (allocator_cgp_b ↦ₐ Cap RW Global heap_b heap_e next ∗
       cgp ↦ᵣ Cap RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       ca0 ↦ᵣ WInt o ∗
       ca1 ↦ᵣ wreq ∗
       ctp ↦ᵣ WInt o ∗
       deref_witness_res dw ∗
       codefrag_pers pc_a allocator_free_code ∗
       (∃ (p : Perm) (g : Locality) (b e a : Addr),
          ⌜wreq.(lw) = Cap p g b e a ∧ (heap_b < b /\ b < e /\ e <= next)%a⌝ ∗
          PC ↦ₚ Cap RX Global pc_b pc_e (pc_a ^+ allocator_free_block_offset 3) ∗
          ct0 ↦ᵣ Cap RW Global heap_b heap_e next ∗
          ct1 ↦ᵣ WInt b ∗
          ct2 ↦ᵣ WInt e ∗
          ca3 ↦ᵣ WInt 0)
       -∗ WP Exec @ E {{ φ }})
    ⊢ WP Exec @ E {{ φ }}.
  Proof.
    iIntros (Hbounds Hnext Hprefix Hπ)
      "(Hslot & HPC & Hcgp & Hca0 & Hca1 & Hctp & Hct0 & Hct1 & Hct2 & Hct3 & Hdw & #Hcode & Hφ)".
    iApply (allocator_free_check_prefix_spec _ _ _ _ _ _ _ _ _ _ _ _ dw emp%I (λ _, True)
      with "[- $Hslot $HPC $Hcgp $Hca0 $Hca1 $Hctp $Hct0 $Hct1 $Hct2 $Hct3 $Hdw $Hcode]");
      [done|done|done| |].
    { by iIntros (C) "_ _". }
    iNext. iIntros "(Hslot & Hcgp & Hca0 & Hca1 & Hctp & Hdw & _ & _ & [Hvalid | (%Hne & _)])";
      last done.
    iApply "Hφ". iFrame "∗ Hcode".
    iDestruct "Hvalid" as (p g b e a) "(Hreq & _ & Hrest)". iExists p, g, b, e, a. iFrame.
  Qed.

  Lemma allocator_free_check_invalid_spec
    (E : coPset) (pc_b pc_e pc_a next : Addr) (o : Z) (wa0 wreq w0 w1 w2 w3 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_free_code_bounds pc_b pc_e pc_a ->
    ¬ allocator_free_in_prefix next wreq.(lw) ->
    allocator_cgp_b ↦ₐ Cap RW Global heap_b heap_e next ∗
    PC ↦ₚ Cap RX Global pc_b pc_e (pc_a ^+ allocator_free_block_offset 1) ∗
    cgp ↦ᵣ Cap RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
    ca0 ↦ᵣ wa0 ∗
    ca1 ↦ᵣ wreq ∗
    ctp ↦ᵣ WInt o ∗
    ct0 ↦ᵣ w0 ∗
    ct1 ↦ᵣ w1 ∗
    ct2 ↦ᵣ w2 ∗
    ca3 ↦ᵣ w3 ∗
    codefrag_pers pc_a allocator_free_code ∗
    ▷ (allocator_cgp_b ↦ₐ Cap RW Global heap_b heap_e next ∗
       cgp ↦ᵣ Cap RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       ca0 ↦ᵣ WInt o ∗
       ca1 ↦ᵣ wreq ∗
       ctp ↦ᵣ WInt o ∗
       codefrag_pers pc_a allocator_free_code ∗
       PC ↦ₚ Cap RX Global pc_b pc_e (pc_a ^+ allocator_free_invalid_offset) ∗
       ct0 ↦ᵣ - ∗
       ct1 ↦ᵣ - ∗
       ct2 ↦ᵣ - ∗
       ca3 ↦ᵣ -
       -∗ WP Exec @ E {{ φ }})
    ⊢ WP Exec @ E {{ φ }}.
  Proof.
    intros (Hpc & Hpc_shadow & Hcgp_pc) Hrequest.
    destruct wreq as [wreq π]; cbn in Hrequest.
    iIntros "(Hslot & HPC & Hcgp & Hca0 & Hca1 & Hctp & Hct0 & Hct1 & Hct2 & Hct3 & #Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_free_unfold_code "Hcode_main".
    pose proof allocator_cgp_size.

    (* Block 1: the request is a capability *)
    focus_block 1 "Hcode_main" of allocator_free_blocks at pc_a as a_req Ha_req
      "Hcode" "Hcont".
    iHide "Hcode_main" as hcode.
    (* Mov ca0 ctp. *)
    iInstr "Hcode".
    (* GetWType ca3 ca1. *)
    iInstr "Hcode".
    (* Sub ca3 ca3 (encodeWordType wt_cap). *)
    iInstr "Hcode".
    destruct (is_cap wreq) eqn:Hreq_cap; last first.
    { assert (Hnoncap : WInt (encodeWordType wreq - encodeWordType wt_cap) ≠ WInt 0).
      { pose proof (encodeWordType_correct wreq wt_cap) as Hencode.
        intro Hzero. injection Hzero as Hzero.
        assert (Heq : encodeWordType wreq = encodeWordType wt_cap) by lia.
        destruct wreq; cbn in Hreq_cap, Hencode; try discriminate.
        all: try (destruct sb; cbn in Hreq_cap, Hencode; try discriminate); contradiction. }
      (* Jne .free_invalid ca3 0. *)
      iInstr "Hcode".
      { transitivity (Some (pc_a ^+ allocator_free_invalid_offset));
          offsets_compute; solve_addr. }
      unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
      change_pc_to (pc_a ^+ allocator_free_invalid_offset).
      iApply "Hφ". iFrame "∗ Hcode_main". }
    destruct wreq; cbn in Hreq_cap; try done.
    destruct sb; cbn in Hreq_cap; try done.
    rewrite (encodeWordType_correct_cap tag p g b e a true (O LG LM) Global 0%a 0%a 0%a)
      /wt_cap Z.sub_diag.
    (* Jne .free_invalid ca3 0. *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    (* Block 2: the tag and the bounds *)
    focus_block 2 "Hcode_main" of allocator_free_blocks at pc_a as a_check Ha_check
      "Hcode" "Hcont".
    iHide "Hcode_main" as hcode.
    (* GetTag ca3 ca1. *)
    iInstrApply "Hcode" wp_gettag_lax with "[$HPC $Hca1 $Hct3]"
      as (z) "(HPC & Hca1 & Hct3 & %Hz)".
    (* Sub ca3 ca3 1. *)
    iInstr "Hcode".
    destruct (decide (z = 1%Z)) as [->|Hz1]; last first.
    { assert (z = 0%Z) as -> by (destruct Hz as [-> | [-> _] ]; [destruct tag; cbn in *; lia | done]).
      cbn.
      (* Jne .free_invalid ca3 0. *)
      iInstr "Hcode".
      { transitivity (Some (pc_a ^+ allocator_free_invalid_offset));
          offsets_compute; solve_addr. }
      unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
      change_pc_to (pc_a ^+ allocator_free_invalid_offset).
      iApply "Hφ". iFrame "∗ Hcode_main". }
    assert (tag = true) as ->
      by (destruct Hz as [Hz | [Hz _] ]; [destruct tag; cbn in Hz; lia | lia]).
    rewrite Z.sub_diag.
    (* Jne .free_invalid ca3 0. *)
    iInstr "Hcode".
    unfold lword_of_word.
    iPoseProof deref_res_none as "-#Hderef".
    (* CLoad ct0 cgp. *)
    iInstrApply "Hcode" wp_load_success_exact
      with "[$HPC $Hct0 $Hcgp $Hslot $Hderef]"
      as "(HPC & Hct0 & Hcgp & Hslot & _)".
    { apply allocator_cgp_not_shadow. }
    { intros _. left. apply allocator_heap_root_authority. }
    { apply withinBounds_true_iff. solve_addr. }
    { intros Heq. apply Hcgp_pc. rewrite Heq elem_of_finz_seq_between. solve_addr. }
    iEval (rewrite /lload_word /lift_word /=) in "Hct0".
    iEval (cbn [load_word]) in "Hct0".
    (* GetB ct1 ca1. *)
    iInstr "Hcode".
    (* GetE ct2 ca1. *)
    iInstr "Hcode".
    (* GetB ca3 ct0. *)
    iInstr "Hcode".
    (* Lt ca3 ca3 ct1. *)
    iInstr "Hcode".
    destruct (decide (heap_b < b)%a) as [Hbase|Hbase]; last first.
    { replace (heap_b <? b)%Z with false by (symmetry; apply Z.ltb_ge; solve_addr).
      (* Jne .free_base_ok ca3 0. *)
      iInstr "Hcode".
      (* Jmp .free_invalid. *)
      iInstr "Hcode".
      { transitivity (Some (pc_a ^+ allocator_free_invalid_offset));
          offsets_compute; solve_addr. }
      unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
      change_pc_to (pc_a ^+ allocator_free_invalid_offset).
      iApply "Hφ". iFrame "∗ Hcode_main". }
    replace (heap_b <? b)%Z with true by (symmetry; apply Z.ltb_lt; solve_addr).
    (* Jne .free_base_ok ca3 0. *)
    iInstr "Hcode".
    (* Lt ca3 ct1 ct2. *)
    iInstr "Hcode".
    destruct (decide (b < e)%a) as [Hnonempty|Hempty]; last first.
    { replace (b <? e)%Z with false by (symmetry; apply Z.ltb_ge; solve_addr).
      (* Jne .free_nonempty ca3 0. *)
      iInstr "Hcode".
      (* Jmp .free_invalid. *)
      iInstr "Hcode".
      { transitivity (Some (pc_a ^+ allocator_free_invalid_offset));
          offsets_compute; solve_addr. }
      unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
      change_pc_to (pc_a ^+ allocator_free_invalid_offset).
      iApply "Hφ". iFrame "∗ Hcode_main". }
    replace (b <? e)%Z with true by (symmetry; apply Z.ltb_lt; solve_addr).
    (* Jne .free_nonempty ca3 0. *)
    iInstr "Hcode".
    (* GetA ca3 ct0. *)
    iInstr "Hcode".
    (* Lt ca3 ca3 ct2. *)
    iInstr "Hcode".
    destruct (decide (next < e)%a) as [Hpast|Hwithin]; last first.
    { exfalso. apply Hrequest. exists p, g, b, e, a. split; first reflexivity. solve_addr. }
    replace (next <? e)%Z with true by (symmetry; apply Z.ltb_lt; solve_addr).
    (* Jne .free_invalid ca3 0. *)
    iInstr "Hcode".
    { transitivity (Some (pc_a ^+ allocator_free_invalid_offset));
        offsets_compute; solve_addr. }
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
    change_pc_to (pc_a ^+ allocator_free_invalid_offset).
    iApply "Hφ". iFrame "∗ Hcode_main".
  Qed.

End AllocatorFreeCheckBlocks2.
