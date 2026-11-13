From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.
From griotte Require Import rules_mem_access.

(** ** Faults of [CLoad], on every copy of the owned registers *)

(** An untagged source faults. *)
Lemma CLoad_fault_untagged `{MachineParameters} dst src imm p lpc (regs : LReg) wa :
  regs !!ₗ src = Some wa → get_tag wa.(lw) = false →
  regs_fault exec_opt (CLoad dst src imm) p lpc regs.
Proof.
  intros Hsrc Htag φ _ Hcopy.
  destruct (regs_fault_llookup regs φ src wa Hcopy Hsrc) as [s Hlook].
  cbn [exec_opt]. rewrite Hlook /=.
  destruct wa as [ [| [ [] p' g b e a|] | |] π]; cbn in Htag; try discriminate;
    destruct s; done.
Qed.

(** A source that is not a capability faults. *)
Lemma CLoad_fault_not_cap `{MachineParameters} dst src imm p lpc (regs : LReg) wa :
  regs !!ₗ src = Some wa → is_cap wa.(lw) = false →
  regs_fault exec_opt (CLoad dst src imm) p lpc regs.
Proof.
  intros Hsrc Hcap φ _ Hcopy.
  destruct (regs_fault_llookup regs φ src wa Hcopy Hsrc) as [s Hlook].
  cbn [exec_opt]. rewrite Hlook /=.
  destruct wa as [ [| [ [] p' g b e a|] | |] π]; cbn in Hcap; try discriminate;
    destruct s; done.
Qed.

(** A source whose address plus the offset overflows faults. *)
Lemma CLoad_fault_address `{MachineParameters} dst src imm p lpc (regs : LReg) wa pa ga ba ea aa :
  regs !!ₗ src = Some wa → wa.(lw) = Cap pa ga ba ea aa → (aa + imm)%a = None →
  regs_fault exec_opt (CLoad dst src imm) p lpc regs.
Proof.
  intros Hsrc Hwa Hadd φ _ Hcopy.
  destruct (regs_fault_llookup regs φ src wa Hcopy Hsrc) as [s Hlook].
  rewrite Hwa in Hlook.
  cbn [exec_opt]. rewrite Hlook /=.
  destruct s; cbn; [by rewrite Hadd | done].
Qed.

Section griotte_lang_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types w : LWord.
  Implicit Types reg : gmap RegName LWord.
  Implicit Types ms : gmap Addr LWord.

  (* The addressing capability's identifier does not matter: only its
     physical word is read. *)
  Definition reg_allows_load_imm (regs : LReg) (r : RegName) (imm : Z) p g b e a ea :=
    lw <$> regs !!ₗ r = Some (Cap p g b e a) ∧
    (a + imm)%a = Some ea ∧ readAllowed p = true ∧ withinBounds b e ea = true.

  Definition reg_allows_load (regs : LReg) (r : RegName) p g b e a  :=
    lw <$> regs !!ₗ r = Some (Cap p g b e a) ∧
    readAllowed p = true ∧ withinBounds b e a = true.

  (** The status witnesses ([load_witness_ok], [load_witness_lookup],
      [load_post_choose]) are in [rules_mem_access.v]. *)

  Lemma decode_load_not_heap_cap_imm (w : LWord) dst src imm :
    decodeInstrW w.(lw) = CLoad dst src imm → is_heap_cap w.(lw) = false.
  Proof. destruct w as [ [] ?]; cbn; try discriminate; done. Qed.

  Lemma decode_load_not_heap_cap (w : LWord) dst src :
    decodeInstrW w.(lw) = CLoad dst src 0 → is_heap_cap w.(lw) = false.
  Proof. exact (decode_load_not_heap_cap_imm w dst src 0). Qed.

  Lemma wp_load_success_notinstr_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a ea πs (imm : Z) pc_a' dq dq' q :
    is_shadow_address ea = false →
    is_heap_cap w'.(lw) = false →
    decodeInstrW w.(lw) = CLoad r1 r2 imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ Cap p g b e a @@? πs
          ∗ ▷ ea ↦ₐ{dq'} w'
          ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w'
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ Cap p g b e a @@? πs
             ∗ ea ↦ₐ{dq'} w'
             ∗ deref_res πs q }}}.
  Proof.
    iIntros (Hshadow Hheap Hinstr Hvpc [Hra Hwb] Hadd Hpca' Hr1 Hr2 Φ)
      "(>HPC & >Hpc_a & >Hr1 & >Hr2 & >Hea & Hdw) HΦ".
    destruct (decide (ea = pc_a)) as [-> | Hne].
    - iDestruct (pointsto_agree with "Hpc_a Hea") as %<-.
      iApply (wp_load_next_2_pc (W := deref_res πs q) with "[$HPC $Hpc_a $Hr1 $Hr2 $Hdw]");
        [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
        | apply load_choice_exact | by apply deref_res_live | exact Hvpc | exact Hpca'
        | exact Hr1 | exact Hr2 | done | exact Hadd | exact Hra | exact Hwb |].
      iIntros "!> (HPC & Hpc_a & Hr1 & Hr2 & Hdw)". iApply "HΦ". iFrame.
    - iApply (wp_load_next_2 (W := deref_res πs q) with "[$HPC $Hpc_a $Hr1 $Hr2 $Hea $Hdw]");
        [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
        | apply load_choice_exact | by apply deref_res_live | exact Hvpc | exact Hpca'
        | exact Hr1 | exact Hr2 | done | exact Hadd | exact Hra | exact Hwb | exact Hne |].
      iIntros "!> (HPC & Hpc_a & Hr1 & Hr2 & Hea & Hdw)". iApply "HΦ". iFrame.
  Qed.

  Lemma wp_load_success_frominstr_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w'' p g b e a πs (imm : Z) pc_a' dq q :
    is_shadow_address pc_a = false →
    is_heap_cap w.(lw) = false →
    decodeInstrW w.(lw) = CLoad r1 r2 imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e pc_a = true →
    (a + imm)%a = Some pc_a →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ Cap p g b e a @@? πs
          ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ Cap p g b e a @@? πs
             ∗ deref_res πs q }}}.
  Proof.
    iIntros (Hshadow Hheap Hinstr Hvpc [Hra Hwb] Hadd Hpca' Hr1 Hr2 Φ)
      "(>HPC & >Hpc_a & >Hr1 & >Hr2 & Hdw) HΦ".
    iApply (wp_load_next_2_pc (W := deref_res πs q) with "[$HPC $Hpc_a $Hr1 $Hr2 $Hdw]");
      [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
      | apply load_choice_exact | by apply deref_res_live | exact Hvpc | exact Hpca'
      | exact Hr1 | exact Hr2 | done | exact Hadd | exact Hra | exact Hwb |].
    iIntros "!> (HPC & Hpc_a & Hr1 & Hr2 & Hdw)". iApply "HΦ". iFrame.
  Qed.

  Lemma wp_load_success_same_notinstr_imm E r1 pc_p pc_g pc_b pc_e pc_a pc_π w w' p g b e a ea πs (imm : Z) pc_a' dq dq' q :
    is_shadow_address ea = false →
    is_heap_cap w'.(lw) = false →
    decodeInstrW w.(lw) = CLoad r1 r1 imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ Cap p g b e a @@? πs
          ∗ ▷ ea ↦ₐ{dq'} w'
          ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w'
             ∗ pc_a ↦ₐ{dq} w
             ∗ ea ↦ₐ{dq'} w'
             ∗ deref_res πs q }}}.
  Proof.
    iIntros (Hshadow Hheap Hinstr Hvpc Hra Hwb Hadd Hpca' Hr1 Φ)
      "(>HPC & >Hpc_a & >Hr1 & >Hea & Hdw) HΦ".
    destruct (decide (ea = pc_a)) as [-> | Hne].
    - iDestruct (pointsto_agree with "Hpc_a Hea") as %<-.
      iApply (wp_load_next_1_pc (W := deref_res πs q) with "[$HPC $Hpc_a $Hr1 $Hdw]");
        [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
        | apply load_choice_exact | by apply deref_res_live | exact Hvpc | exact Hpca'
        | exact Hr1 | done | exact Hadd | exact Hra | exact Hwb |].
      iIntros "!> (HPC & Hpc_a & Hr1 & Hdw)". iApply "HΦ". iFrame.
    - iApply (wp_load_next_1 (W := deref_res πs q) with "[$HPC $Hpc_a $Hr1 $Hea $Hdw]");
        [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
        | apply load_choice_exact | by apply deref_res_live | exact Hvpc | exact Hpca'
        | exact Hr1 | done | exact Hadd | exact Hra | exact Hwb | exact Hne |].
      iIntros "!> (HPC & Hpc_a & Hr1 & Hea & Hdw)". iApply "HΦ". iFrame.
  Qed.

  Lemma wp_load_success_same_frominstr_imm E r1 pc_p pc_g pc_b pc_e pc_a pc_π w p g b e a πs (imm : Z) pc_a' dq q :
    is_shadow_address pc_a = false →
    is_heap_cap w.(lw) = false →
    decodeInstrW w.(lw) = CLoad r1 r1 imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e pc_a = true →
    (a + imm)%a = Some pc_a →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ Cap p g b e a @@? πs
          ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w
             ∗ pc_a ↦ₐ{dq} w
             ∗ deref_res πs q }}}.
  Proof.
    iIntros (Hshadow Hheap Hinstr Hvpc Hra Hwb Hadd Hpca' Hr1 Φ)
      "(>HPC & >Hpc_a & >Hr1 & Hdw) HΦ".
    iApply (wp_load_next_1_pc (W := deref_res πs q) with "[$HPC $Hpc_a $Hr1 $Hdw]");
      [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
      | apply load_choice_exact | by apply deref_res_live | exact Hvpc | exact Hpca'
      | exact Hr1 | done | exact Hadd | exact Hra | exact Hwb |].
    iIntros "!> (HPC & Hpc_a & Hr1 & Hdw)". iApply "HΦ". iFrame.
  Qed.

  Lemma wp_load_fail_tag_imm E pc_p pc_g pc_b pc_e pc_a pc_π
      w dst src (imm : Z) regs wa dq :
    decodeInstrW w.(lw) = CLoad dst src imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs !!ₗ src = Some wa →
    get_tag wa.(lw) = false →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FaultedV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    intros Hinstr Hvpc Hsrc Htag.
    eapply wp_fault_step; [exact Hinstr | exact Hvpc |].
    by eapply CLoad_fault_untagged.
  Qed.

  Lemma wp_load_fail_not_ra_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a πs (imm : Z) dq :
    decodeInstrW w.(lw) = CLoad r1 r2 imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = false ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ Cap p g b e a @@? πs
    }}}
       Instr Executable @ E
       {{{ RET FaultedV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
           pc_a ↦ₐ{dq} w ∗
           r1 ↦ᵣ w'' ∗
           r2 ↦ᵣ Cap p g b e a @@? πs }}}.
  Proof.
    iIntros (Hdecode Hvpc Hra Hsrc φ) "(HPC & Hi & Hd & Hs) Hφ".
    iApply (wp_instr_faulted_2 with "[$HPC $Hd $Hs $Hi]"); [done | done | | ].
    { intros r sr m st td s1 s2 H1 H2.
      rewrite /exec /= /lookup_reg H2 /= (decide_False _ _ Hsrc) /=.
      destruct s2; cbn; last done.
      destruct (a + imm)%a; cbn; [by rewrite Hra | done]. }
    iIntros "!> (HPC & Hd & Hs & Hi)".
    iApply "Hφ". iFrame.
  Qed.

  Lemma wp_load_fail_not_withinbounds_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a ea πs (imm : Z) dq :
    decodeInstrW w.(lw) = CLoad r1 r2 imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    withinBounds b e ea = false →
    (a + imm)%a = Some ea →
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ Cap p g b e a @@? πs
    }}}
       Instr Executable @ E
       {{{ RET FaultedV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
           pc_a ↦ₐ{dq} w ∗
           r1 ↦ᵣ w'' ∗
           r2 ↦ᵣ Cap p g b e a @@? πs }}}.
  Proof.
    iIntros (Hdecode Hvpc Hwb Hadd Hsrc φ) "(HPC & Hi & Hd & Hs) Hφ".
    iApply (wp_instr_faulted_2 with "[$HPC $Hd $Hs $Hi]"); [done | done | | ].
    { intros r sr m st td s1 s2 H1 H2.
      rewrite /exec /= /lookup_reg H2 /= (decide_False _ _ Hsrc) /=.
      destruct s2; cbn; last done.
      by rewrite Hadd /= Hwb andb_false_r. }
    iIntros "!> (HPC & Hd & Hs & Hi)".
    iApply "Hφ". iFrame.
  Qed.

  Lemma wp_load_fail_addr_imm E pc_p pc_g pc_b pc_e pc_a pc_π
      w dst src (imm : Z) regs wa p g b e a dq :
    decodeInstrW w.(lw) = CLoad dst src imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs !!ₗ src = Some wa →
    wa.(lw) = Cap p g b e a →
    (a + imm)%a = None →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FaultedV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    intros Hinstr Hvpc Hsrc Hwa Hadd.
    eapply wp_fault_step; [exact Hinstr | exact Hvpc |].
    by eapply CLoad_fault_address.
  Qed.

  Lemma wp_load_fail_const_imm E pc_p pc_g pc_b pc_e pc_a pc_π
      w dst src (imm : Z) regs wa dq :
    decodeInstrW w.(lw) = CLoad dst src imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs !!ₗ src = Some wa →
    is_cap wa.(lw) = false →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FaultedV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    intros Hinstr Hvpc Hsrc Hcap.
    eapply wp_fault_step; [exact Hinstr | exact Hvpc |].
    by eapply CLoad_fault_not_cap.
  Qed.

  Lemma wp_load_fail_not_cap_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' (wsrc : LWord) (imm : Z) dq :
    decodeInstrW w.(lw) = CLoad r1 r2 imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    is_cap wsrc.(lw) = false ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ wsrc
    }}}
       Instr Executable @ E
       {{{ RET FaultedV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
           pc_a ↦ₐ{dq} w ∗
           r1 ↦ᵣ w'' ∗
           r2 ↦ᵣ wsrc }}}.
  Proof.
    iIntros (Hdecode Hvpc Hcap φ) "(>HPC & >Hi & >Hdst & >Hsrc) Hφ".
    iDestruct (map_of_regs_2 with "Hdst Hsrc") as "[Hmap %Hne]".
    iApply (wp_load_fail_const_imm E pc_p pc_g pc_b pc_e pc_a pc_π w r1 r2 imm _ (if decide (r2 = cnull) then lnull else wsrc) with "[$HPC $Hi $Hmap]"); eauto; simplify_map_eq; eauto.
    1,2: case_decide; done.
    iNext. iIntros "(HPC & Hi & Hmap)".
    iDestruct (regs_of_map_2 with "Hmap") as "[Hdst Hsrc]"; first done.
    iApply "Hφ". iFrame.
  Qed.

  Lemma wp_load_success_notinstr E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a pc_a' dq dq' πs q :
    is_shadow_address a = false →
    is_heap_cap w'.(lw) = false →
    decodeInstrW w.(lw) = CLoad r1 r2 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ Cap p g b e a @@? πs
          ∗ ▷ a ↦ₐ{dq'} w'
          ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w'
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ Cap p g b e a @@? πs
             ∗ a ↦ₐ{dq'} w'
             ∗ deref_res πs q }}}.
  Proof.
    intros.
    eapply wp_load_success_notinstr_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

  (** Without shadow ownership, a load may fail or clear the loaded tag of a
      heap capability ([lload_heap]), in addition to the permission
      transformation performed by [load_word]. *)
  Lemma wp_load_preserve_or_clear E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' πs
    dst src (wi wd : LWord) p g b e a (raw : LWord) dq :
    readAllowed p = true ->
    is_shadow_address a = false ->
    decodeInstrW wi.(lw) = CLoad dst src 0 ->
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) ->
    withinBounds b e a = true ->
    (pc_a + 1)%a = Some pc_a' ->
    dst ≠ cnull -> src ≠ cnull ->
    {{{ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ wd ∗ src ↦ᵣ Cap p g b e a @@? πs ∗ a ↦ₐ raw }}}
      Instr Executable @ E
    {{{ retv, RET retv;
        (⌜retv = FaultedV⌝ ∗
         PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
         pc_a ↦ₐ{dq} wi ∗
         dst ↦ᵣ wd ∗
         src ↦ᵣ Cap p g b e a @@? πs ∗
         a ↦ₐ raw) ∨
        ∃ actual, ⌜retv = NextIV⌝ ∗
        ⌜lload_heap (lload_word p raw) actual⌝ ∗
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗ pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ actual ∗ src ↦ᵣ Cap p g b e a @@? πs ∗ a ↦ₐ raw }}}.
  Proof.
    iIntros (Hread Hshadow Hinstr Hvpc Hbounds Hpc' Hdst Hsrc φ)
      "(HPC & Hi & Hdst & Hsrc & Ha) Hφ".
    iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %Hsrc_dst]".
    iDestruct (memMap_resource_2ne_apply_dq with "Hi Ha") as "[Hmem %Hpc_a]".
    iApply (wp_load_step _ pc_p pc_g pc_b pc_e pc_a pc_π wi (CLoad dst src 0) dst src 0
              griotte_load_filter load_exact (<[pc_a := wi]> (<[a := raw]> ∅))
              (<[pc_a := dq]> (<[a := DfracOwn 1]> ∅)) with "[$HPC $Hmem $Hmap]");
      [exact Hinstr | apply CLoad_member | apply load_choice_exact | solve_mem_instr_ok
      | exact Hvpc | rewrite !dom_insert_L; set_solver
      | right; rewrite !dom_insert_L; set_solver | by simplify_map_eq
      | by rewrite !dom_insert_L | |].
    { intros p0 g0 b0 e0 a0 ea0 (Hsrc0 & Hadd0 & _).
      rewrite llookup_reg_not_cnull // lookup_insert_eq /= in Hsrc0. simplify_eq.
      rewrite finz_add_0 in Hadd0. simplify_eq.
      right. split; [by simplify_map_eq | done]. }
    iIntros "!>" (lpc' regs' retv) "(%Hres & HPC & Hmem & Hmap)".
    iDestruct (memMap_resource_2ne_dq _ _ _ _ _ _ Hpc_a with "Hmem") as "[Hi Ha]".
    destruct Hres as [ (-> & -> & ->)
                     | (p1 & g1 & b1 & e1 & a1 & ea1 & (Hsrc1 & Hadd1 & _) & -> & Hinc & Hcases) ].
    - (* A fault. *)
      iDestruct (regs_of_map_2 with "Hmap") as "[Hsrc Hdst]"; first done.
      iApply "Hφ". iLeft. by iFrame.
    - (* The cell, exactly. *)
      rewrite llookup_reg_not_cnull // lookup_insert_eq /= in Hsrc1. simplify_eq.
      rewrite finz_add_0 in Hadd1. simplify_eq.
      rewrite /incrementPC /incrementPC_gen /= Hpc' in Hinc. simplify_eq.
      destruct Hcases as [ (lv & v' & Hlv & Hpost & ->) | (_ & Hnone & _) ];
        last by simplify_map_eq.
      simplify_map_eq. rewrite /load_exact in Hpost. subst v'.
      rewrite (insert_insert_ne _ dst src) // insert_insert_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "[Hsrc Hdst]"; first done.
      iApply "Hφ". iRight. iExists (lload_word p1 lv).
      iSplitR; first done.
      iSplitR; first (iPureIntro; by left).
      iFrame.
  Qed.

  (** [wp_load_preserve_or_clear] for a source capability without an
      identifier: the load cannot fault. *)
  Lemma wp_load_preserve_or_clear_noid E pc_p pc_g pc_b pc_e pc_a pc_π pc_a'
    dst src (wi wd : LWord) p g b e a (raw : LWord) dq :
    readAllowed p = true ->
    is_shadow_address a = false ->
    decodeInstrW wi.(lw) = CLoad dst src 0 ->
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) ->
    withinBounds b e a = true ->
    (pc_a + 1)%a = Some pc_a' ->
    dst ≠ cnull -> src ≠ cnull ->
    {{{ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ wd ∗
        src ↦ᵣ Cap p g b e a ∗
        a ↦ₐ raw }}}
      Instr Executable @ E
    {{{ actual, RET NextIV;
        ⌜lload_heap (lload_word p raw) actual⌝ ∗
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ actual ∗
        src ↦ᵣ Cap p g b e a ∗
        a ↦ₐ raw }}}.
  Proof.
    iIntros (Hread Hshadow Hinstr Hvpc Hbounds Hpc' Hdst Hsrc φ)
      "(HPC & Hi & Hdst & Hsrc & Ha) Hφ".
    iDestruct (pointsto_ne with "Ha Hi") as %Hne.
    iApply (wp_load_next_2 (W := emp%I) with "[$HPC $Hi $Hdst $Hsrc $Ha]");
      [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
      | apply load_choice_exact | by apply live_witness_no_id | exact Hvpc | exact Hpc'
      | exact Hdst | exact Hsrc | done | by rewrite finz_add_0 | exact Hread | exact Hbounds
      | done |].
    iIntros "!> (HPC & Hi & Hdst & Hsrc & Ha & _)".
    iApply ("Hφ" $! (lload_word p raw)). iSplitR; first (iPureIntro; by left). iFrame.
  Qed.

  Lemma wp_load_success_frominstr E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w'' p g b e pc_a' dq πs q :
    is_shadow_address pc_a = false →
    decodeInstrW w.(lw) = CLoad r1 r2 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e pc_a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ Cap p g b e pc_a @@? πs
          ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ Cap p g b e pc_a @@? πs
             ∗ deref_res πs q }}}.
  Proof.
    intros.
    eapply wp_load_success_frominstr_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

  Lemma wp_load_success_same_notinstr E r1 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a pc_a' dq dq' πs q :
    is_shadow_address a = false →
    is_heap_cap w'.(lw) = false →
    decodeInstrW w.(lw) = CLoad r1 r1 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ Cap p g b e a @@? πs
          ∗ ▷ a ↦ₐ{dq'} w'
          ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w'
             ∗ pc_a ↦ₐ{dq} w
             ∗ a ↦ₐ{dq'} w'
             ∗ deref_res πs q }}}.
  Proof.
    intros.
    eapply wp_load_success_same_notinstr_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

  Lemma wp_load_success_same_frominstr E r1 pc_p pc_g pc_b pc_e pc_a pc_π w p g b e pc_a' dq πs q :
    is_shadow_address pc_a = false →
    decodeInstrW w.(lw) = CLoad r1 r1 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e pc_a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ Cap p g b e pc_a @@? πs
          ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w
             ∗ pc_a ↦ₐ{dq} w
             ∗ deref_res πs q }}}.
  Proof.
    intros.
    eapply wp_load_success_same_frominstr_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

  (* If a points to a capability, the load into PC success if its address can be incr *)

  Lemma wp_load_success_alt E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a pc_a' πs dq q :
    is_shadow_address a = false →
    is_heap_cap w'.(lw) = false →
    decodeInstrW w.(lw) = CLoad r1 r2 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ Cap p g b e a @@? πs
          ∗ ▷ a ↦ₐ w'
          ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w'
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ Cap p g b e a @@? πs
             ∗ a ↦ₐ w'
             ∗ deref_res πs q }}}.
  Proof.
    intros. eapply wp_load_success_notinstr; eauto.
  Qed.

  (* Non-revoked heap capabilities use the usual load_word transformation. *)

  (* Revocation clears the validity tag after the ordinary load transformation. *)
  Lemma wp_load_fail_tag E pc_p pc_g pc_b pc_e pc_a pc_π
      w dst src regs wa dq :
    decodeInstrW w.(lw) = CLoad dst src 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs !!ₗ src = Some wa →
    get_tag wa.(lw) = false →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FaultedV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    intros.
    eapply wp_load_fail_tag_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

End griotte_lang_rules.

Section load_witness_rules.
  Context `{MP: MachineParameters} `{ceriseg: ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.

  (** Loading an identifier-less word that satisfies [load_exact_cond]
      (e.g. a heap root, which has authority) keeps it exactly: the fourth
      variant of the load rule. *)
  Lemma wp_load_success_exact E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w''
      p g b e a pc_a' πs dq q :
    is_shadow_address a = false →
    w'.(lprov) = None →
    load_exact_cond w' →
    decodeInstrW w.(lw) = CLoad r1 r2 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    a ≠ pc_a →
    r1 ≠ cnull → r2 ≠ cnull → r1 ≠ r2 →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r1 ↦ᵣ w'' ∗
        ▷ r2 ↦ᵣ Cap p g b e a @@? πs ∗
        ▷ a ↦ₐ w' ∗
        deref_res πs q }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        r1 ↦ᵣ lload_word p w' ∗
        r2 ↦ᵣ Cap p g b e a @@? πs ∗
        a ↦ₐ w' ∗
        deref_res πs q }}}.
  Proof.
    iIntros (Hshadow Hπ Hexact Hinstr Hvpc Hra Hwb Hpca' Hne Hr1 Hr2 Hr12 φ)
      "(>HPC & >Hi & >Hr1 & >Hr2 & >Ha & Hdw) Hφ".
    iApply (wp_load_next_2 (W := deref_res πs q) with "[$HPC $Hi $Hr1 $Hr2 $Ha $Hdw]");
      [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
      | apply load_choice_exact | by apply deref_res_live | exact Hvpc | exact Hpca'
      | exact Hr1 | exact Hr2 | done | by rewrite finz_add_0 | exact Hra | exact Hwb
      | exact Hne |].
    iIntros "!> (HPC & Hi & Hr1 & Hr2 & Ha & Hdw)". iApply "Hφ". iFrame.
  Qed.

  (** A load with a status witness, through a readable source capability
      in bounds, without identifier: the load cannot fault. *)
  Lemma wp_load_witness_imm_one_inbounds E pc_p pc_g pc_b pc_e pc_a pc_a' dst src
      (imm : Z) (wi wd : LWord) dq p g b e a_src a (raw : LWord) wit :
    decodeInstrW wi.(lw) = CLoad dst src imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (a_src + imm)%a = Some a →
    is_shadow_address a = false →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    src ≠ cnull →
    {{{ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a ∗
        pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ wd ∗
        src ↦ᵣ Cap p g b e a_src ∗
        a ↦ₐ raw ∗
        load_witness_res wit }}}
      Instr Executable @ E
    {{{ actual, RET NextIV;
        ⌜load_post wit p raw actual⌝ ∗
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' ∗
        pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ actual ∗
        src ↦ᵣ Cap p g b e a_src ∗
        a ↦ₐ raw ∗
        load_witness_res wit }}}.
  Proof.
    iIntros (Hinstr Hvpc Hea Hnot_shadow Hread Hbounds Hpca' Hdst Hsrc Φ)
      "(HPC & Hi & Hdst & Hsrc & Ha & Hwit) HΦ".
    iDestruct (pointsto_ne with "Ha Hi") as %Hne.
    iApply (wp_load_choice_next_2 (pc_π := None) (W := load_witness_res wit)
              with "[$HPC $Hi $Hdst $Hsrc $Ha $Hwit]");
      [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
      | apply load_choice_witness | by apply live_witness_no_id | exact Hvpc | exact Hpca'
      | exact Hdst | exact Hsrc | done | exact Hea | exact Hread | exact Hbounds | done |].
    iIntros "!>" (actual) "(%Hpost & HPC & Hi & Hdst & Hsrc & Ha & Hwit)".
    iApply ("HΦ" $! actual). iSplitR; first (iPureIntro; exact Hpost). iFrame.
  Qed.

  (** [wp_load_witness_imm_one_inbounds] for a cell of any fraction: the
      loaded word is exact. *)
  Lemma wp_load_witness_imm_one_inbounds_dq E pc_p pc_g pc_b pc_e pc_a pc_a' dst src
      (imm : Z) (wi wd : LWord) dq dq' p g b e a_src a (raw : LWord) :
    decodeInstrW wi.(lw) = CLoad dst src imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (a_src + imm)%a = Some a →
    is_shadow_address a = false →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    src ≠ cnull →
    {{{ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a ∗
        pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ wd ∗
        src ↦ᵣ Cap p g b e a_src ∗
        a ↦ₐ{dq'} raw }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' ∗
        pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ lload_word p raw ∗
        src ↦ᵣ Cap p g b e a_src ∗
        a ↦ₐ{dq'} raw }}}.
  Proof.
    iIntros (Hinstr Hvpc Hea Hnot_shadow Hread Hbounds Hpca' Hdst Hsrc Φ)
      "(HPC & Hi & Hdst & Hsrc & Ha) HΦ".
    destruct (decide (a = pc_a)) as [-> | Hne].
    - iDestruct (pointsto_agree with "Ha Hi") as %->.
      iApply (wp_load_next_2_pc (pc_π := None) (W := emp%I) with "[$HPC $Hi $Hdst $Hsrc]");
        [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
        | apply load_choice_exact | by apply live_witness_no_id | exact Hvpc | exact Hpca'
        | exact Hdst | exact Hsrc | done | exact Hea | exact Hread | exact Hbounds |].
      iIntros "!> (HPC & Hi & Hdst & Hsrc & _)". iApply "HΦ". iFrame.
    - iApply (wp_load_next_2 (pc_π := None) (W := emp%I) with "[$HPC $Hi $Hdst $Hsrc $Ha]");
        [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
        | apply load_choice_exact | by apply live_witness_no_id | exact Hvpc | exact Hpca'
        | exact Hdst | exact Hsrc | done | exact Hea | exact Hread | exact Hbounds
        | exact Hne |].
      iIntros "!> (HPC & Hi & Hdst & Hsrc & Ha & _)". iApply "HΦ". iFrame.
  Qed.

  (** A load of a cell of any fraction, through a capability with an
      identifier [π], under a status witness and a dereference witness of
      [π]. *)
  Lemma wp_load_witness_imm_one_inbounds_deref E pc_p pc_g pc_b pc_e pc_a pc_a'
      dst src (imm : Z) (wi wd : LWord) dq dq' p g b e a_src a π (raw : LWord) wit dw :
    decodeInstrW wi.(lw) = CLoad dst src imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (a_src + imm)%a = Some a →
    is_shadow_address a = false →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    π = deref_id dw →
    dst ≠ cnull →
    src ≠ cnull →
    {{{ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a ∗
        pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ wd ∗
        src ↦ᵣ (Cap p g b e a_src @@? π) ∗
        a ↦ₐ{dq'} raw ∗
        load_witness_res wit ∗
        deref_witness_res dw }}}
      Instr Executable @ E
    {{{ actual, RET NextIV;
        ⌜load_post wit p raw actual⌝ ∗
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' ∗
        pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ actual ∗
        src ↦ᵣ (Cap p g b e a_src @@? π) ∗
        a ↦ₐ{dq'} raw ∗
        load_witness_res wit ∗
        deref_witness_res dw }}}.
  Proof.
    iIntros (Hinstr Hvpc Hea Hnot_shadow Hread Hbounds Hpca' Hπ Hdst Hsrc Φ)
      "(HPC & Hi & Hdst & Hsrc & Ha & Hwit & Hdw) HΦ".
    destruct (decide (a = pc_a)) as [-> | Hne].
    - iDestruct (pointsto_agree with "Ha Hi") as %->.
      iApply (wp_load_choice_next_2_pc (pc_π := None)
                (W := (load_witness_res wit ∗ deref_witness_res dw)%I)
                with "[$HPC $Hi $Hdst $Hsrc $Hwit $Hdw]");
        [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
        | apply load_choice_sep_l, load_choice_witness
        | apply live_witness_sep_r, deref_witness_live; exact Hπ
        | exact Hvpc | exact Hpca' | exact Hdst | exact Hsrc | done | exact Hea | exact Hread
        | exact Hbounds |].
      iIntros "!>" (actual) "(%Hpost & HPC & Hi & Hdst & Hsrc & [Hwit Hdw])".
      iApply ("HΦ" $! actual). iSplitR; first (iPureIntro; exact Hpost). iFrame.
    - iApply (wp_load_choice_next_2 (pc_π := None)
                (W := (load_witness_res wit ∗ deref_witness_res dw)%I)
                with "[$HPC $Hi $Hdst $Hsrc $Ha $Hwit $Hdw]");
        [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
        | apply load_choice_sep_l, load_choice_witness
        | apply live_witness_sep_r, deref_witness_live; exact Hπ
        | exact Hvpc | exact Hpca' | exact Hdst | exact Hsrc | done | exact Hea | exact Hread
        | exact Hbounds | exact Hne |].
      iIntros "!>" (actual) "(%Hpost & HPC & Hi & Hdst & Hsrc & Ha & [Hwit Hdw])".
      iApply ("HΦ" $! actual). iSplitR; first (iPureIntro; exact Hpost). iFrame.
  Qed.

  (** [wp_load_witness_imm_one_inbounds] when the destination is the
      source register. *)
  Lemma wp_load_witness_imm_same_inbounds E pc_p pc_g pc_b pc_e pc_a pc_a' r
      (imm : Z) (wi : LWord) dq p g b e a_src a (raw : LWord) wit :
    decodeInstrW wi.(lw) = CLoad r r imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (a_src + imm)%a = Some a →
    is_shadow_address a = false →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r ≠ cnull →
    {{{ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a ∗
        pc_a ↦ₐ{dq} wi ∗
        r ↦ᵣ Cap p g b e a_src ∗
        a ↦ₐ raw ∗
        load_witness_res wit }}}
      Instr Executable @ E
    {{{ actual, RET NextIV;
        ⌜load_post wit p raw actual⌝ ∗
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' ∗
        pc_a ↦ₐ{dq} wi ∗
        r ↦ᵣ actual ∗
        a ↦ₐ raw ∗
        load_witness_res wit }}}.
  Proof.
    iIntros (Hinstr Hvpc Hea Hnot_shadow Hread Hbounds Hpca' Hr Φ)
      "(HPC & Hi & Hsrc & Ha & Hwit) HΦ".
    iDestruct (pointsto_ne with "Ha Hi") as %Hne.
    iApply (wp_load_choice_next_1 (pc_π := None) (W := load_witness_res wit)
              with "[$HPC $Hi $Hsrc $Ha $Hwit]");
      [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
      | apply load_choice_witness | by apply live_witness_no_id | exact Hvpc | exact Hpca'
      | exact Hr | done | exact Hea | exact Hread | exact Hbounds | done |].
    iIntros "!>" (actual) "(%Hpost & HPC & Hi & Hsrc & Ha & Hwit)".
    iApply ("HΦ" $! actual). iSplitR; first (iPureIntro; exact Hpost). iFrame.
  Qed.

  (** [wp_load_witness_imm_one_inbounds_dq] when the destination is the
      source register: the loaded word is exact. *)
  Lemma wp_load_witness_imm_same_inbounds_dq E pc_p pc_g pc_b pc_e pc_a pc_a' r
      (imm : Z) (wi : LWord) dq dq' p g b e a_src a (raw : LWord) :
    decodeInstrW wi.(lw) = CLoad r r imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (a_src + imm)%a = Some a →
    is_shadow_address a = false →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r ≠ cnull →
    {{{ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a ∗
        pc_a ↦ₐ{dq} wi ∗
        r ↦ᵣ Cap p g b e a_src ∗
        a ↦ₐ{dq'} raw }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' ∗
        pc_a ↦ₐ{dq} wi ∗
        r ↦ᵣ lload_word p raw ∗
        a ↦ₐ{dq'} raw }}}.
  Proof.
    iIntros (Hinstr Hvpc Hea Hnot_shadow Hread Hbounds Hpca' Hr Φ)
      "(HPC & Hi & Hsrc & Ha) HΦ".
    destruct (decide (a = pc_a)) as [-> | Hne].
    - iDestruct (pointsto_agree with "Ha Hi") as %->.
      iApply (wp_load_next_1_pc (pc_π := None) (W := emp%I) with "[$HPC $Hi $Hsrc]");
        [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
        | apply load_choice_exact | by apply live_witness_no_id | exact Hvpc | exact Hpca'
        | exact Hr | done | exact Hea | exact Hread | exact Hbounds |].
      iIntros "!> (HPC & Hi & Hsrc & _)". iApply "HΦ". iFrame.
    - iApply (wp_load_next_1 (pc_π := None) (W := emp%I) with "[$HPC $Hi $Hsrc $Ha]");
        [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
        | apply load_choice_exact | by apply live_witness_no_id | exact Hvpc | exact Hpca'
        | exact Hr | done | exact Hea | exact Hread | exact Hbounds | exact Hne |].
      iIntros "!> (HPC & Hi & Hsrc & Ha & _)". iApply "HΦ". iFrame.
  Qed.

End load_witness_rules.
