From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export shapes.step.
From griotte Require Import memory_region shapes.memory_access.

(** * The memory accesses: CLoad and Store

    Per instruction: its memory step in closed form (its membership
    [load_member] or [store_member], and its agreement on the checked path,
    to a cell or to a device), registered in [mem_next_ok_db]; [iInstr]
    steps it with the k-ary rules of [shapes/memory_access.v]. Then the
    rules that clients name: the faults, from the fault rules of
    [shapes/step.v], and success rules, from the load and store rules of
    [shapes/memory_access.v]. *)

(** ** CLoad

    Loads with a witness ([wp_load_witness_imm_one_inbounds]) or with
    either outcome ([wp_load_preserve_or_clear]), and a few success
    rules. *)

(** [CLoad dst src imm] loads at the address that [src] authorises at
    offset [imm], into [dst], through the shadow table. *)
Lemma CLoad_member `{MachineParameters} dst src imm :
  load_member exec_opt griotte_load_filter (CLoad dst src imm) dst src imm.
Proof. solve_mem_access_member. Qed.

(** On the checked path to a cell, [CLoad dst src imm] is the access. *)
Lemma cload_next_ok `{MachineParameters} dst src imm :
  mem_load_next_ok exec_opt griotte_load_filter (CLoad dst src imm) dst src imm.
Proof.
  intros pl φ p ea pv w (g & b & e & a & Hsrc & Hperm & Hadd & Hwb) Hmmio Hpv Hflt.
  rewrite /griotte_load_filter /load_filter in Hflt.
  cbn [exec_opt]. rewrite Hsrc /=. rewrite Hadd /=. rewrite Hperm Hwb /=.
  rewrite Hmmio Hpv /=. revert Hflt.
  destruct (heap_cap_base pv) as [base|];
    [destruct (shadowtbl φ !! base) as [ [] |]|]; intros Hflt; simplify_eq/=; done.
Qed.

(** On the checked path to a device, [CLoad dst src imm] reads the
    device. *)
Lemma cload_next_ok_device `{MachineParameters} dst src imm pl φ p ea :
  mem_access_authorised readAllowed φ src imm p ea → is_mmio_address ea = true →
  exec_opt (CLoad dst src imm) pl φ = (w ← mmio_load φ ea; nextPC (φ .[dst :=ᵣ w])).
Proof.
  intros (g & b & e & a & Hsrc & Hperm & Hadd & Hwb) Hmmio.
  cbn [exec_opt]. rewrite Hsrc /=. rewrite Hadd /=. rewrite Hperm Hwb /=. by rewrite Hmmio.
Qed.

#[export] Hint Resolve CLoad_member cload_next_ok : mem_next_ok_db.


(** *** Faults of [CLoad], on every copy of the owned registers *)

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
      [load_post_choose]) are in [shapes/memory_access.v]. *)

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
    iApply (wp_load_next_2 (W := deref_res πs q) with "[$HPC $Hpc_a $Hr1 $Hr2 $Hea $Hdw]");
      [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply cload_next_ok
      | apply load_choice_exact | by apply deref_res_live | exact Hvpc | exact Hpca'
      | exact Hr1 | exact Hr2 | done | exact Hadd | exact Hra | exact Hwb |].
    iIntros "!> (HPC & Hpc_a & Hr1 & Hr2 & Hea & Hdw)". iApply "HΦ". iFrame.
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
      destruct Hcases as [ (lv & v' & Hlv & Hpost & ->) | (Hnone & _) ];
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
    iApply (wp_load_next_2 (W := emp%I) with "[$HPC $Hi $Hdst $Hsrc $Ha]");
      [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply cload_next_ok
      | apply load_choice_exact | by apply live_witness_no_id | exact Hvpc | exact Hpc'
      | exact Hdst | exact Hsrc | done | by rewrite finz_add_0 | exact Hread | exact Hbounds |].
    iIntros "!> (HPC & Hi & Hdst & Hsrc & Ha & _)".
    iApply ("Hφ" $! (lload_word p raw)). iSplitR; first (iPureIntro; by left). iFrame.
  Qed.

  (* If a points to a capability, the load into PC success if its address can be incr *)

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
      [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply cload_next_ok
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
    iApply (wp_load_next_2 (pc_π := None) (W := emp%I) with "[$HPC $Hi $Hdst $Hsrc $Ha]");
      [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply cload_next_ok
      | apply load_choice_exact | by apply live_witness_no_id | exact Hvpc | exact Hpca'
      | exact Hdst | exact Hsrc | done | exact Hea | exact Hread | exact Hbounds |].
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
        [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply cload_next_ok
        | apply load_choice_sep_l, load_choice_witness
        | apply live_witness_sep_r, deref_witness_live; exact Hπ
        | exact Hvpc | exact Hpca' | exact Hdst | exact Hsrc | done | exact Hea | exact Hread
        | exact Hbounds |].
      iIntros "!>" (actual) "(%Hpost & HPC & Hi & Hdst & Hsrc & [Hwit Hdw])".
      iApply ("HΦ" $! actual). iSplitR; first (iPureIntro; exact Hpost). iFrame.
    - iApply (wp_load_choice_next_2 (pc_π := None)
                (W := (load_witness_res wit ∗ deref_witness_res dw)%I)
                with "[$HPC $Hi $Hdst $Hsrc $Ha $Hwit $Hdw]");
        [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply cload_next_ok
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
      [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply cload_next_ok
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
    iApply (wp_load_next_1 (pc_π := None) (W := emp%I) with "[$HPC $Hi $Hsrc $Ha]");
      [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply cload_next_ok
      | apply load_choice_exact | by apply live_witness_no_id | exact Hvpc | exact Hpca'
      | exact Hr | done | exact Hea | exact Hread | exact Hbounds |].
    iIntros "!> (HPC & Hi & Hsrc & Ha & _)". iApply "HΦ". iFrame.
  Qed.

End load_witness_rules.

(** ** Store

    A few success rules. *)

(** [Store dst ρ imm] writes the word of its argument [ρ] at the address
    that [dst] authorises at offset [imm]; that word has [stored_word_ok]. *)
Lemma Store_member `{MachineParameters} (stored_word_ok : ExecConf → Word → Prop) dst ρ imm :
  (∀ φ w, word_of_argument (reg φ) ρ = Some w → stored_word_ok φ w) →
  store_member exec_opt stored_word_ok (Store dst ρ imm) dst imm.
Proof.
  intros Hwok. solve_mem_access_member_with ltac:(by eapply Hwok).
Qed.

(** The same, with the word of the argument itself. *)
Lemma Store_member_argument `{MachineParameters} dst ρ imm :
  store_member exec_opt (λ φ w, word_of_argument (reg φ) ρ = Some w) (Store dst ρ imm) dst imm.
Proof. apply Store_member. intros φ w Hw. exact Hw. Qed.

(** On the checked path to a cell, [Store dst ρ imm] is the access, of the
    word of [ρ]. *)
Lemma store_next_ok `{MachineParameters} dst ρ imm :
  mem_store_next_ok exec_opt (λ φ w, word_of_argument (reg φ) ρ = Some w) (Store dst ρ imm) dst imm.
Proof.
  intros pl φ p ea w (g & b & e & a & Hdst & Hperm & Hadd & Hwb) Hmmio [v Hv] Hw.
  cbv beta in Hw.
  cbn [exec_opt]. rewrite Hw /=. rewrite Hdst /=. rewrite Hadd /=. rewrite Hperm Hwb /=.
  rewrite Hmmio Hv /=. by rewrite /store_effect.
Qed.

(** On the checked path to a device, [Store dst ρ imm] writes the device. *)
Lemma store_next_ok_device `{MachineParameters} dst ρ imm pl φ p ea w :
  mem_access_authorised writeAllowed φ dst imm p ea → is_mmio_address ea = true →
  word_of_argument (reg φ) ρ = Some w →
  exec_opt (Store dst ρ imm) pl φ = (φ' ← mmio_store φ ea w; nextPC φ').
Proof.
  intros (g & b & e & a & Hdst & Hperm & Hadd & Hwb) Hmmio Hw.
  cbn [exec_opt]. rewrite Hw /=. rewrite Hdst /=. rewrite Hadd /=. rewrite Hperm Hwb /=.
  by rewrite Hmmio.
Qed.

#[export] Hint Resolve Store_member_argument store_next_ok : mem_next_ok_db.


(** *** Faults of [Store], on every copy of the owned registers *)

(** An untagged authority faults. *)
Lemma Store_fault_untagged `{MachineParameters} dst ρ imm p lpc (regs : LReg) wd :
  regs !!ₗ dst = Some wd → get_tag wd.(lw) = false →
  regs_fault exec_opt (Store dst ρ imm) p lpc regs.
Proof.
  intros Hdst Htag φ _ Hcopy.
  destruct (regs_fault_llookup regs φ dst wd Hcopy Hdst) as [s Hlook].
  cbn [exec_opt]. destruct (word_of_argument (reg φ) ρ); cbn; last done.
  rewrite Hlook /=.
  destruct wd as [ [| [ [] p' g b e a|] | |] π]; cbn in Htag; try discriminate;
    destruct s; done.
Qed.

(** An authority that is not a capability faults. *)
Lemma Store_fault_not_cap `{MachineParameters} dst ρ imm p lpc (regs : LReg) wd :
  regs !!ₗ dst = Some wd → is_cap wd.(lw) = false →
  regs_fault exec_opt (Store dst ρ imm) p lpc regs.
Proof.
  intros Hdst Hcap φ _ Hcopy.
  destruct (regs_fault_llookup regs φ dst wd Hcopy Hdst) as [s Hlook].
  cbn [exec_opt]. destruct (word_of_argument (reg φ) ρ); cbn; last done.
  rewrite Hlook /=.
  destruct wd as [ [| [ [] p' g b e a|] | |] π]; cbn in Hcap; try discriminate;
    destruct s; done.
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
  Definition reg_allows_store_imm (regs : LReg) (r : RegName) (imm : Z) p g b e a ea :=
    lw <$> regs !!ₗ r = Some (Cap p g b e a) ∧
    (a + imm)%a = Some ea ∧ writeAllowed p = true ∧ withinBounds b e ea = true.

  Definition reg_allows_store (regs : LReg) (r : RegName) p g b e a :=
    lw <$> regs !!ₗ r = Some (Cap p g b e a) ∧
    writeAllowed p = true ∧ withinBounds b e a = true.

  (** The status-independent part of [shadow_store_ok]: the cell is unclaimed,
      or claimed by a painting allocation. *)
  Definition shadow_perm_ok (R : RegState) (C : gmap Addr AddrClaim) (a : Addr) : Prop :=
    C !! a = Some Unclaimed ∨
    (∃ ι x, C !! a = Some (Claimed ι) ∧ R !! ι = Some x ∧ re_status x = APainting).

  (** A store to one owned cell, apart from the fetched instruction. *)
  Lemma wp_store_next_imm E pc_p pc_g pc_b pc_e pc_a pc_π w dst src (imm : Z) regs
      p g b e a ea storev w' dq dw lpc' :
    decodeInstrW w.(lw) = Store dst src imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Store dst src imm) ⊆ dom regs →
    regs !!ₗ dst = Some (Cap p g b e a @@? deref_id dw) →
    (a + imm)%a = Some ea →
    writeAllowed p = true → withinBounds b e ea = true →
    is_shadow_address ea = false →
    lword_of_argument regs src = Some storev →
    incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ ea ↦ₐ w' ∗
        deref_witness_res dw ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        ea ↦ₐ lstore_word p storev ∗
        deref_witness_res dw ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hdecode Hvpc Dregs Hdst Hadd Hwa Hwb Hsh Harg Hinc φ)
      "(HPC & >Hi & >Ha & Hdw & Hmap) Hφ".
    iDestruct (pointsto_ne with "Ha Hi") as %Hne.
    assert (lw <$> regs !!ₗ dst = Some (Cap p g b e a)) as Hdst' by by rewrite Hdst.
    destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hdst') as (Hdst_cnull & _).
    rewrite llookup_reg_not_cnull // in Hdst.
    iApply (wp_store_next (W := deref_witness_res dw) with "[$HPC $Hi $Ha $Hmap $Hdw]");
      [exact Hdecode | solve_mem_instr_ok | apply Store_member_argument | apply store_next_ok
      | by apply store_lift_argument
      | intros v1 Hv1; rewrite Hdst in Hv1; simplify_eq; by apply deref_witness_live
      | exact Hvpc | split_and!; [exact Hdst' | exact Hadd | exact Hwa | exact Hwb]
      | exact Hne | exact Hinc |].
    iIntros "!> (HPC & Hi & Ha & Hmap & Hdw)". iApply "Hφ". iFrame.
  Qed.

    Lemma wp_store_success_reg_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst src w'
         p g b e a ea (imm : Z) w'' dq q :
     is_shadow_address ea = false →
      decodeInstrW w.(lw) = Store dst (inr src) imm →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ Cap p g b e a @@? π
           ∗ ▷ ea ↦ₐ w'
           ∗ deref_res π q }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ{dq} w
              ∗ src ↦ᵣ w''
              ∗ dst ↦ᵣ Cap p g b e a @@? π
              ∗ ea ↦ₐ lstore_word p w''
              ∗ deref_res π q }}}.
    Proof.
    rewrite deref_res_witness.
    generalize (deref_id_witness_of π q). generalize (deref_witness_of π q).
    intros dw <-.
    iIntros (Hsh Hdecode Hvpc Hpca' Hwa Hwb Hadd Hsrc Hdst φ)
      "(HPC & Hi & >Hsrc & >Hdst & Ha & Hdw) Hφ".
    iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %]".
    iApply (wp_store_next_imm with "[$HPC $Hi $Ha $Hdw $Hmap]"); try solve_next_side.
    iIntros "!> (HPC & Hi & Ha & Hdw & Hmap)". iRegsMap "Hmap".
    iApply "Hφ". iFrame.
    Qed.

   Lemma wp_store_success_z_imm E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst z w'
         p g b e a ea (imm : Z) dq q :
     is_shadow_address ea = false →
     decodeInstrW w.(lw) = Store dst (inl z) imm →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ dst ↦ᵣ Cap p g b e a @@? π
           ∗ ▷ ea ↦ₐ w'
           ∗ deref_res π q }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ{dq} w
              ∗ dst ↦ᵣ Cap p g b e a @@? π
              ∗ ea ↦ₐ WInt z
              ∗ deref_res π q }}}.
   Proof.
    rewrite deref_res_witness.
    generalize (deref_id_witness_of π q). generalize (deref_witness_of π q).
    intros dw <-.
    iIntros (Hsh Hdecode Hvpc Hpca' Hwa Hwb Hadd Hdst φ) "(HPC & Hi & >Hdst & Ha & Hdw) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iApply (wp_store_next_imm with "[$HPC $Hi $Ha $Hdw $Hmap]"); try solve_next_side.
    iIntros "!> (HPC & Hi & Ha & Hdw & Hmap)". iRegsMap "Hmap".
    rewrite lstore_word_canStore; last by apply writeAllowed_canStore_int.
    iApply "Hφ". iFrame.
   Qed.

   Lemma wp_store_fail_reg_not_cap_lword_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_π w
     dst src (wdst : LWord) wstore dq :
      decodeInstrW w.(lw) = Store dst (inr src) imm →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     is_cap wdst.(lw) = false ->
     src ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ src ↦ᵣ wstore
           ∗ ▷ dst ↦ᵣ wdst
     }}}
       Instr Executable @ E
       {{{ RET FaultedV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
           pc_a ↦ₐ{dq} w ∗
           src ↦ᵣ wstore ∗
           dst ↦ᵣ wdst }}}.
    Proof.
    iIntros (Hinstr Hvpc Hcap Hsrc φ) "(HPC & Hi & Hs & Hd) Hφ".
    iApply (wp_instr_faulted_2 with "[$HPC $Hs $Hd $Hi]"); [done | done | | ].
    { intros r sr m st td s1 s2 H1 H2.
      rewrite /exec /= /lookup_reg H1 H2 /= (decide_False _ _ Hsrc) /=.
      case_decide; [done|].
      destruct wdst as [wd ?]; cbn in Hcap.
      destruct_word wd; cbn in Hcap; try discriminate; by destruct s2. }
    iIntros "!> (HPC & Hs & Hd & Hi)".
    iApply "Hφ". iFrame.
    Qed.

   Lemma wp_store_fail_reg_perm_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_π π w dst src
         p g b e a w'' dq :
     decodeInstrW w.(lw) = Store dst (inr src) imm →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     writeAllowed p = false ->
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ Cap p g b e a @@? π
     }}}
       Instr Executable @ E
       {{{ RET FaultedV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
           pc_a ↦ₐ{dq} w ∗
           src ↦ᵣ w'' ∗
           dst ↦ᵣ Cap p g b e a @@? π }}}.
    Proof.
    iIntros (Hinstr Hvpc Hwa Hsrc Hdst φ) "(HPC & Hi & Hs & Hd) Hφ".
    iApply (wp_instr_faulted_2 with "[$HPC $Hs $Hd $Hi]"); [done | done | | ].
    { intros r sr m st td s1 s2 H1 H2.
      rewrite /exec /= /lookup_reg H1 H2 /= !decide_False //.
      destruct s2; cbn; last done.
      destruct (a + imm)%a; cbn; [by rewrite Hwa | done]. }
    iIntros "!> (HPC & Hs & Hd & Hi)".
    iApply "Hφ". iFrame.
    Qed.

    Lemma wp_store_fail_z_perm_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_π π w dst
         p g b e a z dq :
      decodeInstrW w.(lw) = Store dst (inl z) imm →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     writeAllowed p = false ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ dst ↦ᵣ Cap p g b e a @@? π
     }}}
       Instr Executable @ E
       {{{ RET FaultedV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
           pc_a ↦ₐ{dq} w ∗
           dst ↦ᵣ Cap p g b e a @@? π }}}.
    Proof.
    iIntros (Hinstr Hvpc Hwa Hdst φ) "(HPC & Hi & Hd) Hφ".
    iApply (wp_instr_faulted_1 with "[$HPC $Hd $Hi]"); [done | done | | ].
    { intros r sr m st td s1 H1.
      rewrite /exec /= /lookup_reg H1 /= !decide_False //.
      destruct s1; cbn; last done.
      destruct (a + imm)%a; cbn; [by rewrite Hwa | done]. }
    iIntros "!> (HPC & Hd & Hi)".
    iApply "Hφ". iFrame.
    Qed.

   Lemma wp_store_fail_reg_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_π π w dst src
         p g b e a ea w'' dq :
      decodeInstrW w.(lw) = Store dst (inr src) imm →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (a + imm)%a = Some ea →
     withinBounds b e ea = false →
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ Cap p g b e a @@? π
     }}}
       Instr Executable @ E
       {{{ RET FaultedV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
           pc_a ↦ₐ{dq} w ∗
           src ↦ᵣ w'' ∗
           dst ↦ᵣ Cap p g b e a @@? π }}}.
    Proof.
    iIntros (Hinstr Hvpc Hadd Hwb Hsrc Hdst φ) "(HPC & Hi & Hs & Hd) Hφ".
    iApply (wp_instr_faulted_2 with "[$HPC $Hs $Hd $Hi]"); [done | done | | ].
    { intros r sr m st td s1 s2 H1 H2.
      rewrite /exec /= /lookup_reg H1 H2 /= !decide_False //.
      destruct s2; cbn; last done.
      by rewrite Hadd /= Hwb andb_false_r. }
    iIntros "!> (HPC & Hs & Hd & Hi)".
    iApply "Hφ". iFrame.
    Qed.

    Lemma wp_store_fail_z_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_π π w dst
         p g b e a ea z dq :
      decodeInstrW w.(lw) = Store dst (inl z) imm →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (a + imm)%a = Some ea →
     withinBounds b e ea = false →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ dst ↦ᵣ Cap p g b e a @@? π
     }}}
       Instr Executable @ E
       {{{ RET FaultedV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
           pc_a ↦ₐ{dq} w ∗
           dst ↦ᵣ Cap p g b e a @@? π }}}.
    Proof.
    iIntros (Hinstr Hvpc Hadd Hwb Hdst φ) "(HPC & Hi & Hd) Hφ".
    iApply (wp_instr_faulted_1 with "[$HPC $Hd $Hi]"); [done | done | | ].
    { intros r sr m st td s1 H1.
      rewrite /exec /= /lookup_reg H1 /= !decide_False //.
      destruct s1; cbn; last done.
      by rewrite Hadd /= Hwb andb_false_r. }
    iIntros "!> (HPC & Hd & Hi)".
    iApply "Hφ". iFrame.
    Qed.

  Lemma wp_store_fail_tag_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_π
      w dst (src : Z + RegName) regs wa dq :
    decodeInstrW w.(lw) = Store dst src imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs !!ₗ dst = Some wa →
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
    intros Hinstr Hvpc Hdst Htag.
    eapply wp_fault_step; [exact Hinstr | exact Hvpc |].
    by eapply Store_fault_untagged.
  Qed.

Lemma wp_store_fail_reg_overflow_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_π π w dst src
         p g b e a w'' dq :
     decodeInstrW w.(lw) = Store dst (inr src) imm →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (a + imm)%a = None →
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ Cap p g b e a @@? π
     }}}
       Instr Executable @ E
       {{{ RET FaultedV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
           pc_a ↦ₐ{dq} w ∗
           src ↦ᵣ w'' ∗
           dst ↦ᵣ Cap p g b e a @@? π }}}.
    Proof.
    iIntros (Hinstr Hvpc Hadd Hsrc Hdst φ) "(HPC & Hi & Hs & Hd) Hφ".
    iApply (wp_instr_faulted_2 with "[$HPC $Hs $Hd $Hi]"); [done | done | | ].
    { intros r sr m st td s1 s2 H1 H2.
      rewrite /exec /= /lookup_reg H1 H2 /= !decide_False //.
      destruct s2; cbn; last done.
      by rewrite Hadd. }
    iIntros "!> (HPC & Hs & Hd & Hi)".
    iApply "Hφ". iFrame.
    Qed.
Lemma wp_store_fail_z_overflow_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_π π w dst
         p g b e a z dq :
     decodeInstrW w.(lw) = Store dst (inl z) imm →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (a + imm)%a = None →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ dst ↦ᵣ Cap p g b e a @@? π
     }}}
       Instr Executable @ E
       {{{ RET FaultedV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
           pc_a ↦ₐ{dq} w ∗
           dst ↦ᵣ Cap p g b e a @@? π }}}.
    Proof.
    iIntros (Hinstr Hvpc Hadd Hdst φ) "(HPC & Hi & Hd) Hφ".
    iApply (wp_instr_faulted_1 with "[$HPC $Hd $Hi]"); [done | done | | ].
    { intros r sr m st td s1 H1.
      rewrite /exec /= /lookup_reg H1 /= !decide_False //.
      destruct s1; cbn; last done.
      by rewrite Hadd. }
    iIntros "!> (HPC & Hd & Hi)".
    iApply "Hφ". iFrame.
    Qed.

End griotte_lang_rules.

Section shadow_store_res.
  Context `{MP: MachineParameters} `{ceriseg: ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.

  (** A store through a word that is not a capability fails, whatever its
      identifier. *)
  Lemma wp_store_fail_not_cap_imm Ep (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_π
      w dst (src : Z + RegName) regs wa dq :
    decodeInstrW w.(lw) = Store dst src imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs !!ₗ dst = Some wa →
    is_cap wa.(lw) = false →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ RET FaultedV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    intros Hinstr Hvpc Hdst Hcap.
    eapply wp_fault_step; [exact Hinstr | exact Hvpc |].
    by eapply Store_fault_not_cap.
  Qed.

End shadow_store_res.
