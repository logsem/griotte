From iris.proofmode Require Import proofmode.
From griotte Require Import rules_Load rules_Store rules_mem_access.

(** * The derived rules of the shadow region *)
Section mmio_shadow_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types w : LWord.
  Implicit Types reg : gmap RegName LWord.
  Implicit Types ms : gmap Addr LWord.

  (** A load from the shadow region by a live authority [src]: [dst] gets
      the status of the heap address as an integer. *)
  Lemma wp_load_shadow {E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dq dst wd src ws imm}
      {p g b e a ea heap_a status sdq} {W : iProp Σ} :
    decodeInstrW w.(lw) = CLoad dst src imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull → src ≠ cnull →
    ws.(lw) = Cap p g b e a → (a + imm)%a = Some ea → readAllowed p = true →
    withinBounds b e ea = true → live_witness W ws →
    is_shadow_address ea = true → shadow_to_heap ea = Some heap_a →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ wd ∗
        ▷ src ↦ᵣ ws ∗
        ▷ heap_a ↦ₛ{sdq} status ∗
        W }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        dst ↦ᵣ WInt (encodeAllocStatus status) ∗
        src ↦ᵣ ws ∗
        heap_a ↦ₛ{sdq} status ∗
        W }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpc_a' Hdst Hsrc Hws Hadd Hra Hwb Hlive Hshadow Htranslate Φ)
      "(>HPC & >Hpc_a & >Hdst & >Hsrc & >Hsh & Hwit) HΦ".
    iDestruct (map_of_regs_2 with "Hdst Hsrc") as "[Hmap %Hdst_src]".
    iApply (wp_instr_step_nosw with "HPC Hpc_a Hmap"); [rewrite Hinstr; by apply sw_of_none | done |].
    iNext; iIntros (r sr m st td lreg lsreg lmem R C c σ') "@".
    iDestruct (Hlive R with "HR Hwit") as %Hns.
    iDestruct (gen_heap_valid with "Hst Hsh") as %Hst_heap.
    (* The live authority is the physical one, and the device answers. *)
    assert (reg_allows_mem_access MemAccessRead (<[dst := wd]> (<[src := ws]> ∅)) src imm
              p g b e a ea) as Hacc.
    { split_and!; [| exact Hadd | exact Hra | exact Hwb].
      by rewrite llookup_reg_not_cnull // lookup_insert_ne // lookup_insert_eq /= Hws. }
    assert (∀ v, <[dst := wd]> (<[src := ws]> (∅ : LReg)) !! src = Some v →
              ¬ stale_id R v) as Hlive_src.
    { intros v Hv. simplify_map_eq. exact Hns. }
    pose proof (mem_access_authorised_live MemAccessRead R C _ _ _ _ _ _ src imm p g b e a ea
                  Her Hlregs Hlive_src Hacc) as Hauth.
    assert (is_mmio_address ea = true) as Hmmio by (by rewrite /is_mmio_address Hshadow).
    assert (mmio_load (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td) ea =
              Some (WInt (encodeAllocStatus status))) as Hload.
    { by rewrite /mmio_load Hshadow /shadow_load /= Htranslate /= Hst_heap. }
    rewrite Hinstr /exec (cload_next_ok_device dst src imm pc_p _ p ea Hauth Hmmio) Hload /= in Hstep.
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ _ dst
      (lword_of_word (WInt (encodeAllocStatus status))) _ _ _ _
      (λ lpc'' regs' retv, lpc'' = Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∧
         regs' = <[dst := lword_of_word (WInt (encodeAllocStatus status))]ₗ>
                   (<[dst := wd]> (<[src := ws]> ∅)) ∧ retv = NextIV)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [HΦ Hpc_a Hsh Hwit]").
    { exact Her. } { exact Hlregs. }
    { right. rewrite !dom_insert_L. set_solver. }
    { apply reg_word_ok_int. } { exact Hstep. } { apply reg_phys_lword_of_word. }
    { intros lpc'' Hinc. rewrite /incrementPC /incrementPC_gen /= Hpc_a' in Hinc. by simplify_eq. }
    { by rewrite /incrementPC /incrementPC_gen /= Hpc_a'. }
    iIntros (lpc'' regs' retv (-> & -> & ->)) "HPC Hmap".
    rewrite linsert_reg_not_cnull // insert_insert decide_True //.
    iDestruct (regs_of_map_2 with "Hmap") as "[Hdst Hsrc]"; first done.
    iApply "HΦ". iFrame.
  Qed.

  (** A store to the shadow region by a live authority [dst], of the word
      of the argument [ρ]: the status of the heap address becomes the
      status of the stored bits. The status may change if [P] gives the
      permission of the address ([shadow_perm_ok]); otherwise the stored
      status is the current one. *)
  Lemma wp_store_shadow {E pc_p pc_g pc_b pc_e pc_a pc_π w dq dst ρ imm} {regs : LReg}
      {p g b e a ea heap_a v old_status} {P W : iProp Σ} {lpc'} :
    decodeInstrW w.(lw) = Store dst ρ imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    reg_allows_mem_access MemAccessWrite regs dst imm p g b e a ea →
    (∀ v0, regs !! dst = Some v0 → live_witness W v0) →
    lword_of_argument regs ρ = Some v →
    is_shadow_address ea = true → shadow_to_heap ea = Some heap_a →
    (∀ R C,
       reg_auth R -∗
       addr_alloc_auth C -∗
       P -∗
       ⌜old_status = decodeAllocStatus (word_to_bits v.(lw)) ∨ shadow_perm_ok R C heap_a⌝) →
    incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        ▷ heap_a ↦ₛ old_status ∗
        P ∗
        W }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        heap_a ↦ₛ decodeAllocStatus (word_to_bits v.(lw)) ∗
        P ∗
        W }}}.
  Proof.
    iIntros (Hinstr Hvpc Hacc Hlive Hv Hshadow Htranslate Hperm_ok Hinc Φ)
      "(>HPC & >Hpc_a & >Hmap & >Hsh & HPr & Hwit) HΦ".
    iApply (wp_instr_step_nosw with "HPC Hpc_a Hmap"); [rewrite Hinstr; by apply sw_of_none | done |].
    iNext; iIntros (r sr m st td lreg lsreg lmem R C c σ') "@".
    iDestruct (live_witness_cond True W regs dst R (λ _, Hlive) with "HR Hwit") as %Hlive_ok.
    iDestruct (Hperm_ok R C with "HR HC HPr") as %Hallowed.
    iDestruct (gen_heap_valid with "Hst Hsh") as %Hst_heap.
    pose proof (mem_access_authorised_live MemAccessWrite R C _ _ _ _ _ _ dst imm p g b e a ea
                  Her Hlregs (Hlive_ok I) Hacc) as Hauth.
    destruct (store_lift_argument regs ρ v Hv R C _ _ _ _ _ Her Hlregs) as (pw & Hpw & _ & Hphys & _).
    destruct (reg_phys_and_tag _ _ _ Hphys) as [s ->].
    assert (is_mmio_address ea = true) as Hmmio by (by rewrite /is_mmio_address Hshadow).
    rewrite Hinstr /exec (store_next_ok_device dst ρ imm pc_p _ p ea _ Hauth Hmmio Hpw) in Hstep.
    assert (mmio_store (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td) ea (and_tag s v.(lw)) =
              Some (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m
                      (<[heap_a := decodeAllocStatus (word_to_bits v.(lw))]> st) td)) as Hstore.
    { by rewrite /mmio_store Hshadow /shadow_store /= Htranslate /= word_to_bits_and_tag. }
    assert (shadow_store_ok R C st heap_a (decodeAllocStatus (word_to_bits v.(lw)))) as Hsok.
    { destruct Hallowed as [<- | Hperm]; [by left | by right]. }
    pose proof (erasure_shadow_store _ _ _ _ _ _ _ _ _ _ _ _ heap_a _ Her
                  (ex_intro _ _ Hst_heap) Hsok) as Her1.
    destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hinc) as (pc'' & Hu & Her2).
    rewrite Hstore /= Hu /= in Hstep. simplify_eq.
    iMod (gen_heap_update _ _ _ (decodeAllocStatus (word_to_bits v.(lw))) with "Hst Hsh")
      as "[Hst Hsh]".
    iMod (PC_update _ _ lpc' with "HPCa HPC") as "[HPCa HPC]".
    iModIntro. iSplit; first (iPureIntro; by apply sys_kept_same_sreg).
    iSplitR "HΦ HPC Hpc_a Hmap Hsh HPr Hwit".
    { iApply (SI_close _ _ _ _ _ _ _ Her2 with "HPCa Hr Hsr Hm Hst HR HC"). }
    iApply "HΦ". iFrame.
  Qed.

  Lemma wp_load_success_from_shadow E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' p g b e a pc_a' heap_a revoked dq sdq πs :
    πs = None →
    is_shadow_address a = true →
    shadow_to_heap a = Some heap_a →
    decodeInstrW w.(lw) = CLoad r1 r2 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r1 ↦ᵣ w'
        ∗ ▷ r2 ↦ᵣ Cap p g b e a @@? πs
        ∗ ▷ heap_a ↦ₛ{sdq} revoked }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ r1 ↦ᵣ WInt (encodeAllocStatus revoked)
        ∗ pc_a ↦ₐ{dq} w
        ∗ r2 ↦ᵣ Cap p g b e a @@? πs
        ∗ heap_a ↦ₛ{sdq} revoked }}}.
  Proof.
    iIntros (-> Hshadow Htranslate Hinstr Hvpc [Hra Hwb] Hpca' Hcnull Hcnull' φ)
      "(>HPC & >Hi & >Hr1 & >Hr2 & >Ha) Hφ".
    iApply (wp_load_shadow (W := emp%I) with "[$HPC $Hi $Hr1 $Hr2 $Ha]");
      [exact Hinstr | exact Hvpc | exact Hpca' | exact Hcnull | exact Hcnull' | done
      | apply finz_add_0 | exact Hra | exact Hwb | by apply live_witness_no_id
      | exact Hshadow | exact Htranslate |].
    iIntros "!> (HPC & Hi & Hr1 & Hr2 & Ha & _)". iApply "Hφ". iFrame.
  Qed.

  (** Point form of the shadow store, storing the current bit. *)
  Lemma wp_store_success_shadow_z_same E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w
    dst p g b e a revoked heap_a dq :
     π = None →
    is_shadow_address a = true →
    shadow_to_heap a = Some heap_a →
    decodeInstrW w.(lw) = Store dst (inl (encodeAllocStatus revoked)) 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    writeAllowed p = true →
    withinBounds b e a = true →
    dst ≠ cnull →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ Cap p g b e a @@? π ∗
        ▷ heap_a ↦ₛ revoked }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        dst ↦ᵣ Cap p g b e a @@? π ∗
        heap_a ↦ₛ revoked }}}.
  Proof.
    iIntros (-> Hshadow Htranslate Hinstr Hvpc Hpca' Hwa Hwb Hdst φ)
      "(>HPC & >Hi & >Hdst & >Ha) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iApply (wp_store_shadow (P := emp%I) (W := emp%I)
              (v := lword_of_word (WInt (encodeAllocStatus revoked)))
              with "[$HPC $Hi $Hmap $Ha]");
      [exact Hinstr | exact Hvpc
      | split_and!; [by rewrite llookup_reg_not_cnull // lookup_singleton_eq | apply finz_add_0
                    | exact Hwa | exact Hwb]
      | intros v0 Hv0; apply live_witness_no_id; by simplify_map_eq
      | done | exact Hshadow | exact Htranslate
      | iIntros (R C) "_ _ _ !%"; left; by rewrite /= decode_encode_alloc_status_inv
      | by apply incrementPC_add | by iSplit |].
    iIntros "!> (HPC & Hi & Hmap & Ha & _ & _)".
    rewrite (_ : decodeAllocStatus
                   (word_to_bits (lword_of_word (WInt (encodeAllocStatus revoked))).(lw)) = revoked);
      last by rewrite /= decode_encode_alloc_status_inv.
    iDestruct (regs_of_map_1 with "Hmap") as "Hdst".
    iApply "Hφ". iFrame.
  Qed.
End mmio_shadow_rules.

Section mmio_shadow_store_res.
  Context `{MP: MachineParameters} `{ceriseg: ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.

  (** A shadow store of an immediate, justified by any resource [P] that
      gives [shadow_store_ok]; [P] is returned unchanged. *)
  Lemma wp_store_success_shadow_z_res E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w
    dst p g b e a revoked old_revoked heap_a (P : iProp Σ) dq :
     π = None →
    (∀ R C, reg_auth R -∗ addr_alloc_auth C -∗ P -∗ ⌜shadow_perm_ok R C heap_a⌝) →
    is_shadow_address a = true →
    shadow_to_heap a = Some heap_a →
    decodeInstrW w.(lw) = Store dst (inl (encodeAllocStatus revoked)) 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    writeAllowed p = true →
    withinBounds b e a = true →
    dst ≠ cnull →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ Cap p g b e a @@? π ∗
        ▷ heap_a ↦ₛ old_revoked ∗
        P }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        dst ↦ᵣ Cap p g b e a @@? π ∗
        heap_a ↦ₛ revoked ∗
        P }}}.
  Proof.
    iIntros (-> HP Hshadow Htranslate Hinstr Hvpc Hpca' Hwa Hwb Hdst φ)
      "(>HPC & >Hi & >Hdst & >Ha & HPr) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iApply (wp_store_shadow (P := P) (W := emp%I)
              (v := lword_of_word (WInt (encodeAllocStatus revoked)))
              with "[$HPC $Hi $Hmap $Ha $HPr]");
      [exact Hinstr | exact Hvpc
      | split_and!; [by rewrite llookup_reg_not_cnull // lookup_singleton_eq | apply finz_add_0
                    | exact Hwa | exact Hwb]
      | intros v0 Hv0; apply live_witness_no_id; by simplify_map_eq
      | done | exact Hshadow | exact Htranslate
      | iIntros (R C) "HR HC HPr"; iDestruct (HP R C with "HR HC HPr") as %Hok;
        iPureIntro; by right
      | by apply incrementPC_add |].
    iIntros "!> (HPC & Hi & Hmap & Ha & HPr & _)".
    rewrite (_ : decodeAllocStatus
                   (word_to_bits (lword_of_word (WInt (encodeAllocStatus revoked))).(lw)) = revoked);
      last by rewrite /= decode_encode_alloc_status_inv.
    iDestruct (regs_of_map_1 with "Hmap") as "Hdst".
    iApply "Hφ". iFrame.
  Qed.
End mmio_shadow_store_res.
