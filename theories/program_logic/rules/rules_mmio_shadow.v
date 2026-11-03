From iris.proofmode Require Import proofmode.
From griotte Require Import rules_Load rules_Store.

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

  (* Reading a shadow-table entry returns its Boolean value as an integer. *)
  Lemma wp_load_success_shadow E pc_p pc_g pc_b pc_e pc_a pc_π
    dst src w regs mem dq shadow sdq p g b e a heap_a revoked lpc' :
    decodeInstrW w.(lw) = CLoad dst src 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (CLoad dst src 0) ⊆ dom regs →
    mem !! pc_a = Some w →
    reg_allows_load regs src p g b e a →
    (∀ v : LWord, regs !!ₗ src = Some v → v.(lprov) = None) →
    is_shadow_address a = true →
    shadow_to_heap a = Some heap_a →
    shadow !! heap_a = Some revoked →
    incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        (▷ [∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
        (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ{sdq} revoked) ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ lpc' ∗
        ([∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
        ([∗ map] a↦revoked ∈ shadow, a ↦ₛ{sdq} revoked) ∗
        [∗ map] k↦y ∈ <[dst:=WInt (encodeAllocStatus revoked)]ₗ> regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hmem Hallow Hnoid Hshadow Htranslate Hlookup Hinc φ)
      "(>HPC & >Hmem & >Hshadow & >Hmap) Hφ".
    iDestruct (mem_remove_dq with "Hmem") as "Hmem".
    iApply (wp_load_general _ pc_p pc_g pc_b pc_e pc_a pc_π dst src w mem _ regs shadow sdq LoadPlain DerefNoId
      with "[$HPC $Hmem $Hshadow $Hmap]"); eauto.
    { intros p0 g0 b0 e0 a0 (Hsrc0 & _).
      destruct Hallow as (Hsrc & _). rewrite Hsrc in Hsrc0. simplify_eq.
      rewrite Hshadow. exists heap_a. split; first done. by eexists. }
    { rewrite create_gmap_default_dom list_to_set_elements_L. auto. }
    iNext. iIntros (lpc0 regs0 retv) "(%Hspec & HPC & Hmem & Hshadow & _ & _ & Hmap)".
    iDestruct (mem_remove_dq with "Hmem") as "Hmem".
    destruct Hallow as (Hsrc & Hra & Hwb).
    destruct Hspec as
      [p0 g0 b0 e0 a0 v0 v0' (Hsrc0 & _) Hshadow0
      |p0 g0 b0 e0 a0 heap_a0 revoked0 (Hsrc0 & _) Hshadow0 Htranslate0 Hlookup0 Hinc0
      |p0 g0 b0 e0 a0 (Hsrc0 & _) Hrev0
      |p0 g0 b0 e0 a0 z (Hsrc0 & _) Htdev0 _ _ _
      |Hfail].
    - rewrite Hsrc in Hsrc0. simplify_eq. congruence.
    - rewrite Hsrc in Hsrc0. simplify_eq. rewrite Hlookup in Hlookup0. simplify_eq.
      iApply "Hφ". iFrame.
    - rewrite Hsrc in Hsrc0. simplify_eq. exfalso.
      apply is_revoker_address_spec in Hrev0. subst.
      by rewrite revoker_not_shadow_address in Hshadow.
    - rewrite Hsrc in Hsrc0. simplify_eq. exfalso.
      by rewrite (time_device_not_shadow_address _ Htdev0) in Hshadow.
    - exfalso.
      destruct Hfail as
        [w0 Hsrc0 Hcap0|p0 g0 b0 e0 a0 Hsrc0|p0 g0 b0 e0 a0 Hsrc0 Hadd0
        |p0 g0 b0 e0 a0 ea0 Hsrc0 Hadd0 Hperm0
        |p0 g0 b0 e0 a0 ea0 loadv0 loadv0' Hsrc0 Hadd0 Hshadow0 _ _ _
        |p0 g0 b0 e0 a0 ea0 heap_a0 revoked0 _ _ _ _ _ Hinc0
        |p0 g0 b0 e0 a0 ea0 Hsrc0 Hadd0 Hrev0 _ _
        |p0 g0 b0 e0 a0 ea0 Hsrc0 Hadd0 Htdev0 _ _
        |p0 g0 b0 e0 a0 π0 Hsrc0 Hπ0].
      all: try (rewrite Hsrc in Hsrc0; simplify_eq).
      all: try (rewrite finz_add_0 in Hadd0; simplify_eq).
      + rewrite Hsrc0 /= in Hsrc. simplify_eq. by rewrite Hsrc in Hcap0.
      + by destruct Hperm0; congruence.
      + congruence.
      + congruence.
      + apply is_revoker_address_spec in Hrev0. subst.
        by rewrite revoker_not_shadow_address in Hshadow.
      + by rewrite (time_device_not_shadow_address _ Htdev0) in Hshadow.
      + by apply Hπ0, (Hnoid _ Hsrc0).
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
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %]".
    rewrite memMap_resource_1_dq.
    iAssert ([∗ map] a0↦bit ∈ {[heap_a:=revoked]}, a0 ↦ₛ{sdq} bit)%I
      with "[Ha]" as "Hshadow"; first by rewrite big_sepM_singleton.
    iApply (wp_load_success_shadow E pc_p pc_g pc_b pc_e pc_a pc_π r1 r2 w _ _ dq _ sdq p g b e a heap_a revoked
      with "[$HPC $Hi $Hmap $Hshadow]"); eauto; simplify_map_eq; eauto.
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    { unfold reg_allows_load. split; first by simplify_map_eq. auto. }
    all: try (by rewrite /incrementPC /incrementPC_gen Hpca').
    iNext. iIntros "(HPC & Hi & Ha & Hmap)".
    rewrite -memMap_resource_1_dq big_sepM_singleton.
    iRegsMap "Hmap"; eauto.
    iApply "Hφ". iFrame.
  Qed.

  (** A shadow store of the status [revoked] to [heap_a]: either it stores the
      current bit, or [heap_a] is in the permission set [sperm]. *)
  Lemma wp_store_success_shadow_fetch E pc_p pc_g pc_b pc_e pc_a pc_π
    dst src w regs lpc' mem shadow (sperm : gset Addr) p g b e a heap_a revoked πs dq :
    decodeInstrW w.(lw) = Store dst src 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Store dst src 0) ⊆ dom regs →
    reg_allows_store regs dst p g b e a →
    (∀ v : LWord, regs !!ₗ dst = Some v → v.(lprov) = None) →
    lword_of_argument regs src = Some (MkLWord (WInt (encodeAllocStatus revoked)) πs) →
    is_shadow_address a = true →
    shadow_to_heap a = Some heap_a →
    is_Some (shadow !! heap_a) →
    shadow_store_allowed sperm shadow heap_a revoked →
    incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
        (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ revoked) ∗
        ([∗ set] a ∈ sperm, shadow_store_perm a) ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        ([∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
        ([∗ map] a↦revoked ∈ <[heap_a:=revoked]> shadow, a ↦ₛ revoked) ∗
        ([∗ set] a ∈ sperm, shadow_store_perm a) ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hallow Hnoid Harg Hshadow Htranslate Hlookup Hok Hinc φ)
      "(>HPC & >Hfetch & >Hmem & >Hshadow & Hperms & >Hmap) Hφ".
    iApply (wp_store_fetch with "[$HPC $Hfetch $Hmem $Hshadow $Hperms $Hmap]"); eauto.
    { intros p0 g0 b0 e0 a0 v0 (Hdst0 & _) Harg0.
      destruct Hallow as (Hdst & _). rewrite Hdst in Hdst0. simplify_eq.
      rewrite Hshadow. exists heap_a. split_and!; [done|done|].
      by rewrite decode_encode_alloc_status_inv. }
    iNext. iIntros (lpc0 mem0 shadow0 retv) "(%Hspec & HPC & Hfetch & Hmem & Hshadow & Hperms & Hmap)".
    destruct Hallow as (Hdst & Hwa & Hwb).
    destruct Hspec as
      [p0 g0 b0 e0 a0 ea0 v0 oldv0 Harg0 (Hdst0 & Hadd0 & _) Hshadow0 Hlookup0 -> -> Hinc0
      |p0 g0 b0 e0 a0 ea0 heap_a0 v0 old_status0 Harg0 (Hdst0 & Hadd0 & _) Hshadow0 Htranslate0 Hlookup0 -> -> Hinc0
      |p0 g0 b0 e0 a0 ea0 v0 Harg0 (Hdst0 & Hadd0 & _) Htdev0 _ _ _ _ _
      |Hmem_eq Hshadow_eq Hfail].
    - rewrite Hdst in Hdst0. simplify_eq.
      rewrite finz_add_0 in Hadd0. simplify_eq. congruence.
    - rewrite Hdst in Hdst0. simplify_eq.
      rewrite finz_add_0 in Hadd0. simplify_eq.
      try (rewrite Harg in Harg0; simplify_eq). try (rewrite Hinc in Hinc0; simplify_eq).
      iApply "Hφ". rewrite decode_encode_alloc_status_inv. iFrame.
    - exfalso. rewrite Hdst in Hdst0. simplify_eq.
      rewrite finz_add_0 in Hadd0. simplify_eq.
      by rewrite (time_device_not_shadow_address _ Htdev0) in Hshadow.
    - exfalso. destruct Hfail as
        [w0 Hreg0 Hcap0|p0 g0 b0 e0 a0 Hreg0|p0 g0 b0 e0 a0 Hreg0 Hadd0|
         p0 g0 b0 e0 a0 ea0 Hreg0 Hadd0 Hbounds0|Hpc0|
         p0 g0 b0 e0 a0 π0 Hreg0 Hπ0|
         p0 g0 b0 e0 a0 ea0 Hreg0 Hadd0 _ _ Hshadow0 _ _ _|
         p0 g0 b0 e0 a0 ea0 storev0 Hreg0 Hadd0 Htdev0 _ _ _].
      + rewrite Hreg0 in Hdst. by destruct w0; simplify_eq/=.
      + rewrite Hreg0 in Hdst. simplify_eq.
      + rewrite finz_add_0 in Hadd0. discriminate.
      + rewrite finz_add_0 in Hadd0. simplify_eq.
        destruct Hbounds0; congruence.
      + congruence.
      + by apply Hπ0, (Hnoid _ Hreg0).
      + rewrite Hreg0 in Hdst. simplify_eq.
        rewrite finz_add_0 in Hadd0. simplify_eq. congruence.
      + rewrite Hreg0 in Hdst. simplify_eq.
        rewrite finz_add_0 in Hadd0. simplify_eq.
        by rewrite (time_device_not_shadow_address _ Htdev0) in Hshadow.
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
    iIntros (-> Hshadow Htranslate Hinstr Hvpc Hpca' Hwa Hwb ? φ)
      "(>HPC & >Hi & >Hdst & >Ha) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iAssert ([∗ map] a↦w ∈ (∅ : LMem), a ↦ₐ w)%I as "-#Hmem"; first by rewrite big_sepM_empty.
    iAssert ([∗ map] a0↦rev ∈ {[heap_a:=revoked]}, a0 ↦ₛ rev)%I
      with "[Ha]" as "Hshadow".
    { by rewrite big_sepM_singleton. }
    iAssert ([∗ set] a0 ∈ (∅ : gset Addr), shadow_store_perm a0)%I as "Hperms".
    { by rewrite big_sepS_empty. }
    iApply (wp_store_success_shadow_fetch _ pc_p pc_g pc_b pc_e pc_a pc_π _ _ w _
              (Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π)
            with "[$HPC $Hi $Hmem $Hshadow $Hperms $Hmap]");
      [..|iNext; iIntros "(HPC & Hi & Hmem & Hshadow & _ & Hmap)"].
    all: try (by eauto; simplify_map_eq).
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    all: try (by unfold reg_allows_store; split; [simplify_map_eq | split_and!; auto]).
    all: try (by rewrite /shadow_store_allowed; left; by simplify_map_eq).
    all: try (by rewrite /incrementPC /incrementPC_gen; simplify_map_eq).
    all: try (by intros ? ?; simplify_map_eq).
    iApply "Hφ".
    iEval (rewrite insert_insert_eq big_sepM_singleton) in "Hshadow".
    iRegsMap "Hmap"; eauto. iFrame.
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
    iAssert ([∗ map] a↦w ∈ (∅ : LMem), a ↦ₐ w)%I as "-#Hmem"; first by rewrite big_sepM_empty.
    iAssert ([∗ map] a0↦rev ∈ {[heap_a:=old_revoked]}, a0 ↦ₛ rev)%I
      with "[Ha]" as "Hshadow".
    { by rewrite big_sepM_singleton. }
    iAssert ([∗ set] a0 ∈ ({[heap_a]} : gset Addr), (λ _, P) a0)%I
      with "[HPr]" as "Hperms".
    { by rewrite big_sepS_singleton. }
    iApply (wp_store_shadow_imm_res_fetch _ _ _ _ _ _ _ dst (inl (encodeAllocStatus revoked)) 0
      _ _ _ _ _ _ _ DerefNoId
      with "[$HPC $Hi $Hmem $Hshadow $Hperms $Hmap]"); eauto; simplify_map_eq; eauto.
    { intros R C a0 Ha0. iIntros "HR HC Hperms".
      rewrite big_sepS_singleton. apply elem_of_singleton in Ha0 as ->.
      iApply (HP with "HR HC Hperms"). }
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    { intros p0 g0 b0 e0 a0 ea0 v0 (Hdst0 & Hadd0 & _) Harg0.
      simplify_map_eq. rewrite finz_add_0 in Hadd0. simplify_eq.
      rewrite Hshadow. exists heap_a. split_and!; [done|by simplify_map_eq|].
      right. set_solver. }
    iNext. iIntros (lpc' mem' shadow' retv) "(%Hspec & HPC & Hi & Hmem & Hshadow & Hperms & _ & Hmap)".
    destruct Hspec as
      [p0 g0 b0 e0 a0 ea0 v0 oldv0 Harg0 (Hdst0 & Hadd0 & _) Hshadow0 Hlookup0 -> -> Hinc0
      |p0 g0 b0 e0 a0 ea0 heap_a0 v0 old_status0 Harg0 (Hdst0 & Hadd0 & _) Hshadow0 Htranslate0 Hlookup0 -> -> Hinc0
      |p0 g0 b0 e0 a0 ea0 v0 Harg0 (Hdst0 & Hadd0 & _) Htdev0 _ _ _ _ _
      |Hmem_eq Hshadow_eq Hfail].
    - simplify_map_eq.
    - simplify_map_eq. rewrite finz_add_0 in Hadd0. simplify_eq.
      rewrite decode_encode_alloc_status_inv.
      iRegsMap "Hshadow". iRegsMap "Hmap".
      iEval (rewrite big_sepS_singleton) in "Hperms".
      try (rewrite /incrementPC /incrementPC_gen in Hinc0; simplify_map_eq).
      iApply "Hφ". iFrame.
    - exfalso. simplify_map_eq. rewrite finz_add_0 in Hadd0. simplify_eq.
      by rewrite (time_device_not_shadow_address _ Htdev0) in Hshadow.
    - exfalso. destruct Hfail as
        [w0 Hreg0 Hcap0|p0 g0 b0 e0 a0 Hreg0|p0 g0 b0 e0 a0 Hreg0 Hadd0|
         p0 g0 b0 e0 a0 ea0 Hreg0 Hadd0 Hbounds0|Hpc0|
         p0 g0 b0 e0 a0 π0 Hreg0 Hπ0|
         p0 g0 b0 e0 a0 ea0 Hreg0 Hadd0 _ _ Hshadow0 _ _ _|
         p0 g0 b0 e0 a0 ea0 storev0 Hreg0 Hadd0 Htdev0 _ _ _];
        simplify_map_eq; try (rewrite finz_add_0 in Hadd0; simplify_eq); try congruence.
      all: try (by rewrite (time_device_not_shadow_address _ Htdev0) in Hshadow).
      all: try (destruct Hbounds0; congruence).
      all: try (rewrite /incrementPC /incrementPC_gen in Hpc0; simplify_map_eq).
  Qed.
End mmio_shadow_store_res.
