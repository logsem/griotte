From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.
From griotte Require Import rules_mem_access.

(** ** Faults of [Store], on every copy of the owned registers *)

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

  (** A shadow store keeps erasure if it stores the cell's current bit, or if
      the caller holds the cell's permission: the cell is unclaimed, or
      claimed by a painting allocation. Heap roots are never painted. *)
  Definition shadow_store_perm (a : Addr) : iProp Σ :=
    addr_alloc a Unclaimed ∨ ∃ ι q, addr_alloc a (Claimed ι) ∗ ι ↦st{q} APainting.

  Definition shadow_store_allowed (sperm : gset Addr) (shadow : ShadowTbl)
      (a : Addr) (s : AllocStatus) : Prop :=
    shadow !! a = Some s ∨ a ∈ sperm.

  Lemma shadow_store_perms_ok (sperm : gset Addr) R C st a s :
    a ∈ sperm →
    reg_auth R -∗ addr_alloc_auth C -∗ ([∗ set] a ∈ sperm, shadow_store_perm a) -∗
    ⌜shadow_store_ok R C st a s⌝.
  Proof.
    iIntros (Ha) "HR HC Hperms".
    iDestruct (big_sepS_elem_of with "Hperms") as "[Hu | (%ι & %q & Hc & Htok)]"; first exact Ha.
    - iDestruct (addr_alloc_lookup with "HC Hu") as %Hc. iPureIntro. right. by left.
    - iDestruct (addr_alloc_lookup with "HC Hc") as %Hc.
      iDestruct (reg_lookup_own with "HR Htok") as %(b & e & γ & HRι).
      iPureIntro. right. right. exists ι, (b, e, γ, APainting). done.
  Qed.

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
      [exact Hdecode | solve_mem_instr_ok | apply Store_member_argument | apply Store_agree
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

   Lemma wp_store_fail_reg_not_cap_lword E pc_p pc_g pc_b pc_e pc_a pc_π w
     dst src (wdst : LWord) wstore dq :
      decodeInstrW w.(lw) = Store dst (inr src) 0 →
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
    intros. eapply wp_store_fail_reg_not_cap_lword_imm with (imm := 0); eauto; try by rewrite finz_add_0.
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

   Lemma wp_store_fail_reg E pc_p pc_g pc_b pc_e pc_a pc_π π w dst src
         p g b e a w'' dq :
      decodeInstrW w.(lw) = Store dst (inr src) 0 →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     withinBounds b e a = false →
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
    intros. eapply wp_store_fail_reg_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

    Lemma wp_store_fail_z E pc_p pc_g pc_b pc_e pc_a pc_π π w dst
         p g b e a z dq :
      decodeInstrW w.(lw) = Store dst (inl z) 0 →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     withinBounds b e a = false →
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
    intros. eapply wp_store_fail_z_imm with (imm := 0); eauto; try by rewrite finz_add_0.
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
