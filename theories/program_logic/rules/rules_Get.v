From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.
From griotte Require Import rules_regs.

Section griotte_lang_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types a b : Addr.
  Implicit Types o : OType.
  Implicit Types r : RegName.
  Implicit Types w : LWord.
  Implicit Types reg : gmap RegName LWord.
  Implicit Types ms : gmap Addr LWord.

  (* Generalized denote function, since multiple cases result in similar success *)
  Definition denote (i: instr) (w : Word): option Z :=
    match i with
    | GetP _ _ => Some (encodePermSum (get_p w))
    | GetL _ _ => Some (encodeLoc (get_l w))
    | GetB _ _ => Some (get_b w)
    | GetE _ _ => Some (get_e w)
    | GetLen _ _ => Some (get_e w - get_b w)%Z
    | GetA _ _ => Some (get_a w)
    | GetOType _ _ =>
        match w with
        | WSealed o _ => Some (o:Z)
        | _ => Some (-1)%Z
        end
    | GetTag _ _ => Some (Z.b2z (get_tag w))
    | GetWType _ _ => Some (encodeWordType w)
    | _ => None
    end.

  #[global] Arguments denote : simpl nomatch.

  Definition is_Get (i: instr) (dst src: RegName) :=
    i = GetP dst src ∨
    i = GetL dst src ∨
    i = GetB dst src ∨
    i = GetE dst src ∨
    i = GetLen dst src ∨
    i = GetA dst src \/
    i = GetOType dst src \/
    i = GetWType dst src \/
    i = GetTag dst src
  .

  Lemma operands_of_is_Get i dst src :
    is_Get i dst src →
    operands_of i = {[ dst; src ]}.
  Proof.
    intros HH. destruct_or! HH; subst i; reflexivity.
  Qed.

  (** Every Get reads a result from any word. *)
  Lemma denote_is_Get i dst src (w : Word) :
    is_Get i dst src → is_Some (denote i w).
  Proof. intros HH. destruct_or! HH; subst i; cbn; destruct w; by eexists. Qed.

  Inductive Get_failure (i: instr) (lpc : LWord) (regs : LReg) (dst src: RegName) :=
    | Get_fail_overflow_PC w z:
        regs !!ₗ src = Some w →
        denote i w.(lw) = Some z →
        incrementPC lpc = None →
        Get_failure i lpc regs dst src.

  (** The words whose physical tag may be cleared while the logical one is
      set: words with an identifier, and heap-based words without
      authority. *)
  Definition tag_strippable (w : LWord) : Prop :=
    get_tag w.(lw) = true ∧
    (is_Some w.(lprov) ∨ (¬ has_authority w.(lw) ∧ is_Some (heap_cap_base w.(lw)))).

  Lemma reg_phys_tag_strippable R (v : LWord) :
    reg_phys R v (clear_tag v.(lw)) → get_tag v.(lw) = true → tag_strippable v.
  Proof.
    intros [ [Heq | [_ [ [(ι & _ & Hι & _) _] | Hh] ] ] _] Ht; split; try done.
    - by rewrite -Heq get_tag_clear_tag in Ht.
    - left. by rewrite Hι.
    - by right.
  Qed.

  Inductive Get_spec {k : kind} (i: instr) (lpc : LWord) (regs : LReg) (dst src: RegName)
    (lpc' : LWord) (regs' : LReg): tval k -> Prop :=
    | Get_spec_success w z:
        regs !!ₗ src = Some w →
        denote i w.(lw) = Some z →
        incrementPC lpc = Some lpc' →
        regs' = <[ dst := WInt z ]ₗ> regs →
        Get_spec i lpc regs dst src lpc' regs' NextIV
    (* GetTag returns 0 on a word whose tag may have been cleared. *)
    | Get_spec_success_cleared w:
        i = GetTag dst src →
        regs !!ₗ src = Some w →
        tag_strippable w →
        incrementPC lpc = Some lpc' →
        regs' = <[ dst := WInt 0 ]ₗ> regs →
        Get_spec i lpc regs dst src lpc' regs' NextIV
    | Get_spec_failure:
        Get_failure i lpc regs dst src →
        lpc' = lpc →
        regs' = regs →
        Get_spec i lpc regs dst src lpc' regs' FaultedV.

  Lemma exec_opt_Get i dst src p (pc : Word) (r : Reg) sr m st td (wsrc : Word) :
    is_Get i dst src →
    lookup_reg src r = Some wsrc →
    exec_opt i p (MkExecConf pc r sr m st td) =
      match denote i wsrc with
      | Some z => nextPC (update_reg (MkExecConf pc r sr m st td) dst (WInt z))
      | None => None
      end.
  Proof.
    intros Hi Hs. destruct_or! Hi; subst i; cbn; rewrite Hs /=.
    all: destruct wsrc as [| [] | | ? [] ]; cbn; done.
  Qed.

  Lemma denote_and_tag i s (w : Word) :
    denote i (and_tag s w) =
      match i with
      | GetTag _ _ => Some (Z.b2z (s && get_tag w))
      | _ => denote i w
      end.
  Proof.
    destruct i; cbn; try done.
    all: try (by destruct s, w as [| [] | | ? [] ]).
    f_equal. pose proof (encodeWordType_correct (and_tag s w) w) as Heq.
    by destruct w as [| [] | | ? [] ].
  Qed.

  Lemma wp_Get Ep pc_p pc_g pc_b pc_e pc_a pc_π w get_i dst src regs dq :
    decodeInstrW w.(lw) = get_i →
    is_Get get_i dst src →

    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_of get_i ⊆ dom regs →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lpc' regs' retv, RET retv;
        ⌜ Get_spec (decodeInstrW w.(lw)) (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst src lpc' regs' retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc Dregs φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step_nosw with "HPC Hpc_a Hmap"); [rewrite Hdecode; apply sw_of_none; intros ->; destruct_or! Hinstr; discriminate|..]; eauto.
    iNext; iIntros (r sr m st td lreg lsreg lmem R C c σ') "@".
    rewrite Hdecode /exec in Hstep. rewrite Hdecode.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri.
    erewrite operands_of_is_Get in Hri; eauto.
    destruct (Hri src) as [wsrc [H'src _] ]; first by set_solver+.
    destruct (llookup_reg_phys _ _ _ _ _ Hregs H'src) as (s & Hsrc & Hrel).
    rewrite (exec_opt_Get _ _ _ _ _ _ _ _ _ _ _ Hinstr Hsrc) denote_and_tag in Hstep.
    destruct (decide (get_i = GetTag dst src ∧ s = false ∧ get_tag wsrc.(lw) = true))
      as [(-> & -> & Ht) | Hexact].
    { (* The physical tag is cleared. *)
      rewrite Ht /= in Hstep.
      iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ _ dst (lword_of_word (WInt 0)) _ _ _ _
        (λ lpc' regs' retv, Get_spec (GetTag dst src) _ regs dst src lpc' regs' retv)
        with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
      { exact Her. } { exact Hlregs. }
      { eapply elem_of_lregs_dom; [exact Dregs | erewrite operands_of_is_Get; eauto; set_solver+]. }
      { apply reg_word_ok_int. } { exact Hstep. } { apply reg_phys_lword_of_word. }
      { intros. eapply Get_spec_success_cleared; eauto.
        apply (reg_phys_tag_strippable R); last done. by rewrite and_tag_false in Hrel. }
      { intros. apply Get_spec_failure; [|done..]. by eapply (Get_fail_overflow_PC _ _ _ _ _ wsrc (Z.b2z (get_tag wsrc.(lw)))). }
      iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame. }
    assert ((match get_i with
             | GetTag _ _ => Some (Z.b2z (s && get_tag wsrc.(lw)))
             | _ => denote get_i wsrc.(lw)
             end) = denote get_i wsrc.(lw)) as Hden.
    { destruct_or! Hinstr; rewrite Hinstr; cbn; try done. f_equal.
      destruct s, (get_tag wsrc.(lw)); naive_solver. }
    rewrite Hden in Hstep.
    destruct (denote_is_Get _ _ _ wsrc.(lw) Hinstr) as [z Hwsrc].
    rewrite Hwsrc in Hstep.
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ _ dst (lword_of_word (WInt z)) _ _ _ _
      (λ lpc' regs' retv, Get_spec get_i _ regs dst src lpc' regs' retv)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
    { exact Her. } { exact Hlregs. }
    { eapply elem_of_lregs_dom; [exact Dregs | erewrite operands_of_is_Get; eauto; set_solver+]. }
    { apply reg_word_ok_int. } { exact Hstep. } { apply reg_phys_lword_of_word. }
    { intros. by econstructor. }
    { intros. apply Get_spec_failure; [|done..]. by eapply Get_fail_overflow_PC. }
    iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
  Qed.

  (* Note that other cases than WCap in the PC are irrelevant, as that will result in having an incorrect PC *)

  (** The results a Get may write: the denotation of its source, or 0 for a
      GetTag of a word whose tag may have been cleared. *)
  Definition get_result (i : instr) (w : LWord) (z : Z) : Prop :=
    denote i w.(lw) = Some z ∨
    ((∃ d s, i = GetTag d s) ∧ z = 0%Z ∧ tag_strippable w).

  (** The result of a Get other than GetTag is its denotation. *)
  Lemma get_result_exact i w z z' :
    get_result i w z → denote i w.(lw) = Some z' →
    (∀ dst' src', i ≠ GetTag dst' src') → z = z'.
  Proof.
    intros [Hz | ((d & s & ->) & -> & Hs)] Hz' Hnot; first congruence.
    by exfalso; apply (Hnot d s).
  Qed.

  (** A successful Get writes a [get_result]. *)
  Lemma Get_spec_next {k : kind} i lpc regs dst src lpc' regs' wsrc :
    regs !!ₗ src = Some wsrc →
    Get_spec i lpc regs dst src lpc' regs' (@NextIV k) →
    incrementPC lpc = Some lpc' ∧
    ∃ z, get_result i wsrc z ∧ regs' = <[dst := WInt z]ₗ> regs.
  Proof.
    intros Hsrc Hspec. inversion Hspec as [w z Hw Hz Hinc | w Hi Hw Hs Hinc | ]; subst;
      rewrite Hsrc in Hw; simplify_eq; split; try done.
    - exists z. split; [by left | done].
    - exists 0%Z. split; [right; eauto | done].
  Qed.

  (** A Get whose source denotes and whose PC increments does not fail. *)
  Lemma Get_spec_not_faulted {k : kind} i lpc regs dst src lpc' regs' wsrc lpc0 :
    regs !!ₗ src = Some wsrc →
    is_Some (denote i wsrc.(lw)) →
    incrementPC lpc = Some lpc0 →
    ¬ Get_spec i lpc regs dst src lpc' regs' (@FaultedV k).
  Proof.
    intros Hsrc [z Hz] Hinc Hspec. inversion Hspec as [| | Hfail]; subst.
    destruct Hfail as [w z' Hw Hd Hi]; rewrite Hsrc in Hw; simplify_eq; congruence.
  Qed.

  (** The map-form success rule, from which the register-shaped ones
      follow. *)
  Lemma wp_Get_next E get_i dst src pc_p pc_g pc_b pc_e pc_a pc_π w regs wsrc lpc' dq :
    decodeInstrW w.(lw) = get_i →
    is_Get get_i dst src →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    {[dst; src]} ∖ {[ cnull ]} ⊆ dom regs →
    regs !!ₗ src = Some wsrc →
    is_Some (denote get_i wsrc.(lw)) →
    incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ z, RET NextIV;
        ⌜get_result get_i wsrc z⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ <[dst := WInt z]ₗ> regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hdecode Hi Hvpc Hdom Hsrc Hden Hinc φ) "(HPC & Hpc_a & Hmap) Hφ".
    iApply (wp_Get with "[$HPC $Hpc_a $Hmap]"); eauto.
    { rewrite /regs_of. by erewrite operands_of_is_Get. }
    iIntros "!>" (lpc0 regs' retv) "(%Hspec & HPC & Hpc_a & Hmap)".
    rewrite Hdecode in Hspec.
    assert (retv = NextIV) as ->.
    { inversion Hspec; subst; [done | done |]. exfalso. by eapply Get_spec_not_faulted. }
    destruct (Get_spec_next _ _ _ _ _ _ _ _ Hsrc Hspec) as (Hinc' & z & Hz & ->).
    rewrite Hinc in Hinc'. simplify_eq. iApply "Hφ". by iFrame.
  Qed.

  Lemma wp_Get_same_success E get_i r pc_p pc_g pc_b pc_e pc_a pc_π w wr pc_a' z dq:
    decodeInstrW w.(lw) = get_i →
    is_Get get_i r r →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' ->
    (∀ dst' src', get_i ≠ GetTag dst' src') →
    denote get_i wr.(lw) = Some z →
    r ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r ↦ᵣ wr }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r ↦ᵣ WInt z }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc Hpca' Hnot_tag Hdenote Hcnull φ) "(HPC & Hpc_a & >Hr) Hφ".
    iDestruct (map_of_regs_1 with "Hr") as "Hmap".
    iApply (wp_Get_next _ get_i r r _ _ _ _ _ _ _ _ wr with "[$HPC $Hpc_a $Hmap]");
      try solve_next_side; try by eexists.
    iIntros "!>" (z') "(%Hz & HPC & Hpc_a & Hmap)".
    rewrite (get_result_exact _ _ _ z Hz Hdenote Hnot_tag).
    iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_Get_success E get_i dst src pc_p pc_g pc_b pc_e pc_a pc_π w wsrc wdst pc_a' z dq :
    decodeInstrW w.(lw) = get_i →
    is_Get get_i dst src →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' ->
    (∀ dst' src', get_i ≠ GetTag dst' src') →
    denote get_i wsrc.(lw) = Some z →
    src ≠ cnull ->
    dst ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ src ↦ᵣ wsrc
        ∗ ▷ dst ↦ᵣ wdst }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ src ↦ᵣ wsrc
          ∗ dst ↦ᵣ WInt z }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc Hpca' Hnot_tag Hdenote Hcnull Hcnull' φ)
      "(HPC & Hpc_a & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "Hdst Hsrc") as "[Hmap %]".
    iApply (wp_Get_next _ get_i dst src _ _ _ _ _ _ _ _ wsrc with "[$HPC $Hpc_a $Hmap]");
      try solve_next_side; try by eexists.
    iIntros "!>" (z') "(%Hz & HPC & Hpc_a & Hmap)".
    rewrite (get_result_exact _ _ _ z Hz Hdenote Hnot_tag).
    iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_GetTag_cnull E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dq :
    decodeInstrW w.(lw) = GetTag cnull cnull →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ{dq} w }}}
      Instr Executable @ E
    {{{ RET NextIV; PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗ pc_a ↦ₐ{dq} w }}}.
  Proof.
    iIntros (Hdecode Hvpc Hpca' φ) "(HPC & Hpc_a) Hφ".
    iApply (wp_Get_next _ (GetTag cnull cnull) cnull cnull _ _ _ _ _ _ _ ∅ lnull
      with "[$HPC $Hpc_a]"); try solve_next_side; try (by unfold is_Get; tauto); try by eexists.
    iIntros "!>" (z') "(_ & HPC & Hpc_a & _)". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_GetTag_from_cnull E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst wd dq :
    decodeInstrW w.(lw) = GetTag dst cnull →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' → dst ≠ cnull →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ{dq} w ∗ ▷ dst ↦ᵣ wd }}}
      Instr Executable @ E
    {{{ RET NextIV; PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗ pc_a ↦ₐ{dq} w ∗ dst ↦ᵣ WInt 0%Z }}}.
  Proof.
    iIntros (Hdecode Hvpc Hpca' Hne φ) "(HPC & Hpc_a & >Hd) Hφ".
    iDestruct (map_of_regs_1 with "Hd") as "Hmap".
    iApply (wp_Get_next _ (GetTag dst cnull) dst cnull _ _ _ _ _ _ _ _ lnull
      with "[$HPC $Hpc_a $Hmap]"); try solve_next_side; try (by unfold is_Get; tauto); try by eexists.
    iIntros "!>" (z') "(%Hz & HPC & Hpc_a & Hmap)".
    assert (z' = 0%Z) as -> by (destruct Hz as [Hz | (_ & -> & [Ht _])]; by simplify_eq/=).
    iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_GetTag_to_cnull E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src ws dq :
    decodeInstrW w.(lw) = GetTag cnull src →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' → src ≠ cnull →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ{dq} w ∗ ▷ src ↦ᵣ ws }}}
      Instr Executable @ E
    {{{ RET NextIV; PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗ pc_a ↦ₐ{dq} w ∗ src ↦ᵣ ws }}}.
  Proof.
    iIntros (Hdecode Hvpc Hpca' Hne φ) "(HPC & Hpc_a & >Hs) Hφ".
    iDestruct (map_of_regs_1 with "Hs") as "Hmap".
    iApply (wp_Get_next _ (GetTag cnull src) cnull src _ _ _ _ _ _ _ _ ws
      with "[$HPC $Hpc_a $Hmap]"); try solve_next_side;
      try (by unfold is_Get; tauto); try (destruct_word (lw ws); by eexists).
    iIntros "!>" (z') "(_ & HPC & Hpc_a & Hmap)".
    rewrite linsert_reg_cnull. iRegsMap "Hmap". iApply "Hφ". iFrame.
  Qed.

  (** ** GetTag with a witness and an observation

      The result is the logical tag, or 0 on a word whose tag may be
      cleared. It is exact under a dereference witness for a word with
      authority or without a heap base. A result of 1 on a word with
      authority observes the claim of its base: by its identifier, or as a
      heap root. The claims are read from any resource [P] that bounds the
      claim map, by [Φc]. *)
  Definition gettag_result (dw : deref_witness) (Φc : gmap Addr AddrClaim → Prop)
      (v : LWord) (z : Z) : Prop :=
    (z = Z.b2z (get_tag v.(lw)) ∨ (z = 0%Z ∧ tag_strippable v)) ∧
    (v.(lprov) = deref_id dw → load_exact_cond v → z = Z.b2z (get_tag v.(lw))) ∧
    (z = 1%Z → ∃ C, Φc C ∧
       ∀ b, heap_authority_base v.(lw) = Some b →
         match v.(lprov) with
         | Some ι => C !! b = Some (Claimed ι)
         | None => C !! b = Some HeapRoot
         end).

  (** The source of GetTag: the written integer is a copy of the logical
      tag, with [gettag_result] under the witness facts. *)
  Lemma gettag_source dw Φc regs lpc src wsrc :
    regs !!ₗ src = Some wsrc →
    lsource_witness_ok (λ R C, deref_witness_ok R dw ∧ Φc C) regs lpc
      (λ S, WInt (Z.b2z (S src && get_tag wsrc.(lw)))) (λ _, true)
      (λ v, ∃ z, v = WInt z ∧ gettag_result dw Φc wsrc z).
  Proof.
    intros Hsrc R C st S Hreg [Hdw HΦc] Hregs _ _.
    split_and!; [apply reg_word_ok_int | rewrite and_tag_true; apply reg_phys_lword_of_word |].
    eexists; split; first done.
    destruct (get_tag wsrc.(lw)) eqn:Ht; last first.
    { rewrite andb_false_r /gettag_result Ht. split_and!; [by left | done | done]. }
    assert (src ≠ cnull) as Hne.
    { intros ->. rewrite llookup_reg_cnull in Hsrc. by simplify_eq. }
    rewrite llookup_reg_not_cnull // in Hsrc.
    destruct (Hregs src wsrc Hsrc) as [Hok Hrel].
    rewrite /gettag_result. split_and!.
    - destruct (S src); first by left; rewrite Ht.
      right. split; first done. apply (reg_phys_tag_strippable R); last done.
      by rewrite and_tag_false in Hrel.
    - intros Hπ Hcond. rewrite -Ht -get_tag_and_tag.
      by rewrite (deref_exact _ _ _ _ Hdw Hπ Hcond Hrel).
    - intros Hz. exists C. split; first done. intros b Hab.
      assert (get_tag (and_tag (S src) wsrc.(lw)) = true) as Htw.
      { rewrite get_tag_and_tag Ht. by destruct (S src). }
      pose proof (reg_phys_observe _ _ _ _ _ _ Hreg Hok Hrel Htw Hab) as Hobs.
      destruct (lprov wsrc); [by destruct Hobs as (? & ? & ? & ?) | done].
  Qed.

  (** The agreement of GetTag: it writes the tag of the copy. *)
  Lemma gettag_agree p lpc regs dst src wsrc :
    regs !!ₗ src = Some wsrc →
    regs_next_agree_strip exec_opt (GetTag dst src) p lpc regs dst
      (λ S, WInt (Z.b2z (S src && get_tag wsrc.(lw)))) 1 (λ _, true).
  Proof.
    intros Hsrc [pc r sr m st td] S _ Hcopy.
    rewrite /regs_effect (exec_opt_Get (GetTag dst src) dst src _ _ _ _ _ _ _ _
                            ltac:(unfold is_Get; tauto) (regs_copy_llookup _ _ _ _ _ Hcopy Hsrc)).
    by rewrite and_tag_true /= get_tag_and_tag.
  Qed.

  Lemma wp_GetTag_obs Ep pc_p pc_g pc_b pc_e pc_a pc_π w dst src regs dq dw
      (P : iProp Σ) (Φc : gmap Addr AddrClaim → Prop) :
    decodeInstrW w.(lw) = GetTag dst src →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (GetTag dst src) ⊆ dom regs →
    (∀ C, addr_alloc_auth C -∗ P -∗ ⌜Φc C⌝) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        deref_witness_res dw ∗
        P ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lpc' regs' retv, RET retv;
        ⌜ (∃ (v : LWord) z, retv = NextIV ∧ regs !!ₗ src = Some v ∧ gettag_result dw Φc v z ∧
             incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' ∧
             regs' = <[dst := WInt z]ₗ> regs) ∨
          (retv = FaultedV ∧ incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) = None ∧
             regs' = regs ∧ lpc' = Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        deref_witness_res dw ∗
        P ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hdecode Hvpc Dregs HP φ) "(HPC & Hpc_a & Hdw & HPr & Hmap) Hφ".
    assert (is_Some (regs !!ₗ src)) as [wsrc Hsrc].
    { apply (llookup_reg_of_dom {[dst; src]}); last set_solver+.
      by rewrite /regs_of /operands_of in Dregs. }
    iApply (wp_regs_step _ _ _ _ _ _ _ _ _ _ _ dst _ 1 _ _ (deref_witness_res dw ∗ P)
              (λ R C, deref_witness_ok R dw ∧ Φc C) with "[$HPC $Hpc_a $Hdw $HPr $Hmap]");
      [done | rewrite /regs_instr_ok; by apply sw_of_none | done
      | by apply gettag_source | by apply gettag_agree | | |].
    { destruct (decide (dst = cnull)) as [Hdst | Hdst]; [by left | right].
      rewrite /regs_of /operands_of in Dregs. set_solver. }
    { iIntros (R C) "HR HC [Hdw HPr]".
      iDestruct (deref_witness_lookup with "HR Hdw") as %Hdw.
      by iDestruct (HP with "HC HPr") as %HΦc. }
    iIntros "!>" (lpc' regs' retv) "(%Hout & HPC & Hpc_a & [Hdw HPr] & Hmap)".
    iApply "Hφ". iFrame. iPureIntro.
    rewrite /regs_outcome in Hout.
    destruct (incrementPC_gen _ 1) as [lpc_next |] eqn:Hinc.
    - destruct Hout as (-> & -> & v & (z & -> & Hres) & ->). left. by exists wsrc, z.
    - destruct Hout as (-> & -> & ->). right. by split_and!.
  Qed.

  (** [wp_GetTag_obs] on two distinct registers. *)
  Lemma wp_gettag_obs E dst src pc_p pc_g pc_b pc_e pc_a pc_π w wsrc wdst pc_a' dq dw
      (P : iProp Σ) (Φc : gmap Addr AddrClaim → Prop) :
    decodeInstrW w.(lw) = GetTag dst src →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ dst →
    src ≠ cnull →
    dst ≠ cnull →
    (∀ C, addr_alloc_auth C -∗ P -∗ ⌜Φc C⌝) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ src ↦ᵣ wsrc
        ∗ ▷ dst ↦ᵣ wdst
        ∗ deref_witness_res dw
        ∗ P }}}
      Instr Executable @ E
      {{{ z, RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ src ↦ᵣ wsrc
          ∗ dst ↦ᵣ WInt z
          ∗ deref_witness_res dw
          ∗ P
          ∗ ⌜gettag_result dw Φc wsrc z⌝ }}}.
  Proof.
    iIntros (Hdecode Hvpc Hpca' Hne Hsrc_null Hcnull HP φ) "(>HPC & >Hpc_a & >Hsrc & >Hdst & Hdw & HPr) Hφ".
    iDestruct (map_of_regs_2 with "Hdst Hsrc") as "[Hmap %]".
    iApply (wp_GetTag_obs _ _ _ _ _ _ _ _ _ _ _ _ dw P Φc
      with "[$HPC $Hpc_a $Hdw $HPr $Hmap]"); eauto.
    { rewrite /regs_of /operands_of !dom_insert_L. set_solver+. }
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hpc_a & Hdw & HPr & Hmap)".
    destruct Hspec as [(v & z & -> & Hv & Hres & Hinc & ->) | (-> & Hinc & -> & ->)].
    - incrementPC_inv; simplify_map_eq.
      iRegsMap "Hmap"; eauto.
      iApply "Hφ". iFrame. done.
    - exfalso. incrementPC_inv; simplify_map_eq; eauto; try congruence.
  Qed.

  (** GetTag returns the tag, or 0 on a word whose tag may have been
      cleared. *)
  Lemma wp_gettag_lax E dst src pc_p pc_g pc_b pc_e pc_a pc_π w wsrc wdst pc_a' dq :
    decodeInstrW w.(lw) = GetTag dst src →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    dst ≠ cnull →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ src ↦ᵣ wsrc
        ∗ ▷ dst ↦ᵣ wdst }}}
      Instr Executable @ E
      {{{ z, RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ src ↦ᵣ wsrc
          ∗ dst ↦ᵣ WInt z
          ∗ ⌜z = Z.b2z (get_tag wsrc.(lw)) ∨ (z = 0%Z ∧ tag_strippable wsrc)⌝ }}}.
  Proof.
    iIntros (Hdecode Hvpc Hpca' Hcnull Hcnull' φ) "(HPC & Hpc_a & >Hsrc & >Hdst) Hφ".
    iDestruct (regname_neq with "Hsrc Hdst") as %Hne.
    iApply (wp_gettag_obs _ _ _ _ _ _ _ _ _ _ _ _ _ _ DerefNoId emp%I (λ _, True)
      with "[$HPC $Hpc_a $Hsrc $Hdst]");
      [done | done | done | done | done | done | by iIntros | done |].
    iIntros "!>" (z) "(HPC & Hpc_a & Hsrc & Hdst & _ & _ & %Hres)".
    iApply "Hφ". iFrame. iPureIntro. apply Hres.
  Qed.

  (** GetTag returns the tag of a word under the dereference resource of its
      identifier, when it has authority or no heap base. *)
  Lemma wp_gettag_success E dst src pc_p pc_g pc_b pc_e pc_a pc_π w ws πs wdst pc_a' dq q :
    decodeInstrW w.(lw) = GetTag dst src →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    load_exact_cond (ws @@? πs) →
    src ≠ cnull →
    dst ≠ cnull →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ src ↦ᵣ ws @@? πs
        ∗ ▷ dst ↦ᵣ wdst
        ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ src ↦ᵣ ws @@? πs
          ∗ dst ↦ᵣ WInt (Z.b2z (get_tag ws))
          ∗ deref_res πs q }}}.
  Proof.
    iIntros (Hdecode Hvpc Hpca' Hcond Hsrc_null Hcnull φ)
      "(HPC & Hpc_a & >Hsrc & >Hdst & Hdw) Hφ".
    iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %Hne]".
    iDestruct (regs_of_map_2 with "Hmap") as "[Hsrc Hdst]"; first done.
    rewrite deref_res_witness.
    iApply (wp_gettag_obs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ emp%I (λ _, True)
      with "[$HPC $Hpc_a $Hsrc $Hdst $Hdw]"); eauto.
    iNext. iIntros (z) "(HPC & Hpc_a & Hsrc & Hdst & Hdw & _ & %Hres)".
    destruct Hres as (_ & Hexact & _).
    rewrite (Hexact (eq_sym (deref_id_witness_of _ _)) Hcond).
    iApply "Hφ". iFrame.
  Qed.

End griotte_lang_rules.

(* Hints to automate proofs of is_Get *)

Lemma is_Get_GetP dst src : is_Get (GetP dst src) dst src.
Proof. intros; unfold is_Get; eauto. Qed.
Lemma is_Get_GetL dst src : is_Get (GetL dst src) dst src.
Proof. intros; unfold is_Get; eauto. Qed.
Lemma is_Get_GetB dst src : is_Get (GetB dst src) dst src.
Proof. intros; unfold is_Get; eauto. Qed.
Lemma is_Get_GetE dst src : is_Get (GetE dst src) dst src.
Proof. intros; unfold is_Get; eauto. Qed.
Lemma is_Get_GetLen dst src : is_Get (GetLen dst src) dst src.
Proof. intros; unfold is_Get; eauto; firstorder. Qed.
Lemma is_Get_GetA dst src : is_Get (GetA dst src) dst src.
Proof. intros; unfold is_Get; eauto; firstorder. Qed.
Lemma is_Get_GetOType dst src : is_Get (GetOType dst src) dst src.
Proof. intros; unfold is_Get; eauto; firstorder. Qed.
Lemma is_Get_GetWType dst src : is_Get (GetWType dst src) dst src.
Proof. intros; unfold is_Get; eauto; firstorder. Qed.
Lemma getwtype_denote `{MachineParameters} r1 r2 w : denote (GetWType r1 r2) w = Some (encodeWordType w).
Proof. by destruct_word w ; cbn. Qed.

#[export] Hint Resolve is_Get_GetP : core.
#[export] Hint Resolve is_Get_GetL : core.
#[export] Hint Resolve is_Get_GetB : core.
#[export] Hint Resolve is_Get_GetE : core.
#[export] Hint Resolve is_Get_GetLen : core.
#[export] Hint Resolve is_Get_GetA : core.
#[export] Hint Resolve is_Get_GetOType : core.
#[export] Hint Resolve is_Get_GetWType : core.
#[export] Hint Resolve getwtype_denote : core.

Lemma is_Get_GetTag dst src : is_Get (GetTag dst src) dst src.
Proof. unfold is_Get; tauto. Qed.

Lemma gettag_denote `{MachineParameters} dst src w :
  denote (GetTag dst src) w = Some (Z.b2z (get_tag w)).
Proof. by destruct_word w. Qed.
#[export] Hint Resolve is_Get_GetTag gettag_denote : core.
