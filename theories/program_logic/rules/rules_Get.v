From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.

Section griotte_lang_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : griotte_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types o : OType.
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
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

  Lemma regs_of_is_Get i dst src :
    is_Get i dst src →
    regs_of i = {[ dst; src ]}.
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
    intros [[Heq | [_ [[(ι & _ & Hι & _) _] | Hh]]] _] Ht; split; try done.
    - by rewrite -Heq get_tag_clear_tag in Ht.
    - left. by rewrite Hι.
    - by right.
  Qed.

  Inductive Get_spec (i: instr) (lpc : LWord) (regs : LReg) (dst src: RegName)
    (lpc' : LWord) (regs' : LReg): griotte_lang.val -> Prop :=
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

  Lemma exec_opt_Get i dst src p (pc : Word) (r : Reg) sr m st (wsrc : Word) :
    is_Get i dst src →
    lookup_reg src r = Some wsrc →
    exec_opt i p (pc, r, sr, m, st) =
      match denote i wsrc with
      | Some z => nextPC (update_reg (pc, r, sr, m, st) dst (WInt z))
      | None => None
      end.
  Proof.
    intros Hi Hs. destruct_or! Hi; subst i; cbn; rewrite Hs /=.
    all: destruct wsrc as [| [] | | ? []]; cbn; done.
  Qed.

  Lemma denote_and_tag i s (w : Word) :
    denote i (and_tag s w) =
      match i with
      | GetTag _ _ => Some (Z.b2z (s && get_tag w))
      | _ => denote i w
      end.
  Proof.
    destruct i; cbn; try done.
    all: try (by destruct s, w as [| [] | | ? []]).
    f_equal. pose proof (encodeWordType_correct (and_tag s w) w) as Heq.
    by destruct w as [| [] | | ? []].
  Qed.

  Lemma wp_Get Ep pc_p pc_g pc_b pc_e pc_a pc_π w get_i dst src regs dq :
    decodeInstrW w.(lw) = get_i →
    is_Get get_i dst src →

    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of get_i ⊆ dom regs →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lpc' regs' retv, RET retv;
        ⌜ Get_spec (decodeInstrW w.(lw)) (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst src lpc' regs' retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc Dregs φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
    iNext; iIntros (r sr m st lreg lsreg lmem R C c σ') "@".
    rewrite Hdecode /exec in Hstep. rewrite Hdecode.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri.
    erewrite regs_of_is_Get in Hri; eauto.
    destruct (Hri src) as [wsrc [H'src _]]; first by set_solver+.
    destruct (llookup_reg_phys _ _ _ _ _ Hregs H'src) as (s & Hsrc & Hrel).
    rewrite (exec_opt_Get _ _ _ _ _ _ _ _ _ _ Hinstr Hsrc) denote_and_tag in Hstep.
    destruct (decide (get_i = GetTag dst src ∧ s = false ∧ get_tag wsrc.(lw) = true))
      as [(-> & -> & Ht) | Hexact].
    { (* The physical tag is cleared. *)
      rewrite Ht /= in Hstep.
      iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ dst (lword_of_word (WInt 0)) _ _ _ _
        (λ lpc' regs' retv, Get_spec (GetTag dst src) _ regs dst src lpc' regs' retv)
        with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
      { exact Her. } { exact Hlregs. }
      { apply Dregs. erewrite regs_of_is_Get; eauto. set_solver+. }
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
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ dst (lword_of_word (WInt z)) _ _ _ _
      (λ lpc' regs' retv, Get_spec get_i _ regs dst src lpc' regs' retv)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
    { exact Her. } { exact Hlregs. }
    { apply Dregs. erewrite regs_of_is_Get; eauto. set_solver+. }
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
  Lemma Get_spec_next i lpc regs dst src lpc' regs' wsrc :
    regs !!ₗ src = Some wsrc →
    Get_spec i lpc regs dst src lpc' regs' NextIV →
    incrementPC lpc = Some lpc' ∧
    ∃ z, get_result i wsrc z ∧ regs' = <[dst := WInt z]ₗ> regs.
  Proof.
    intros Hsrc Hspec. inversion Hspec as [w z Hw Hz Hinc | w Hi Hw Hs Hinc | ]; subst;
      rewrite Hsrc in Hw; simplify_eq; split; try done.
    - exists z. split; [by left | done].
    - exists 0%Z. split; [right; eauto | done].
  Qed.

  (** A Get whose source denotes and whose PC increments does not fail. *)
  Lemma Get_spec_not_faulted i lpc regs dst src lpc' regs' wsrc lpc0 :
    regs !!ₗ src = Some wsrc →
    is_Some (denote i wsrc.(lw)) →
    incrementPC lpc = Some lpc0 →
    ¬ Get_spec i lpc regs dst src lpc' regs' FaultedV.
  Proof.
    intros Hsrc [z Hz] Hinc Hspec. inversion Hspec as [| | Hfail]; subst.
    destruct Hfail as [w z' Hw Hd Hi]; rewrite Hsrc in Hw; simplify_eq; congruence.
  Qed.

  (** The map-form success rule, from which the register-shaped ones
      follow. *)
  Lemma wp_Get_next E get_i dst src pc_p pc_g pc_b pc_e pc_a pc_π w regs wsrc lpc' dq :
    decodeInstrW w.(lw) = get_i →
    is_Get get_i dst src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    {[dst; src]} ⊆ dom regs →
    regs !!ₗ src = Some wsrc →
    is_Some (denote get_i wsrc.(lw)) →
    incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
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
    { by erewrite regs_of_is_Get. }
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
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' ->
    (∀ dst' src', get_i ≠ GetTag dst' src') →
    denote get_i wr.(lw) = Some z →
    r ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r ↦ᵣ wr }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
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
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' ->
    (∀ dst' src', get_i ≠ GetTag dst' src') →
    denote get_i wsrc.(lw) = Some z →
    src ≠ cnull ->
    dst ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ src ↦ᵣ wsrc
        ∗ ▷ dst ↦ᵣ wdst }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
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

  Lemma wp_GetTag_cnull E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w wn dq :
    decodeInstrW w.(lw) = GetTag cnull cnull →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ{dq} w ∗ ▷ cnull ↦ᵣ wn }}}
      Instr Executable @ E
    {{{ RET NextIV; PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗ pc_a ↦ₐ{dq} w ∗ cnull ↦ᵣ WInt 0%Z }}}.
  Proof.
    iIntros (Hdecode Hvpc Hpca' φ) "(HPC & Hpc_a & >Hn) Hφ".
    iDestruct (map_of_regs_1 with "Hn") as "Hmap".
    iApply (wp_Get_next _ (GetTag cnull cnull) cnull cnull _ _ _ _ _ _ _ _ lnull
      with "[$HPC $Hpc_a $Hmap]"); try solve_next_side; try (by unfold is_Get; tauto); try by eexists.
    iIntros "!>" (z') "(_ & HPC & Hpc_a & Hmap)".
    iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_GetTag_from_cnull E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst wd wn dq :
    decodeInstrW w.(lw) = GetTag dst cnull →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' → dst ≠ cnull →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ{dq} w ∗ ▷ cnull ↦ᵣ wn ∗ ▷ dst ↦ᵣ wd }}}
      Instr Executable @ E
    {{{ RET NextIV; PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗ pc_a ↦ₐ{dq} w ∗ dst ↦ᵣ WInt 0%Z ∗ cnull ↦ᵣ wn }}}.
  Proof.
    iIntros (Hdecode Hvpc Hpca' Hne φ) "(HPC & Hpc_a & >Hs & >Hd) Hφ".
    iDestruct (map_of_regs_2 with "Hd Hs") as "[Hmap %]".
    iApply (wp_Get_next _ (GetTag dst cnull) dst cnull _ _ _ _ _ _ _ _ lnull
      with "[$HPC $Hpc_a $Hmap]"); try solve_next_side; try (by unfold is_Get; tauto); try by eexists.
    iIntros "!>" (z') "(%Hz & HPC & Hpc_a & Hmap)".
    assert (z' = 0%Z) as -> by (destruct Hz as [Hz | (_ & -> & [Ht _])]; by simplify_eq/=).
    iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_GetTag_to_cnull E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src wn ws dq :
    decodeInstrW w.(lw) = GetTag cnull src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' → src ≠ cnull →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ{dq} w ∗ ▷ cnull ↦ᵣ wn ∗ ▷ src ↦ᵣ ws }}}
      Instr Executable @ E
    {{{ RET NextIV; PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗ pc_a ↦ₐ{dq} w ∗ cnull ↦ᵣ WInt 0%Z ∗ src ↦ᵣ ws }}}.
  Proof.
    iIntros (Hdecode Hvpc Hpca' Hne φ) "(HPC & Hpc_a & >Hd & >Hs) Hφ".
    iDestruct (map_of_regs_2 with "Hd Hs") as "[Hmap %]".
    iApply (wp_Get_next _ (GetTag cnull src) cnull src _ _ _ _ _ _ _ _ ws
      with "[$HPC $Hpc_a $Hmap]"); try solve_next_side;
      try (by unfold is_Get; tauto); try (destruct_word (lw ws); by eexists).
    iIntros "!>" (z') "(_ & HPC & Hpc_a & Hmap)".
    iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
  Qed.

  (** GetTag returns the tag, or 0 on a word whose tag may have been
      cleared. *)
  Lemma wp_gettag_lax E dst src pc_p pc_g pc_b pc_e pc_a pc_π w wsrc wdst pc_a' dq :
    decodeInstrW w.(lw) = GetTag dst src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    dst ≠ cnull →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ src ↦ᵣ wsrc
        ∗ ▷ dst ↦ᵣ wdst }}}
      Instr Executable @ E
      {{{ z, RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ src ↦ᵣ wsrc
          ∗ dst ↦ᵣ WInt z
          ∗ ⌜z = Z.b2z (get_tag wsrc.(lw)) ∨ (z = 0%Z ∧ tag_strippable wsrc)⌝ }}}.
  Proof.
    iIntros (Hdecode Hvpc Hpca' Hcnull Hcnull' φ) "(HPC & Hpc_a & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "Hdst Hsrc") as "[Hmap %]".
    iApply (wp_Get_next _ (GetTag dst src) dst src _ _ _ _ _ _ _ _ wsrc
      with "[$HPC $Hpc_a $Hmap]"); try solve_next_side;
      try (by unfold is_Get; tauto); try (destruct_word (lw wsrc); by eexists).
    iIntros "!>" (z) "(%Hz & HPC & Hpc_a & Hmap)".
    iRegsMapWrite "Hmap". iApply "Hφ". iFrame. iPureIntro.
    destruct Hz as [Hz | (_ & -> & Hs)]; [left | by right].
    cbn in Hz. by simplify_eq.
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

  Lemma wp_GetTag_obs Ep pc_p pc_g pc_b pc_e pc_a pc_π w dst src regs dq dw
      (P : iProp Σ) (Φc : gmap Addr AddrClaim → Prop) :
    decodeInstrW w.(lw) = GetTag dst src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (GetTag dst src) ⊆ dom regs →
    (∀ C, addr_alloc_auth C -∗ P -∗ ⌜Φc C⌝) →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        deref_witness_res dw ∗
        P ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lpc' regs' retv, RET retv;
        ⌜ (∃ (v : LWord) z, retv = NextIV ∧ regs !!ₗ src = Some v ∧ gettag_result dw Φc v z ∧
             incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' ∧
             regs' = <[dst := WInt z]ₗ> regs) ∨
          (retv = FaultedV ∧ incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) = None ∧
             regs' = regs ∧ lpc' = WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        deref_witness_res dw ∗
        P ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hdecode Hvpc Dregs HP φ) "(>HPC & >Hpc_a & Hdw & HPr & >Hmap) Hφ".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
    iNext; iIntros (r sr m st lreg lsreg lmem R C c σ') "@".
    iDestruct (deref_witness_lookup with "HR Hdw") as %Hdw.
    iDestruct (HP with "HC HPr") as %HΦc.
    rewrite Hdecode /exec in Hstep.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri. unfold regs_of in Hri.
    destruct (Hri src) as [v [Hv Hv']]; first by set_solver+.
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hv) as (s & Hsrc & Hrel).
    rewrite (exec_opt_Get (GetTag dst src) dst src _ _ _ _ _ _ _ ltac:(unfold is_Get; tauto)
               Hsrc) /= in Hstep.
    rewrite get_tag_and_tag in Hstep.
    (* The result is a copy of the logical tag. *)
    assert (gettag_result dw Φc v (Z.b2z (s && get_tag v.(lw)))) as Hres.
    { split_and!.
      - destruct s; first by left. destruct (get_tag v.(lw)) eqn:Ht; last by left.
        right. split; first done. apply (reg_phys_tag_strippable R); last done.
        by rewrite and_tag_false in Hrel.
      - intros Hπ Hcond. rewrite -get_tag_and_tag.
        by rewrite (deref_exact _ _ _ _ Hdw Hπ Hcond Hrel).
      - intros Hz. exists C. split; first done. intros b Hab.
        assert (get_tag (and_tag s v.(lw)) = true) as Htw.
        { rewrite get_tag_and_tag. by destruct (s && get_tag v.(lw)). }
        assert (get_tag v.(lw) = true) as Ht.
        { pose proof (reg_phys_tagged _ _ _ Hrel Htw) as Heq. by rewrite -Heq. }
        pose proof (reg_phys_observe _ _ _ _ _ _ (er_registry _ _ _ _ _ _ _ Her)
                      (erasure_llookup_reg_word _ _ _ _ _ _ _ _ _ _ Her Hlregs Hv) Hrel Htw Hab) as Hobs.
        destruct (lprov v); [by destruct Hobs as (? & ? & ? & ?) | done]. }
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ dst
      (lword_of_word (WInt (Z.b2z (s && get_tag v.(lw))))) _ _ _ _
      (λ lpc' regs' retv,
         (∃ (v : LWord) z, retv = NextIV ∧ regs !!ₗ src = Some v ∧ gettag_result dw Φc v z ∧
            incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' ∧
            regs' = <[dst := WInt z]ₗ> regs) ∨
         (retv = FaultedV ∧ incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) = None ∧
            regs' = regs ∧ lpc' = WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π))
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hdw HPr]").
    { exact Her. } { exact Hlregs. } { apply Dregs. set_solver+. }
    { apply reg_word_ok_int. } { exact Hstep. } { apply reg_phys_lword_of_word. }
    { intros lpc' Hi. left. by exists v, (Z.b2z (s && get_tag v.(lw))). }
    { intros Hi. right. by split_and!. }
    iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
  Qed.

  (** [wp_GetTag_obs] on two distinct registers. *)
  Lemma wp_gettag_obs E dst src pc_p pc_g pc_b pc_e pc_a pc_π w wsrc wdst pc_a' dq dw
      (P : iProp Σ) (Φc : gmap Addr AddrClaim → Prop) :
    decodeInstrW w.(lw) = GetTag dst src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ dst →
    src ≠ cnull →
    dst ≠ cnull →
    (∀ C, addr_alloc_auth C -∗ P -∗ ⌜Φc C⌝) →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ src ↦ᵣ wsrc
        ∗ ▷ dst ↦ᵣ wdst
        ∗ deref_witness_res dw
        ∗ P }}}
      Instr Executable @ E
      {{{ z, RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
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
    { rewrite /regs_of !dom_insert_L. set_solver+. }
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hpc_a & Hdw & HPr & Hmap)".
    destruct Hspec as [(v & z & -> & Hv & Hres & Hinc & ->) | (-> & Hinc & -> & ->)].
    - incrementPC_inv; simplify_map_eq.
      iRegsMap "Hmap"; eauto.
      iApply "Hφ". iFrame. done.
    - exfalso. incrementPC_inv; simplify_map_eq; eauto; try congruence.
  Qed.

  (** GetTag returns the tag of a word under the dereference resource of its
      identifier, when it has authority or no heap base. *)
  Lemma wp_gettag_success E dst src pc_p pc_g pc_b pc_e pc_a pc_π w ws πs wdst pc_a' dq q :
    decodeInstrW w.(lw) = GetTag dst src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    load_exact_cond (ws @@? πs) →
    src ≠ cnull →
    dst ≠ cnull →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ src ↦ᵣ ws @@? πs
        ∗ ▷ dst ↦ᵣ wdst
        ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
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
