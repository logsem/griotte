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
    | GetP _ _ =>
        match get_p w with
        | Some p => Some (encodePermSum p)
        | None => None
        end
    | GetL _ _ =>
        match get_l w with
        | Some g => Some (encodeLoc g)
        | None => None
        end
    | GetB _ _ => get_b w
    | GetE _ _ => get_e w
    | GetA _ _ => get_a w
    | GetOType _ _ =>
        match w with
        | WSealed o _ => Some (o:Z)
        | _ => Some (-1)%Z
        end
    | GetTag _ _ => Some (Z.b2z (get_tag w))
    | GetWType _ _ => Some (encodeWordType w)
    | _ => None
    end.

  Global Arguments denote : simpl nomatch.

  Definition is_Get (i: instr) (dst src: RegName) :=
    i = GetP dst src ∨
    i = GetL dst src ∨
    i = GetB dst src ∨
    i = GetE dst src ∨
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

  (* Simpler definition, easier to use when proving wp-rules *)
  Definition denote_cap (i: instr) (t : bool) (p : Perm) (g : Locality) (b e a : Addr): Z :=
      match i with
      | GetP _ _ => (encodePerm p)
      | GetL _ _ => (encodeLoc g)
      | GetB _ _ => b
      | GetE _ _ => e
      | GetA _ _ => a
      | GetOType _ _ => (-1)%Z
      | GetTag _ _ => Z.b2z t
      | GetWType _ _ => (encodeWordType (WCap t p g b e a))
      | _ => 0%Z
      end.
  Lemma denote_cap_denote i (t : bool) p g b e a z src dst:
    is_Get i src dst → denote_cap i t p g b e a = z → denote i (WCap t p g b e a) = Some z.
  Proof.
    unfold denote_cap, denote, is_Get.
    intros Hi <-. destruct_or! Hi; subst; done.
  Qed.

  Definition denote_seal (i: instr) (t : bool) (p : SealPerms) (g : Locality) (b e a : OType): Z :=
      match i with
      | GetP _ _ => (encodeSealPerms p)
      | GetL _ _ => (encodeLoc g)
      | GetB _ _ => b
      | GetE _ _ => e
      | GetA _ _ => a
      | GetOType _ _ => (-1)%Z
      | GetTag _ _ => Z.b2z t
      | GetWType _ _ => (encodeWordType (WSealRange t p g b e a))
      | _ => 0%Z
      end.
  Lemma denote_seal_denote i (t : bool) (p : SealPerms) (g : Locality) (b e a : OType) z src dst:
    is_Get i src dst → denote_seal i t p g b e a = z → denote i (WSealRange t p g b e a) = Some z.
  Proof.
    unfold denote_seal, denote, is_Get.
    intros Hi <-. destruct_or! Hi; subst; done.
  Qed.

  Inductive Get_failure (i: instr) (lpc : LWord) (regs : LReg) (dst src: RegName) :=
    | Get_fail_src_denote w:
        regs !!ₗ src = Some w →
        denote i w.(lw) = None →
        Get_failure i lpc regs dst src
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

  (** A Get result is exact, except a GetTag on a word whose tag may be
      cleared. *)
  Definition get_exact (i : instr) (w : LWord) : Prop :=
    match i with
    | GetTag _ _ => ¬ tag_strippable w
    | _ => True
    end.

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
        Get_spec i lpc regs dst src lpc' regs' FailedV.

  Lemma exec_opt_Get i dst src p (pc : Word) (r : Reg) sr m st (wsrc : Word) :
    is_Get i dst src →
    lookup_reg src r = Some wsrc →
    exec_opt i p (pc, r, sr, m, st) =
      match denote i wsrc with
      | Some z => updatePC (update_reg (pc, r, sr, m, st) dst (WInt z))
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
    iNext. iIntros (r sr m st lreg lmem R C c σ' Her Hlregs Hregs Hpc_a Hstep)
      "HPCa Hr Hsr Hm Hst HR HC HPC Hpc_a Hmap".
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
      iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ dst (lword_of_word (WInt 0)) _ _ _ _
        (λ lpc' regs' retv, Get_spec (GetTag dst src) _ regs dst src lpc' regs' retv)
        with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
      { exact Her. } { exact Hlregs. }
      { apply Dregs. erewrite regs_of_is_Get; eauto. set_solver+. }
      { apply reg_word_ok_int. } { exact Hstep. } { apply reg_phys_lword_of_word. }
      { intros. eapply Get_spec_success_cleared; eauto.
        apply (reg_phys_tag_strippable R); last done. by rewrite and_tag_false in Hrel. }
      { intros. constructor. by eapply (Get_fail_overflow_PC _ _ _ _ _ wsrc (Z.b2z (get_tag wsrc.(lw)))). }
      iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame. }
    assert ((match get_i with
             | GetTag _ _ => Some (Z.b2z (s && get_tag wsrc.(lw)))
             | _ => denote get_i wsrc.(lw)
             end) = denote get_i wsrc.(lw)) as Hden.
    { destruct_or! Hinstr; rewrite Hinstr; cbn; try done. f_equal.
      destruct s, (get_tag wsrc.(lw)); naive_solver. }
    rewrite Hden in Hstep.
    destruct (denote get_i wsrc.(lw)) as [z | ] eqn:Hwsrc.
    2 : { (* Failure: src is not of the right word type *)
      simplify_eq.
      iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); first exact Her.
      iIntros "HPC Hmap". iApply "Hφ". iFrame. iPureIntro. constructor.
      by eapply Get_fail_src_denote. }
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ dst (lword_of_word (WInt z)) _ _ _ _
      (λ lpc' regs' retv, Get_spec get_i _ regs dst src lpc' regs' retv)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
    { exact Her. } { exact Hlregs. }
    { apply Dregs. erewrite regs_of_is_Get; eauto. set_solver+. }
    { apply reg_word_ok_int. } { exact Hstep. } { apply reg_phys_lword_of_word. }
    { intros. by econstructor. }
    { intros. constructor. by eapply Get_fail_overflow_PC. }
    iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
  Qed.

  (* Note that other cases than WCap in the PC are irrelevant, as that will result in having an incorrect PC *)

  Lemma wp_Get_same_success E get_i r pc_p pc_g pc_b pc_e pc_a pc_π w wr pc_a' z dq:
    decodeInstrW w.(lw) = get_i →
    is_Get get_i r r →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' ->
    denote get_i wr.(lw) = Some z →
    get_exact get_i wr →
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
    iIntros (Hdecode Hinstr Hvpc Hpca' Hdenote Hexact Hcnull φ) "(>HPC & >Hpc_a & >Hr) Hφ".
    iDestruct (map_of_regs_1 with "Hr") as "Hmap".
    iApply (wp_Get with "[$HPC $Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    all: try (by erewrite regs_of_is_Get; eauto; rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| ? Hi Hw Hstrip | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. try incrementPC_inv; simplify_map_eq.
      iRegsMap "Hmap"; eauto; iFrame. }
    { (* Cleared tag (contradiction) *)
      exfalso. rewrite Hi in Hexact. simplify_map_eq; by apply Hexact. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto; try congruence. }
  Qed.

  Lemma wp_Get_success E get_i dst src pc_p pc_g pc_b pc_e pc_a pc_π w wsrc wdst pc_a' z dq :
    decodeInstrW w.(lw) = get_i →
    is_Get get_i dst src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' ->
    denote get_i wsrc.(lw) = Some z →
    get_exact get_i wsrc →
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
    iIntros (Hdecode Hinstr Hvpc Hpca' Hdenote Hexact Hcnull Hcnull' φ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "Hdst Hsrc") as "[Hmap %]".
    iApply (wp_Get with "[$HPC $Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    all: try (by erewrite regs_of_is_Get; eauto; rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| ? Hi Hw Hstrip | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. try incrementPC_inv; simplify_map_eq.
      iRegsMap "Hmap"; eauto; iFrame. }
    { (* Cleared tag (contradiction) *)
      exfalso. rewrite Hi in Hexact. simplify_map_eq; by apply Hexact. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto; try congruence. }
  Qed.

  Lemma wp_Get_fail E get_i dst src pc_p pc_g pc_b pc_e pc_a pc_π w wsrc zsrc wdst dq :
    decodeInstrW w.(lw) = get_i →
    is_Get get_i dst src →
    IsLInt wsrc zsrc →
    (forall dst' src', get_i <> GetOType dst' src') ->
    (forall dst' src', get_i <> GetWType dst' src') ->
    (forall dst' src', get_i <> GetTag dst' src') ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    src ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
      ∗ ▷ pc_a ↦ₐ{dq} w
      ∗ ▷ dst ↦ᵣ wdst
      ∗ ▷ src ↦ᵣ wsrc }}}
      Instr Executable @ E
      {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hdecode Hinstr Hwsrc Hnot_otype Hnot_wtype Hnot_tag Hvpc Hcnull φ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
    destruct (IsLInt_inv _ _ Hwsrc) as [πsrc ->].
    iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %]".
    iApply (wp_Get with "[$HPC $Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    all: try (by erewrite regs_of_is_Get; eauto; rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [* Hsucc | * Hi | ].
    { (* Success (contradiction) *)
      destruct_or! Hinstr; simplify_map_eq; match goal with H : denote _ _ = Some _ |- _ => rewrite Hinstr /denote in H end; naive_solver.
    }
    { (* Cleared tag (contradiction) *) by exfalso; eapply Hnot_tag. }
    { (* Failure, done *) by iApply "Hφ". }
  Qed.

  Lemma wp_Get_unknown E get_i dst src pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w wsrc wdst dq :
    decodeInstrW w.(lw) = get_i →
    is_Get get_i dst src →
    (forall dst' src', get_i <> GetOType dst' src') ->
    (forall dst' src', get_i <> GetWType dst' src') ->
    (forall dst' src', get_i <> GetTag dst' src') ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull ->
    dst ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
      ∗ ▷ pc_a ↦ₐ{dq} w
      ∗ ▷ dst ↦ᵣ wdst
      ∗ ▷ src ↦ᵣ wsrc }}}
      Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝
        ∨ (∃ z,
           ⌜ denote get_i wsrc.(lw) = Some z ⌝
           ∗ ⌜ (is_cap wsrc.(lw) || is_sealr wsrc.(lw) || is_sentry wsrc.(lw) || is_sealed wsrc.(lw)) = true ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
           ∗ pc_a ↦ₐ{dq} w
           ∗ src ↦ᵣ wsrc
           ∗ dst ↦ᵣ WInt z
          )
       }}}.
  Proof.
    iIntros (Hdecode Hinstr Hnot_otype Hnot_wtype Hnot_tag Hvpc Hpc_a' Hcnull Hcnull' φ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %]".
    iApply (wp_Get with "[$HPC $Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    all: try (by erewrite regs_of_is_Get; eauto; rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [* Hsucc | * Hi | ].
    2: { (* Cleared tag (contradiction) *) by exfalso; eapply Hnot_tag. }
    2: { (* Failure, done *) by iApply "Hφ"; iLeft. }
    { (* Success *)
      iApply "Hφ".
      iRight.
      iExists z.
      iFrame. try incrementPC_inv; simplify_map_eq.
      iRegsMap "Hmap"; eauto; iFrame.
      iFrame "%".
      iSplit; last done.
      iPureIntro.
      destruct wsrc as [[| [|] | |] ?]; cbn; try done
      ; destruct_or! Hinstr; simplify_map_eq; match goal with H : denote _ _ = Some _ |- _ => rewrite Hinstr /denote in H end; naive_solver.
    }
  Qed.

  Lemma wp_GetTag_cnull E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w wn dq :
    decodeInstrW w.(lw) = GetTag cnull cnull →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ{dq} w ∗ ▷ cnull ↦ᵣ wn }}}
      Instr Executable @ E
    {{{ RET NextIV; PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗ pc_a ↦ₐ{dq} w ∗ cnull ↦ᵣ WInt 0%Z }}}.
  Proof.
    iIntros (Hdecode Hvpc Hinc φ) "(>HPC & >Hmem & >Hn) Hφ".
    iDestruct (map_of_regs_1 with "Hn") as "Hmap".
    iApply (wp_Get with "[$HPC $Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    { unfold is_Get. do 7 right. reflexivity. }
    all: try (by unfold regs_of; rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hmem & Hmap)".
    rewrite Hdecode in Hspec.
    destruct Hspec as [| * Hi Hw Hstrip | * Hfail].
    - try incrementPC_inv; simplify_map_eq; eauto.
      iRegsMap "Hmap"; eauto.
      iApply "Hφ". iFrame.
    - exfalso. erewrite llookup_reg_cnull in Hw; last by simplify_map_eq. simplify_eq. by destruct Hstrip.
    - destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto; congruence.
  Qed.

  Lemma wp_GetTag_from_cnull E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst wd wn dq :
    decodeInstrW w.(lw) = GetTag dst cnull →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' → dst ≠ cnull →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ{dq} w ∗ ▷ cnull ↦ᵣ wn ∗ ▷ dst ↦ᵣ wd }}}
      Instr Executable @ E
    {{{ RET NextIV; PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗ pc_a ↦ₐ{dq} w ∗ dst ↦ᵣ WInt 0%Z ∗ cnull ↦ᵣ wn }}}.
  Proof.
    iIntros (Hdecode Hvpc Hinc Hne φ) "(>HPC & >Hmem & >Hs & >Hd) Hφ".
    iDestruct (map_of_regs_2 with "Hd Hs") as "[Hmap %]".
    iApply (wp_Get with "[$HPC $Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    { unfold is_Get. do 7 right. reflexivity. }
    all: try (by unfold regs_of; rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hmem & Hmap)".
    rewrite Hdecode in Hspec.
    destruct Hspec as [| * Hi Hw Hstrip | * Hfail].
    - try incrementPC_inv; simplify_map_eq; try exact lnull.
      iRegsMap "Hmap"; eauto.
      iApply "Hφ". iFrame.
    - exfalso. erewrite llookup_reg_cnull in Hw; last by simplify_map_eq. simplify_eq. by destruct Hstrip.
    - destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto; congruence.
  Qed.

  Lemma wp_GetTag_to_cnull E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src wn ws dq :
    decodeInstrW w.(lw) = GetTag cnull src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' → src ≠ cnull →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ{dq} w ∗ ▷ cnull ↦ᵣ wn ∗ ▷ src ↦ᵣ ws }}}
      Instr Executable @ E
    {{{ RET NextIV; PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗ pc_a ↦ₐ{dq} w ∗ cnull ↦ᵣ WInt 0%Z ∗ src ↦ᵣ ws }}}.
  Proof.
    iIntros (Hdecode Hvpc Hinc Hne φ) "(>HPC & >Hmem & >Hd & >Hs) Hφ".
    iDestruct (map_of_regs_2 with "Hd Hs") as "[Hmap %]".
    iApply (wp_Get with "[$HPC $Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    { unfold is_Get. do 7 right. reflexivity. }
    all: try (by unfold regs_of; rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hmem & Hmap)".
    rewrite Hdecode in Hspec.
    destruct Hspec as [| * Hi Hw Hstrip Hinc' -> | * Hfail].
    - try incrementPC_inv; simplify_map_eq; eauto.
      iRegsMap "Hmap"; eauto.
      iApply "Hφ". iFrame.
    - try incrementPC_inv; simplify_map_eq; eauto.
      iRegsMap "Hmap"; eauto.
      iApply "Hφ". iFrame.
    - destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto; try congruence.
      all: match goal with H : denote (GetTag _ _) ?v = None |- _ =>
        destruct_word v; discriminate end.
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
    iIntros (Hdecode Hvpc Hpca' Hcnull Hcnull' φ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "Hdst Hsrc") as "[Hmap %]".
    iApply (wp_Get with "[$HPC $Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { unfold is_Get. tauto. }
    all: try (by unfold regs_of; rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hpc_a & Hmap)".
    rewrite Hdecode in Hspec.
    destruct Hspec as [wv z Hw Hz Hinc -> | wv Hi Hw Hstrip Hinc -> | * Hfail].
    - incrementPC_inv; simplify_map_eq.
      iRegsMap "Hmap"; eauto.
      iApply "Hφ". iFrame. iPureIntro. left. by destruct_word (lw wsrc); simplify_eq.
    - incrementPC_inv; simplify_map_eq.
      iRegsMap "Hmap"; eauto.
      iApply "Hφ". iFrame. iPureIntro. by right.
    - exfalso. destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto; try congruence.
      all: match goal with H : denote (GetTag _ _) ?v = None |- _ => destruct_word v; discriminate end.
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
          (retv = FailedV ∧ incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) = None ∧
             regs' = regs) ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        deref_witness_res dw ∗
        P ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hdecode Hvpc Dregs HP φ) "(>HPC & >Hpc_a & Hdw & HPr & >Hmap) Hφ".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
    iNext. iIntros (r sr m st lreg lmem R C c σ' Her Hlregs Hregs Hpc_a Hstep)
      "HPCa Hr Hsr Hm Hst HR HC HPC Hpc_a Hmap".
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
        pose proof (reg_phys_observe _ _ _ _ _ _ (er_registry _ _ _ _ _ _ Her)
                      (erasure_llookup_reg_word _ _ _ _ _ _ _ _ _ Her Hlregs Hv) Hrel Htw Hab) as Hobs.
        destruct (lprov v); [by destruct Hobs as (? & ? & ? & ?) | done]. }
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ dst
      (lword_of_word (WInt (Z.b2z (s && get_tag v.(lw))))) _ _ _ _
      (λ lpc' regs' retv,
         (∃ (v : LWord) z, retv = NextIV ∧ regs !!ₗ src = Some v ∧ gettag_result dw Φc v z ∧
            incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' ∧
            regs' = <[dst := WInt z]ₗ> regs) ∨
         (retv = FailedV ∧ incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) = None ∧
            regs' = regs))
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hdw HPr]").
    { exact Her. } { exact Hlregs. } { apply Dregs. set_solver+. }
    { apply reg_word_ok_int. } { exact Hstep. } { apply reg_phys_lword_of_word. }
    { intros lpc' Hi. left. by exists v, (Z.b2z (s && get_tag v.(lw))). }
    { intros Hi. by right. }
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
    destruct Hspec as [(v & z & -> & Hv & Hres & Hinc & ->) | (-> & Hinc & ->)].
    - incrementPC_inv; simplify_map_eq.
      iRegsMap "Hmap"; eauto.
      iApply "Hφ". iFrame. done.
    - exfalso. incrementPC_inv; simplify_map_eq; eauto; try congruence.
  Qed.

  (** GetTag returns the tag of a word under a dereference witness for its
      identifier, when it has authority or no heap base. *)
  Lemma wp_gettag_success_dw E dst src pc_p pc_g pc_b pc_e pc_a pc_π w wsrc wdst pc_a' dq dw :
    decodeInstrW w.(lw) = GetTag dst src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    wsrc.(lprov) = deref_id dw →
    load_exact_cond wsrc →
    src ≠ dst →
    src ≠ cnull →
    dst ≠ cnull →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ src ↦ᵣ wsrc
        ∗ ▷ dst ↦ᵣ wdst
        ∗ deref_witness_res dw }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ src ↦ᵣ wsrc
          ∗ dst ↦ᵣ WInt (Z.b2z (get_tag wsrc.(lw)))
          ∗ deref_witness_res dw }}}.
  Proof.
    iIntros (Hdecode Hvpc Hpca' Hπ Hcond Hne Hsrc_null Hcnull φ)
      "(HPC & Hpc_a & Hsrc & Hdst & Hdw) Hφ".
    iApply (wp_gettag_obs _ _ _ _ _ _ _ _ _ _ _ _ _ _ dw emp%I (λ _, True)
      with "[$HPC $Hpc_a $Hsrc $Hdst $Hdw]"); eauto.
    iNext. iIntros (z) "(HPC & Hpc_a & Hsrc & Hdst & Hdw & _ & %Hres)".
    destruct Hres as (_ & Hexact & _). rewrite (Hexact Hπ Hcond).
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
Lemma is_Get_GetA dst src : is_Get (GetA dst src) dst src.
Proof. intros; unfold is_Get; eauto; firstorder. Qed.
Lemma is_Get_GetOType dst src : is_Get (GetOType dst src) dst src.
Proof. intros; unfold is_Get; eauto; firstorder. Qed.
Lemma is_Get_GetWType dst src : is_Get (GetWType dst src) dst src.
Proof. intros; unfold is_Get; eauto; firstorder. Qed.
Lemma getwtype_denote `{MachineParameters} r1 r2 w : denote (GetWType r1 r2) w = Some (encodeWordType w).
Proof. by destruct_word w ; cbn. Qed.

Global Hint Resolve is_Get_GetP : core.
Global Hint Resolve is_Get_GetL : core.
Global Hint Resolve is_Get_GetB : core.
Global Hint Resolve is_Get_GetE : core.
Global Hint Resolve is_Get_GetA : core.
Global Hint Resolve is_Get_GetOType : core.
Global Hint Resolve is_Get_GetWType : core.
Global Hint Resolve getwtype_denote : core.

Lemma is_Get_GetTag dst src : is_Get (GetTag dst src) dst src.
Proof. unfold is_Get; tauto. Qed.
Lemma get_exact_gettag_untagged `{MachineParameters} dst src (w : LWord) :
  get_tag w.(lw) = false → get_exact (GetTag dst src) w.
Proof. intros Ht [Ht' _]. congruence. Qed.

Lemma gettag_denote `{MachineParameters} dst src w :
  denote (GetTag dst src) w = Some (Z.b2z (get_tag w)).
Proof. by destruct_word w. Qed.
Global Hint Resolve is_Get_GetTag gettag_denote : core.
