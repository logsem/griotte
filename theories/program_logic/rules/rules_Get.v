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

  Inductive Get_spec (i: instr) (lpc : LWord) (regs : LReg) (dst src: RegName)
    (lpc' : LWord) (regs' : LReg): griotte_lang.val -> Prop :=
    | Get_spec_success w z:
        regs !!ₗ src = Some w →
        denote i w.(lw) = Some z →
        incrementPC lpc = Some lpc' →
        regs' = <[ dst := WInt z ]ₗ> regs →
        Get_spec i lpc regs dst src lpc' regs' NextIV
    | Get_spec_failure:
        Get_failure i lpc regs dst src →
        Get_spec i lpc regs dst src lpc' regs' FailedV.

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
    assert (lookup_reg src r = Some wsrc.(lw)) as Hsrc.
    { eapply lookup_reg_weaken; last exact Hregs. by rewrite lookup_reg_erase H'src. }
    destruct (denote get_i wsrc.(lw)) as [z | ] eqn:Hwsrc.
    2 : { (* Failure: src is not of the right word type *)
      assert (c = Failed ∧ σ' = (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st)) as (-> & ->).
      { destruct_or! Hinstr; rewrite Hinstr in Hstep; cbn in Hstep.
        all: rewrite Hsrc /= in Hstep.
        all : destruct wsrc as [[ | [  |  ] | | ] ?]; try (inversion Hstep; auto);
          rewrite /denote /= in Hwsrc; rewrite Hinstr in Hwsrc; congruence. }
      iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); first exact Her.
      iIntros "HPC Hmap". iApply "Hφ". iFrame. iPureIntro. constructor.
      by eapply Get_fail_src_denote. }

    assert (exec_opt get_i pc_p (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) =
              updatePC (update_reg (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) dst (lword_of_word (WInt z)).(lw))) as HH.
    { destruct_or! Hinstr; rewrite Hinstr in Hwsrc |- *; cbn [exec_opt reg fst snd]; rewrite Hsrc /update_reg /=.
      all : destruct wsrc as [[ | [  |  ] | | ] ?]; inversion Hwsrc; auto.
    }
    rewrite HH in Hstep.
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ dst (lword_of_word (WInt z)) _ _ _
      (λ lpc' regs' retv, Get_spec get_i _ regs dst src lpc' regs' retv)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
    { exact Her. } { exact Hlregs. }
    { apply Dregs. erewrite regs_of_is_Get; eauto. set_solver+. }
    { apply reg_word_ok_int. } { exact Hstep. }
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
    iIntros (Hdecode Hinstr Hvpc Hpca' Hdenote Hcnull φ) "(>HPC & >Hpc_a & >Hr) Hφ".
    iDestruct (map_of_regs_1 with "Hr") as "Hmap".
    iApply (wp_Get with "[$HPC $Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    all: try (by erewrite regs_of_is_Get; eauto; rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. try incrementPC_inv; simplify_map_eq.
      iRegsMap "Hmap"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto; try congruence. }
  Qed.

  Lemma wp_Get_success E get_i dst src pc_p pc_g pc_b pc_e pc_a pc_π w wsrc wdst pc_a' z dq :
    decodeInstrW w.(lw) = get_i →
    is_Get get_i dst src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' ->
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
    iIntros (Hdecode Hinstr Hvpc Hpca' Hdenote Hcnull Hcnull' φ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "Hdst Hsrc") as "[Hmap %]".
    iApply (wp_Get with "[$HPC $Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    all: try (by erewrite regs_of_is_Get; eauto; rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. try incrementPC_inv; simplify_map_eq.
      iRegsMap "Hmap"; eauto; iFrame. }
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
    destruct Hspec as [* Hsucc |].
    { (* Success (contradiction) *)
      destruct_or! Hinstr; simplify_map_eq; match goal with H : denote _ _ = Some _ |- _ => rewrite Hinstr /denote in H end; naive_solver.
    }
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
    destruct Hspec as [* Hsucc |].
    { (* Success (contradiction) *)
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
    { (* Failure, done *) by iApply "Hφ"; iLeft. }
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
    destruct Hspec as [| * Hfail].
    - try incrementPC_inv; simplify_map_eq; eauto.
      iRegsMap "Hmap"; eauto.
      iApply "Hφ". iFrame.
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
    destruct Hspec as [| * Hfail].
    - try incrementPC_inv; simplify_map_eq; try exact lnull.
      iRegsMap "Hmap"; eauto.
      iApply "Hφ". iFrame.
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
    destruct Hspec as [| * Hfail].
    - try incrementPC_inv; simplify_map_eq; eauto.
      iRegsMap "Hmap"; eauto.
      iApply "Hφ". iFrame.
    - destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto; try congruence.
      all: match goal with H : denote (GetTag _ _) ?v = None |- _ =>
        destruct_word v; discriminate end.
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
Lemma gettag_denote `{MachineParameters} dst src w :
  denote (GetTag dst src) w = Some (Z.b2z (get_tag w)).
Proof. by destruct_word w. Qed.
Global Hint Resolve is_Get_GetTag gettag_denote : core.
