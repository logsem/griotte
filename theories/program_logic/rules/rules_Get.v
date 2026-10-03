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
    match w with
    | WCap t p g b e a =>
        match i with
        | GetP _ _ => Some (encodePerm p)
        | GetL _ _ => Some (encodeLoc g)
        | GetB _ _ => Some (b:Z)
        | GetE _ _ => Some (e:Z)
        | GetA _ _ => Some (a:Z)
        | GetOType _ _ => Some (-1)%Z
        | GetTag _ _ => Some (Z.b2z (get_tag w))
        | GetWType _ _ => Some (encodeWordType w)
        | _ => None
        end
    | WSentry t p g b e a =>
        match i with
        | GetP _ _ => Some (encodePerm p)
        | GetL _ _ => Some (encodeLoc g)
        | GetB _ _ => Some (b:Z)
        | GetE _ _ => Some (e:Z)
        | GetA _ _ => Some (a:Z)
        | GetOType _ _ => Some (-1)%Z
        | GetTag _ _ => Some (Z.b2z (get_tag w))
        | GetWType _ _ => Some (encodeWordType w)
        | _ => None
        end
    | WSealRange t p g b e a =>
        match i with
        | GetP _ _ => Some (encodeSealPerms p)
        | GetL _ _ => Some (encodeLoc g)
        | GetB _ _ => Some (b:Z)
        | GetE _ _ => Some (e:Z)
        | GetA _ _ => Some (a:Z)
        | GetOType _ _ => Some (-1)%Z
        | GetTag _ _ => Some (Z.b2z (get_tag w))
        | GetWType _ _ => Some (encodeWordType w)
        | _ => None
        end
    | WSealed o _ =>
        match i with
        | GetOType _ _ => Some (o:Z)
        | GetTag _ _ => Some (Z.b2z (get_tag w))
        | GetWType _ _ => Some (encodeWordType w)
        | _ => None
        end
    | WInt _ =>
        match i with
        | GetOType _ _ => Some (-1)%Z
        | GetTag _ _ => Some (Z.b2z (get_tag w))
        | GetWType _ _ => Some (encodeWordType w)
        | _ => None
        end
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


  Inductive Get_failure (i: instr) (regs : LReg) (dst src: RegName) :=
    | Get_fail_src_denote w:
        regs !!ₗ src = Some w →
        denote i w.(lw) = None →
        Get_failure i regs dst src
    | Get_fail_overflow_PC w z:
        regs !!ₗ src = Some w →
        denote i w.(lw) = Some z →
        incrementPC (<[ dst := WInt z ]ₗ> regs) = None →
        Get_failure i regs dst src.

  Inductive Get_spec (i: instr) (regs : LReg) (dst src: RegName) (regs' : LReg): griotte_lang.val -> Prop :=
    | Get_spec_success w z:
        regs !!ₗ src = Some w →
        denote i w.(lw) = Some z →
        incrementPC (<[ dst := WInt z ]ₗ> regs) = Some regs' →
        Get_spec i regs dst src regs' NextIV
    | Get_spec_failure:
        Get_failure i regs dst src →
        Get_spec i regs dst src regs' FailedV.

  Lemma wp_Get Ep pc_p pc_g pc_b pc_e pc_a pc_π w get_i dst src regs :
    decodeInstrW w.(lw) = get_i →
    is_Get get_i dst src →

    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs_of get_i ⊆ dom regs →
    {{{ ▷ pc_a ↦ₐ w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ Get_spec (decodeInstrW w.(lw)) regs dst src regs' retv ⌝ ∗
        pc_a ↦ₐ w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "Hpc_a Hmap"); eauto.
    iNext. iIntros (r sr m st lreg lmem R C c σ' Her Hlregs Hregs Hpc_a Hstep)
      "Hr Hsr Hm Hst HR HC Hpc_a Hmap".
    rewrite Hdecode /exec in Hstep. rewrite Hdecode.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri.
    erewrite regs_of_is_Get in Hri; eauto.
    destruct (Hri src) as [wsrc [H'src _]]; first by set_solver+.
    assert (lookup_reg src r = Some wsrc.(lw)) as Hsrc.
    { eapply lookup_reg_weaken; last exact Hregs. by rewrite lookup_reg_erase H'src. }
    destruct (denote get_i wsrc.(lw)) as [z | ] eqn:Hwsrc.
    2 : { (* Failure: src is not of the right word type *)
      assert (c = Failed ∧ σ' = (r, sr, m, st)) as (-> & ->).
      { destruct_or! Hinstr; rewrite Hinstr in Hstep; cbn in Hstep.
        all: rewrite Hsrc /= in Hstep.
        all : destruct wsrc as [[ | [  |  ] | | ] ?]; try (inversion Hstep; auto);
          rewrite /denote /= in Hwsrc; rewrite Hinstr in Hwsrc; congruence. }
      iApply (instr_close_fail with "Hr Hsr Hm Hst HR HC Hmap"); first exact Her.
      iIntros "Hmap". iApply "Hφ". iFrame. iPureIntro. constructor.
      by eapply Get_fail_src_denote. }

    assert (exec_opt get_i pc_p (r, sr, m, st) =
              updatePC (update_reg (r, sr, m, st) dst (lword_of_word (WInt z)).(lw))) as HH.
    { destruct_or! Hinstr; rewrite Hinstr in Hwsrc |- *; cbn [exec_opt reg fst]; rewrite Hsrc /update_reg /=.
      all : destruct wsrc as [[ | [  |  ] | | ] ?]; inversion Hwsrc; auto.
    }
    rewrite HH in Hstep.
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ dst (lword_of_word (WInt z)) _ _ _
      (λ regs' retv, Get_spec get_i regs dst src regs' retv)
      with "Hr Hsr Hm Hst HR HC Hmap [Hφ Hpc_a]").
    { exact Her. } { exact Hlregs. }
    { apply Dregs. erewrite regs_of_is_Get; eauto. set_solver+. } { by eexists. }
    { apply reg_word_ok_int. } { exact Hstep. }
    { intros. by econstructor. }
    { intros. constructor. by eapply Get_fail_overflow_PC. }
    iIntros (regs' retv Hspec) "Hmap". iApply "Hφ". by iFrame.
  Qed.

  (* Note that other cases than WCap in the PC are irrelevant, as that will result in having an incorrect PC *)
  Lemma wp_Get_PC_success E get_i dst pc_p pc_g pc_b pc_e pc_a pc_π w wdst pc_a' z :
    decodeInstrW w.(lw) = get_i →
    is_Get get_i dst PC →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' ->
    denote get_i (WCap true pc_p pc_g pc_b pc_e pc_a) = Some z →
    dst ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ wdst }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ dst ↦ᵣ WInt z }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc Hpca' Hdenote Hcnull φ) "(>HPC & >Hpc_a & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iApply (wp_Get with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_Get; eauto; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite insert_insert_ne // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "[? ?]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; pose proof PC_not_cnull; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_Get_same_success E get_i r pc_p pc_g pc_b pc_e pc_a pc_π w wr pc_a' z:
    decodeInstrW w.(lw) = get_i →
    is_Get get_i r r →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' ->
    denote get_i wr.(lw) = Some z →
    r ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r ↦ᵣ wr }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r ↦ᵣ WInt z }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc Hpca' Hdenote Hcnull φ) "(>HPC & >Hpc_a & >Hr) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr") as "[Hmap %]".
    iApply (wp_Get with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_Get; eauto; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite insert_insert_ne // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "[? ?]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; pose proof PC_not_cnull; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_Get_success E get_i dst src pc_p pc_g pc_b pc_e pc_a pc_π w wsrc wdst pc_a' z :
    decodeInstrW w.(lw) = get_i →
    is_Get get_i dst src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' ->
    denote get_i wsrc.(lw) = Some z →
    src ≠ cnull ->
    dst ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ src ↦ᵣ wsrc
        ∗ ▷ dst ↦ᵣ wdst }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ src ↦ᵣ wsrc
          ∗ dst ↦ᵣ WInt z }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc Hpca' Hdenote Hcnull Hcnull' φ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hdst Hsrc") as "[Hmap (%&%&%)]".
    iApply (wp_Get with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_Get; eauto; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite insert_insert_ne // insert_insert_eq (insert_insert_ne _ PC dst) // insert_insert_eq.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; pose proof PC_not_cnull; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_Get_fail E get_i dst src pc_p pc_g pc_b pc_e pc_a pc_π w zsrc wdst :
    decodeInstrW w.(lw) = get_i →
    is_Get get_i dst src →
    (forall dst' src', get_i <> GetOType dst' src') ->
    (forall dst' src', get_i <> GetWType dst' src') ->
    (forall dst' src', get_i <> GetTag dst' src') ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    src ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
      ∗ ▷ pc_a ↦ₐ w
      ∗ ▷ dst ↦ᵣ wdst
      ∗ ▷ src ↦ᵣ WInt zsrc }}}
      Instr Executable @ E
      {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hdecode Hinstr Hnot_otype Hnot_wtype Hnot_tag Hvpc Hcnull φ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Get with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_Get; eauto; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [* Hsucc |].
    { (* Success (contradiction) *)
      destruct_or! Hinstr; simplify_map_eq; rewrite Hinstr /denote in H2; naive_solver.
    }
    { (* Failure, done *) by iApply "Hφ". }
  Qed.

  Lemma wp_Get_unknown E get_i dst src pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w wsrc wdst :
    decodeInstrW w.(lw) = get_i →
    is_Get get_i dst src →
    (forall dst' src', get_i <> GetOType dst' src') ->
    (forall dst' src', get_i <> GetWType dst' src') ->
    (forall dst' src', get_i <> GetTag dst' src') ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull ->
    dst ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
      ∗ ▷ pc_a ↦ₐ w
      ∗ ▷ dst ↦ᵣ wdst
      ∗ ▷ src ↦ᵣ wsrc }}}
      Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝
        ∨ (∃ z,
           ⌜ denote get_i wsrc.(lw) = Some z ⌝
           ∗ ⌜ (is_cap wsrc.(lw) || is_sealr wsrc.(lw) || is_sentry wsrc.(lw)) = true ⌝
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
           ∗ pc_a ↦ₐ w
           ∗ src ↦ᵣ wsrc
           ∗ dst ↦ᵣ WInt z
          )
       }}}.
  Proof.
    iIntros (Hdecode Hinstr Hnot_otype Hnot_wtype Hnot_tag Hvpc Hpc_a' Hcnull Hcnull' φ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Get with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_Get; eauto; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [* Hsucc |].
    { (* Success (contradiction) *)
      iApply "Hφ".
      iRight.
      iExists z.
      iFrame. incrementPC_inv; simplify_map_eq.
      rewrite insert_insert_ne // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame.
      iFrame "%".
      iSplit; last done.
      iPureIntro.
      destruct wsrc as [[| [|] | |] ?]; cbn; try done
      ; destruct_or! Hinstr; simplify_map_eq; rewrite Hinstr /denote in H2; naive_solver.
    }
    { (* Failure, done *) by iApply "Hφ"; iLeft. }
  Qed.

  Lemma wp_GetTag_cnull E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w wn :
    decodeInstrW w.(lw) = GetTag cnull cnull →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ w ∗ ▷ cnull ↦ᵣ wn }}}
      Instr Executable @ E
    {{{ RET NextIV; PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗ pc_a ↦ₐ w ∗ cnull ↦ᵣ WInt 0%Z }}}.
  Proof.
    iIntros (Hdecode Hvpc Hinc φ) "(>HPC & >Hmem & >Hn) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hn") as "[Hmap %]".
    iApply (wp_Get with "[$Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    { unfold is_Get. do 7 right. reflexivity. }
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    rewrite Hdecode in Hspec.
    destruct Hspec as [| * Hfail].
    - incrementPC_inv; simplify_map_eq; eauto.
      rewrite insert_insert_ne // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto.
      iApply "Hφ". iFrame.
    - destruct Hfail; pose proof PC_not_cnull; try incrementPC_inv; simplify_map_eq; eauto; congruence.
  Qed.

  Lemma wp_GetTag_from_cnull E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst wd wn :
    decodeInstrW w.(lw) = GetTag dst cnull →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' → dst ≠ cnull →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ w ∗ ▷ cnull ↦ᵣ wn ∗ ▷ dst ↦ᵣ wd }}}
      Instr Executable @ E
    {{{ RET NextIV; PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗ pc_a ↦ₐ w ∗ dst ↦ᵣ WInt 0%Z ∗ cnull ↦ᵣ wn }}}.
  Proof.
    iIntros (Hdecode Hvpc Hinc Hne φ) "(>HPC & >Hmem & >Hs & >Hd) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hd Hs") as "[Hmap (%&%&%)]".
    iApply (wp_Get with "[$Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    { unfold is_Get. do 7 right. reflexivity. }
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    rewrite Hdecode in Hspec.
    destruct Hspec as [| * Hfail].
    - incrementPC_inv; simplify_map_eq; try exact lnull.
      rewrite insert_insert_ne // insert_insert_eq (insert_insert_ne _ PC dst) // insert_insert_eq.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto.
      iApply "Hφ". iFrame.
    - destruct Hfail; pose proof PC_not_cnull; try incrementPC_inv; simplify_map_eq; eauto; congruence.
  Qed.

  Lemma wp_GetTag_to_cnull E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src wn ws :
    decodeInstrW w.(lw) = GetTag cnull src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' → src ≠ cnull →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ w ∗ ▷ cnull ↦ᵣ wn ∗ ▷ src ↦ᵣ ws }}}
      Instr Executable @ E
    {{{ RET NextIV; PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗ pc_a ↦ₐ w ∗ cnull ↦ᵣ WInt 0%Z ∗ src ↦ᵣ ws }}}.
  Proof.
    iIntros (Hdecode Hvpc Hinc Hne φ) "(>HPC & >Hmem & >Hd & >Hs) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hd Hs") as "[Hmap (%&%&%)]".
    iApply (wp_Get with "[$Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    { unfold is_Get. do 7 right. reflexivity. }
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    rewrite Hdecode in Hspec.
    destruct Hspec as [| * Hfail].
    - incrementPC_inv; simplify_map_eq; eauto.
      rewrite insert_insert_ne // insert_insert_eq (insert_insert_ne _ PC cnull) // insert_insert_eq.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto.
      iApply "Hφ". iFrame.
    - destruct Hfail; pose proof PC_not_cnull; try incrementPC_inv; simplify_map_eq; eauto; try congruence.
      match goal with H : denote (GetTag _ _) ?v = None |- _ =>
        destruct_word v; discriminate end.
  Qed.

  Lemma wp_GetTag_PC_to_cnull E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w wn :
    decodeInstrW w.(lw) = GetTag cnull PC →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ w ∗ ▷ cnull ↦ᵣ wn }}}
      Instr Executable @ E
    {{{ RET NextIV; PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗ pc_a ↦ₐ w ∗ cnull ↦ᵣ WInt 0%Z }}}.
  Proof.
    iIntros (Hdecode Hvpc Hinc φ) "(>HPC & >Hmem & >Hn) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hn") as "[Hmap %]".
    iApply (wp_Get with "[$Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    { unfold is_Get. do 7 right. reflexivity. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    rewrite Hdecode in Hspec.
    destruct Hspec as [| * Hfail].
    - incrementPC_inv; simplify_map_eq; eauto.
      rewrite insert_insert_ne // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto.
      iApply "Hφ". iFrame.
    - destruct Hfail; pose proof PC_not_cnull; try incrementPC_inv; simplify_map_eq; eauto; congruence.
  Qed.

  Lemma wp_GetTag_cnull_toPC E pc_p pc_g pc_b pc_e pc_a pc_π w wn :
    decodeInstrW w.(lw) = GetTag PC cnull →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ w ∗ ▷ cnull ↦ᵣ wn }}}
      Instr Executable @ E
    {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hdecode Hvpc φ) "(>HPC & >Hmem & >Hn) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hn") as "[Hmap %]".
    iApply (wp_Get with "[$Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    { unfold is_Get. do 7 right. reflexivity. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    rewrite Hdecode in Hspec.
    destruct Hspec as [| * Hfail].
    - incrementPC_inv; simplify_map_eq; eauto.
    - by iApply "Hφ".
  Qed.

  Lemma wp_GetTag_toPC_failure E pc_p pc_g pc_b pc_e pc_a pc_π w src ws :
    decodeInstrW w.(lw) = GetTag PC src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    src ≠ cnull →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ w ∗ ▷ src ↦ᵣ ws }}}
      Instr Executable @ E
    {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hdecode Hvpc Hne φ) "(>HPC & >Hmem & >Hsrc) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hsrc") as "[Hmap %]".
    iApply (wp_Get with "[$Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    { unfold is_Get. do 7 right. reflexivity. }
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    rewrite Hdecode in Hspec.
    destruct Hspec as [|].
    - incrementPC_inv; simplify_map_eq; try exact lnull.
    - by iApply "Hφ".
  Qed.

  Lemma wp_GetTag_PC_failure E pc_p pc_g pc_b pc_e pc_a pc_π w  :
    decodeInstrW w.(lw) = GetTag PC PC →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ w }}}
      Instr Executable @ E
    {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hdecode Hvpc φ) "(>HPC & >Hmem) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iApply (wp_Get with "[$Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    { unfold is_Get. do 7 right. reflexivity. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    rewrite Hdecode in Hspec.
    destruct Hspec as [|].
    - incrementPC_inv; simplify_map_eq; try exact lnull.
    - by iApply "Hφ".
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
