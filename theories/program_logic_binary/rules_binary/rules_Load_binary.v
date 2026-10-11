From iris.proofmode Require Import proofmode.
From griotte Require Export rules_base_binary.
From griotte Require Import rules_Load.

(** * Spec rules for [Load] (spec copies of [rules_Load.v]) *)

Section spec_rules.
  Context `{MP: MachineParameters} `{!invGS Σ} `{specg : specG Σ}.
  Implicit Types σ : ExecConf.
  Implicit Types c : griotte_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  (** Physical spec-side outcomes, for the spec run. *)

  Definition spec_reg_allows_load_imm (regs : Reg) (r : RegName) (imm : Z) p g b e a ea :=
    regs !!ᵣ r = Some (WCap true p g b e a) ∧
    (a + imm)%a = Some ea ∧ readAllowed p = true ∧ withinBounds b e ea = true.

  Inductive spec_Load_failure_imm (regs: Reg) (r1 r2: RegName) (imm : Z) (mem : gmap Addr Word) :=
  | spec_Load_fail_const_imm w:
      regs !!ᵣ r2 = Some w ->
      is_cap w = false →
      spec_Load_failure_imm regs r1 r2 imm mem
  | spec_Load_fail_tag_imm p g b e a:
      regs !!ᵣ r2 = Some (WCap false p g b e a) →
      spec_Load_failure_imm regs r1 r2 imm mem
  | spec_Load_fail_addr_imm p g b e a:
      regs !!ᵣ r2 = Some (WCap true p g b e a) →
      (a + imm)%a = None →
      spec_Load_failure_imm regs r1 r2 imm mem
  | spec_Load_fail_bounds_imm p g b e a ea:
      regs !!ᵣ r2 = Some (WCap true p g b e a) ->
      (a + imm)%a = Some ea →
      (readAllowed p = false ∨ withinBounds b e ea = false) →
      spec_Load_failure_imm regs r1 r2 imm mem
  (* Notice how the None below also includes all cases where we read an inl value into the PC, because then incrementing it will fail *)
  | spec_Load_fail_invalid_PC_imm p g b e a ea loadv:
      regs !!ᵣ r2 = Some (WCap true p g b e a) ->
      (a + imm)%a = Some ea →
      mem !! ea = Some loadv →
      spec_incrementPC (<[ r1 := (load_word p loadv) ]ᵣ> regs) = None ->
      spec_Load_failure_imm regs r1 r2 imm mem
  .

  Inductive spec_Load_spec_imm
    (regs: Reg) (r1 r2: RegName) (imm : Z)
    (regs': Reg) (mem : gmap Addr Word) : griotte_lang.val → Prop
  :=
  | spec_Load_spec_success_imm p g b e a ea loadv :
    spec_reg_allows_load_imm regs r2 imm p g b e a ea →
    mem !! ea = Some loadv →
    spec_incrementPC
      (<[ r1 := (load_word p loadv) ]ᵣ> regs) = Some regs' ->
    spec_Load_spec_imm regs r1 r2 imm regs' mem NextIV

  | spec_Load_spec_failure_imm :
    spec_Load_failure_imm regs r1 r2 imm mem ->
    spec_Load_spec_imm regs r1 r2 imm regs' mem FailedV.

  Definition spec_allow_load_map_or_true_imm r (imm : Z) (regs : Reg) (mem : gmap Addr Word):=
    ∃ t p g b e a, spec_read_reg_inr regs r t p g b e a ∧
      match (a + imm)%a with
      | None => True
      | Some ea => if decide (spec_reg_allows_load_imm regs r imm p g b e a ea) then
        ∃ w, mem !! ea = Some w ∧ (is_heap_cap w = false ∨ get_tag w = false)
      else True
      end.

  Lemma spec_allow_load_implies_loadv_imm r2 imm mem regs p g b e a ea :
    spec_allow_load_map_or_true_imm r2 imm regs mem →
    spec_reg_allows_load_imm regs r2 imm p g b e a ea →
    ∃ loadv, mem !! ea = Some loadv.
  Proof.
    intros (t & p0 & g0 & b0 & e0 & a0 & Hsrc & Hmem) Hallow.
    destruct Hallow as (Hreg & Hadd & Hra & Hwb).
    assert (r2 ≠ cnull).
    { intros ->. simplify_map_eq. destruct (regs !! cnull); cbn in *; done. }
    unfold spec_read_reg_inr in Hsrc. simpl_map_regs by eauto.
    rewrite Hreg in Hsrc. inversion Hsrc; subst.
    unfold spec_reg_allows_load_imm in Hmem. rewrite Hadd in Hmem. case_decide as Hdec.
    { destruct Hmem as (w & Hw & _). eauto. }
    exfalso. apply Hdec. repeat split; auto. by simplify_map_eq.
  Qed.

  Lemma spec_allow_load_implies_not_heap_cap_imm r2 imm mem regs p g b e a ea loadv :
    spec_allow_load_map_or_true_imm r2 imm regs mem →
    spec_reg_allows_load_imm regs r2 imm p g b e a ea →
    mem !! ea = Some loadv →
    is_heap_cap loadv = false ∨ get_tag loadv = false.
  Proof.
    intros (t & p0 & g0 & b0 & e0 & a0 & Hsrc & Hmem) Hallow Hl.
    destruct Hallow as (Hreg & Hadd & Hra & Hwb).
    assert (r2 ≠ cnull).
    { intros ->. simplify_map_eq. destruct (regs !! cnull); cbn in *; done. }
    unfold spec_read_reg_inr in Hsrc. simpl_map_regs by eauto.
    rewrite Hreg in Hsrc. inversion Hsrc; subst.
    unfold spec_reg_allows_load_imm in Hmem. rewrite Hadd in Hmem. case_decide as Hdec.
    { destruct Hmem as (w & Hw & Hh). by simplify_eq. }
    exfalso. apply Hdec. repeat split; auto. by simplify_map_eq.
  Qed.

  Definition spec_reg_allows_load (regs : Reg) (r : RegName) p g b e a  :=
    regs !!ᵣ r = Some (WCap true p g b e a) ∧
    readAllowed p = true ∧ withinBounds b e a = true.

  Inductive spec_Load_failure (regs: Reg) (r1 r2: RegName) (mem : gmap Addr Word) :=
  | spec_Load_fail_const w:
      regs !!ᵣ r2 = Some w ->
      is_cap w = false →
      spec_Load_failure regs r1 r2 mem
  | spec_Load_fail_tag p g b e a:
      regs !!ᵣ r2 = Some (WCap false p g b e a) →
      spec_Load_failure regs r1 r2 mem
  | spec_Load_fail_bounds p g b e a:
      regs !!ᵣ r2 = Some (WCap true p g b e a) ->
      (readAllowed p = false ∨ withinBounds b e a = false) →
      spec_Load_failure regs r1 r2 mem
  (* Notice how the None below also includes all cases where we read an inl value into the PC, because then incrementing it will fail *)
  | spec_Load_fail_invalid_PC p g b e a loadv:
      regs !!ᵣ r2 = Some (WCap true p g b e a) ->
      mem !! a = Some loadv →
      spec_incrementPC (<[ r1 := (load_word p loadv) ]ᵣ> regs) = None ->
      spec_Load_failure regs r1 r2 mem
  .

  Inductive spec_Load_spec
    (regs: Reg) (r1 r2: RegName)
    (regs': Reg) (mem : gmap Addr Word) : griotte_lang.val → Prop
  :=
  | spec_Load_spec_success p g b e a loadv :
    spec_reg_allows_load regs r2 p g b e a →
    mem !! a = Some loadv →
    spec_incrementPC
      (<[ r1 := (load_word p loadv) ]ᵣ> regs) = Some regs' ->
    spec_Load_spec regs r1 r2 regs' mem NextIV

  | spec_Load_spec_failure :
    spec_Load_failure regs r1 r2 mem ->
    spec_Load_spec regs r1 r2 regs' mem FailedV.

  Definition spec_allow_load_map_or_true r (regs : Reg) (mem : gmap Addr Word):=
    ∃ t p g b e a, spec_read_reg_inr regs r t p g b e a ∧
      if decide (spec_reg_allows_load regs r p g b e a) then
        ∃ w, mem !! a = Some w ∧ (is_heap_cap w = false ∨ get_tag w = false)
      else True.

  Lemma spec_reg_allows_load_imm_zero regs r p g b e a ea :
    spec_reg_allows_load_imm regs r 0 p g b e a ea ↔
    ea = a ∧ spec_reg_allows_load regs r p g b e a.
  Proof. unfold spec_reg_allows_load_imm, spec_reg_allows_load. rewrite finz_add_0. naive_solver. Qed.

  Lemma spec_allow_load_map_or_true_imm_zero r regs mem :
    spec_allow_load_map_or_true_imm r 0 regs mem ↔ spec_allow_load_map_or_true r regs mem.
  Proof.
    unfold spec_allow_load_map_or_true_imm, spec_allow_load_map_or_true.
    unfold spec_reg_allows_load_imm, spec_reg_allows_load.
    setoid_rewrite finz_add_0.
    split; intros (t & p & g & b & e & a & Hr & Hmem);
      exists t,p,g,b,e,a; split; try done.
    all: cbn in Hmem |- *; repeat case_decide; pose proof (finz_add_0 MemNum a); naive_solver.
  Qed.

  Definition spec_Load_failure_imm_zero regs r1 r2 mem :
    spec_Load_failure_imm regs r1 r2 0 mem → spec_Load_failure regs r1 r2 mem.
  Proof.
    intros H; destruct H.
    all: try match goal with H : (_ + 0)%a = _ |- _ => rewrite finz_add_0 in H; simplify_eq end.
    - eapply spec_Load_fail_const; eauto.
    - eapply spec_Load_fail_tag; eauto.
    - eapply spec_Load_fail_bounds; eauto.
    - eapply spec_Load_fail_invalid_PC; eauto.
  Defined.

  Definition spec_Load_failure_zero_imm regs r1 r2 mem :
    spec_Load_failure regs r1 r2 mem → spec_Load_failure_imm regs r1 r2 0 mem.
  Proof.
    intros H; destruct H.
    - eapply spec_Load_fail_const_imm; eauto.
    - eapply spec_Load_fail_tag_imm; eauto.
    - eapply spec_Load_fail_bounds_imm; eauto. by rewrite finz_add_0.
    - eapply spec_Load_fail_invalid_PC_imm; eauto. by rewrite finz_add_0.
  Defined.

  Lemma spec_Load_spec_imm_zero regs r1 r2 regs' mem retv :
    spec_Load_spec_imm regs r1 r2 0 regs' mem retv ↔ spec_Load_spec regs r1 r2 regs' mem retv.
  Proof.
    split; intros H; destruct H.
    - apply spec_reg_allows_load_imm_zero in H as [-> H]. econstructor; eauto.
    - constructor. by apply spec_Load_failure_imm_zero.
    - econstructor; eauto. apply spec_reg_allows_load_imm_zero. done.
    - constructor. by apply spec_Load_failure_zero_imm.
  Qed.

  Lemma spec_allow_load_implies_loadv:
    ∀ (r2 : RegName) (mem0 : gmap Addr Word) (r : Reg) (p : Perm)
      (g : Locality) (b e a : Addr),
      spec_allow_load_map_or_true r2 r mem0
      → r !!ᵣ r2 = Some (WCap true p g b e a)
      → readAllowed p = true
      → withinBounds b e a = true
      → ∃ (loadv : Word),
          mem0 !! a = Some loadv.
  Proof.
    intros r2 mem0 r p g b e a HaLoad Hr2v Hra Hwb.
    unfold spec_allow_load_map_or_true, spec_read_reg_inr in HaLoad.
    destruct HaLoad as (t&?&?&?&?&?& Hrinr & Hmem).
    assert (r2 ≠ cnull).
    { intros -> ; simplify_map_eq.
      destruct (r !! cnull); cbn in * ; done.
    }
    simpl_map_regs by eauto.
    rewrite Hr2v in Hrinr. inversion Hrinr; subst.
    case_decide as Hrega.
    - destruct Hmem as (w & Hw & _). eauto.
    - assert (r !!ᵣ r2 = Some (WCap true x x0 x1 x2 x3)); eauto.
      { by simplify_map_eq. }
      contradiction Hrega. done.
  Qed.

  Lemma spec_mem_eq_implies_allow_load_map:
    ∀ (regs : Reg)(mem : gmap Addr Word)(r2 : RegName) (w : Word) p g b e a,
      mem = <[a:=w]> ∅
      → is_heap_cap w = false
      → regs !!ᵣ r2 = Some (WCap true p g b e a)
      → spec_allow_load_map_or_true r2 regs mem.
  Proof.
    intros regs mem r2 w p g b e a Hmem Hheap Hrr2.
    assert (r2 ≠ cnull).
    { intros -> ; simplify_map_eq.
      destruct (regs !! cnull); cbn in * ; done.
    }
    simplify_map_eq.
    exists true,p,g,b,e,a; split.
    - unfold spec_read_reg_inr. by rewrite Hrr2.
    - case_decide; last done.
      exists w. simplify_map_eq. split; [|left]; auto.
  Qed.

  Lemma spec_mem_neq_implies_allow_load_map:
    ∀ (regs : Reg)(mem : gmap Addr Word)(r2 : RegName) (pc_a : Addr)
      (w w' : Word) p g b e a,
      a ≠ pc_a
      → mem = <[pc_a:=w]> (<[a:=w']> ∅)
      → is_heap_cap w' = false
      → regs !!ᵣ r2 = Some (WCap true p g b e a)
      → spec_allow_load_map_or_true r2 regs mem.
  Proof.
    intros regs mem r2 pc_a w w' p g b e a H4 Hrr2 Hheap Hreg2.
    assert (r2 ≠ cnull).
    { intros -> ; simplify_map_eq.
      destruct (regs !! cnull); cbn in * ; done.
    }
    simplify_map_eq.
    exists true,p,g,b,e,a; split.
    - unfold spec_read_reg_inr. by rewrite Hreg2.
    - case_decide; last done.
      exists w'. simplify_map_eq. split; [|left]; auto.
  Qed.

  Lemma spec_mem_implies_allow_load_map:
    ∀ (regs : Reg)(mem : gmap Addr Word)(r2 : RegName) (pc_a : Addr)
      (w w' : Word) p g b e a,
      (if (a =? pc_a)%a
       then mem = <[pc_a:=w]> ∅
       else mem = <[pc_a:=w]> (<[a:=w']> ∅))
      → is_heap_cap (if (a =? pc_a)%a then w else w') = false
      → regs !!ᵣ r2 = Some (WCap true p g b e a)
      → spec_allow_load_map_or_true r2 regs mem.
  Proof.
    intros regs mem r2 pc_a w w' p g b e a H4 Hheap Hrr2.
    assert (r2 ≠ cnull).
    { intros -> ; simplify_map_eq.
      destruct (regs !! cnull); cbn in * ; done.
    }
    simplify_map_eq.
    destruct (a =? pc_a)%a eqn:Heq.
      + apply Z.eqb_eq, finz_to_z_eq in Heq. subst a. eapply spec_mem_eq_implies_allow_load_map; eauto.
        by simplify_map_eq.
      + apply Z.eqb_neq in Heq. eapply spec_mem_neq_implies_allow_load_map; eauto.
        2: by simplify_map_eq.
        congruence.
  Qed.

  Lemma spec_mem_eq_implies_allow_load_map_imm:
    ∀ (regs : Reg)(mem : gmap Addr Word)(r2 : RegName) (w : Word) p g b e a ea (imm : Z),
      mem = <[ea:=w]> ∅
      → is_heap_cap w = false
      → regs !!ᵣ r2 = Some (WCap true p g b e a)
      → (a + imm)%a = Some ea
      → spec_allow_load_map_or_true_imm r2 imm regs mem.
  Proof.
    intros regs mem r2 w p g b e a ea imm Hmem Hheap Hrr2 Hadd.
    assert (r2 ≠ cnull).
    { intros -> ; simplify_map_eq.
      destruct (regs !! cnull); cbn in * ; done.
    }
    simplify_map_eq.
    exists true,p,g,b,e,a; split.
    - unfold spec_read_reg_inr. by rewrite Hrr2.
    - unfold spec_reg_allows_load_imm. rewrite Hadd. case_decide; last done.
      exists w. simplify_map_eq. split; [|left]; auto.
  Qed.

  Lemma spec_mem_neq_implies_allow_load_map_imm:
    ∀ (regs : Reg)(mem : gmap Addr Word)(r2 : RegName) (pc_a : Addr)
      (w w' : Word) p g b e a ea (imm : Z),
      ea ≠ pc_a
      → mem = <[pc_a:=w]> (<[ea:=w']> ∅)
      → is_heap_cap w' = false
      → regs !!ᵣ r2 = Some (WCap true p g b e a)
      → (a + imm)%a = Some ea
      → spec_allow_load_map_or_true_imm r2 imm regs mem.
  Proof.
    intros regs mem r2 pc_a w w' p g b e a ea imm H4 Hrr2 Hheap Hreg2 Hadd.
    assert (r2 ≠ cnull).
    { intros -> ; simplify_map_eq.
      destruct (regs !! cnull); cbn in * ; done.
    }
    simplify_map_eq.
    exists true,p,g,b,e,a; split.
    - unfold spec_read_reg_inr. by rewrite Hreg2.
    - unfold spec_reg_allows_load_imm. rewrite Hadd. case_decide; last done.
      exists w'. simplify_map_eq. split; [|left]; auto.
  Qed.

  Lemma spec_mem_implies_allow_load_map_imm:
    ∀ (regs : Reg)(mem : gmap Addr Word)(r2 : RegName) (pc_a : Addr)
      (w w' : Word) p g b e a ea (imm : Z),
      (if (ea =? pc_a)%a
       then mem = <[pc_a:=w]> ∅
       else mem = <[pc_a:=w]> (<[ea:=w']> ∅))
      → is_heap_cap (if (ea =? pc_a)%a then w else w') = false
      → regs !!ᵣ r2 = Some (WCap true p g b e a)
      → (a + imm)%a = Some ea
      → spec_allow_load_map_or_true_imm r2 imm regs mem.
  Proof.
    intros regs mem r2 pc_a w w' p g b e a ea imm H4 Hheap Hrr2 Hadd.
    assert (r2 ≠ cnull).
    { intros -> ; simplify_map_eq.
      destruct (regs !! cnull); cbn in * ; done.
    }
    simplify_map_eq.
    destruct (ea =? pc_a)%a eqn:Heq.
      + apply Z.eqb_eq, finz_to_z_eq in Heq. subst ea. eapply spec_mem_eq_implies_allow_load_map_imm; eauto.
        by simplify_map_eq.
      + apply Z.eqb_neq in Heq. eapply spec_mem_neq_implies_allow_load_map_imm; eauto.
        2: by simplify_map_eq.
        congruence.
  Qed.

  Lemma spec_mem_implies_loadv:
    ∀ (pc_a : Addr) (w w' : Word) (a0 : Addr)
      (mem0 : gmap Addr Word) (loadv : Word),
      (if (a0 =? pc_a)%a
       then mem0 = <[pc_a:=w]> ∅
       else mem0 = <[pc_a:=w]> (<[a0:=w']> ∅))→
      mem0 !! a0 = Some loadv →
      loadv = (if (a0 =? pc_a)%a then w else w').
  Proof.
    intros pc_a w w' a0 mem0 loadv H4 H6.
    destruct (a0 =? pc_a)%a eqn:Heq; rewrite H4 in H6.
    + apply Z.eqb_eq, finz_to_z_eq in Heq; subst a0. by simplify_map_eq.
    + apply Z.eqb_neq in Heq. rewrite lookup_insert_ne in H6; last congruence. by simplify_map_eq.
  Qed.

  (* The heap premise of the derived rules, when the loaded word is either
     the instruction or the word at the loaded address. *)
  Local Hint Extern 1 (is_heap_cap (if ?c then _ else _) = false) =>
    match goal with
    | H : c = true |- _ => rewrite H; assumption
    | H : c = false |- _ => rewrite H; assumption
    | _ => destruct c; assumption
    end : core.

  (** An instruction word is not a heap capability. *)
  Lemma spec_decode_load_not_heap_cap (w : Word) dst src imm :
    decodeInstrW w = Load dst src imm → is_heap_cap w = false.
  Proof. destruct w; cbn; try discriminate; done. Qed.

  (** The outcome of a load of the implementation run, on a lifted register
      file and memory, is a physical outcome, when the loaded word is kept by
      the Load filter and the loaded address is neither the shadow table nor
      the revoker. *)
  Lemma Load_spec_lift regs r1 r2 imm lregs' (mem : Mem) shadow v :
    (∀ p g b e a ea, regs !!ᵣ r2 = Some (WCap true p g b e a) → (a + imm)%a = Some ea →
       readAllowed p = true → withinBounds b e ea = true →
       is_shadow_address ea = false ∧ is_revoker_address ea = false ∧
       ∀ w, mem !! ea = Some w → is_heap_cap w = false ∨ get_tag w = false) →
    Load_spec (lift_regs regs) r1 r2 imm lregs' (lword_of_word <$> mem) shadow LoadPlain v →
    ∃ regs', (v = NextIV → lregs' = lift_regs regs') ∧ spec_Load_spec_imm regs r1 r2 imm regs' mem v.
  Proof.
    intros Hok Hspec.
    assert (Hexact : ∀ p (w : Word) loadv', load_post LoadPlain p (lword_of_word w) loadv' →
              (is_heap_cap w = false ∨ get_tag w = false) → loadv' = lword_of_word (load_word p w)).
    { intros p w loadv' (Hheap & _ & _ & _) Hw.
      destruct Hheap as [-> | [Hh ->]]; first done.
      destruct Hw as [Hw|Hw].
      - cbn in Hh. rewrite is_heap_cap_load_word in Hh. congruence.
      - rewrite /lclear_tag /lload_word /lift_word /=. rewrite clear_tag_untagged //.
        by rewrite get_tag_load_word. }
    destruct Hspec as [p g b e ea loadv loadv' Hallow Hsh Hl Hpost Hinc
                      | p g b e ea heap_a revoked Hallow Hsh Hsh2 Hlk Hinc
                      | p g b e ea Hallow Hrev Hl Hinc | Hfail].
    - destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a (Hr & Hadd & Hra & Hwb)].
      rewrite lift_regs_lw_llookup in Hr.
      rewrite lookup_fmap in Hl. apply fmap_Some in Hl as (w & Hl & ->).
      destruct (Hok _ _ _ _ _ _ Hr Hadd Hra Hwb) as (_ & _ & Hw).
      rewrite (Hexact _ _ _ Hpost (Hw _ Hl)) in Hinc.
      lift_regs_simpl.
      eexists; split; [intros _; reflexivity|].
      eapply spec_Load_spec_success_imm; eauto. by repeat split.
    - exfalso. destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a (Hr & Hadd & Hra & Hwb)].
      rewrite lift_regs_lw_llookup in Hr.
      destruct (Hok _ _ _ _ _ _ Hr Hadd Hra Hwb) as (Hns & _ & _). congruence.
    - exfalso. destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a (Hr & Hadd & Hra & Hwb)].
      rewrite lift_regs_lw_llookup in Hr.
      destruct (Hok _ _ _ _ _ _ Hr Hadd Hra Hwb) as (_ & Hnr & _). congruence.
    - exists regs; split; [intros ?; discriminate|].
      destruct Hfail as [w Hr Hc | p g b e a Hr | p g b e a Hr Hadd | p g b e a ea Hr Hadd Hb
                        | p g b e a ea loadv loadv' Hr Hadd Hsh Hl Hpost Hinc
                        | p g b e a ea heap_a revoked Hr Hadd Hsh Hsh2 Hlk Hinc
                        | p g b e a ea Hr Hadd Hrev Hl Hinc].
      all: rewrite ?lift_regs_lw_llookup in Hr.
      + rewrite lift_regs_llookup in Hr. apply fmap_Some in Hr as (w' & Hr & ->).
        apply spec_Load_spec_failure_imm. by eapply spec_Load_fail_const_imm.
      + apply spec_Load_spec_failure_imm. by eapply spec_Load_fail_tag_imm.
      + apply spec_Load_spec_failure_imm. by eapply spec_Load_fail_addr_imm.
      + apply spec_Load_spec_failure_imm. by eapply spec_Load_fail_bounds_imm.
      + rewrite lookup_fmap in Hl. apply fmap_Some in Hl as (w & Hl & ->).
        destruct (readAllowed p && withinBounds b e ea) eqn:HRA.
        2: { apply andb_false_iff in HRA. apply spec_Load_spec_failure_imm.
             by eapply spec_Load_fail_bounds_imm. }
        apply andb_true_iff in HRA as [Hra Hwb].
        destruct (Hok _ _ _ _ _ _ Hr Hadd Hra Hwb) as (_ & _ & Hw).
        rewrite (Hexact _ _ _ Hpost (Hw _ Hl)) in Hinc.
        lift_regs_simpl.
        apply spec_Load_spec_failure_imm. by eapply spec_Load_fail_invalid_PC_imm.
      + destruct (readAllowed p && withinBounds b e ea) eqn:HRA.
        2: { apply andb_false_iff in HRA. apply spec_Load_spec_failure_imm.
             by eapply spec_Load_fail_bounds_imm. }
        apply andb_true_iff in HRA as [Hra Hwb].
        destruct (Hok _ _ _ _ _ _ Hr Hadd Hra Hwb) as (Hns & _ & _). congruence.
      + destruct (readAllowed p && withinBounds b e ea) eqn:HRA.
        2: { apply andb_false_iff in HRA. apply spec_Load_spec_failure_imm.
             by eapply spec_Load_fail_bounds_imm. }
        apply andb_true_iff in HRA as [Hra Hwb].
        destruct (Hok _ _ _ _ _ _ Hr Hadd Hra Hwb) as (_ & Hnr & _). congruence.
  Qed.

  Lemma Load_spec_determ regs r1 r2 mem regs1 regs2 v1 v2 :
    spec_Load_spec regs r1 r2 regs1 mem v1 →
    spec_Load_spec regs r1 r2 regs2 mem v2 →
    v1 = v2 ∧ (v1 = NextIV → regs1 = regs2).
  Proof. solve_spec_determ_gen spec_Load_failure ltac:(unfold spec_reg_allows_load in * ). Qed.

  Lemma Load_spec_imm_determ regs r1 r2 imm mem regs1 regs2 v1 v2 :
    spec_Load_spec_imm regs r1 r2 imm regs1 mem v1 →
    spec_Load_spec_imm regs r1 r2 imm regs2 mem v2 →
    v1 = v2 ∧ (v1 = NextIV → regs1 = regs2).
  Proof. solve_spec_determ_gen spec_Load_failure_imm ltac:(unfold spec_reg_allows_load_imm in * ). Qed.

  Lemma step_load_general_imm Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 r2 (imm : Z) w mem (dfracs : gmap Addr dfrac) regs :
    ↑specN ⊆ Ep →
   decodeInstrW w = Load r1 r2 imm →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Load r1 r2 imm) ⊆ dom regs →
   mem !! pc_a = Some w →
   spec_allow_load_map_or_true_imm r2 imm regs mem →
   dom mem = dom dfracs →

   spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↣ₐ{dw.1} dw.2) ∗
    ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗
    ∃ retv regs',
      ⤇ Seq (of_val retv) ∗
      ⌜ spec_Load_spec_imm regs r1 r2 imm regs' mem retv⌝ ∗
      ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↣ₐ{dw.1} dw.2) ∗
      [∗ map] k↦y ∈ regs', k ↣ᵣ y.
  Proof.
    iIntros (HE Hinstr Hvpc HPC Dregs Hmem_pc HaLoad Hdomeq) "(#Hctx & Hj & Hmem & Hmap)".
    iApply (spec_step_exec_1 with "Hctx Hj"); first done.
    iIntros (Φ) "Hφ". iIntros ([[[r sr] m] st] c σ2 Hstep) "[[Hr Hsr] Hm] /=".
    iDestruct (spec_regs_valid_inclSepM with "Hr Hmap") as %Hregs.

    (* Derive necessary register values in r *)
    pose proof (lookup_weaken _ _ _ _ HPC Hregs).
    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
    odestruct (Hri r2) as [r2v [Hr'2 Hr2]]; first by set_solver+.
    odestruct (Hri r1) as [r1v [Hr'1 _]]; first by set_solver+.
    clear Hri.
    (* Derive the PC in memory *)
    assert (is_Some (dfracs !! pc_a)) as [dq Hdq].
    { apply elem_of_dom. rewrite -Hdomeq. apply elem_of_dom;eauto. }
    assert (prod_merge dfracs mem !! pc_a = Some (dq,w)) as Hmem_dpc.
    { rewrite lookup_merge Hmem_pc Hdq //. }
    iDestruct (spec_mem_valid_inSepM_general (prod_merge dfracs mem) m with "Hm Hmem") as %Hma; eauto.

    eapply step_exec_inv in Hstep; eauto.

    rewrite /exec /= Hr2 /= in Hstep.

     (* Now we start splitting on the different cases in the Load spec, and prove them one at a time *)
     destruct (is_cap r2v) eqn:Hr2v.
     2:{ (* Failure: r2 is not a capability *)
       assert (c = Failed ∧ σ2 = (r, sr, m, st)) as (-> & ->).
       {
         unfold is_cap in Hr2v.
         destruct_word r2v; by simplify_pair_eq.
       }
        iFailWP "Hφ" spec_Load_fail_const_imm.
     }
     destruct r2v as [ | [t p g b e a | ] | | ]; try inversion Hr2v. clear Hr2v.
     destruct t.
     2: {
       inversion Hstep; subst c σ2.
       iFailWP "Hφ" spec_Load_fail_tag_imm.
     }

    destruct (a + imm)%a as [ea|] eqn:Hadd; cbn in Hstep.
    2: { inversion Hstep; subst c σ2. iFailWP "Hφ" spec_Load_fail_addr_imm. }
    destruct (readAllowed p && withinBounds b e ea) eqn:HRA.
    2 : { (* Failure: r2 is either not within bounds or doesnt allow reading *)
      symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
      apply andb_false_iff in HRA.
      iFailWP "Hφ" spec_Load_fail_bounds_imm.
    }
    apply andb_true_iff in HRA; destruct HRA as (Hra & Hwb).

    (* Prove that a is in the memory map now, otherwise we cannot continue *)
    assert (spec_reg_allows_load_imm regs r2 imm p g b e a ea) as Hallow.
    { repeat split; auto. }
    destruct (spec_allow_load_implies_loadv_imm r2 imm mem regs p g b e a ea HaLoad Hallow) as (loadv & Hmema).
    pose proof (spec_allow_load_implies_not_heap_cap_imm r2 imm mem regs p g b e a ea loadv HaLoad Hallow Hmema) as Hnh.

    assert (is_Some (dfracs !! ea)) as [dq' Hdq'].
    { apply elem_of_dom. rewrite -Hdomeq. apply elem_of_dom;eauto. }
    assert (prod_merge dfracs mem !! ea = Some (dq',loadv)) as Hmemadq.
    { rewrite lookup_merge Hmema Hdq' //. }
    iDestruct (spec_mem_valid_inSepM_general (prod_merge dfracs mem) m ea loadv with "Hm Hmem" ) as %Hma' ; eauto.

    iDestruct (spec_mem_avoids_mmio with "Hm") as %Hmmio.
    rewrite (mem_avoids_mmio_not_shadow _ _ _ Hmmio Hma')
      (mem_avoids_mmio_not_revoker _ _ _ Hmmio Hma') /= Hma' /= in Hstep.
    (* The Load filter keeps the loaded word: it is not a heap capability, or
       it is untagged. *)
    iDestruct (spec_mem_shadow_ok with "Hm") as %Hshadow.
    assert ((match heap_cap_base loadv with
             | Some base =>
                 status ← st !! base;
                 updatePC (update_reg (r, sr, m, st) r1
                   (match status with
                    | ShadowLive => load_word p loadv
                    | ShadowQuarantined => clear_tag (load_word p loadv)
                    end))
             | None => updatePC (update_reg (r, sr, m, st) r1 (load_word p loadv))
             end) = updatePC (update_reg (r, sr, m, st) r1 (load_word p loadv))) as Hfilter.
    { destruct (heap_cap_base loadv) as [base|] eqn:Hbase; last done.
      destruct Hnh as [Hnh|Huntag]; first by rewrite /is_heap_cap Hbase in Hnh.
      assert (is_heap_address base = true) as Hheap.
      { rewrite /heap_cap_base in Hbase.
        destruct (memory_cap_base loadv); last done.
        by destruct (is_heap_address _) eqn:?; simplify_eq. }
      destruct (Hshadow base Hheap) as [[] Hst]; rewrite Hst /=; first done.
      by rewrite clear_tag_untagged // get_tag_load_word. }
    rewrite Hfilter in Hstep.
    destruct (spec_incrementPC (<[ r1 := (load_word p loadv) ]ᵣ> regs)) as  [ regs' |] eqn:Hregs'.
    2: { (* Failure: the PC could not be incremented correctly *)
      assert (spec_incrementPC (<[ r1 := (load_word p loadv) ]ᵣ> r) = None).
      { eapply spec_incrementPC_overflow_mono; first eapply Hregs'.
          + simplify_map_eq; by rewrite lookup_insert_is_Some'; eauto.
          + by apply insert_mono; eauto. }

      rewrite spec_incrementPC_fail_updatePC /= in Hstep; auto.
      symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
       (* Update the heap resource, using the resource for r2 *)
      iFailWP "Hφ" spec_Load_fail_invalid_PC_imm.
    }

    (* Success *)
    rewrite /update_reg /= in Hstep.
    eapply (spec_incrementPC_success_updatePC _ sr m st) in Hregs'
      as (t1 & p1 & g1 & b1 & e1 & a1 & a_pc1 & HPC'' & Ha_pc' & HuPC & ->).
    eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono.
    rewrite HuPC in Hstep; clear HuPC; inversion Hstep; clear Hstep; subst c σ2. cbn.
    iFrame.
    iMod ((spec_regs_update_inSepM _ _ r1) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    { apply is_Some_lookup_reg; done. }
    iMod ((spec_regs_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iModIntro. iApply "Hφ". iFrame.
    iPureIntro. eapply spec_Load_spec_success_imm; auto.
    * exact Hallow.
    * exact Hmema.
    * rewrite /spec_incrementPC /spec_incrementPC_gen. by rewrite HPC'' Ha_pc'.
      Unshelve. all: auto.
  Qed.

  Lemma step_load_imm Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 r2 (imm : Z) w mem regs dq :
    ↑specN ⊆ Ep →
   decodeInstrW w = Load r1 r2 imm →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Load r1 r2 imm) ⊆ dom regs →
   mem !! pc_a = Some w →
   spec_allow_load_map_or_true_imm r2 imm regs mem →
   spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    ([∗ map] a↦w ∈ mem, a ↣ₐ{dq} w) ∗
    ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗
    ∃ retv regs',
      ⤇ Seq (of_val retv) ∗
      ⌜ spec_Load_spec_imm regs r1 r2 imm regs' mem retv⌝ ∗
      ([∗ map] a↦w ∈ mem, a ↣ₐ{dq} w) ∗
      [∗ map] k↦y ∈ regs', k ↣ᵣ y.
  Proof.
    intros. iIntros "(#Hctx & Hj & Hmem & Hreg)".
    iDestruct (spec_mem_remove_dq with "Hmem") as "Hmem".
    iMod (step_load_general_imm with "[$Hctx $Hj $Hmem $Hreg]")
      as (retv regs') "(Hj & Hspec & Hmem & Hmap)"; eauto.
    { rewrite create_gmap_default_dom list_to_set_elements_L. auto. }
    iDestruct (spec_mem_remove_dq with "Hmem") as "Hmem".
    iModIntro. iExists retv, regs'. iFrame.
  Qed.

  Lemma step_load_general Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 r2 w mem (dfracs : gmap Addr dfrac) regs :
    ↑specN ⊆ Ep →
   decodeInstrW w = Load r1 r2 0 →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Load r1 r2 0) ⊆ dom regs →
   mem !! pc_a = Some w →
   spec_allow_load_map_or_true r2 regs mem →
   dom mem = dom dfracs →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↣ₐ{dw.1} dw.2) ∗
    ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗
    ∃ retv regs',
      ⤇ Seq (of_val retv) ∗
      ⌜ spec_Load_spec regs r1 r2 regs' mem retv⌝ ∗
      ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↣ₐ{dw.1} dw.2) ∗
      [∗ map] k↦y ∈ regs', k ↣ᵣ y.
  Proof.
    iIntros (HE Hinstr Hvpc HPC Dregs Hmem HaLoad Hdom) "(#Hctx & Hj & Hres)".
    iMod (step_load_general_imm with "[$Hctx $Hj $Hres]")
      as (retv regs') "(Hj & %Hspec & Hmem & Hregs)"; eauto.
    { by apply spec_allow_load_map_or_true_imm_zero. }
    iModIntro. iExists retv, regs'. iFrame. iPureIntro. by apply spec_Load_spec_imm_zero.
  Qed.

  Lemma step_load Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 r2 w mem regs dq :
    ↑specN ⊆ Ep →
   decodeInstrW w = Load r1 r2 0 →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Load r1 r2 0) ⊆ dom regs →
   mem !! pc_a = Some w →
   spec_allow_load_map_or_true r2 regs mem →
   spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    ([∗ map] a↦w ∈ mem, a ↣ₐ{dq} w) ∗
    ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗
    ∃ retv regs',
      ⤇ Seq (of_val retv) ∗
      ⌜ spec_Load_spec regs r1 r2 regs' mem retv⌝ ∗
      ([∗ map] a↦w ∈ mem, a ↣ₐ{dq} w) ∗
      [∗ map] k↦y ∈ regs', k ↣ᵣ y.
  Proof.
    intros. iIntros "(#Hctx & Hj & Hmem & Hreg)".
    iDestruct (spec_mem_remove_dq with "Hmem") as "Hmem".
    iMod (step_load_general with "[$Hctx $Hj $Hmem $Hreg]")
      as (retv regs') "(Hj & Hspec & Hmem & Hmap)"; eauto.
    { rewrite create_gmap_default_dom list_to_set_elements_L. auto. }
    iDestruct (spec_mem_remove_dq with "Hmem") as "Hmem".
    iModIntro. iExists retv, regs'. iFrame.
  Qed.

  Lemma step_load_success E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a pc_a' dq dq' :
    ↑specN ⊆ E →
    is_heap_cap (if (a =? pc_a)%a then w else w') = false →
    decodeInstrW w = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    (if (eqb_addr a pc_a) then emp else a ↣ₐ{dq'} w')
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ (if (eqb_addr a pc_a) then (load_word p w) else (load_word p w')) ∗
    pc_a ↣ₐ{dq} w ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    (if (eqb_addr a pc_a) then emp else a ↣ₐ{dq'} w').
  Proof.
    iIntros (HE Hheap Hinstr Hvpc [Hra Hwb] Hpca' Hcnull Hcnull') "(#Hctx & Hj & HPC & Hi & Hr1 & Hr2 & Hr2a)".
    iDestruct (spec_map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iDestruct (memMap_resource_2gen_dq _ _ _ _ _ _ (λ a dq w, a ↣ₐ{dq} w)%I with "Hi Hr2a") as (mem dfracs) "[Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hdfracs].

    iMod (step_load_general with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct (a =? pc_a)%a; by simplify_map_eq. }
    { eapply spec_mem_implies_allow_load_map; eauto. by simplify_map_eq. }
    { destruct (a =? pc_a)%a; simplify_eq. all: rewrite !dom_insert_L;set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       (* FIXME: fragile *)
       destruct H2 as [Hrr2 _]. simplify_map_eq.
       iDestruct (spec_memMap_resource_2gen_d_dq with "[Hmem]") as "[Hpc_a Ha]".
       { iExists mem,dfracs; iSplitL; auto. }
       spec_incrementPC_inv.
       pose proof (spec_mem_implies_loadv _ _ _ _ _ _ Hmem H3) as Hloadv; eauto.
       simplify_map_eq.
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
       iDestruct (spec_regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto.
       iModIntro. iFrame.
       by destruct (a0 =? x4)%Z.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; try spec_incrementPC_inv; simplify_map_eq; eauto; [destruct o|].
       all: congruence.
     }
  Qed.

  Lemma step_load_success_notinstr E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a pc_a' dq dq' :
    ↑specN ⊆ E →
    is_heap_cap w' = false →
    decodeInstrW w = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ{dq'} w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ load_word p w' ∗
    pc_a ↣ₐ{dq} w ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ{dq'} w'.
  Proof.
    iIntros (HE Hheap Hinstr Hvpc Hrawb Hpca' Hcnull Hcnull') "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Hr2 & Ha)".
    destruct (a =? pc_a)%Z eqn:Ha.
    - rewrite (_: a = pc_a); cycle 1.
      { apply Z.eqb_eq in Ha. solve_addr. }
      iDestruct (spec_mem_pointsto_agree with "Hpc_a Ha") as %->.
      iMod (step_load_success _ _ _ _ _ _ _ _ _ w' _ _ _ _ _ _ _ _ dq'
             with "[$Hctx $Hj $HPC $Hpc_a $Hr1 $Hr2]") as "(Hj & HPC & Hr1 & Hpc_a & Hr2 & _)"; eauto.
      { apply Z.eqb_eq,finz_to_z_eq in Ha. subst a. auto. }
      { apply Z.eqb_eq,finz_to_z_eq in Ha. subst a. by rewrite /eqb_addr Z.eqb_refl. }
      rewrite /eqb_addr Z.eqb_refl.
      iModIntro. iFrame.
    - iMod (step_load_success _ _ _ _ _ _ _ _ _ w' with "[$Hctx $Hj $HPC $Hpc_a $Hr1 $Hr2 Ha]")
        as "(Hj & HPC & Hr1 & Hpc_a & Hr2 & Ha)"; eauto.
      { rewrite /eqb_addr Ha. iFrame. }
      rewrite /eqb_addr Ha.
      iModIntro. iFrame.
  Qed.

  Lemma step_load_success_frominstr E r1 r2 pc_p pc_g pc_b pc_e pc_a w w'' p g b e pc_a' dq :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e pc_a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ WCap true p g b e pc_a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ load_word p w ∗
    pc_a ↣ₐ{dq} w ∗
    r2 ↣ᵣ WCap true p g b e pc_a.
  Proof.
    iIntros (HE Hinstr Hvpc Hrawb Hpca' Hcnull Hcnull') "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Hr2)".
    pose proof (spec_decode_load_not_heap_cap _ _ _ _ Hinstr) as Hheap.
    iMod (step_load_success _ _ _ _ _ _ _ _ _ w _ _ _ _ _ _ _ _ DfracDiscarded
           with "[$Hctx $Hj $HPC $Hpc_a $Hr1 $Hr2]") as "(Hj & HPC & Hr1 & Hpc_a & Hr2 & _)"; eauto.
    { by rewrite /eqb_addr Z.eqb_refl. }
    rewrite /eqb_addr Z.eqb_refl.
    iModIntro. iFrame.
  Qed.

  Lemma step_load_success_same E r1 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a pc_a' dq dq' :
    ↑specN ⊆ E →
    is_heap_cap (if (a =? pc_a)%a then w else w') = false →
    decodeInstrW w = Load r1 r1 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ WCap true p g b e a ∗
    (if (a =? pc_a)%a then emp else a ↣ₐ{dq'} w')
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ (if (a =? pc_a)%a then load_word p w else load_word p w') ∗
    pc_a ↣ₐ{dq} w ∗
    (if (a =? pc_a)%a then emp else a ↣ₐ{dq'} w').
  Proof.
    iIntros (HE Hheap Hinstr Hvpc Hra Hwb Hpca' Hcnull) "(#Hctx & Hj & HPC & Hi & Hr1 & Hr1a)".
    iDestruct (spec_map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iDestruct (memMap_resource_2gen_dq _ _ _ _ _ _ (λ a dq w, a ↣ₐ{dq} w)%I with "Hi Hr1a") as
        (mem dfracs) "[Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hfracs].

    iMod (step_load_general with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct (a =? pc_a)%a; by simplify_map_eq. }
    { eapply spec_mem_implies_allow_load_map; eauto. by simplify_map_eq. }
    { destruct (a =? pc_a)%a; by set_solver. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iModIntro.
       destruct H0 as [Hrr2 _]. simplify_map_eq.
       iDestruct (spec_memMap_resource_2gen_d_dq with "[Hmem]") as "[Hpc_a Ha]".
       {iExists mem,dfracs; iSplitL; auto. }
       spec_incrementPC_inv.
       pose proof (spec_mem_implies_loadv _ _ _ _ _ _ Hmem H1) as Hloadv; eauto.
       simplify_map_eq.
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto. iFrame.
       by destruct (a0 =? x4)%Z.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; try spec_incrementPC_inv; simplify_map_eq; eauto; [ destruct o |]; congruence. }
    Qed.

  Lemma step_load_success_same_notinstr E r1 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a pc_a' dq dq' :
    ↑specN ⊆ E →
    is_heap_cap w' = false →
    decodeInstrW w = Load r1 r1 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ{dq'} w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ load_word p w' ∗
    pc_a ↣ₐ{dq} w ∗
    a ↣ₐ{dq'} w'.
  Proof.
    iIntros (HE Hheap Hinstr Hvpc Hra Hwb Hpca' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Ha)".
    destruct (a =? pc_a)%a eqn:Ha.
    - assert (a = pc_a) as -> by (apply Z.eqb_eq in Ha; solve_addr).
      iDestruct (spec_mem_pointsto_agree with "Hpc_a Ha") as %->.
      iMod (step_load_success_same _ _ _ _ _ _ _ _ w' w'' _ _ _ _ _ _ _ dq'
             with "[$Hctx $Hj $HPC $Hpc_a $Hr1]") as "(Hj & HPC & Hr1 & Hpc_a & _)"; eauto.
      { by rewrite Ha. }
      rewrite Ha.
      iModIntro. iFrame.
    - iMod (step_load_success_same _ _ _ _ _ _ _ _ w' with "[$Hctx $Hj $HPC $Hpc_a $Hr1 Ha]")
        as "(Hj & HPC & Hr1 & Hpc_a & Ha)"; eauto.
      { rewrite Ha. iFrame. }
      rewrite Ha.
      iModIntro. iFrame.
  Qed.

  Lemma step_load_success_same_frominstr E r1 pc_p pc_g pc_b pc_e pc_a w p g b e pc_a' dq :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r1 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e pc_a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ WCap true p g b e pc_a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ load_word p w ∗
    pc_a ↣ₐ{dq} w.
  Proof.
    iIntros (HE Hinstr Hvpc Hra Hwb Hpca' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hr1)".
    pose proof (spec_decode_load_not_heap_cap _ _ _ _ Hinstr) as Hheap.
    iMod (step_load_success_same _ _ _ _ _ _ _ _ w w _ _ _ _ _ _ _ DfracDiscarded
           with "[$Hctx $Hj $HPC $Hpc_a $Hr1]") as "(Hj & HPC & Hr1 & Hpc_a & _)"; eauto.
    { by rewrite Z.eqb_refl. }
    rewrite Z.eqb_refl.
    iModIntro. iFrame.
  Qed.

  Lemma step_load_success_PC E r2 pc_p pc_g pc_b pc_e pc_a w
        p g b e a (t : bool) p' g' b' e' a' a'' :
    ↑specN ⊆ E →
    is_heap_cap (WCap t p' g' b' e' a') = false →
    decodeInstrW w = Load PC r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (a' + 1)%a = Some a'' →
    r2 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ WCap t p' g' b' e' a'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ load_word p (WCap t p' g' b' e' a'') ∗
    pc_a ↣ₐ w ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ WCap t p' g' b' e' a'.
  Proof.
    iIntros (HE Hheap Hinstr Hvpc [Hra Hwb] Hpca' Hcnull) "(#Hctx & Hj & HPC & Hi & Hr2 & Hr2a)".
    iDestruct (spec_map_of_regs_2 with "HPC Hr2") as "[Hmap %]".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hr2a") as "[Hmem %]"; auto.
    iMod (step_load with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply spec_mem_neq_implies_allow_load_map with (a := a) (pc_a := pc_a); eauto.
      by simplify_map_eq. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iModIntro.
       destruct H1 as [Hrr2 _]. simplify_map_eq.
       iDestruct (spec_memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       spec_incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_eq insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hr2]"; eauto.
       iFrame.
       by destruct p0; destruct dro,dl; rewrite /load_word in H1 |- *; cbn in *; simplify_eq.
     }
     { (* Failure (contradiction) *)
       destruct Hfail.
       + simplify_map_eq; eauto.
       + simplify_map_eq; eauto.
       + simplify_map_eq; eauto.
         destruct o ; congruence.
       + simplify_map_eq; eauto.
         rewrite /load_word in e3 |- *.
         destruct (isDRO p0) eqn:HDRO, (isDL p0) eqn:HDL; cbn.
         all: try spec_incrementPC_inv; simplify_map_eq; eauto.
         all: try congruence.
     }
  Qed.

  Lemma step_load_success_fromPC E r1 pc_p pc_g pc_b pc_e pc_a pc_a' w w'' dq :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 PC 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ w''
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ load_word pc_p w.
  Proof.
    iIntros (HE Hinstr Hvpc Hpca' Hcnull) "(#Hctx & Hj & HPC & Hi & Hr1)".
    pose proof (spec_decode_load_not_heap_cap _ _ _ _ Hinstr) as Hheap.
    iDestruct (spec_map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    rewrite spec_memMap_resource_1_dq.
    iMod (step_load with "[$Hctx $Hj $Hmap $Hi]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply spec_mem_eq_implies_allow_load_map with (a := pc_a); eauto.
      by simplify_map_eq. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iModIntro.
       destruct H0 as [Hrr2 _]. simplify_map_eq.
       rewrite -spec_memMap_resource_1_dq.
       spec_incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_ne //= insert_insert_eq insert_insert_ne //= insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try spec_incrementPC_inv; simplify_map_eq; eauto.
       + apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [Hra Hwb].
         destruct o; apply Is_true_false in H0; try congruence. done.
       + congruence.
     }
  Qed.

  Lemma step_load_success_alt E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a pc_a' :
    ↑specN ⊆ E →
    is_heap_cap w' = false →
    decodeInstrW w = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ load_word p w' ∗
    pc_a ↣ₐ w ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ w'.
  Proof.
    iIntros (HE Hheap Hinstr Hvpc [Hra Hwb] Hpca' Hcnull Hcnull') "(#Hctx & Hj & HPC & Hi & Hr1 & Hr2 & Hr2a)".
    iAssert (⌜(a =? pc_a)%a = false⌝)%I as %Hfalse.
    { rewrite Z.eqb_neq. iDestruct (spec_address_neq with "Hr2a Hi") as %Hneq. iIntros (->%finz_to_z_eq). done. }
    iMod (step_load_success _ _ _ _ _ _ _ _ _ w' with "[$Hctx $Hj $HPC $Hi $Hr1 $Hr2 Hr2a]")
      as "(Hj & HPC & Hr1 & Hi & Hr2 & Hr2a)"; eauto.
    { rewrite /eqb_addr Hfalse. iFrame. }
    rewrite /eqb_addr Hfalse.
    iModIntro. iFrame.
  Qed.

  Lemma step_load_success_same_alt E r1 pc_p pc_g pc_b pc_e pc_a w w' p g b e a pc_a' :
    ↑specN ⊆ E →
    is_heap_cap w' = false →
    decodeInstrW w = Load r1 r1 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ load_word p w' ∗
    pc_a ↣ₐ w ∗
    a ↣ₐ w'.
  Proof.
    iIntros (HE Hheap Hinstr Hvpc [Hra Hwb] Hpca' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Ha)".
    iAssert (⌜(a =? pc_a)%a = false⌝)%I as %Hfalse.
    { rewrite Z.eqb_neq. iDestruct (spec_address_neq with "Ha Hpc_a") as %Hneq. iIntros (->%finz_to_z_eq). done. }
    iMod (step_load_success_same _ _ _ _ _ _ _ _ w' with "[$Hctx $Hj $HPC $Hpc_a $Hr1 Ha]") as "H"; eauto.
    { rewrite /eqb_addr Hfalse. iFrame. }
    rewrite /eqb_addr Hfalse.
    iModIntro. iExact "H".
  Qed.

  Lemma step_load_fail_not_cap E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' wsrc :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    is_cap wsrc = false ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ wsrc
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
  Proof.
     iIntros (HE Hdecode Hvpc Hbounds) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
     iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
     rewrite spec_memMap_resource_1_dq.
     iMod (step_load with "[$Hctx $Hj $Hmap $Hi]") as "H"; eauto; simplify_map_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     { rewrite /spec_allow_load_map_or_true.
       destruct_word wsrc; cbn in *; try done.
       all: eexists true, RO, Global, za, za, za. (* dummy values *)
       all: split; rewrite /spec_read_reg_inr; first by simplify_map_eq.
       all: rewrite /spec_reg_allows_load; simplify_map_eq.
       all: rewrite decide_False; first done.
       all: intros (?&_&_); try done;  simplify_map_eq.
       all: destruct (decide (r2 = cnull)); done.
     }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".
     destruct Hspec as [| Hfail].
     {
       rewrite /spec_reg_allows_load in H2; simplify_map_eq.
       destruct H2 as (? & _ & ?); simplify_eq.
       destruct (decide (r2 = cnull)); first done.
       simplify_eq.
     }
     by iModIntro; iFrame.
  Qed.

  Lemma step_load_fail_not_ra E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = false ->
    r2 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
  Proof.
     iIntros (HE Hdecode Hvpc Hbounds Hcnull) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
     iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
     rewrite spec_memMap_resource_1_dq.
     iMod (step_load with "[$Hctx $Hj $Hmap $Hi]") as "H"; eauto; simplify_map_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     { rewrite /spec_allow_load_map_or_true.
       exists true, p, g, b, e, a.
       split.
       + rewrite /spec_read_reg_inr; by simplify_map_eq.
       + rewrite /spec_reg_allows_load; simplify_map_eq.
         rewrite decide_False; first done.
         rewrite Hbounds.
         intros (_&?&_); done.
     }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".
     destruct Hspec as [| Hfail].
     {
       rewrite /spec_reg_allows_load in H2; simplify_map_eq.
       destruct H2 as (? & ? & ?); simplify_eq.
       by rewrite H5 in Hbounds.
     }
     by iModIntro; iFrame.
  Qed.

  Lemma step_load_fail_not_withinbounds E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    withinBounds b e a = false →
    r2 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr Failed).
  Proof.
     iIntros (HE Hdecode Hvpc Hbounds Hcnull) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
     iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
     rewrite spec_memMap_resource_1_dq.
     iMod (step_load with "[$Hctx $Hj $Hmap $Hi]") as "H"; eauto; simplify_map_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     { rewrite /spec_allow_load_map_or_true.
       exists true, p, g, b, e, a.
       split.
       + rewrite /spec_read_reg_inr; by simplify_map_eq.
       + rewrite /spec_reg_allows_load; simplify_map_eq.
         rewrite decide_False; first done.
         rewrite Hbounds.
         intros (_&_&?); done.
     }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".
     destruct Hspec as [| Hfail].
     {
       rewrite /spec_reg_allows_load in H2; simplify_map_eq.
       destruct H2 as (? & _ & ?); simplify_eq.
       by rewrite H5 in Hbounds.
     }
     by iModIntro.
  Qed.

  Lemma step_load_fail_tag E pc_p pc_g pc_b pc_e pc_a
      w dst src regs wa :
    ↑specN ⊆ E →
    decodeInstrW w = Load dst src 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !!ᵣ src = Some wa →
    get_tag wa = false →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    pc_a ↣ₐ w ∗ ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    pc_a ↣ₐ w ∗ [∗ map] k↦y ∈ regs, k ↣ᵣ y.
  Proof.
    iIntros (HE Hinstr Hvpc HPC Hsrc Htag) "(#Hctx & Hj & Hpc_a & Hmap)".
    iApply (step_instr_failed_map with "[$Hctx $Hj $Hpc_a $Hmap]"); [done..|].
    intros r sr m st Hregs.
    have Hsrc' := lookup_reg_weaken _ _ _ _ Hsrc Hregs.
    rewrite /exec /= Hsrc' /=.
    destruct wa as [| [t p g b e a|] | |]; cbn in Htag;
      subst; done.
  Qed.

  Lemma step_load_success_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a ea (imm : Z) pc_a' dq dq' :
    ↑specN ⊆ E →
    is_heap_cap (if (ea =? pc_a)%a then w else w') = false →
    decodeInstrW w = Load r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    (if (eqb_addr ea pc_a) then emp else ea ↣ₐ{dq'} w')
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ (if (eqb_addr ea pc_a) then (load_word p w) else (load_word p w')) ∗
    pc_a ↣ₐ{dq} w ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    (if (eqb_addr ea pc_a) then emp else ea ↣ₐ{dq'} w').
  Proof.
    iIntros (HE Hheap Hinstr Hvpc [Hra Hwb] Hadd Hpca' Hcnull Hcnull') "(#Hctx & Hj & HPC & Hi & Hr1 & Hr2 & Hr2a)".
    iDestruct (spec_map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iDestruct (memMap_resource_2gen_dq _ _ _ _ _ _ (λ a dq w, a ↣ₐ{dq} w)%I with "Hi Hr2a") as (mem dfracs) "[Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hdfracs].

    iMod (step_load_general_imm with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct (ea =? pc_a)%a; by simplify_map_eq. }
    { eapply spec_mem_implies_allow_load_map_imm; eauto. by simplify_map_eq. }
    { destruct (ea =? pc_a)%a; simplify_eq. all: rewrite !dom_insert_L;set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       (* FIXME: fragile *)
       destruct H2 as (Hrr2 & Hea & _). simplify_map_eq. try (rewrite Hadd in Hea; simplify_eq).
       iDestruct (spec_memMap_resource_2gen_d_dq with "[Hmem]") as "[Hpc_a Ha]".
       { iExists mem,dfracs; iSplitL; auto. }
       spec_incrementPC_inv.
       pose proof (spec_mem_implies_loadv _ _ _ _ _ _ Hmem H3) as Hloadv; eauto.
       simplify_map_eq.
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
       iDestruct (spec_regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto.
       iModIntro. iFrame.
       by repeat case_match.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; try congruence.
       all: try spec_incrementPC_inv; simplify_map_eq; eauto.
       all: try congruence.
       all: match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
     }
  Qed.

  Lemma step_load_success_same_imm E r1 pc_p pc_g pc_b pc_e pc_a w w' p g b e a ea (imm : Z) pc_a' dq dq' :
    ↑specN ⊆ E →
    is_heap_cap (if (ea =? pc_a)%a then w else w') = false →
    decodeInstrW w = Load r1 r1 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ WCap true p g b e a ∗
    (if (ea =? pc_a)%a then emp else ea ↣ₐ{dq'} w')
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ (if (ea =? pc_a)%a then load_word p w else load_word p w') ∗
    pc_a ↣ₐ{dq} w ∗
    (if (ea =? pc_a)%a then emp else ea ↣ₐ{dq'} w').
  Proof.
    iIntros (HE Hheap Hinstr Hvpc Hra Hwb Hadd Hpca' Hcnull) "(#Hctx & Hj & HPC & Hi & Hr1 & Hr1a)".
    iDestruct (spec_map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iDestruct (memMap_resource_2gen_dq _ _ _ _ _ _ (λ a dq w, a ↣ₐ{dq} w)%I with "Hi Hr1a") as
        (mem dfracs) "[Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hfracs].

    iMod (step_load_general_imm with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct (ea =? pc_a)%a; by simplify_map_eq. }
    { eapply spec_mem_implies_allow_load_map_imm; eauto. by simplify_map_eq. }
    { destruct (ea =? pc_a)%a; by set_solver. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iModIntro.
       destruct H0 as (Hrr2 & Hea & _). simplify_map_eq. try (rewrite Hadd in Hea; simplify_eq).
       iDestruct (spec_memMap_resource_2gen_d_dq with "[Hmem]") as "[Hpc_a Ha]".
       {iExists mem,dfracs; iSplitL; auto. }
       spec_incrementPC_inv.
       pose proof (spec_mem_implies_loadv _ _ _ _ _ _ Hmem H1) as Hloadv; eauto.
       simplify_map_eq.
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto. iFrame.
       by repeat case_match.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; try congruence.
       all: try spec_incrementPC_inv; simplify_map_eq; eauto.
       all: try congruence.
       all: match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
     }
  Qed.

  Lemma step_load_success_notinstr_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a ea (imm : Z) pc_a' dq dq' :
    ↑specN ⊆ E →
    is_heap_cap w' = false →
    decodeInstrW w = Load r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ{dq'} w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ load_word p w' ∗
    pc_a ↣ₐ{dq} w ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ{dq'} w'.
  Proof.
    iIntros (HE Hheap Hinstr Hvpc Hrawb Hadd Hpca' Hcnull Hcnull') "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Hr2 & Ha)".
    destruct (ea =? pc_a)%a eqn:Ha.
    - assert (ea = pc_a) as -> by (apply Z.eqb_eq in Ha; solve_addr).
      iDestruct (spec_mem_pointsto_agree with "Hpc_a Ha") as %<-.
      iMod (step_load_success_imm _ _ _ _ _ _ _ _ _ w _ _ _ _ _ _ _ _ _ _ dq'
             with "[$Hctx $Hj $HPC $Hpc_a $Hr1 $Hr2]") as "(Hj & HPC & Hr1 & Hpc_a & Hr2 & _)"; eauto.
      { by rewrite /eqb_addr Ha. }
      rewrite /eqb_addr Ha.
      iModIntro. iFrame.
    - iMod (step_load_success_imm _ _ _ _ _ _ _ _ _ w' with "[$Hctx $Hj $HPC $Hpc_a $Hr1 $Hr2 Ha]")
        as "(Hj & HPC & Hr1 & Hpc_a & Hr2 & Ha)"; eauto.
      { rewrite ?Ha; done. }
      { rewrite /eqb_addr Ha. iFrame. }
      rewrite /eqb_addr Ha.
      iModIntro. iFrame.
  Qed.

  Lemma step_load_success_frominstr_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a w w'' p g b e a (imm : Z) pc_a' dq :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e pc_a = true →
    (a + imm)%a = Some pc_a →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ load_word p w ∗
    pc_a ↣ₐ{dq} w ∗
    r2 ↣ᵣ WCap true p g b e a.
  Proof.
    iIntros (HE Hinstr Hvpc Hrawb Hadd Hpca' Hcnull Hcnull') "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Hr2)".
    pose proof (spec_decode_load_not_heap_cap _ _ _ _ Hinstr) as Hheap.
    iMod (step_load_success_imm _ _ _ _ _ _ _ _ _ w _ _ _ _ _ _ pc_a _ _ _ DfracDiscarded
           with "[$Hctx $Hj $HPC $Hpc_a $Hr1 $Hr2]") as "(Hj & HPC & Hr1 & Hpc_a & Hr2 & _)"; eauto.
    { by rewrite /eqb_addr Z.eqb_refl. }
    rewrite /eqb_addr Z.eqb_refl.
    iModIntro. iFrame.
  Qed.

  Lemma step_load_success_same_notinstr_imm E r1 pc_p pc_g pc_b pc_e pc_a w w' p g b e a ea (imm : Z) pc_a' dq dq' :
    ↑specN ⊆ E →
    is_heap_cap w' = false →
    decodeInstrW w = Load r1 r1 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ{dq'} w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ load_word p w' ∗
    pc_a ↣ₐ{dq} w ∗
    ea ↣ₐ{dq'} w'.
  Proof.
    iIntros (HE Hheap Hinstr Hvpc Hra Hwb Hadd Hpca' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Ha)".
    destruct (ea =? pc_a)%a eqn:Ha.
    - assert (ea = pc_a) as -> by (apply Z.eqb_eq in Ha; solve_addr).
      iDestruct (spec_mem_pointsto_agree with "Hpc_a Ha") as %<-.
      iMod (step_load_success_same_imm _ _ _ _ _ _ _ _ w _ _ _ _ _ _ _ _ _ dq'
             with "[$Hctx $Hj $HPC $Hpc_a $Hr1]") as "(Hj & HPC & Hr1 & Hpc_a & _)"; eauto.
      { by rewrite Ha. }
      rewrite Ha.
      iModIntro. iFrame.
    - iMod (step_load_success_same_imm _ _ _ _ _ _ _ _ w' with "[$Hctx $Hj $HPC $Hpc_a $Hr1 Ha]")
        as "(Hj & HPC & Hr1 & Hpc_a & Ha)"; eauto.
      { rewrite ?Ha; done. }
      { rewrite Ha. iFrame. }
      rewrite Ha.
      iModIntro. iFrame.
  Qed.

  Lemma step_load_success_same_frominstr_imm E r1 pc_p pc_g pc_b pc_e pc_a w p g b e a (imm : Z) pc_a' dq :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r1 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e pc_a = true →
    (a + imm)%a = Some pc_a →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ load_word p w ∗
    pc_a ↣ₐ{dq} w.
  Proof.
    iIntros (HE Hinstr Hvpc Hra Hwb Hadd Hpca' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hr1)".
    pose proof (spec_decode_load_not_heap_cap _ _ _ _ Hinstr) as Hheap.
    iMod (step_load_success_same_imm _ _ _ _ _ _ _ _ w _ _ _ _ _ pc_a _ _ _ DfracDiscarded
           with "[$Hctx $Hj $HPC $Hpc_a $Hr1]") as "(Hj & HPC & Hr1 & Hpc_a & _)"; eauto.
    { by rewrite Z.eqb_refl. }
    rewrite Z.eqb_refl.
    iModIntro. iFrame.
  Qed.

  Lemma step_load_success_alt_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a ea (imm : Z) pc_a' :
    ↑specN ⊆ E →
    is_heap_cap (if (ea =? pc_a)%a then w else w') = false →
    decodeInstrW w = Load r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ load_word p w' ∗
    pc_a ↣ₐ w ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ w'.
  Proof.
    iIntros (HE Hheap Hinstr Hvpc [Hra Hwb] Hadd Hpca' Hcnull Hcnull') "(#Hctx & Hj & HPC & Hi & Hr1 & Hr2 & Hr2a)".
    iAssert (⌜(ea =? pc_a)%a = false⌝)%I as %Hfalse.
    { rewrite Z.eqb_neq. iDestruct (spec_address_neq with "Hr2a Hi") as %Hneq. iIntros (->%finz_to_z_eq). done. }
    iMod (step_load_success_imm _ _ _ _ _ _ _ _ _ w' with "[$Hctx $Hj $HPC $Hi $Hr1 $Hr2 Hr2a]") as "H"; eauto.
    { rewrite /eqb_addr Hfalse. iFrame. }
    rewrite /eqb_addr Hfalse.
    iModIntro. iExact "H".
  Qed.

  Lemma step_load_success_same_alt_imm E r1 pc_p pc_g pc_b pc_e pc_a w w' p g b e a ea (imm : Z) pc_a' :
    ↑specN ⊆ E →
    is_heap_cap (if (ea =? pc_a)%a then w else w') = false →
    decodeInstrW w = Load r1 r1 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ load_word p w' ∗
    pc_a ↣ₐ w ∗
    ea ↣ₐ w'.
  Proof.
    iIntros (HE Hheap Hinstr Hvpc [Hra Hwb] Hadd Hpca' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Ha)".
    iAssert (⌜(ea =? pc_a)%a = false⌝)%I as %Hfalse.
    { rewrite Z.eqb_neq. iDestruct (spec_address_neq with "Ha Hpc_a") as %Hneq. iIntros (->%finz_to_z_eq). done. }
    iMod (step_load_success_same_imm _ _ _ _ _ _ _ _ w' with "[$Hctx $Hj $HPC $Hpc_a $Hr1 Ha]") as "H"; eauto.
    { rewrite /eqb_addr Hfalse. iFrame. }
    rewrite /eqb_addr Hfalse.
    iModIntro. iExact "H".
  Qed.

  Lemma step_load_fail_tag_imm E pc_p pc_g pc_b pc_e pc_a
      w dst src (imm : Z) regs wa :
    ↑specN ⊆ E →
    decodeInstrW w = Load dst src imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !!ᵣ src = Some wa →
    get_tag wa = false →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    pc_a ↣ₐ w ∗ ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    pc_a ↣ₐ w ∗ [∗ map] k↦y ∈ regs, k ↣ᵣ y.
  Proof.
    iIntros (HE Hinstr Hvpc HPC Hsrc Htag) "(#Hctx & Hj & Hpc_a & Hmap)".
    iApply (step_instr_failed_map with "[$Hctx $Hj $Hpc_a $Hmap]"); [done..|].
    intros r sr m st Hregs.
    have Hsrc' := lookup_reg_weaken _ _ _ _ Hsrc Hregs.
    rewrite /exec /= Hsrc' /=.
    destruct wa as [| [t p g b e a|] | |]; cbn in Htag;
      subst; done.
  Qed.

  Lemma step_load_fail_not_ra_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a (imm : Z) :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = false ->
    r2 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
  Proof.
     iIntros (HE Hdecode Hvpc Hbounds Hcnull) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
     iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
     rewrite spec_memMap_resource_1_dq.
     iMod (step_load_imm with "[$Hctx $Hj $Hmap $Hi]") as "H"; eauto; simplify_map_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     { rewrite /spec_allow_load_map_or_true_imm.
       exists true, p, g, b, e, a.
       split.
       + rewrite /spec_read_reg_inr; by simplify_map_eq.
       + rewrite /spec_reg_allows_load_imm; simplify_map_eq.
         destruct (a + imm)%a; cbn; last done.
         rewrite decide_False; first done.
         rewrite Hbounds.
         intros (_&_&?&_); done.
     }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".
     destruct Hspec as [| Hfail].
     {
       destruct H2 as (Hreg & Hea & Hra & Hwb).
       simplify_map_eq. congruence.
     }
     by iModIntro; iFrame.
  Qed.

  Lemma step_load_fail_not_withinbounds_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a ea (imm : Z) :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    withinBounds b e ea = false →
    (a + imm)%a = Some ea →
    r2 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
  Proof.
     iIntros (HE Hdecode Hvpc Hbounds Hadd Hcnull) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
     iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
     rewrite spec_memMap_resource_1_dq.
     iMod (step_load_imm with "[$Hctx $Hj $Hmap $Hi]") as "H"; eauto; simplify_map_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     { rewrite /spec_allow_load_map_or_true_imm.
       exists true, p, g, b, e, a.
       split.
       + rewrite /spec_read_reg_inr; by simplify_map_eq.
       + rewrite /spec_reg_allows_load_imm; simplify_map_eq.
         try rewrite Hadd.
         rewrite decide_False; first done.
         rewrite Hbounds.
         intros (_&_&_&?); done.
     }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".
     destruct Hspec as [| Hfail].
     {
       destruct H2 as (Hreg & Hea & Hra & Hwb).
       simplify_map_eq. try (rewrite Hadd in Hea; simplify_eq). congruence.
     }
     by iModIntro; iFrame.
  Qed.

  Lemma step_load_success_PC_imm E r2 pc_p pc_g pc_b pc_e pc_a w
        p g b e a ea (imm : Z) (t : bool) p' g' b' e' a' a'' :
    ↑specN ⊆ E →
    is_heap_cap (WCap t p' g' b' e' a') = false →
    decodeInstrW w = Load PC r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (a' + 1)%a = Some a'' →
    r2 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ WCap t p' g' b' e' a'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ load_word p (WCap t p' g' b' e' a'') ∗
    pc_a ↣ₐ w ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ WCap t p' g' b' e' a'.
  Proof.
    iIntros (HE Hheap Hinstr Hvpc [Hra Hwb] Hadd Hpca' Hcnull) "(#Hctx & Hj & HPC & Hi & Hr2 & Hr2a)".
    iDestruct (spec_map_of_regs_2 with "HPC Hr2") as "[Hmap %]".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hr2a") as "[Hmem %]"; auto.
    iMod (step_load_imm with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply spec_mem_neq_implies_allow_load_map_imm with (a := a) (ea := ea) (pc_a := pc_a); eauto.
      by simplify_map_eq. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iModIntro.
       destruct H1 as (Hrr2 & Hea & _). simplify_map_eq. try (rewrite Hadd in Hea; simplify_eq).
       iDestruct (spec_memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       spec_incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_eq insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hr2]"; eauto.
       iFrame.
       by destruct p0; destruct dro,dl; rewrite /load_word in H1 |- *; cbn in *; simplify_eq.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; try congruence.
       all: try match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
       all: match goal with H : spec_incrementPC _ = None |- _ =>
         rewrite /load_word in H end.
       all: destruct (isDRO p0) eqn:HDRO, (isDL p0) eqn:HDL; cbn.
       all: try spec_incrementPC_inv; simplify_map_eq; eauto; try congruence.
     }
  Qed.

  Lemma step_load_fail_addr_imm E pc_p pc_g pc_b pc_e pc_a
      w dst src (imm : Z) regs p g b e a :
    ↑specN ⊆ E →
    decodeInstrW w = Load dst src imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !!ᵣ src = Some (WCap true p g b e a) →
    (a + imm)%a = None →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    pc_a ↣ₐ w ∗ ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    pc_a ↣ₐ w ∗ [∗ map] k↦y ∈ regs, k ↣ᵣ y.
  Proof.
    iIntros (HE Hinstr Hvpc HPC Hsrc Hadd) "(#Hctx & Hj & Hpc_a & Hmap)".
    iApply (step_instr_failed_map with "[$Hctx $Hj $Hpc_a $Hmap]"); [done..|].
    intros r sr m st Hregs.
    have Hsrc' := lookup_reg_weaken _ _ _ _ Hsrc Hregs.
    rewrite /exec /= Hsrc' /=.
    rewrite Hadd /=. done.
  Qed.

  Lemma step_load_fail_const_imm E pc_p pc_g pc_b pc_e pc_a
      w dst src (imm : Z) regs wa :
    ↑specN ⊆ E →
    decodeInstrW w = Load dst src imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !!ᵣ src = Some wa →
    is_cap wa = false →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    pc_a ↣ₐ w ∗ ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    pc_a ↣ₐ w ∗ [∗ map] k↦y ∈ regs, k ↣ᵣ y.
  Proof.
    iIntros (HE Hinstr Hvpc HPC Hsrc Htag) "(#Hctx & Hj & Hpc_a & Hmap)".
    iApply (step_instr_failed_map with "[$Hctx $Hj $Hpc_a $Hmap]"); [done..|].
    intros r sr m st Hregs.
    have Hsrc' := lookup_reg_weaken _ _ _ _ Hsrc Hregs.
    rewrite /exec /= Hsrc' /=.
    destruct wa as [| [t p g b e a|] | |]; cbn in Htag;
      subst; done.
  Qed.

  Lemma step_load_fail_not_cap_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' wsrc (imm : Z) :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    is_cap wsrc = false ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ wsrc
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
  Proof.
    iIntros (HE Hdecode Hvpc Hcap) "(#Hctx & Hj & HPC & Hi & Hdst & Hsrc)".
    iDestruct (spec_map_of_regs_3 with "HPC Hdst Hsrc") as "[Hmap (%&%&%)]".
    iMod (step_load_fail_const_imm E pc_p pc_g pc_b pc_e pc_a w r1 r2 imm _ (if decide (r2 = cnull) then WInt 0 else wsrc) with "[$Hctx $Hj $Hi $Hmap]") as "(Hj & _)"; eauto; simplify_map_eq; eauto.
    all: try by case_decide.
    all: by iModIntro; iFrame.
  Qed.

  Lemma step_load_success_fromPC_imm E r1 pc_p pc_g pc_b pc_e pc_a w w' w'' ea (imm : Z) pc_a' dq dq' :
    ↑specN ⊆ E →
    is_heap_cap w' = false →
    decodeInstrW w = Load r1 PC imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    withinBounds pc_b pc_e ea = true →
    (pc_a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ w'' ∗
    (if (ea =? pc_a)%a then emp else ea ↣ₐ{dq'} w')
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ (if (ea =? pc_a)%a then load_word pc_p w else load_word pc_p w') ∗
    pc_a ↣ₐ{dq} w ∗
    (if (ea =? pc_a)%a then emp else ea ↣ₐ{dq'} w').
  Proof.
    iIntros (HE Hheap Hinstr Hvpc Hwb Hadd Hpca' Hcnull) "(#Hctx & Hj & HPC & Hi & Hr1 & Hr1a)".
    pose proof (spec_decode_load_not_heap_cap _ _ _ _ Hinstr) as Hheapw.
    assert (readAllowed pc_p = true) as Hra.
    { pose proof (isCorrectPC_ra_wb _ _ _ _ _ _ Hvpc) as Hpc. apply andb_prop_elim in Hpc as [Hra _]. by apply Is_true_true. }
    iDestruct (spec_map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iDestruct (memMap_resource_2gen_dq _ _ _ _ _ _ (λ a dq w, a ↣ₐ{dq} w)%I with "Hi Hr1a") as
        (mem dfracs) "[Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hfracs].

    iMod (step_load_general_imm with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct (ea =? pc_a)%a; by simplify_map_eq. }
    { eapply spec_mem_implies_allow_load_map_imm; eauto. by simplify_map_eq. }
    { destruct (ea =? pc_a)%a; by set_solver. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iModIntro.
       destruct H0 as (Hrr2 & Hea & _). simplify_map_eq. try (rewrite Hadd in Hea; simplify_eq).
       iDestruct (spec_memMap_resource_2gen_d_dq with "[Hmem]") as "[Hpc_a Ha]".
       {iExists mem,dfracs; iSplitL; auto. }
       spec_incrementPC_inv.
       pose proof (spec_mem_implies_loadv _ _ _ _ _ _ Hmem H1) as Hloadv; eauto.
       simplify_map_eq.
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto. iFrame.
       by repeat case_match.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; try congruence.
       all: try spec_incrementPC_inv; simplify_map_eq; eauto.
       all: try congruence.
       all: match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
     }
  Qed.

  Lemma step_load_success_PC_PC_imm E pc_p pc_g pc_b pc_e pc_a w
        ea (imm : Z) (t : bool) p' g' b' e' a' a'' :
    ↑specN ⊆ E →
    is_heap_cap (WCap t p' g' b' e' a') = false →
    decodeInstrW w = Load PC PC imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    withinBounds pc_b pc_e ea = true →
    (pc_a + imm)%a = Some ea →
    (a' + 1)%a = Some a'' →

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    ea ↣ₐ WCap t p' g' b' e' a'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ load_word pc_p (WCap t p' g' b' e' a'') ∗
    pc_a ↣ₐ w ∗
    ea ↣ₐ WCap t p' g' b' e' a'.
  Proof.
    iIntros (HE Hheap Hinstr Hvpc Hwb Hadd Hpca') "(#Hctx & Hj & HPC & Hi & Hr2a)".
    assert (readAllowed pc_p = true) as Hra.
    { apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [Hra _]. by apply Is_true_true. }
    iDestruct (spec_map_of_regs_1 with "HPC") as "Hmap".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hr2a") as "[Hmem %]"; auto.
    iMod (step_load_imm with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { eapply spec_mem_neq_implies_allow_load_map_imm with (a := pc_a) (ea := ea) (pc_a := pc_a); eauto.
    }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iModIntro.
       destruct H0 as (Hrr2 & Hea & _). simplify_map_eq. try (rewrite Hadd in Hea; simplify_eq).
       iDestruct (spec_memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       spec_incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (spec_regs_of_map_1 with "Hmap") as "HPC".
       iFrame.
       by destruct p; destruct dro,dl; rewrite /load_word in H0 |- *; cbn in *; simplify_eq.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; try congruence.
       all: try match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
       all: match goal with H : spec_incrementPC _ = None |- _ =>
         rewrite /load_word in H end.
       all: destruct (isDRO p) eqn:HDRO, (isDL p) eqn:HDL; cbn.
       all: try spec_incrementPC_inv; simplify_map_eq; eauto; try congruence.
     }
  Qed.

  Lemma step_load_success_fromPC_notinstr_imm E r1 pc_p pc_g pc_b pc_e pc_a w w' w'' ea (imm : Z) pc_a' dq dq' :
    ↑specN ⊆ E →
    is_heap_cap w' = false →
    decodeInstrW w = Load r1 PC imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    withinBounds pc_b pc_e ea = true →
    (pc_a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ w'' ∗
    ea ↣ₐ{dq'} w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ load_word pc_p w' ∗
    pc_a ↣ₐ{dq} w ∗
    ea ↣ₐ{dq'} w'.
  Proof.
    iIntros (HE Hheap Hinstr Hvpc Hwb Hadd Hincr Hnull) "(#Hctx & Hj & HPC & Hi & Hr & Hm)".
    destruct (ea =? pc_a)%a eqn:Heq.
    - assert (ea = pc_a) as -> by (apply Z.eqb_eq in Heq; solve_addr).
      iDestruct (spec_mem_pointsto_agree with "Hi Hm") as %<-.
      iMod (step_load_success_fromPC_imm _ _ _ _ _ _ _ _ w _ _ _ _ _ dq'
             with "[$Hctx $Hj $HPC $Hi $Hr]") as "(Hj & HPC & Hr & Hi & _)"; eauto.
      { by rewrite Heq. }
      rewrite Heq.
      iModIntro. iFrame.
    - iMod (step_load_success_fromPC_imm with "[$Hctx $Hj $HPC $Hi $Hr Hm]")
        as "(Hj & HPC & Hr & Hi & Hm)"; eauto.
      { rewrite Heq. iFrame. }
      rewrite Heq.
      iModIntro. iFrame.
  Qed.

  Lemma step_load_success_fromPC_frominstr_imm E r1 pc_p pc_g pc_b pc_e pc_a pc_a' w w'' dq (imm : Z) :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 PC imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + imm)%a = Some pc_a →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ w''
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ load_word pc_p w.
  Proof.
    iIntros (HE Hinstr Hvpc Hadd Hincr Hnull) "(#Hctx & Hj & HPC & Hi & Hr)".
    pose proof (spec_decode_load_not_heap_cap _ _ _ _ Hinstr) as Hheap.
    assert (withinBounds pc_b pc_e pc_a = true) as Hwb.
    { pose proof (isCorrectPC_ra_wb _ _ _ _ _ _ Hvpc) as Hpc.
      apply andb_prop_elim in Hpc as [_ Hwb]. by apply Is_true_true. }
    iMod (step_load_success_fromPC_imm _ _ _ _ _ _ _ _ w _ pc_a _ _ _ DfracDiscarded
           with "[$Hctx $Hj $HPC $Hi $Hr]") as "(Hj & HPC & Hr & Hi & _)"; eauto.
    { by rewrite Z.eqb_refl. }
    rewrite Z.eqb_refl.
    iModIntro. iFrame.
  Qed.


End spec_rules.
