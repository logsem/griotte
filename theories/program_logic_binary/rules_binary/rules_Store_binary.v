From iris.proofmode Require Import proofmode.
From griotte Require Export rules_base_binary.
From griotte Require Import rules_Store.

(** * Spec rules for [Store] (spec copies of [rules_Store.v]) *)

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

  Definition spec_reg_allows_store_imm (regs : Reg) (r : RegName) (imm : Z) p g b e a ea :=
    regs !!ᵣ r = Some (WCap true p g b e a) ∧
    (a + imm)%a = Some ea ∧ writeAllowed p = true ∧ withinBounds b e ea = true.

  Inductive spec_Store_failure_imm (regs: Reg) (r1 : RegName)(r2 : Z + RegName) (imm : Z) (mem : gmap Addr Word):=
  | spec_Store_fail_const_imm w:
      regs !!ᵣ r1 = Some w ->
      is_cap w = false →
      spec_Store_failure_imm regs r1 r2 imm mem
  | spec_Store_fail_tag_imm p g b e a:
      regs !!ᵣ r1 = Some (WCap false p g b e a) →
      spec_Store_failure_imm regs r1 r2 imm mem
  | spec_Store_fail_addr_imm p g b e a:
      regs !!ᵣ r1 = Some (WCap true p g b e a) →
      (a + imm)%a = None →
      spec_Store_failure_imm regs r1 r2 imm mem
  | spec_Store_fail_bounds_imm p g b e a ea:
      regs !!ᵣ r1 = Some(WCap true p g b e a) ->
      (a + imm)%a = Some ea →
      (writeAllowed p = false ∨ withinBounds b e ea = false) →
      spec_Store_failure_imm regs r1 r2 imm mem
  | spec_Store_fail_invalid_PC_imm:
      spec_incrementPC (regs) = None ->
      spec_Store_failure_imm regs r1 r2 imm mem
  .

  Inductive spec_Store_spec_imm
    (regs: Reg) (r1 : RegName) (r2 : Z + RegName) (imm : Z)
    (regs': Reg) (mem mem' : gmap Addr Word) : griotte_lang.val → Prop
  :=
  | spec_Store_spec_success_imm p g b e a ea storev oldv :
      word_of_argument regs r2 = Some storev ->
      spec_reg_allows_store_imm regs r1 imm p g b e a ea →
      mem !! ea = Some oldv →
      mem' = (<[ea := store_word p storev]> mem) →
      spec_incrementPC(regs) = Some regs' ->
      spec_Store_spec_imm regs r1 r2 imm regs' mem mem' NextIV
  | spec_Store_spec_failure_store_imm :
      mem' = mem →
      spec_Store_failure_imm regs r1 r2 imm mem ->
      spec_Store_spec_imm regs r1 r2 imm regs' mem mem' FailedV.

  Definition spec_allow_store_map_or_true_imm
    (r1 : RegName) (r2 : Z + RegName) (imm : Z) (regs : Reg) (mem : Mem):=
    ∃ t p g b e a storev,
      spec_read_reg_inr regs r1 t p g b e a ∧ word_of_argument regs r2 = Some storev ∧
      match (a + imm)%a with
      | None => True
      | Some ea => if decide (spec_reg_allows_store_imm regs r1 imm p g b e a ea) then
        ∃ w, mem !! ea = Some w
      else True
      end.

  Lemma spec_allow_store_implies_storev_imm:
    ∀ (r1 : RegName)(r2 : Z + RegName) (mem0 : gmap Addr Word) (r : Reg)
      (p : Perm) (g : Locality) (b e a ea : Addr) (imm : Z) storev,
      spec_allow_store_map_or_true_imm r1 r2 imm r mem0
      → r !!ᵣ r1 = Some (WCap true p g b e a)
      → word_of_argument r r2 = Some storev
      → writeAllowed p = true
      → (a + imm)%a = Some ea
      → withinBounds b e ea = true
      → ∃ (storev : Word),
          mem0 !! ea = Some storev.
  Proof.
    intros r1 r2 mem0 r p g b e a ea imm storev HaStore Hr2v Hwoa Hwa Hadd Hwb.
    assert (r1 ≠ cnull).
    { intros -> ; simplify_map_eq.
      destruct (r !! cnull); cbn in * ; done.
    }
    simplify_map_eq.
    unfold spec_allow_store_map_or_true_imm, spec_read_reg_inr in HaStore.
    destruct HaStore as (t&?&?&?&?&?&?&Hrinr&Hwo&Hmem).
    rewrite Hr2v in Hrinr. inversion Hrinr; subst.
    unfold spec_reg_allows_store_imm in Hmem. rewrite Hadd in Hmem.
    case_decide as HAL.
    - auto.
    - unfold spec_reg_allows_store_imm in HAL.
      destruct HAL. rewrite Hwo in Hwoa; inversion Hwoa. repeat split; auto.
      by simplify_map_eq.
  Qed.

  Lemma spec_mem_eq_implies_allow_store_map_imm:
    ∀ (regs : Reg)(mem : Mem)(r1 : RegName)(r2 : Z + RegName)(w storev : Word) p g b e a ea (imm : Z),
      (a + imm)%a = Some ea
      → mem = <[ea:=w]> ∅
      → regs !!ᵣ r1 = Some (WCap true p g b e a)
      → word_of_argument regs r2 = Some storev
      → spec_allow_store_map_or_true_imm r1 r2 imm regs mem.
  Proof.
    intros regs mem r1 r2 w storev p g b e a ea imm Hadd Hmem Hrr2.
    assert (r1 ≠ cnull).
    { intros -> ; simplify_map_eq.
      destruct (regs !! cnull); cbn in * ; done.
    }
    simplify_map_eq.
    exists true,p,g,b,e,a,storev; split.
    - unfold spec_read_reg_inr. by rewrite Hrr2.
    - unfold spec_reg_allows_store_imm. rewrite Hadd. case_decide; last done.
      split; auto. exists w. simplify_map_eq. auto.
  Qed.

  Lemma spec_mem_neq_implies_allow_store_map_imm:
    ∀ (regs : Reg)(mem : Mem)(r1 : RegName)(r2 : Z + RegName)(pc_a : Addr)
      (w w' storev : Word) p g b e a ea (imm : Z),
      (a + imm)%a = Some ea
      → ea ≠ pc_a
      → mem = <[pc_a:= w]> (<[ea:= w']> ∅)
      → regs !!ᵣ r1 = Some (WCap true p g b e a)
      → word_of_argument regs r2 = Some storev
      → spec_allow_store_map_or_true_imm r1 r2 imm regs mem.
  Proof.
    intros regs mem r1 r2 pc_a w w' storev p g b e a ea imm Hadd H4 Hrr2 Hreg1 Hwoa.
    assert (r1 ≠ cnull).
    { intros -> ; simplify_map_eq.
      destruct (regs !! cnull); cbn in * ; done.
    }
    simplify_map_eq.
    exists true,p,g,b,e,a,storev; split.
    - unfold spec_read_reg_inr. by rewrite Hreg1.
    - unfold spec_reg_allows_store_imm. rewrite Hadd. case_decide; last done.
      split; auto. exists w'. simplify_map_eq. split; auto.
  Qed.

  Lemma spec_mem_implies_allow_store_map_imm:
    ∀ (regs : Reg)(mem : Mem)(r1 : RegName)(r2 : Z + RegName)(pc_a : Addr)
      (w w' storev : Word) p g b e a ea (imm : Z),
      (a + imm)%a = Some ea
      → (if (ea =? pc_a)%a
       then mem = <[pc_a:= w]> ∅
       else mem = <[pc_a:= w]> (<[ea:= w']> ∅))
      → regs !!ᵣ r1 = Some (WCap true p g b e a)
      → word_of_argument regs r2 = Some storev
      → spec_allow_store_map_or_true_imm r1 r2 imm regs mem.
  Proof.
    intros regs mem r1 r2 pc_a w w' storev p g b e a ea imm Hadd H4 Hrr2 Hwoa.
    assert (r1 ≠ cnull).
    { intros -> ; simplify_map_eq.
      destruct (regs !! cnull); cbn in * ; done.
    }
    simplify_map_eq.
    destruct (ea =? pc_a)%a eqn:Heq.
      + apply Z.eqb_eq, finz_to_z_eq in Heq. subst ea. eapply spec_mem_eq_implies_allow_store_map_imm; eauto.
        by simplify_map_eq.
      + apply Z.eqb_neq in Heq. eapply spec_mem_neq_implies_allow_store_map_imm; eauto; first congruence.
        by simplify_map_eq.
  Qed.

  Definition spec_reg_allows_store (regs : Reg) (r : RegName) p g b e a :=
    regs !!ᵣ r = Some (WCap true p g b e a) ∧
    writeAllowed p = true ∧ withinBounds b e a = true.

  Inductive spec_Store_failure (regs: Reg) (r1 : RegName)(r2 : Z + RegName) (mem : gmap Addr Word):=
  | spec_Store_fail_const w:
      regs !!ᵣ r1 = Some w ->
      is_cap w = false →
      spec_Store_failure regs r1 r2 mem
  | spec_Store_fail_tag p g b e a:
      regs !!ᵣ r1 = Some (WCap false p g b e a) →
      spec_Store_failure regs r1 r2 mem
  | spec_Store_fail_bounds p g b e a:
      regs !!ᵣ r1 = Some(WCap true p g b e a) ->
      (writeAllowed p = false ∨ withinBounds b e a = false) →
      spec_Store_failure regs r1 r2 mem
  | spec_Store_fail_invalid_PC:
      spec_incrementPC (regs) = None ->
      spec_Store_failure regs r1 r2 mem
  .

  Inductive spec_Store_spec
    (regs: Reg) (r1 : RegName) (r2 : Z + RegName)
    (regs': Reg) (mem mem' : gmap Addr Word) : griotte_lang.val → Prop
  :=
  | spec_Store_spec_success p g b e a storev oldv :
      word_of_argument regs r2 = Some storev ->
      spec_reg_allows_store regs r1 p g b e a →
      mem !! a = Some oldv →
      mem' = (<[a := store_word p storev]> mem) →
      spec_incrementPC(regs) = Some regs' ->
      spec_Store_spec regs r1 r2 regs' mem mem' NextIV
  | spec_Store_spec_failure_store :
      mem' = mem →
      spec_Store_failure regs r1 r2 mem ->
      spec_Store_spec regs r1 r2 regs' mem mem' FailedV.

  Definition spec_allow_store_map_or_true
    (r1 : RegName) (r2 : Z + RegName) (regs : Reg) (mem : Mem):=
    ∃ t p g b e a storev,
      spec_read_reg_inr regs r1 t p g b e a ∧ word_of_argument regs r2 = Some storev ∧
      if decide (spec_reg_allows_store regs r1 p g b e a) then
        ∃ w, mem !! a = Some w
      else True.

  Lemma spec_allow_store_implies_storev:
    ∀ (r1 : RegName)(r2 : Z + RegName) (mem0 : gmap Addr Word) (r : Reg)
      (p : Perm) (g : Locality) (b e a : Addr) storev,
      spec_allow_store_map_or_true r1 r2 r mem0
      → r !!ᵣ r1 = Some (WCap true p g b e a)
      → word_of_argument r r2 = Some storev
      → writeAllowed p = true
      → withinBounds b e a = true
      → ∃ (storev : Word),
          mem0 !! a = Some storev.
  Proof.
    intros r1 r2 mem0 r p g b e a storev HaStore Hr2v Hwoa Hwa Hwb.
    assert (r1 ≠ cnull).
    { intros -> ; simplify_map_eq.
      destruct (r !! cnull); cbn in * ; done.
    }
    simplify_map_eq.
    unfold spec_allow_store_map_or_true, spec_read_reg_inr in HaStore.
    destruct HaStore as (t&?&?&?&?&?&?&Hrinr&Hwo&Hmem).
    rewrite Hr2v in Hrinr. inversion Hrinr; subst.
    case_decide as HAL.
    - auto.
    - unfold spec_reg_allows_store in HAL.
      destruct HAL. rewrite Hwo in Hwoa; inversion Hwoa. split; auto.
      by simplify_map_eq.
  Qed.

  Lemma spec_mem_eq_implies_allow_store_map:
    ∀ (regs : Reg)(mem : Mem)(r1 : RegName)(r2 : Z + RegName)(w storev : Word) p g b e a,
      mem = <[a:=w]> ∅
      → regs !!ᵣ r1 = Some (WCap true p g b e a)
      → word_of_argument regs r2 = Some storev
      → spec_allow_store_map_or_true r1 r2 regs mem.
  Proof.
    intros regs mem r1 r2 w storev p g b e a Hmem Hrr2.
    assert (r1 ≠ cnull).
    { intros -> ; simplify_map_eq.
      destruct (regs !! cnull); cbn in * ; done.
    }
    simplify_map_eq.
    exists true,p,g,b,e,a,storev; split.
    - unfold spec_read_reg_inr. by rewrite Hrr2.
    - case_decide; last done.
      split; auto. exists w. simplify_map_eq. auto.
  Qed.

  Lemma spec_mem_neq_implies_allow_store_map:
    ∀ (regs : Reg)(mem : Mem)(r1 : RegName)(r2 : Z + RegName)(pc_a : Addr)
      (w w' storev : Word) p g b e a,
      a ≠ pc_a
      → mem = <[pc_a:= w]> (<[a:= w']> ∅)
      → regs !!ᵣ r1 = Some (WCap true p g b e a)
      → word_of_argument regs r2 = Some storev
      → spec_allow_store_map_or_true r1 r2 regs mem.
  Proof.
    intros regs mem r1 r2 pc_a w w' storev p g b e a H4 Hrr2 Hreg1 Hwoa.
    assert (r1 ≠ cnull).
    { intros -> ; simplify_map_eq.
      destruct (regs !! cnull); cbn in * ; done.
    }
    simplify_map_eq.
    exists true,p,g,b,e,a,storev; split.
    - unfold spec_read_reg_inr. by rewrite Hreg1.
    - case_decide; last done.
      split; auto. exists w'. simplify_map_eq. split; auto.
  Qed.

  Lemma spec_mem_implies_allow_store_map:
    ∀ (regs : Reg)(mem : Mem)(r1 : RegName)(r2 : Z + RegName)(pc_a : Addr)
      (w w' storev : Word) p g b e a,
      (if (a =? pc_a)%a
       then mem = <[pc_a:= w]> ∅
       else mem = <[pc_a:= w]> (<[a:= w']> ∅))
      → regs !!ᵣ r1 = Some (WCap true p g b e a)
      → word_of_argument regs r2 = Some storev
      → spec_allow_store_map_or_true r1 r2 regs mem.
  Proof.
    intros regs mem r1 r2 pc_a w w' storev p g b e a H4 Hrr2 Hwoa.
    assert (r1 ≠ cnull).
    { intros -> ; simplify_map_eq.
      destruct (regs !! cnull); cbn in * ; done.
    }
    simplify_map_eq.
    destruct (a =? pc_a)%a eqn:Heq.
      + apply Z.eqb_eq, finz_to_z_eq in Heq. subst a. eapply spec_mem_eq_implies_allow_store_map; eauto.
        by simplify_map_eq.
      + apply Z.eqb_neq in Heq. eapply spec_mem_neq_implies_allow_store_map; eauto; first congruence.
        by simplify_map_eq.
  Qed.

  (** The outcome of a store of the implementation run, on a lifted register
      file and memory, is a physical outcome, when the stored address is not
      the shadow table. *)
  Lemma Store_spec_lift regs r1 r2 imm lregs' (mem : Mem) lmem' shadow' v :
    (∀ p g b e a ea, regs !!ᵣ r1 = Some (WCap true p g b e a) → (a + imm)%a = Some ea →
       writeAllowed p = true → withinBounds b e ea = true → is_shadow_address ea = false) →
    Store_spec (lift_regs regs) r1 r2 imm lregs' (lword_of_word <$> mem) lmem' ∅ shadow' v →
    ∃ regs' mem', (v = NextIV → lregs' = lift_regs regs' ∧ lmem' = lword_of_word <$> mem') ∧
                  spec_Store_spec_imm regs r1 r2 imm regs' mem mem' v.
  Proof.
    intros Hok Hspec.
    destruct Hspec as [p g b e a ea storev oldv Harg Hallow Hsh Hl -> -> Hinc
                      | p g b e a ea heap_a z π old Harg Hallow Hsh Hsh2 Hlk -> -> Hinc
                      | -> -> Hfail].
    - destruct Hallow as (Hr & Hadd & Hwa & Hwb).
      rewrite lift_regs_lw_llookup in Hr.
      rewrite lookup_fmap in Hl. apply fmap_Some in Hl as (w & Hl & ->).
      lift_regs_simpl.
      eexists _, _; split.
      { intros _; split; [reflexivity|]. rewrite lstore_word_lword_of_word -fmap_insert. reflexivity. }
      eapply spec_Store_spec_success_imm; eauto. by repeat split.
    - exfalso. destruct Hallow as (Hr & Hadd & Hwa & Hwb).
      rewrite lift_regs_lw_llookup in Hr.
      pose proof (Hok _ _ _ _ _ _ Hr Hadd Hwa Hwb). congruence.
    - exists regs, mem; split; [intros ?; discriminate|].
      destruct Hfail as [w Hr Hc | p g b e a Hr | p g b e a Hr Hadd | p g b e a ea Hr Hadd Hb
                        | Hinc | p g b e a ea storev Hr Hadd Hsh Harg Hz].
      all: try rewrite lift_regs_lw_llookup in Hr.
      + rewrite lift_regs_llookup in Hr. apply fmap_Some in Hr as (w' & Hr & ->).
        apply spec_Store_spec_failure_store_imm; first done. by eapply spec_Store_fail_const_imm.
      + apply spec_Store_spec_failure_store_imm; first done. by eapply spec_Store_fail_tag_imm.
      + apply spec_Store_spec_failure_store_imm; first done. by eapply spec_Store_fail_addr_imm.
      + apply spec_Store_spec_failure_store_imm; first done. by eapply spec_Store_fail_bounds_imm.
      + lift_regs_simpl. apply spec_Store_spec_failure_store_imm; first done.
        by eapply spec_Store_fail_invalid_PC_imm.
      + destruct (writeAllowed p && withinBounds b e ea) eqn:HWA.
        2: { apply andb_false_iff in HWA. apply spec_Store_spec_failure_store_imm; first done.
             by eapply spec_Store_fail_bounds_imm. }
        apply andb_true_iff in HWA as [Hwa Hwb].
        pose proof (Hok _ _ _ _ _ _ Hr Hadd Hwa Hwb). congruence.
  Qed.

  Lemma Store_spec_determ regs r1 r2 mem regs1 regs2 mem1 mem2 v1 v2 :
    spec_Store_spec regs r1 r2 regs1 mem mem1 v1 →
    spec_Store_spec regs r1 r2 regs2 mem mem2 v2 →
    v1 = v2 ∧ (v1 = NextIV → regs1 = regs2 ∧ mem1 = mem2).
  Proof. solve_spec_determ_gen spec_Store_failure ltac:(unfold spec_reg_allows_store in * ). Qed.

  Lemma Store_spec_determ_arg regs r1 (r2 : Z + RegName) mem regs1 regs2 mem1 mem2 v1 v2 :
    spec_Store_spec regs r1 r2 regs1 mem mem1 v1 →
    spec_Store_spec regs r1 r2 regs2 mem mem2 v2 →
    v1 = v2 ∧ (v1 = NextIV → regs1 = regs2 ∧ mem1 = mem2).
  Proof. solve_spec_determ_gen spec_Store_failure ltac:(unfold spec_reg_allows_store in * ). Qed.

  Lemma Store_spec_imm_determ regs r1 (r2 : Z + RegName) imm mem regs1 regs2 mem1 mem2 v1 v2 :
    spec_Store_spec_imm regs r1 r2 imm regs1 mem mem1 v1 →
    spec_Store_spec_imm regs r1 r2 imm regs2 mem mem2 v2 →
    v1 = v2 ∧ (v1 = NextIV → regs1 = regs2 ∧ mem1 = mem2).
  Proof. solve_spec_determ_gen spec_Store_failure_imm ltac:(unfold spec_reg_allows_store_imm in * ). Qed.

   Lemma step_store_imm Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 (r2 : Z + RegName) (imm : Z) w mem regs :
    ↑specN ⊆ Ep →
   decodeInstrW w = Store r1 r2 imm →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Store r1 r2 imm) ⊆ dom regs →
   mem !! pc_a = Some w →
   spec_allow_store_map_or_true_imm r1 r2 imm regs mem →

   spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    ([∗ map] a↦w ∈ mem, a ↣ₐ w) ∗
    ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗
    ∃ retv regs' mem',
      ⤇ Seq (of_val retv) ∗
      ⌜ spec_Store_spec_imm regs r1 r2 imm regs' mem mem' retv⌝ ∗
      ([∗ map] a↦w ∈ mem', a ↣ₐ w) ∗
      [∗ map] k↦y ∈ regs', k ↣ᵣ y.
   Proof.
     iIntros (HE Hinstr Hvpc HPC Dregs Hmem_pc HaStore) "(#Hctx & Hj & Hmem & Hmap)".
     iApply (spec_step_exec_2 with "Hctx Hj"); first done.
     iIntros (Φ) "Hφ". iIntros ([[[r sr] m] st] c σ2 Hstep) "[[Hr Hsr] Hm] /=".
     iDestruct (spec_regs_valid_inclSepM with "Hr Hmap") as %Hregs.

     (* Derive necessary register values in r *)
     pose proof (lookup_weaken _ _ _ _ HPC Hregs).
     specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
     odestruct (Hri r1) as [r1v [Hr'1 Hr1]]; first by set_solver+.
     iDestruct (spec_mem_valid_inSepM mem m with "Hm Hmem") as %Hma; eauto.

     eapply step_exec_inv in Hstep; eauto.

     rewrite /exec /= Hr1 /= in Hstep.

     (* Now we start splitting on the different cases in the Store spec, and prove them one at a time *)

     destruct (word_of_argument regs r2) as [ storev | ] eqn:HSV.
     2: {
       destruct r2 as [z | r2].
       - cbn in HSV; inversion HSV.
       - destruct (Hri r2) as [r0v [Hr0 _] ]; first by set_solver+.
         cbn in HSV. rewrite Hr0 in HSV. inversion HSV.
     }
     apply (word_of_arg_mono _ r) in HSV as HSV'; auto. rewrite HSV' in Hstep. cbn in Hstep.

     destruct (is_cap r1v) eqn:Hr1v.
     2: { (* Failure: r1 is not a capability *)
       assert (c = Failed ∧ σ2 = (r, sr, m, st)) as (-> & ->).
       {
         unfold is_cap in Hr1v.
         destruct_word r1v; by simplify_pair_eq.
       }
       iFailWP "Hφ" spec_Store_fail_const_imm.
     }
     destruct r1v as [ | [t p g b e a | ] | | ]; try inversion Hr1v. clear Hr1v.
     destruct t.
     2: {
       inversion Hstep; subst c σ2.
       iFailWP "Hφ" spec_Store_fail_tag_imm.
     }

     destruct (a + imm)%a as [ea|] eqn:Hadd.
     2: { inversion Hstep; subst. iFailWP "Hφ" spec_Store_fail_addr_imm. }
     cbn in Hstep.
     destruct (writeAllowed p && withinBounds b e ea) eqn:HWA.
     2 : { (* Failure: r2 is either not within bounds or doesnt allow reading *)
       inversion Hstep.
       apply andb_false_iff in HWA.
       iFailWP "Hφ" spec_Store_fail_bounds_imm.
     }
     apply andb_true_iff in HWA; destruct HWA as (Hwa & Hwb).

     (* Prove that a is in the memory map now, otherwise we cannot continue *)
     pose proof (spec_allow_store_implies_storev_imm r1 r2 mem regs p g b e a ea imm storev) as (oldv & Hmema); auto.

     (* Given this, prove that a is also present in the memory itself *)
     iDestruct (spec_mem_valid_inSepM mem m ea oldv with "Hm Hmem" ) as %Hma' ; auto.
     iDestruct (spec_mem_avoids_mmio with "Hm") as %Hmmio.
     rewrite (mem_avoids_mmio_not_shadow _ _ _ Hmmio Hma')
       (mem_avoids_mmio_not_revoker _ _ _ Hmmio Hma') /= in Hstep.

     destruct (spec_incrementPC regs ) as [ regs' |] eqn:Hregs'.
     2: { (* Failure: the PC could not be incremented correctly *)
       assert (spec_incrementPC r = None).
       { eapply spec_incrementPC_overflow_mono; first eapply Hregs'; eauto. }
       rewrite spec_incrementPC_fail_updatePC /= in Hstep; auto.
       inversion Hstep.
       cbn; iFrame; iApply "Hφ"; iFrame.
       iPureIntro. eapply spec_Store_spec_failure_store_imm;eauto. by constructor.
     }

     iMod ((spec_mem_update_inSepM _ _ ea) with "Hm Hmem") as "[Hm Hmem]"; eauto.

     (* Success *)
     rewrite /update_mem /= in Hstep.
     eapply (spec_incrementPC_success_updatePC _ sr (<[ea:=store_word p storev]> m) st) in Hregs'
         as (t1 & p1 & g1 & b1 & e1 & a1 & a'1 & a_pc1 & HPC'' & HuPC & ->).
     eapply (updatePC_success_incl _ (<[ea:=store_word p storev]> m)) in HuPC. 2: by eauto.
     rewrite HuPC in Hstep; clear HuPC; inversion Hstep; clear Hstep; subst c σ2; cbn in *.

     iFrame.
     iMod ((spec_regs_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     iFrame. iModIntro. iApply "Hφ". iFrame.
     iPureIntro. eapply spec_Store_spec_success_imm; eauto.
     * split; first exact Hr'1. repeat split; assumption.
     * rewrite /spec_incrementPC /spec_incrementPC_gen. rewrite a_pc1 HPC''.
       Unshelve. all: auto.
   Qed.

   Lemma step_store Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 (r2 : Z + RegName) w mem regs :
    ↑specN ⊆ Ep →
   decodeInstrW w = Store r1 r2 0 →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Store r1 r2 0) ⊆ dom regs →
   mem !! pc_a = Some w →
   spec_allow_store_map_or_true r1 r2 regs mem →
     spec_ctx ∗
     ⤇ Seq (Instr Executable) ∗
     ([∗ map] a↦w ∈ mem, a ↣ₐ w) ∗
     ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
     ={Ep}=∗
     ∃ retv regs' mem',
       ⤇ Seq (of_val retv) ∗
       ⌜ spec_Store_spec regs r1 r2 regs' mem mem' retv⌝ ∗
       ([∗ map] a↦w ∈ mem', a ↣ₐ w) ∗
       [∗ map] k↦y ∈ regs', k ↣ᵣ y.
   Proof.
     iIntros (HE Hinstr Hvpc HPC Dregs Hmem_pc HaStore) "(#Hctx & Hj & Hres)".
     have HaStore0 : spec_allow_store_map_or_true_imm r1 r2 0 regs mem.
     { destruct HaStore as (t & p & g & b & e & a & storev & Hr & Hv & Hmem).
       exists t, p, g, b, e, a, storev. split; first done. split; first done.
       unfold spec_reg_allows_store_imm. rewrite finz_add_0.
       unfold spec_reg_allows_store in Hmem.
       case_decide; case_decide; naive_solver. }
     iMod (step_store_imm with "[$Hctx $Hj $Hres]") as (retv regs' mem') "(Hj & %Hspec & Hmem & Hregs)"; eauto.
     iModIntro. iExists retv, regs', mem'. iFrame. iPureIntro.
     destruct Hspec as [p g b e a ea storev oldv Hv Hr Hm Hm' Hpc | Hm Hfail].
     - destruct Hr as (Hr & Hadd & Hwa & Hwb).
       rewrite finz_add_0 in Hadd. simplify_eq.
       eapply spec_Store_spec_success; eauto. split; first exact Hr. split; assumption.
     - eapply spec_Store_spec_failure_store; eauto.
       destruct Hfail as [wv Hr Hcap | p g b e a Hr | p g b e a Hr Hadd | p g b e a ea Hr Hadd Hbounds | Hpc].
       + eapply spec_Store_fail_const; eauto.
       + eapply spec_Store_fail_tag; eauto.
       + rewrite finz_add_0 in Hadd. discriminate.
       + rewrite finz_add_0 in Hadd. simplify_eq. eapply spec_Store_fail_bounds; eauto.
       + by apply spec_Store_fail_invalid_PC.
   Qed.

  Lemma step_store_success_z_PC E pc_p pc_g pc_b pc_e pc_a pc_a' w z :
    ↑specN ⊆ E →
     decodeInstrW w = Store PC (inl z) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ (WInt z).
  Proof.
    iIntros (HE Hinstr Hvpc Hpca' Hwa) "(#Hctx & Hj & HPC & Hi)".
    iDestruct (spec_map_of_regs_1 with "HPC") as "Hmap".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem".

    iMod (step_store with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { eapply spec_mem_eq_implies_allow_store_map; eauto. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H0 as [Hrr2 _]. simplify_map_eq.
       rewrite spec_memMap_resource_1.
       spec_incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (spec_regs_of_map_1 with "[$Hmap]") as "HPC"; eauto.
       rewrite /store_word (writeAllowed_canStore_int _ _ Hwa).
       iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try spec_incrementPC_inv; simplify_map_eq; eauto.
       - apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [_ Hwb].
         destruct o as [Hwa' | Hbounds]; first congruence.
         apply Is_true_false in Hbounds. done.
       - congruence.
     }
   Qed.

   Lemma step_store_success_reg_PC_store_word E src wsrc pc_p pc_g pc_b pc_e pc_a pc_a' w :
    ↑specN ⊆ E →
     decodeInstrW w = Store PC (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →
     src ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ wsrc
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ store_word pc_p wsrc ∗
    src ↣ᵣ wsrc.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa ?) "(#Hctx & Hj & HPC & Hi & Hsrc)".
     iDestruct (spec_map_of_regs_2 with "HPC Hsrc") as "[Hmap %]".
     iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem".

    iMod (step_store with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply spec_mem_eq_implies_allow_store_map; eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H2 as (Hrdst & Hwa' & Hbounds).
       simplify_map_eq.
       rewrite spec_memMap_resource_1.
       spec_incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto.
       all: iFrame.
     }
     { (* Failure (contradiction) *)
       destruct X; try spec_incrementPC_inv; simplify_map_eq; eauto
       ; try congruence.
       apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [_ Hwb].
       destruct o; last apply Is_true_false in H1; try congruence ; try done.
     }
    Qed.

   Lemma step_store_success_reg_PC_same_store_word E pc_p pc_g pc_b pc_e pc_a pc_a' w w' :
    ↑specN ⊆ E →
     decodeInstrW w = Store PC (inr PC) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ store_word pc_p (WCap true pc_p pc_g pc_b pc_e pc_a).
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa) "(#Hctx & Hj & HPC & Hi)".
     iDestruct (spec_map_of_regs_1 with "HPC") as "Hmap".
     iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem".

    iMod (step_store with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { eapply spec_mem_eq_implies_allow_store_map; eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H0 as [Hrr2 _]. simplify_map_eq.
       rewrite spec_memMap_resource_1.
       spec_incrementPC_inv.
       simplify_map_eq.
       do 2 rewrite insert_insert_eq.
       iDestruct (spec_regs_of_map_1 with "[$Hmap]") as "HPC"; eauto.
       all: iFrame. }
      { (* Failure (contradiction) *)
       destruct X; try spec_incrementPC_inv; simplify_map_eq; eauto; try congruence.
       apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [_ Hwb].
       destruct o; last apply Is_true_false in H; [congruence| done].
     }
    Qed.

   Lemma step_store_success_same E pc_p pc_g pc_b pc_e pc_a pc_a' w dst z w'
         p g b e :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inl z) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     dst ≠ cnull ->
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e pc_a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ (WInt z) ∗
    dst ↣ᵣ WCap true p g b e pc_a.
    Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb ?) "(#Hctx & Hj & HPC & Hi & Hdst)".
     have Hstore_word : store_word p (WInt z) = WInt z.
     { apply store_word_canStore, writeAllowed_canStore_int, Hwa. }
     iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
     iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem".

    iMod (step_store _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply spec_mem_eq_implies_allow_store_map; eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H2 as [? _]; simplify_map_eq.
       rewrite spec_memMap_resource_1.
       spec_incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto.
       all: try rewrite Hstore_word; iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try spec_incrementPC_inv; simplify_map_eq; eauto.
       - destruct o; congruence.
       - congruence.
     }
     Qed.

   Lemma step_store_success_reg_same'_store_word E pc_p pc_g pc_b pc_e pc_a pc_a' w dst
         p g b e :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr dst) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     dst ≠ cnull ->
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e pc_a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ store_word p (WCap true p g b e pc_a) ∗
    dst ↣ᵣ WCap true p g b e pc_a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb ?) "(#Hctx & Hj & HPC & Hi & Hdst)".
     iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
     iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem".

    iMod (step_store _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply spec_mem_eq_implies_allow_store_map; eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H2 as [? _]; simplify_map_eq.
       rewrite spec_memMap_resource_1.
       spec_incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try spec_incrementPC_inv; simplify_map_eq; eauto; try congruence.
       destruct o; congruence.
     }
   Qed.

   Lemma step_store_success_reg_same_a_store_word E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src
         p g b e w'' :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     src ≠ cnull ->
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e pc_a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ store_word p w'' ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e pc_a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb ??) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
     iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
     iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem".

    iMod (step_store _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply spec_mem_eq_implies_allow_store_map; eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H5 as [? _]; simplify_map_eq.
       rewrite spec_memMap_resource_1.
       spec_incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (spec_regs_of_map_3 with "[$Hmap]") as "[HPC [Hsrc Hdst] ]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try spec_incrementPC_inv; simplify_map_eq; eauto; try congruence.
       destruct o; congruence.
     }
   Qed.

   Lemma step_store_success_reg_store_word E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src w'
         p g b e a w'' :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →
     src ≠ cnull ->
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ store_word p w''.
    Proof.
      iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb ??) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst & Hsrca)".
    iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iMod (step_store _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply spec_mem_neq_implies_allow_store_map with (a := a); eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H6 as [? _]; simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (spec_memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       spec_incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_eq.
       iDestruct (spec_regs_of_map_3 with "[$Hmap]") as "[HPC [Hsrc Hdst] ]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try spec_incrementPC_inv; simplify_map_eq; eauto; try congruence.
       destruct o; congruence.
     }
    Qed.

   Lemma step_store_success_reg_same_store_word E pc_p pc_g pc_b pc_e pc_a pc_a' w dst w'
         p g b e a :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr dst) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ store_word p (WCap true p g b e a).
   Proof.
    iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb ?) "(#Hctx & Hj & HPC & Hi & Hdst & Hsrca)".
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iMod (step_store _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply spec_mem_neq_implies_allow_store_map with (a := a); eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H3 as [Hrr2 _]. simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (spec_memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       spec_incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hdst]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try spec_incrementPC_inv; simplify_map_eq; eauto; try congruence.
       destruct o; congruence.
     }
    Qed.

   Lemma step_store_success_z E pc_p pc_g pc_b pc_e pc_a pc_a' w dst z w'
         p g b e a :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inl z) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →
     dst ≠ cnull ->
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ WInt z.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb ?) "(#Hctx & Hj & HPC & Hi & Hdst & Hsrca)".
     have Hstore_word : store_word p (WInt z) = WInt z.
     { apply store_word_canStore, writeAllowed_canStore_int, Hwa. }
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iMod (step_store _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply spec_mem_neq_implies_allow_store_map with (a := a); eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H3 as [Hrr2 _]. simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (spec_memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       spec_incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hdst]"; eauto.
       all: try rewrite Hstore_word; iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try spec_incrementPC_inv; simplify_map_eq; eauto; last congruence.
       - destruct o; congruence.
     }
    Qed.

   Lemma step_store_success_reg_PC E src wsrc pc_p pc_g pc_b pc_e pc_a pc_a' w :
    ↑specN ⊆ E →
     decodeInstrW w = Store PC (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →
     canStore pc_p wsrc = true →
     src ≠ cnull →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ wsrc
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ wsrc ∗
    src ↣ᵣ wsrc.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa HcanStore Hsrc) "(#Hctx & Hj & Hres)".
     iMod (step_store_success_reg_PC_store_word with "[$Hctx $Hj $Hres]") as "(Hj & HPC & Hi & Hsrc)"; eauto.
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Hi".
     iModIntro. iFrame.
   Qed.

   Lemma step_store_success_reg_PC_same E pc_p pc_g pc_b pc_e pc_a pc_a' w w' :
    ↑specN ⊆ E →
     decodeInstrW w = Store PC (inr PC) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →
     canStore pc_p (WCap true pc_p pc_g pc_b pc_e pc_a) = true →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ WCap true pc_p pc_g pc_b pc_e pc_a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa HcanStore) "(#Hctx & Hj & Hres)".
     iMod (step_store_success_reg_PC_same_store_word with "[$Hctx $Hj $Hres]") as "(Hj & HPC & Hi)"; eauto.
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Hi".
     iModIntro. iFrame.
   Qed.

   Lemma step_store_success_reg_same' E pc_p pc_g pc_b pc_e pc_a pc_a' w dst
       p g b e :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr dst) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     canStore p (WCap true p g b e pc_a) = true →
     dst ≠ cnull →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e pc_a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ WCap true p g b e pc_a ∗
    dst ↣ᵣ WCap true p g b e pc_a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb HcanStore Hdst) "(#Hctx & Hj & Hres)".
     iMod (step_store_success_reg_same'_store_word with "[$Hctx $Hj $Hres]") as "(Hj & HPC & Hi & Hdst)"; eauto.
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Hi".
     iModIntro. iFrame.
   Qed.

   Lemma step_store_success_reg_same_a E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src
       p g b e w'' :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     canStore p w'' = true →
     src ≠ cnull → dst ≠ cnull →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e pc_a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w'' ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e pc_a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb HcanStore Hsrc Hdst) "(#Hctx & Hj & Hres)".
     iMod (step_store_success_reg_same_a_store_word with "[$Hctx $Hj $Hres]") as "(Hj & HPC & Hi & Hsrc & Hdst)"; eauto.
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Hi".
     iModIntro. iFrame.
   Qed.

   Lemma step_store_success_reg E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src w'
       p g b e a w'' :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →
     canStore p w'' = true →
     src ≠ cnull → dst ≠ cnull →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ w''.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb HcanStore Hsrc Hdst) "(#Hctx & Hj & Hres)".
     iMod (step_store_success_reg_store_word with "[$Hctx $Hj $Hres]") as "(Hj & HPC & Hi & Hsrc & Hdst & Ha)"; eauto.
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Ha".
     iModIntro. iFrame.
   Qed.

   Lemma step_store_success_reg_same E pc_p pc_g pc_b pc_e pc_a pc_a' w dst w'
       p g b e a :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr dst) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →
     canStore p (WCap true p g b e a) = true →
     dst ≠ cnull →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ WCap true p g b e a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb HcanStore Hdst) "(#Hctx & Hj & Hres)".
     iMod (step_store_success_reg_same_store_word with "[$Hctx $Hj $Hres]") as "(Hj & HPC & Hi & Hdst & Ha)"; eauto.
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Ha".
     iModIntro. iFrame.
   Qed.

   Lemma step_store_fail_reg_not_cap E pc_p pc_g pc_b pc_e pc_a w
     dst src wdst wstore :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     is_cap wdst = false ->
     src ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ wstore ∗
    dst ↣ᵣ wdst
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
    Proof.
      iIntros (HE Hinstr Hvpc Hnot_cap ?) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
    iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem"; auto.

    iMod (step_store _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /spec_allow_store_map_or_true.
      eexists true,_,_,_,_,_,_; eauto.
      simplify_map_eq.
      split; [|split]; eauto.
      - rewrite /spec_read_reg_inr; simplify_map_eq.
        destruct wdst as [| [] | |]; cbn in Hnot_cap; done.
      - rewrite /spec_reg_allows_store; simplify_map_eq.
        rewrite decide_False; auto.
        intros [].
        destruct (decide (dst = cnull)); first done.
        destruct wdst as [| [] | |]; cbn in Hnot_cap; simplify_eq.
    }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /spec_reg_allows_store in H4.
       destruct H4 as (? & ? & ?); simplify_map_eq.
       destruct (decide (dst = cnull)); first done.
       simplify_map_eq.
     }
     by iModIntro; iFrame.
     Unshelve. all: done.
    Qed.

    Lemma step_store_fail_z_not_cap E pc_p pc_g pc_b pc_e pc_a w
     dst z wdst :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inl z) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     is_cap wdst = false ->
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ wdst
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
    Proof.
      iIntros (HE Hinstr Hvpc Hnot_cap ?) "(#Hctx & Hj & HPC & Hi & Hdst)".
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem"; auto.

    iMod (step_store _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /spec_allow_store_map_or_true.
      eexists true,_,_,_,_,_,_; eauto.
      simplify_map_eq.
      split; [|split]; eauto.
      - rewrite /spec_read_reg_inr; simplify_map_eq.
        destruct wdst as [| [] | |]; cbn in Hnot_cap; done.
      - rewrite /spec_reg_allows_store; simplify_map_eq.
        rewrite decide_False; auto.
        intros [].
        destruct (decide (dst = cnull)); first done.
        destruct wdst as [| [] | |]; cbn in Hnot_cap; simplify_eq.
    }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /spec_reg_allows_store in H2.
       simplify_map_eq.
       destruct H2 as (? & ? & ?); simplify_map_eq.
     }
     by iModIntro; iFrame.
     Unshelve. all: done.
    Qed.

   Lemma step_store_fail_reg_perm E pc_p pc_g pc_b pc_e pc_a w dst src
         p g b e a w'' :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     writeAllowed p = false ->
     src ≠ cnull ->
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
    Proof.
      iIntros (HE Hinstr Hvpc Hwa ??) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
    iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem"; auto.

    iMod (step_store _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /spec_allow_store_map_or_true.
      eexists true,p,g,b,e,a,w''.
      split.
      { rewrite /spec_read_reg_inr.
        by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert_eq.
      }
      split.
      { rewrite /word_of_argument.
        by simplify_map_eq.
      }
      rewrite /spec_reg_allows_store.
      rewrite Hwa.
      rewrite decide_False; auto.
      intro; naive_solver.
      }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /spec_reg_allows_store in H5.
       destruct H5 as (? & Hwa' & ?); simplify_map_eq.
       congruence.
     }
     { (* Failure (contradiction) *)
       destruct X; try spec_incrementPC_inv; simplify_map_eq; eauto; by iModIntro; iFrame.
     }
    Qed.

    Lemma step_store_fail_z_perm E pc_p pc_g pc_b pc_e pc_a w dst
         p g b e a z :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inl z) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     writeAllowed p = false ->
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
    Proof.
      iIntros (HE Hinstr Hvpc HcanStore ?) "(#Hctx & Hj & HPC & Hi & Hdst)".
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem"; auto.

    iMod (step_store _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /spec_allow_store_map_or_true.
      eexists true,p,g,b,e,a,_.
      split.
      { rewrite /spec_read_reg_inr.
        by rewrite lookup_insert_ne // lookup_insert_eq.
      }
      split.
      { rewrite /word_of_argument.
        eauto.
      }
      rewrite /spec_reg_allows_store.
      rewrite HcanStore.
      rewrite decide_False; auto.
      intro; naive_solver.
      }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /spec_reg_allows_store in H2.
       destruct H2 as (? & Hwa' & ?); simplify_map_eq.
       congruence.
     }
     { (* Failure (contradiction) *)
       destruct X; try spec_incrementPC_inv; simplify_map_eq; eauto; by iModIntro; iFrame.
     }
    Qed.

   Lemma step_store_fail_reg E pc_p pc_g pc_b pc_e pc_a w dst src
         p g b e a w'' :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     withinBounds b e a = false →
     src ≠ cnull ->
     dst ≠ cnull ->
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr Failed).
    Proof.
      iIntros (HE Hinstr Hvpc Hwb ??) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
    iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem"; auto.

    iMod (step_store _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /spec_allow_store_map_or_true.
      eexists true,p,g,b,e,a,w''.
      split.
      { rewrite /spec_read_reg_inr.
        by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert_eq.
      }
      split.
      { rewrite /word_of_argument.
        by simplify_map_eq.
      }
      rewrite /spec_reg_allows_store.
      rewrite Hwb.
      rewrite decide_False; auto.
      intro; naive_solver.
      }
    iDestruct "H" as (retv regs' mem') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /spec_reg_allows_store in H5.
       destruct H5 as (? & ? & Hbounds); simplify_map_eq.
       by rewrite Hbounds in Hwb.
     }
     { (* Failure (contradiction) *)
       destruct X; try spec_incrementPC_inv; simplify_map_eq; eauto; by iModIntro.
     }
    Qed.

    Lemma step_store_fail_z E pc_p pc_g pc_b pc_e pc_a w dst
         p g b e a z :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inl z) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     withinBounds b e a = false →
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr Failed).
    Proof.
      iIntros (HE Hinstr Hvpc Hwb ?) "(#Hctx & Hj & HPC & Hi & Hdst)".
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem"; auto.

    iMod (step_store _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /spec_allow_store_map_or_true.
      eexists true,p,g,b,e,a,_.
      split.
      { rewrite /spec_read_reg_inr.
        by rewrite lookup_insert_ne // lookup_insert_eq.
      }
      split.
      { rewrite /word_of_argument. eauto.
      }
      rewrite /spec_reg_allows_store.
      rewrite Hwb.
      rewrite decide_False; auto.
      intro; naive_solver.
      }
    iDestruct "H" as (retv regs' mem') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /spec_reg_allows_store in H2.
       destruct H2 as (? & ? & Hbounds); simplify_map_eq.
       by rewrite Hbounds in Hwb.
     }
     { (* Failure (contradiction) *)
       destruct X; try spec_incrementPC_inv; simplify_map_eq; eauto; by iModIntro.
     }
    Qed.

  Lemma step_store_fail_tag E pc_p pc_g pc_b pc_e pc_a
      w dst (src : Z + RegName) regs wa :
    ↑specN ⊆ E →
    decodeInstrW w = Store dst src 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !!ᵣ dst = Some wa →
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
    destruct wa as [| [t p g b e a|] | |]; cbn in Htag; subst; cbn.
    all: destruct (word_of_argument r src); done.
  Qed.

   Lemma step_store_success_reg_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src w'
         p g b e a ea (imm : Z) w'' :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     src ≠ cnull ->
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ store_word p w''.
    Proof.
      iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd ??) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst & Hsrca)".
    iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply spec_mem_neq_implies_allow_store_map_imm with (a := a) (ea := ea); eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H6 as [? [Hadd2 _]]; simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (spec_memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       spec_incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_eq.
       iDestruct (spec_regs_of_map_3 with "[$Hmap]") as "[HPC [Hsrc Hdst] ]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try spec_incrementPC_inv; simplify_map_eq; eauto; try congruence; try (destruct o; congruence).

     }
    Qed.

   Lemma step_store_success_reg_same_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst w'
         p g b e a ea (imm : Z) :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr dst) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ store_word p (WCap true p g b e a).
   Proof.
    iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd ?) "(#Hctx & Hj & HPC & Hi & Hdst & Hsrca)".
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply spec_mem_neq_implies_allow_store_map_imm with (a := a) (ea := ea); eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H3 as [Hrr2 [Hadd2 _]]. simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (spec_memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       spec_incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hdst]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try spec_incrementPC_inv; simplify_map_eq; eauto; try congruence; try (destruct o; congruence).

     }
    Qed.

   Lemma step_store_success_z_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst z w'
         p g b e a ea (imm : Z) :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ WInt z.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd ?) "(#Hctx & Hj & HPC & Hi & Hdst & Hsrca)".
     have Hstore_word : store_word p (WInt z) = WInt z.
     { apply store_word_canStore, writeAllowed_canStore_int, Hwa. }
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply spec_mem_neq_implies_allow_store_map_imm with (a := a) (ea := ea); eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H3 as [Hrr2 [Hadd2 _]]. simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (spec_memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       spec_incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hdst]"; eauto.
       all: try rewrite Hstore_word; iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try spec_incrementPC_inv; simplify_map_eq; eauto; last congruence.
       - destruct o; congruence.
     }
    Qed.

   Lemma step_store_success_reg_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src w'
       p g b e a ea (imm : Z) w'' :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     canStore p w'' = true →
     src ≠ cnull → dst ≠ cnull →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ w''.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd HcanStore Hsrc Hdst) "(#Hctx & Hj & Hres)".
     iMod (step_store_success_reg_store_word_imm with "[$Hctx $Hj $Hres]") as "(Hj & HPC & Hi & Hsrc & Hdst & Ha)"; eauto.
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Ha".
     iModIntro. iFrame.
   Qed.

   Lemma step_store_success_same_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst z
         p g b e a (imm : Z) :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     (a + imm)%a = Some pc_a →
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ (WInt z) ∗
    dst ↣ᵣ WCap true p g b e a.
    Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd ?) "(#Hctx & Hj & HPC & Hi & Hdst)".
     have Hstore_word : store_word p (WInt z) = WInt z.
     { apply store_word_canStore, writeAllowed_canStore_int, Hwa. }
     iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
     iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem".

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply spec_mem_eq_implies_allow_store_map_imm; eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H2 as [? [Hadd2 _]]; simplify_map_eq.
       rewrite spec_memMap_resource_1.
       spec_incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto.
       all: try rewrite Hstore_word; iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try spec_incrementPC_inv; simplify_map_eq; eauto.
       - destruct o; congruence.
       - congruence.
     }
     Qed.

   Lemma step_store_success_reg_same'_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst
         p g b e a (imm : Z) :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr dst) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     (a + imm)%a = Some pc_a →
     dst ≠ cnull ->
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ store_word p (WCap true p g b e a) ∗
    dst ↣ᵣ WCap true p g b e a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd ?) "(#Hctx & Hj & HPC & Hi & Hdst)".
     iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
     iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem".

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply spec_mem_eq_implies_allow_store_map_imm; eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H2 as [? [Hadd2 _]]; simplify_map_eq.
       rewrite spec_memMap_resource_1.
       spec_incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try spec_incrementPC_inv; simplify_map_eq; eauto; try congruence; try (destruct o; congruence).

     }
   Qed.

   Lemma step_store_success_reg_same_a_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src
         p g b e a (imm : Z) w'' :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     (a + imm)%a = Some pc_a →
     src ≠ cnull ->
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ store_word p w'' ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd ??) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
     iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
     iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem".

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply spec_mem_eq_implies_allow_store_map_imm; eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H5 as [? [Hadd2 _]]; simplify_map_eq.
       rewrite spec_memMap_resource_1.
       spec_incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (spec_regs_of_map_3 with "[$Hmap]") as "[HPC [Hsrc Hdst] ]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try spec_incrementPC_inv; simplify_map_eq; eauto; try congruence; try (destruct o; congruence).

     }
   Qed.

   Lemma step_store_success_reg_same'_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst
       p g b e a (imm : Z) :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr dst) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     (a + imm)%a = Some pc_a →
     canStore p (WCap true p g b e a) = true →
     dst ≠ cnull →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ WCap true p g b e a ∗
    dst ↣ᵣ WCap true p g b e a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd HcanStore Hdst) "(#Hctx & Hj & Hres)".
     iMod (step_store_success_reg_same'_store_word_imm with "[$Hctx $Hj $Hres]") as "(Hj & HPC & Hi & Hdst)"; eauto.
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Hi".
     iModIntro. iFrame.
   Qed.

   Lemma step_store_success_reg_same_a_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src
       p g b e a (imm : Z) w'' :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     (a + imm)%a = Some pc_a →
     canStore p w'' = true →
     src ≠ cnull → dst ≠ cnull →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w'' ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd HcanStore Hsrc Hdst) "(#Hctx & Hj & Hres)".
     iMod (step_store_success_reg_same_a_store_word_imm with "[$Hctx $Hj $Hres]") as "(Hj & HPC & Hi & Hsrc & Hdst)"; eauto.
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Hi".
     iModIntro. iFrame.
   Qed.

   Lemma step_store_fail_reg_not_cap_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a w
     dst src wdst wstore :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     is_cap wdst = false ->
     src ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ wstore ∗
    dst ↣ᵣ wdst
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
    Proof.
      iIntros (HE Hinstr Hvpc Hnot_cap ?) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
    iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem"; auto.

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /spec_allow_store_map_or_true_imm.
      eexists true,_,_,_,_,_,_; eauto.
      simplify_map_eq.
      split; [|split]; eauto.
      - rewrite /spec_read_reg_inr; simplify_map_eq.
        destruct wdst as [| [] | |]; cbn in Hnot_cap; done.
      - rewrite /spec_reg_allows_store_imm.
        destruct (_ + imm)%a; simpl; last done. simplify_map_eq.
        rewrite decide_False; auto.
        intros [].
        destruct (decide (dst = cnull)); first done.
        destruct wdst as [| [] | |]; cbn in Hnot_cap; simplify_eq.
    }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /spec_reg_allows_store_imm in H4.
       destruct H4 as (? & ? & ? & ?); simplify_map_eq.
       destruct (decide (dst = cnull)); first done.
       simplify_map_eq.
     }
     by iModIntro; iFrame.
     Unshelve. all: done.
    Qed.

    Lemma step_store_fail_z_not_cap_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a w
     dst z wdst :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     is_cap wdst = false ->
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ wdst
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
    Proof.
      iIntros (HE Hinstr Hvpc Hnot_cap ?) "(#Hctx & Hj & HPC & Hi & Hdst)".
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem"; auto.

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /spec_allow_store_map_or_true_imm.
      eexists true,_,_,_,_,_,_; eauto.
      simplify_map_eq.
      split; [|split]; eauto.
      - rewrite /spec_read_reg_inr; simplify_map_eq.
        destruct wdst as [| [] | |]; cbn in Hnot_cap; done.
      - rewrite /spec_reg_allows_store_imm.
        destruct (_ + imm)%a; simpl; last done. simplify_map_eq.
        rewrite decide_False; auto.
        intros [].
        destruct (decide (dst = cnull)); first done.
        destruct wdst as [| [] | |]; cbn in Hnot_cap; simplify_eq.
    }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /spec_reg_allows_store_imm in H2.
       simplify_map_eq.
       destruct H2 as (? & ? & ? & ?); simplify_map_eq.
     }
     by iModIntro; iFrame.
     Unshelve. all: done.
    Qed.

   Lemma step_store_fail_reg_perm_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a w dst src
         p g b e a w'' :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     writeAllowed p = false ->
     src ≠ cnull ->
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
    Proof.
      iIntros (HE Hinstr Hvpc Hwa ??) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
    iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem"; auto.

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /spec_allow_store_map_or_true_imm.
      eexists true,p,g,b,e,a,w''.
      split.
      { rewrite /spec_read_reg_inr.
        by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert_eq.
      }
      split.
      { rewrite /word_of_argument.
        by simplify_map_eq.
      }
      rewrite /spec_reg_allows_store_imm.
      destruct (a + imm)%a eqn:Haddr; simpl; last done.
      rewrite Hwa.
      rewrite decide_False; auto.
      intro; naive_solver.
      }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /spec_reg_allows_store_imm in H5.
       destruct H5 as (? & ? & Hwa' & ?); simplify_map_eq.
       congruence.
     }
     { (* Failure (contradiction) *)
       destruct X; try spec_incrementPC_inv; simplify_map_eq; eauto; by iModIntro; iFrame.
     }
    Qed.

    Lemma step_store_fail_z_perm_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a w dst
         p g b e a z :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     writeAllowed p = false ->
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
    Proof.
      iIntros (HE Hinstr Hvpc HcanStore ?) "(#Hctx & Hj & HPC & Hi & Hdst)".
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem"; auto.

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /spec_allow_store_map_or_true_imm.
      eexists true,p,g,b,e,a,_.
      split.
      { rewrite /spec_read_reg_inr.
        by rewrite lookup_insert_ne // lookup_insert_eq.
      }
      split.
      { rewrite /word_of_argument.
        eauto.
      }
      rewrite /spec_reg_allows_store_imm.
      destruct (a + imm)%a eqn:Haddr; simpl; last done.
      rewrite HcanStore.
      rewrite decide_False; auto.
      intro; naive_solver.
      }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /spec_reg_allows_store_imm in H2.
       destruct H2 as (? & ? & Hwa' & ?); simplify_map_eq.
       congruence.
     }
     { (* Failure (contradiction) *)
       destruct X; try spec_incrementPC_inv; simplify_map_eq; eauto; by iModIntro; iFrame.
     }
    Qed.

   Lemma step_store_fail_reg_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a w dst src
         p g b e a ea w'' :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (a + imm)%a = Some ea →
     withinBounds b e ea = false →
     src ≠ cnull ->
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
    Proof.
      iIntros (HE Hinstr Hvpc Hadd Hwb ??) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
    iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem"; auto.

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /spec_allow_store_map_or_true_imm.
      eexists true,p,g,b,e,a,w''.
      split.
      { rewrite /spec_read_reg_inr.
        by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert_eq.
      }
      split.
      { rewrite /word_of_argument.
        by simplify_map_eq.
      }
      rewrite /spec_reg_allows_store_imm.
      rewrite Hadd Hwb.
      rewrite decide_False; auto.
      intro; naive_solver.
      }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /spec_reg_allows_store_imm in H5.
       destruct H5 as (? & Haddr & ? & Hbounds); simplify_map_eq.
       by rewrite Hbounds in Hwb.
     }
     { (* Failure (contradiction) *)
       destruct X; try spec_incrementPC_inv; simplify_map_eq; eauto; by iModIntro; iFrame.
     }
    Qed.

    Lemma step_store_fail_z_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a w dst
         p g b e a ea z :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (a + imm)%a = Some ea →
     withinBounds b e ea = false →
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
    Proof.
      iIntros (HE Hinstr Hvpc Hadd Hwb ?) "(#Hctx & Hj & HPC & Hi & Hdst)".
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem"; auto.

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /spec_allow_store_map_or_true_imm.
      eexists true,p,g,b,e,a,_.
      split.
      { rewrite /spec_read_reg_inr.
        by rewrite lookup_insert_ne // lookup_insert_eq.
      }
      split.
      { rewrite /word_of_argument. eauto.
      }
      rewrite /spec_reg_allows_store_imm.
      rewrite Hadd Hwb.
      rewrite decide_False; auto.
      intro; naive_solver.
      }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /spec_reg_allows_store_imm in H2.
       destruct H2 as (? & Haddr & ? & Hbounds); simplify_map_eq.
       by rewrite Hbounds in Hwb.
     }
     { (* Failure (contradiction) *)
       destruct X; try spec_incrementPC_inv; simplify_map_eq; eauto; by iModIntro; iFrame.
     }
    Qed.

  Lemma step_store_fail_tag_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a
      w dst (src : Z + RegName) regs wa :
    ↑specN ⊆ E →
    decodeInstrW w = Store dst src imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !!ᵣ dst = Some wa →
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
    destruct wa as [| [t p g b e a|] | |]; cbn in Htag; subst; cbn.
    all: destruct (word_of_argument r src); done.
  Qed.

   Lemma step_store_success_reg_PC_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w src w'
         ea (imm : Z) w'' :
    ↑specN ⊆ E →
      decodeInstrW w = Store PC (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true → withinBounds pc_b pc_e ea = true →
     (pc_a + imm)%a = Some ea →
     src ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    ea ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    ea ↣ₐ store_word pc_p w''.
    Proof.
      iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd ?) "(#Hctx & Hj & HPC & Hi & Hsrc & Hsrca)".
    iDestruct (spec_map_of_regs_2 with "HPC Hsrc") as "[Hmap %]".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply spec_mem_neq_implies_allow_store_map_imm with (a := pc_a) (ea := ea); eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [p0 g0 b0 e0 a0 ea0 storev oldv Harg Hallow Hold Hmem' Hinc | Hmem' Hfail].
     { (* Success *)
       iModIntro.
       destruct Hallow as [Hrr2 [Hadd2 _]]; simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (spec_memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       spec_incrementPC_inv.
       simplify_map_eq.
       try rewrite insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try spec_incrementPC_inv; simplify_map_eq; eauto; try congruence; try (destruct o; congruence).

     }
    Qed.

   Lemma step_store_success_reg_PC_same_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w w'
         ea (imm : Z) :
    ↑specN ⊆ E →
     decodeInstrW w = Store PC (inr PC) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true → withinBounds pc_b pc_e ea = true →
     (pc_a + imm)%a = Some ea →

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    ea ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    ea ↣ₐ store_word pc_p (WCap true pc_p pc_g pc_b pc_e pc_a).
   Proof.
    iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd) "(#Hctx & Hj & HPC & Hi & Hsrca)".
    iDestruct (spec_map_of_regs_1 with "HPC") as "Hmap".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { eapply spec_mem_neq_implies_allow_store_map_imm with (a := pc_a) (ea := ea); eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [p0 g0 b0 e0 a0 ea0 storev oldv Harg Hallow Hold Hmem' Hinc | Hmem' Hfail].
     { (* Success *)
       iModIntro.
       destruct Hallow as [Hrr2 [Hadd2 _]]. simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (spec_memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       spec_incrementPC_inv.
       simplify_map_eq.
       try rewrite insert_insert_eq.
       iDestruct (spec_regs_of_map_1 with "[$Hmap]") as "HPC"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try spec_incrementPC_inv; simplify_map_eq; eauto; try congruence; try (destruct o; congruence).

     }
    Qed.

   Lemma step_store_success_z_PC_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w z w'
         ea (imm : Z) :
    ↑specN ⊆ E →
     decodeInstrW w = Store PC (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true → withinBounds pc_b pc_e ea = true →
     (pc_a + imm)%a = Some ea →

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    ea ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    ea ↣ₐ WInt z.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd) "(#Hctx & Hj & HPC & Hi & Hsrca)".
     have Hstore_word : store_word pc_p (WInt z) = WInt z.
     { apply store_word_canStore, writeAllowed_canStore_int, Hwa. }
    iDestruct (spec_map_of_regs_1 with "HPC") as "Hmap".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { eapply spec_mem_neq_implies_allow_store_map_imm with (a := pc_a) (ea := ea); eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [p0 g0 b0 e0 a0 ea0 storev oldv Harg Hallow Hold Hmem' Hinc | Hmem' Hfail].
     { (* Success *)
       iModIntro.
       destruct Hallow as [Hrr2 [Hadd2 _]]. simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (spec_memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       spec_incrementPC_inv.
       simplify_map_eq.
       try rewrite insert_insert_eq.
       iDestruct (spec_regs_of_map_1 with "[$Hmap]") as "HPC"; eauto.
       all: try rewrite Hstore_word; iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try spec_incrementPC_inv; simplify_map_eq; eauto; last congruence.
       - destruct o; congruence.
     }
    Qed.

Lemma step_store_fail_reg_overflow_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a w dst src
         p g b e a w'' :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (a + imm)%a = None →
     src ≠ cnull ->
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
    Proof.
      iIntros (HE Hinstr Hvpc Hadd ??) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
    iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem"; auto.

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /spec_allow_store_map_or_true_imm.
      eexists true,p,g,b,e,a,w''.
      split.
      { rewrite /spec_read_reg_inr.
        by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert_eq.
      }
      split.
      { rewrite /word_of_argument.
        by simplify_map_eq.
      }
      rewrite /spec_reg_allows_store_imm.
      by rewrite Hadd.
      }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /spec_reg_allows_store_imm in H5.
       destruct H5 as (? & Haddr & ? & Hbounds); simplify_map_eq.
     }
     { (* Failure (contradiction) *)
       destruct X; try spec_incrementPC_inv; simplify_map_eq; eauto; by iModIntro; iFrame.
     }
    Qed.

Lemma step_store_fail_z_overflow_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a w dst
         p g b e a z :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (a + imm)%a = None →
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
    Proof.
      iIntros (HE Hinstr Hvpc Hadd ?) "(#Hctx & Hj & HPC & Hi & Hdst)".
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem"; auto.

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /spec_allow_store_map_or_true_imm.
      eexists true,p,g,b,e,a,_.
      split.
      { rewrite /spec_read_reg_inr.
        by rewrite lookup_insert_ne // lookup_insert_eq.
      }
      split.
      { rewrite /word_of_argument. eauto.
      }
      rewrite /spec_reg_allows_store_imm.
      by rewrite Hadd.
      }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /spec_reg_allows_store_imm in H2.
       destruct H2 as (? & Haddr & ? & Hbounds); simplify_map_eq.
     }
     { (* Failure (contradiction) *)
       destruct X; try spec_incrementPC_inv; simplify_map_eq; eauto; by iModIntro; iFrame.
     }
    Qed.

   Lemma step_store_success_reg_same_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst w'
         p g b e a ea (imm : Z) :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr dst) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     dst ≠ cnull ->

     canStore p (WCap true p g b e a) = true →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ WCap true p g b e a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd ? HcanStore) "(#Hctx & Hj & Hres)".
     iMod (step_store_success_reg_same_store_word_imm with "[$Hctx $Hj $Hres]") as "[Hj Hpost]"; eauto.
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Hpost".
     iModIntro. iFrame.
   Qed.

   Lemma step_store_success_reg_PC_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w src w'
         ea (imm : Z) w'' :
    ↑specN ⊆ E →
      decodeInstrW w = Store PC (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true → withinBounds pc_b pc_e ea = true →
     (pc_a + imm)%a = Some ea →
     src ≠ cnull ->

     canStore pc_p (w'') = true →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    ea ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    ea ↣ₐ w''.
    Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd ? HcanStore) "(#Hctx & Hj & Hres)".
     iMod (step_store_success_reg_PC_store_word_imm with "[$Hctx $Hj $Hres]") as "[Hj Hpost]"; eauto.
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Hpost".
     iModIntro. iFrame.
   Qed.

   Lemma step_store_success_reg_PC_same_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w w'
         ea (imm : Z) :
    ↑specN ⊆ E →
     decodeInstrW w = Store PC (inr PC) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true → withinBounds pc_b pc_e ea = true →
     (pc_a + imm)%a = Some ea →

     canStore pc_p (WCap true pc_p pc_g pc_b pc_e pc_a) = true →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    ea ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    ea ↣ₐ WCap true pc_p pc_g pc_b pc_e pc_a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd HcanStore) "(#Hctx & Hj & Hres)".
     iMod (step_store_success_reg_PC_same_store_word_imm with "[$Hctx $Hj $Hres]") as "[Hj Hpost]"; eauto.
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Hpost".
     iModIntro. iFrame.
   Qed.

   Lemma step_store_success_reg_fromPC_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst w'
         p g b e a ea (imm : Z) :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr PC) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ store_word p (WCap true pc_p pc_g pc_b pc_e pc_a).
   Proof.
    iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd ?) "(#Hctx & Hj & HPC & Hi & Hdst & Hsrca)".
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply spec_mem_neq_implies_allow_store_map_imm with (a := a) (ea := ea); eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H3 as [Hrr2 [Hadd2 _]]. simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (spec_memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       spec_incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hdst]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try spec_incrementPC_inv; simplify_map_eq; eauto; try congruence; try (destruct o; congruence).

     }
    Qed.

   Lemma step_store_success_reg_fromPC_same_a_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst
         p g b e a (imm : Z) :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr PC) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     (a + imm)%a = Some pc_a →
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ store_word p (WCap true pc_p pc_g pc_b pc_e pc_a) ∗
    dst ↣ᵣ WCap true p g b e a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd ?) "(#Hctx & Hj & HPC & Hi & Hdst)".
     iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
     iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem".

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply spec_mem_eq_implies_allow_store_map_imm; eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H2 as [? [Hadd2 _]]; simplify_map_eq.
       rewrite spec_memMap_resource_1.
       spec_incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try spec_incrementPC_inv; simplify_map_eq; eauto; try congruence; try (destruct o; congruence).

     }
   Qed.

Lemma step_store_success_z_PC_same_a_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_a' w z :
    ↑specN ⊆ E →
     decodeInstrW w = Store PC (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →

     (pc_a + imm)%a = Some pc_a →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ (WInt z).
  Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hadd) "(#Hctx & Hj & Hres)".
     have Himm : imm = 0 by solve_finz. subst imm.
     iApply (step_store_success_z_PC with "[$Hctx $Hj $Hres]"); eauto.
   Qed.

Lemma step_store_success_reg_PC_same_a_store_word_imm E (imm : Z) src wsrc pc_p pc_g pc_b pc_e pc_a pc_a' w :
    ↑specN ⊆ E →
     decodeInstrW w = Store PC (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →
     src ≠ cnull ->

     (pc_a + imm)%a = Some pc_a →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ wsrc
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ store_word pc_p wsrc ∗
    src ↣ᵣ wsrc.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa ? Hadd) "(#Hctx & Hj & Hres)".
     have Himm : imm = 0 by solve_finz. subst imm.
     iApply (step_store_success_reg_PC_store_word with "[$Hctx $Hj $Hres]"); eauto.
   Qed.

Lemma step_store_success_reg_PC_same_same_a_store_word_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_a' w :
    ↑specN ⊆ E →
     decodeInstrW w = Store PC (inr PC) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →

     (pc_a + imm)%a = Some pc_a →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ store_word pc_p (WCap true pc_p pc_g pc_b pc_e pc_a).
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hadd) "(#Hctx & Hj & Hres)".
     have Himm : imm = 0 by solve_finz. subst imm.
     iApply (step_store_success_reg_PC_same_store_word E pc_p pc_g pc_b pc_e pc_a pc_a' w (WInt 0) with "[$Hctx $Hj $Hres]"); eauto.
   Qed.


End spec_rules.
