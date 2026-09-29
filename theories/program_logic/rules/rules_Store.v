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
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  Definition reg_allows_store_imm (regs : Reg) (r : RegName) (imm : Z) p g b e a ea :=
    regs !!ᵣ r = Some (WCap true p g b e a) ∧
    (a + imm)%a = Some ea ∧ writeAllowed p = true ∧ withinBounds b e ea = true.

  (* Store relations carry the instruction's immediate and both heaps. *)
  Inductive Store_failure
      (regs: Reg) (r1 : RegName) (r2 : Z + RegName) (imm : Z)
      (mem : gmap Addr Word) : Prop :=
  | Store_fail_const w :
      regs !!ᵣ r1 = Some w -> is_cap w = false ->
      Store_failure regs r1 r2 imm mem
  | Store_fail_tag p g b e a :
      regs !!ᵣ r1 = Some (WCap false p g b e a) ->
      Store_failure regs r1 r2 imm mem
  | Store_fail_addr p g b e a :
      regs !!ᵣ r1 = Some (WCap true p g b e a) ->
      (a + imm)%a = None ->
      Store_failure regs r1 r2 imm mem
  | Store_fail_bounds p g b e a ea :
      regs !!ᵣ r1 = Some (WCap true p g b e a) ->
      (a + imm)%a = Some ea ->
      (writeAllowed p = false \/ withinBounds b e ea = false) ->
      Store_failure regs r1 r2 imm mem
  | Store_fail_invalid_PC :
      incrementPC regs = None ->
      Store_failure regs r1 r2 imm mem
  | Store_fail_invalid_shadow p g b e a ea storev :
      regs !!ᵣ r1 = Some (WCap true p g b e a) ->
      (a + imm)%a = Some ea ->
      is_shadow_address ea = true ->
      word_of_argument regs r2 = Some storev ->
      (forall z, storev <> WInt z) ->
      Store_failure regs r1 r2 imm mem.

  Inductive Store_spec
      (regs : Reg) (r1 : RegName) (r2 : Z + RegName) (imm : Z)
      (regs' : Reg) (mem mem' : gmap Addr Word)
      (shadow shadow' : ShadowTbl) : griotte_lang.val -> Prop :=
  | Store_spec_success p g b e a ea storev oldv :
      word_of_argument regs r2 = Some storev ->
      reg_allows_store_imm regs r1 imm p g b e a ea ->
      is_shadow_address ea = false ->
      mem !! ea = Some oldv ->
      mem' = <[ea := store_word p storev]> mem ->
      shadow' = shadow ->
      incrementPC regs = Some regs' ->
      Store_spec regs r1 r2 imm regs' mem mem' shadow shadow' NextIV
  | Store_spec_success_shadow p g b e a ea heap_a z old_status :
      word_of_argument regs r2 = Some (WInt z) ->
      reg_allows_store_imm regs r1 imm p g b e a ea ->
      is_shadow_address ea = true ->
      shadow_to_heap ea = Some heap_a ->
      shadow !! heap_a = Some old_status ->
      mem' = mem ->
      shadow' = <[heap_a := decodeAllocStatus z]> shadow ->
      incrementPC regs = Some regs' ->
      Store_spec regs r1 r2 imm regs' mem mem' shadow shadow' NextIV
  | Store_spec_failure_store :
      mem' = mem -> shadow' = shadow ->
      Store_failure regs r1 r2 imm mem ->
      Store_spec regs r1 r2 imm regs' mem mem' shadow shadow' FailedV.

  Lemma Store_failure_impossible regs r1 (r2 : Z + RegName) imm mem p g b e a ea :
    regs !!ᵣ r1 = Some (WCap true p g b e a) ->
    (a + imm)%a = Some ea ->
    writeAllowed p = true -> withinBounds b e ea = true ->
    is_shadow_address ea = false ->
    incrementPC regs ≠ None ->
    Store_failure regs r1 r2 imm mem -> False.
  Proof.
    intros Hreg Hadd Hwa Hbounds Hshadow Hpc Hfail.
    destruct Hfail.
    - rewrite Hreg in H. inversion H; subst. discriminate.
    - rewrite Hreg in H. discriminate.
    - rewrite Hreg in H. inversion H; subst. congruence.
    - rewrite Hreg in H. inversion H; subst.
      rewrite Hadd in H0. inversion H0; subst.
      destruct H1; congruence.
    - congruence.
    - rewrite Hreg in H. inversion H; subst.
      rewrite Hadd in H0. inversion H0; subst. congruence.
  Qed.

  Definition allow_store_map_or_true_imm
    (r1 : RegName) (r2 : Z + RegName) (imm : Z) (regs : Reg) (mem : Mem):=
    ∃ t p g b e a storev,
      read_reg_inr regs r1 t p g b e a ∧ word_of_argument regs r2 = Some storev ∧
      match (a + imm)%a with
      | None => True
      | Some ea => if decide (reg_allows_store_imm regs r1 imm p g b e a ea) then
        ∃ w, mem !! ea = Some w
      else True
      end.

  Lemma allow_store_implies_storev_imm:
    ∀ (r1 : RegName)(r2 : Z + RegName) (mem0 : gmap Addr Word) (r : Reg)
      (p : Perm) (g : Locality) (b e a ea : Addr) (imm : Z) storev,
      allow_store_map_or_true_imm r1 r2 imm r mem0
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
    unfold allow_store_map_or_true_imm, read_reg_inr in HaStore.
    destruct HaStore as (t&?&?&?&?&?&?&Hrinr&Hwo&Hmem).
    rewrite Hr2v in Hrinr. inversion Hrinr; subst.
    unfold reg_allows_store_imm in Hmem. rewrite Hadd in Hmem.
    case_decide as HAL.
    - auto.
    - unfold reg_allows_store_imm in HAL.
      destruct HAL. rewrite Hwo in Hwoa; inversion Hwoa. repeat split; auto.
      by simplify_map_eq.
  Qed.

  Lemma mem_eq_implies_allow_store_map_imm:
    ∀ (regs : Reg)(mem : Mem)(r1 : RegName)(r2 : Z + RegName)(w storev : Word) p g b e a ea (imm : Z),
      (a + imm)%a = Some ea
      → mem = <[ea:=w]> ∅
      → regs !!ᵣ r1 = Some (WCap true p g b e a)
      → word_of_argument regs r2 = Some storev
      → allow_store_map_or_true_imm r1 r2 imm regs mem.
  Proof.
    intros regs mem r1 r2 w storev p g b e a ea imm Hadd Hmem Hrr2.
    assert (r1 ≠ cnull).
    { intros -> ; simplify_map_eq.
      destruct (regs !! cnull); cbn in * ; done.
    }
    simplify_map_eq.
    exists true,p,g,b,e,a,storev; split.
    - unfold read_reg_inr. by rewrite Hrr2.
    - unfold reg_allows_store_imm. rewrite Hadd. case_decide; last done.
      split; auto. exists w. simplify_map_eq. auto.
  Qed.

  Lemma mem_neq_implies_allow_store_map_imm:
    ∀ (regs : Reg)(mem : Mem)(r1 : RegName)(r2 : Z + RegName)(pc_a : Addr)
      (w w' storev : Word) p g b e a ea (imm : Z),
      (a + imm)%a = Some ea
      → ea ≠ pc_a
      → mem = <[pc_a:= w]> (<[ea:= w']> ∅)
      → regs !!ᵣ r1 = Some (WCap true p g b e a)
      → word_of_argument regs r2 = Some storev
      → allow_store_map_or_true_imm r1 r2 imm regs mem.
  Proof.
    intros regs mem r1 r2 pc_a w w' storev p g b e a ea imm Hadd H4 Hrr2 Hreg1 Hwoa.
    assert (r1 ≠ cnull).
    { intros -> ; simplify_map_eq.
      destruct (regs !! cnull); cbn in * ; done.
    }
    simplify_map_eq.
    exists true,p,g,b,e,a,storev; split.
    - unfold read_reg_inr. by rewrite Hreg1.
    - unfold reg_allows_store_imm. rewrite Hadd. case_decide; last done.
      split; auto. exists w'. simplify_map_eq. split; auto.
  Qed.

  Lemma mem_implies_allow_store_map_imm:
    ∀ (regs : Reg)(mem : Mem)(r1 : RegName)(r2 : Z + RegName)(pc_a : Addr)
      (w w' storev : Word) p g b e a ea (imm : Z),
      (a + imm)%a = Some ea
      → (if (ea =? pc_a)%a
       then mem = <[pc_a:= w]> ∅
       else mem = <[pc_a:= w]> (<[ea:= w']> ∅))
      → regs !!ᵣ r1 = Some (WCap true p g b e a)
      → word_of_argument regs r2 = Some storev
      → allow_store_map_or_true_imm r1 r2 imm regs mem.
  Proof.
    intros regs mem r1 r2 pc_a w w' storev p g b e a ea imm Hadd H4 Hrr2 Hwoa.
    assert (r1 ≠ cnull).
    { intros -> ; simplify_map_eq.
      destruct (regs !! cnull); cbn in * ; done.
    }
    simplify_map_eq.
    destruct (ea =? pc_a)%a eqn:Heq.
      + apply Z.eqb_eq, finz_to_z_eq in Heq. subst ea. eapply mem_eq_implies_allow_store_map_imm; eauto.
        by simplify_map_eq.
      + apply Z.eqb_neq in Heq. eapply mem_neq_implies_allow_store_map_imm; eauto; first congruence.
        by simplify_map_eq.
  Qed.

  Definition reg_allows_store (regs : Reg) (r : RegName) p g b e a :=
    regs !!ᵣ r = Some (WCap true p g b e a) ∧
    writeAllowed p = true ∧ withinBounds b e a = true.

  Definition allow_store_map_or_true
    (r1 : RegName) (r2 : Z + RegName) (regs : Reg) (mem : Mem):=
    ∃ t p g b e a storev,
      read_reg_inr regs r1 t p g b e a ∧ word_of_argument regs r2 = Some storev ∧
      if decide (reg_allows_store regs r1 p g b e a) then
        ∃ w, mem !! a = Some w
      else True.

  Lemma allow_store_implies_storev:
    ∀ (r1 : RegName)(r2 : Z + RegName) (mem0 : gmap Addr Word) (r : Reg)
      (p : Perm) (g : Locality) (b e a : Addr) storev,
      allow_store_map_or_true r1 r2 r mem0
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
    unfold allow_store_map_or_true, read_reg_inr in HaStore.
    destruct HaStore as (t&?&?&?&?&?&?&Hrinr&Hwo&Hmem).
    rewrite Hr2v in Hrinr. inversion Hrinr; subst.
    case_decide as HAL.
    - auto.
    - unfold reg_allows_store in HAL.
      destruct HAL. rewrite Hwo in Hwoa; inversion Hwoa. split; auto.
      by simplify_map_eq.
  Qed.

  Lemma mem_eq_implies_allow_store_map:
    ∀ (regs : Reg)(mem : Mem)(r1 : RegName)(r2 : Z + RegName)(w storev : Word) p g b e a,
      mem = <[a:=w]> ∅
      → regs !!ᵣ r1 = Some (WCap true p g b e a)
      → word_of_argument regs r2 = Some storev
      → allow_store_map_or_true r1 r2 regs mem.
  Proof.
    intros regs mem r1 r2 w storev p g b e a Hmem Hrr2.
    assert (r1 ≠ cnull).
    { intros -> ; simplify_map_eq.
      destruct (regs !! cnull); cbn in * ; done.
    }
    simplify_map_eq.
    exists true,p,g,b,e,a,storev; split.
    - unfold read_reg_inr. by rewrite Hrr2.
    - case_decide; last done.
      split; auto. exists w. simplify_map_eq. auto.
  Qed.

  Lemma mem_neq_implies_allow_store_map:
    ∀ (regs : Reg)(mem : Mem)(r1 : RegName)(r2 : Z + RegName)(pc_a : Addr)
      (w w' storev : Word) p g b e a,
      a ≠ pc_a
      → mem = <[pc_a:= w]> (<[a:= w']> ∅)
      → regs !!ᵣ r1 = Some (WCap true p g b e a)
      → word_of_argument regs r2 = Some storev
      → allow_store_map_or_true r1 r2 regs mem.
  Proof.
    intros regs mem r1 r2 pc_a w w' storev p g b e a H4 Hrr2 Hreg1 Hwoa.
    assert (r1 ≠ cnull).
    { intros -> ; simplify_map_eq.
      destruct (regs !! cnull); cbn in * ; done.
    }
    simplify_map_eq.
    exists true,p,g,b,e,a,storev; split.
    - unfold read_reg_inr. by rewrite Hreg1.
    - case_decide; last done.
      split; auto. exists w'. simplify_map_eq. split; auto.
  Qed.

  Lemma mem_implies_allow_store_map:
    ∀ (regs : Reg)(mem : Mem)(r1 : RegName)(r2 : Z + RegName)(pc_a : Addr)
      (w w' storev : Word) p g b e a,
      (if (a =? pc_a)%a
       then mem = <[pc_a:= w]> ∅
       else mem = <[pc_a:= w]> (<[a:= w']> ∅))
      → regs !!ᵣ r1 = Some (WCap true p g b e a)
      → word_of_argument regs r2 = Some storev
      → allow_store_map_or_true r1 r2 regs mem.
  Proof.
    intros regs mem r1 r2 pc_a w w' storev p g b e a H4 Hrr2 Hwoa.
    assert (r1 ≠ cnull).
    { intros -> ; simplify_map_eq.
      destruct (regs !! cnull); cbn in * ; done.
    }
    simplify_map_eq.
    destruct (a =? pc_a)%a eqn:Heq.
      + apply Z.eqb_eq, finz_to_z_eq in Heq. subst a. eapply mem_eq_implies_allow_store_map; eauto.
        by simplify_map_eq.
      + apply Z.eqb_neq in Heq. eapply mem_neq_implies_allow_store_map; eauto; first congruence.
        by simplify_map_eq.
  Qed.

  Definition allow_store_mem_or_shadow
    (r1 : RegName) (r2 : Z + RegName) (regs : Reg)
    (mem : Mem) (shadow : ShadowTbl) :=
    ∀ p g b e a storev,
      reg_allows_store regs r1 p g b e a →
      word_of_argument regs r2 = Some storev →
      if is_shadow_address a then
        (∃ z, storev = WInt z) →
        ∃ heap_a, shadow_to_heap a = Some heap_a ∧ is_Some (shadow !! heap_a)
      else is_Some (mem !! a).

  Definition allow_store_mem_or_shadow_imm
    (r1 : RegName) (r2 : Z + RegName) (imm : Z) (regs : Reg)
    (mem : Mem) (shadow : ShadowTbl) :=
    forall p g b e a ea storev,
      reg_allows_store_imm regs r1 imm p g b e a ea ->
      word_of_argument regs r2 = Some storev ->
      if is_shadow_address ea then
        (exists z, storev = WInt z) ->
        exists heap_a, shadow_to_heap ea = Some heap_a ∧
          is_Some (shadow !! heap_a)
      else is_Some (mem !! ea).

   Lemma wp_store_shadow_imm Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 (r2 : Z + RegName) (imm : Z) w mem regs shadow :
   decodeInstrW w = Store r1 r2 imm →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Store r1 r2 imm) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_store_mem_or_shadow_imm r1 r2 imm regs mem shadow →

   {{{ (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
       (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ revoked) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ regs' mem' shadow' retv, RET retv;
       ⌜ Store_spec regs r1 r2 imm regs' mem mem' shadow shadow' retv⌝ ∗
         ([∗ map] a↦w ∈ mem', a ↦ₐ w) ∗
         ([∗ map] a↦revoked ∈ shadow', a ↦ₛ revoked) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
   Proof.
     iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaStore φ) "(>Hmem & >Hshadow & >Hmap) Hφ".
     iApply wp_lift_atomic_base_step_no_fork; auto.
     iIntros (σ1 ns l1 l2 nt) "[ [ [Hr Hsr] Hm ] Hst ] /=".
     destruct σ1 as [ [ [r sr] m] st]; cbn.
     iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.

     (* Derive necessary register values in r *)
     pose proof (lookup_weaken _ _ _ _ HPC Hregs).
     specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
     odestruct (Hri r1) as [r1v [Hr'1 Hr1]]; first by set_solver+.
     iDestruct (gen_mem_valid_inSepM mem m with "Hm Hmem") as %Hma; eauto.

     iModIntro. iSplitR; first (by iPureIntro; apply normal_always_base_reducible).
     iNext. iIntros (e2 σ2 efs Hpstep).
     apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
     iIntros "_".
     iSplitR; auto. eapply step_exec_inv in Hstep; eauto.

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
       iFailWP "Hφ" Store_fail_const.
     }
     destruct r1v as [ | [t p g b e a | ] | | ]; try inversion Hr1v. clear Hr1v.
     destruct t.
     2: { inversion Hstep; subst c σ2. iFailWP "Hφ" Store_fail_tag. }
     destruct (a + imm)%a as [ea|] eqn:Hadd.
     2: { inversion Hstep; subst c σ2. iFailWP "Hφ" Store_fail_addr; eauto. }
     cbn in Hstep.

     destruct (writeAllowed p && withinBounds b e ea) eqn:HWA.
     2 : { (* Failure: the destination is out of bounds or does not allow writing *)
       inversion Hstep.
       apply andb_false_iff in HWA.
       iFailWP "Hφ" Store_fail_bounds; eauto.
     }
     apply andb_true_iff in HWA; destruct HWA as (Hwa & Hwb).


     assert (Hallow : reg_allows_store_imm regs r1 imm p g b e a ea)
       by (repeat split; auto).
     specialize (HaStore p g b e a ea storev Hallow HSV).
     destruct (is_shadow_address ea) eqn:Hshadow.
     - (* Shadow-table store: the capability addresses the shadow region,
          while its points-to is indexed by the corresponding heap address. *)
       destruct (proj2 (shadow_to_heap_domain ea) Hshadow) as [heap_a Htranslate].
       rewrite Htranslate /= in Hstep.
       destruct storev as [z | | |].
       2: { assert (c = Failed ∧ σ2 = (r, sr, m, st)) as (-> & ->).
             { inversion Hstep; subst; auto. }
             iFailWP "Hφ" Store_fail_invalid_shadow; eauto; intros z Hcontra; discriminate. }
       2: { assert (c = Failed ∧ σ2 = (r, sr, m, st)) as (-> & ->)
              by (inversion Hstep; subst; auto).
             iFailWP "Hφ" Store_fail_invalid_shadow; eauto; intros z Hcontra; discriminate. }
       2: { assert (c = Failed ∧ σ2 = (r, sr, m, st)) as (-> & ->)
              by (inversion Hstep; subst; auto).
             iFailWP "Hφ" Store_fail_invalid_shadow; eauto; intros z Hcontra; discriminate. }
       set (status := decodeAllocStatus z).
       assert (Hshadow_step :
         match updatePC (update_shadowtbl (r, sr, m, st) heap_a status) with
         | Some conf => conf
         | None => (Failed, (r, sr, m, st))
         end = (c, σ2)).
       { exact Hstep. }
       clear Hstep. rename Hshadow_step into Hstep.
       rewrite /update_shadowtbl /= in Hstep.
       destruct (incrementPC regs) as [regs'|] eqn:Hregs'.
       2: { (* Failure: the PC could not be incremented correctly *)
         assert (incrementPC r = None) as Hfail.
         { eapply incrementPC_overflow_mono; first eapply Hregs'; eauto. }
         rewrite incrementPC_fail_updatePC /= in Hstep; auto.
         inversion Hstep.
         iFailWP "Hφ" Store_fail_invalid_PC.
       }
       destruct HaStore as (heap_a' & Htranslate' & old_revoked & Hshadowa); first by eexists.
       assert (heap_a' = heap_a) as -> by congruence.
       pose proof Hregs' as Hinc.
       eapply (incrementPC_success_updatePC _ sr m (<[heap_a:=status]> st)) in Hregs'
         as (t1 & p1 & g1 & b1 & e1 & a1 & a'1 & a_pc1 & HPC'' & HuPC & ->).
       eapply updatePC_success_incl with
         (sregs':=sr) (m':=m) (shadow':=<[heap_a:=status]> st) in HuPC; last exact Hregs.
       rewrite HuPC in Hstep. simplify_pair_eq. cbn.
       iDestruct (big_sepM_delete _ _ heap_a with "Hshadow") as "[Ha Hshadow]"; first exact Hshadowa.
       iMod (gen_heap_update with "Hst Ha") as "[Hst Ha]".
       iDestruct (big_sepM_insert _ _ heap_a with "[$Hshadow $Ha]") as "Hshadow".
       { apply lookup_delete_eq. }
       iEval (rewrite insert_delete_eq) in "Hshadow".
       iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
       iFrame. iModIntro. iApply "Hφ". iFrame.
       iPureIntro. eapply Store_spec_success_shadow; eauto.
     - (* Ordinary-memory store *)
       destruct HaStore as [oldv Hmema].
       rewrite /update_mem /= in Hstep.
       destruct (incrementPC regs) as [regs'|] eqn:Hregs'.
       2: { (* Failure: the PC could not be incremented correctly *)
         assert (incrementPC r = None) as Hfail.
         { eapply incrementPC_overflow_mono; first eapply Hregs'; eauto. }
         rewrite incrementPC_fail_updatePC /= in Hstep; auto.
         inversion Hstep.
         iFailWP "Hφ" Store_fail_invalid_PC.
       }
       pose proof Hregs' as Hinc.
       eapply (incrementPC_success_updatePC _ sr (<[ea:=store_word p storev]> m) st) in Hregs'
         as (t1 & p1 & g1 & b1 & e1 & a1 & a'1 & a_pc1 & HPC'' & HuPC & ->).
       eapply updatePC_success_incl with
         (sregs':=sr) (m':=<[ea:=store_word p storev]> m) (shadow':=st) in HuPC; last exact Hregs.
       rewrite HuPC in Hstep. simplify_pair_eq. cbn.
       iMod ((gen_mem_update_inSepM _ _ ea) with "Hm Hmem") as "[Hm Hmem]"; eauto.
       iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
       iFrame. iModIntro. iApply "Hφ". iFrame.
       iPureIntro. eapply Store_spec_success; eauto.
     Unshelve. all: auto.
   Qed.

  Lemma wp_store_imm Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 (r2 : Z + RegName) (imm : Z) w mem regs :
   decodeInstrW w = Store r1 r2 imm →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Store r1 r2 imm) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_store_map_or_true_imm r1 r2 imm regs mem →
   (∀ p g b e a ea, reg_allows_store_imm regs r1 imm p g b e a ea →
      is_shadow_address ea = false) →
   {{{ (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ regs' mem' retv, RET retv;
       ⌜ Store_spec regs r1 r2 imm regs' mem mem' (∅ : ShadowTbl) (∅ : ShadowTbl) retv⌝ ∗
         ([∗ map] a↦w ∈ mem', a ↦ₐ w) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaStore Hordinary φ) "Hres Hφ".
    iDestruct "Hres" as "[Hmem Hmap]".
    iAssert ((▷ ([∗ map] k↦revoked ∈ (∅ : ShadowTbl), k ↦ₛ revoked))%I) as "Hshadow".
    { iNext. rewrite big_sepM_empty. done. }
    assert (HaStoreOffset : allow_store_mem_or_shadow_imm r1 r2 imm regs mem (∅ : ShadowTbl)).
    { intros p g b e a ea storev Hreg Harg.
      unfold reg_allows_store_imm in Hreg.
      destruct Hreg as (Hcap & Hadd & Hwa & Hwb).
      destruct (is_shadow_address ea) eqn:Hshadowea.
      - specialize (Hordinary p g b e a ea (conj Hcap (conj Hadd (conj Hwa Hwb)))).
        congruence.
      - destruct (allow_store_implies_storev_imm r1 r2 mem regs p g b e a ea imm storev
          HaStore Hcap Harg Hwa Hadd Hwb) as [oldv Hlookup].
        exists oldv. exact Hlookup. }
    iApply (wp_store_shadow_imm Ep pc_p pc_g pc_b pc_e pc_a r1 r2 imm w mem regs (∅ : ShadowTbl)
      with "[$Hmem $Hshadow $Hmap]"); try done.
    iNext. iIntros (regs' mem' shadow' retv) "(%Hspec & Hmem' & Hshadow' & Hregs')".
    destruct Hspec as
      [p g b e a ea storev oldv Harg Hallow Hnotshadow Hlookup Hmem_eq Hshadow_eq Hinc
      |p g b e a ea heap_a z old_status Harg Hallow Hshadowea Htranslate Hold Hmem_eq Hshadow_eq Hinc
      |Hmem_eq Hshadow_eq Hfail].
    - iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
    - exfalso. simplify_map_eq.
    - iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
  Qed.

  Lemma wp_store Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 (r2 : Z + RegName) w mem regs shadow :
   decodeInstrW w = Store r1 r2 0 →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Store r1 r2 0) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_store_mem_or_shadow r1 r2 regs mem shadow →
   {{{ (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
       (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ revoked) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ regs' mem' shadow' retv, RET retv;
       ⌜ Store_spec regs r1 r2 0 regs' mem mem' shadow shadow' retv ⌝ ∗
         ([∗ map] a↦w ∈ mem', a ↦ₐ w) ∗
         ([∗ map] a↦revoked ∈ shadow', a ↦ₛ revoked) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc Hallow φ) "Hres Hφ".
    assert (Hallow0 : allow_store_mem_or_shadow_imm r1 r2 0 regs mem shadow).
    { intros p g b e a ea storev Hreg Harg.
      unfold reg_allows_store_imm in Hreg.
      destruct Hreg as (Hdst & Hadd & Hwa & Hwb).
      rewrite finz_add_0 in Hadd. inversion Hadd; subst ea.
      specialize (Hallow p g b e a storev ltac:(repeat split; assumption) Harg).
      destruct (is_shadow_address a); auto. }
    iApply (wp_store_shadow_imm Ep pc_p pc_g pc_b pc_e pc_a r1 r2 0 w mem regs shadow
      with "Hres"); try done.
  Qed.

  Lemma wp_store_success_mem_imm E pc_p pc_g pc_b pc_e pc_a
    dst src imm w regs regs' mem p g b e a ea storev oldv :
    decodeInstrW w = Store dst src imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Store dst src imm) ⊆ dom regs →
    mem !! pc_a = Some w →
    reg_allows_store_imm regs dst imm p g b e a ea →
    word_of_argument regs src = Some storev →
    is_shadow_address ea = false →
    mem !! ea = Some oldv →
    incrementPC regs = Some regs' →
    {{{ (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        ([∗ map] a↦w ∈ <[ea:=store_word p storev]> mem, a ↦ₐ w) ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem Hallow Harg Hshadow Hlookup Hinc φ)
      "(>Hmem & >Hmap) Hφ".
    iAssert ((▷ ([∗ map] k↦revoked ∈ (∅ : ShadowTbl), k ↦ₛ revoked))%I) as "Hshadow".
    { iNext. rewrite big_sepM_empty. done. }
    iApply (wp_store_shadow_imm with "[$Hmem $Hshadow $Hmap]"); eauto.
    { intros p0 g0 b0 e0 a0 ea0 v0 (Hdst0 & Hadd0 & _) Harg0.
      destruct Hallow as (Hdst & Hadd & Hwa & Hwb).
      rewrite Hdst in Hdst0. inversion Hdst0; subst.
      rewrite Hadd in Hadd0. inversion Hadd0; subst.
      rewrite Hshadow. by eexists. }
    iNext. iIntros (regs0 mem0 shadow0 retv) "(%Hspec & Hmem & _ & Hmap)".
    destruct Hallow as (Hdst & Hadd & Hwa & Hwb).
    destruct Hspec as
      [p0 g0 b0 e0 a0 ea0 v0 oldv0 Harg0 (Hdst0 & Hadd0 & _) Hshadow0 Hlookup0 -> -> Hinc0
      |p0 g0 b0 e0 a0 ea0 heap_a0 z0 old_status0 Harg0 (Hdst0 & Hadd0 & _) Hshadow0 Htranslate0 Hlookup0 -> -> Hinc0
      |Hmem_eq Hshadow_eq Hfail].
    - rewrite Hdst in Hdst0. inversion Hdst0; subst.
      rewrite Hadd in Hadd0. inversion Hadd0; subst.
      rewrite Harg in Harg0. inversion Harg0; subst.
      rewrite Hinc in Hinc0. inversion Hinc0; subst.
      iApply "Hφ". iFrame.
    - simplify_map_eq.
    - exfalso. eapply (Store_failure_impossible _ _ _ _ _ p g b e a ea); eauto.
      congruence.
  Qed.

Lemma wp_store_success_z_PC_same_a_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_a' w z :
     is_shadow_address pc_a = false →
     decodeInstrW w = Store PC (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →

     (pc_a + imm)%a = Some pc_a →
     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ (WInt z) }}}.
  Proof.
    iIntros (Hshadow Hinstr Hvpc Hpca' Hwa Hadd φ)
            "(>HPC & >Hi) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iDestruct (memMap_resource_1 with "Hi") as "Hmem".


    iApply (wp_store_success_mem_imm _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { unfold reg_allows_store_imm. repeat split; auto; try by simplify_map_eq.
      apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [_ Hwb].
      by apply Is_true_true. }
    { by rewrite /incrementPC /incrementPC_gen; simplify_map_eq. }
    iNext. iIntros "(Hmem & Hmap)".
    iEval (rewrite /store_word ?HcanStore ?Hcan /=) in "Hmem". iApply "Hφ".
    rewrite !insert_insert_eq memMap_resource_1.
    iDestruct (regs_of_map_1 with "Hmap") as "HPC"; eauto. iFrame.
    all: rewrite /store_word /=; repeat case_match; iFrame.
  Qed.

Lemma wp_store_success_reg_PC_same_a_store_word_imm E (imm : Z) src wsrc pc_p pc_g pc_b pc_e pc_a pc_a' w :
     is_shadow_address pc_a = false →
     decodeInstrW w = Store PC (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →
     src ≠ cnull ->

     (pc_a + imm)%a = Some pc_a →
     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ wsrc }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ store_word pc_p wsrc
              ∗ src ↦ᵣ wsrc }}}.
   Proof.
     iIntros (Hshadow Hinstr Hvpc Hpca' Hwa ? Hadd φ)
            "(>HPC & >Hi & >Hsrc) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hsrc") as "[Hmap %]".
     iDestruct (memMap_resource_1 with "Hi") as "Hmem".


    iApply (wp_store_success_mem_imm _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { unfold reg_allows_store_imm. repeat split; auto; try by simplify_map_eq.
      apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [_ Hwb].
      by apply Is_true_true. }
    { by rewrite /incrementPC /incrementPC_gen; simplify_map_eq. }
    iNext. iIntros "(Hmem & Hmap)".
iApply "Hφ".
    rewrite !insert_insert_eq memMap_resource_1.
    iDestruct (regs_of_map_2 with "Hmap") as "[HPC Hr]"; eauto. iFrame.
  Qed.

Lemma wp_store_success_reg_PC_same_same_a_store_word_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_a' w :
     is_shadow_address pc_a = false →
     decodeInstrW w = Store PC (inr PC) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →

     (pc_a + imm)%a = Some pc_a →
     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ store_word pc_p (WCap true pc_p pc_g pc_b pc_e pc_a) }}}.
   Proof.
     iIntros (Hshadow Hinstr Hvpc Hpca' Hwa Hadd φ)
            "(>HPC & >Hi) Hφ".
     iDestruct (map_of_regs_1 with "HPC") as "Hmap".
     iDestruct (memMap_resource_1 with "Hi") as "Hmem".


    iApply (wp_store_success_mem_imm _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { unfold reg_allows_store_imm. repeat split; auto; try by simplify_map_eq.
      apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [_ Hwb].
      by apply Is_true_true. }
    { by rewrite /incrementPC /incrementPC_gen; simplify_map_eq. }
    iNext. iIntros "(Hmem & Hmap)".
iApply "Hφ".
    rewrite !insert_insert_eq memMap_resource_1.
    iDestruct (regs_of_map_1 with "Hmap") as "HPC"; eauto. iFrame.
  Qed.

    Lemma wp_store_success_reg_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src w'
         p g b e a ea (imm : Z) w'' :
     is_shadow_address ea = false →
      decodeInstrW w = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ WCap true p g b e a
           ∗ ▷ ea ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ w
              ∗ src ↦ᵣ w''
              ∗ dst ↦ᵣ WCap true p g b e a
              ∗ ea ↦ₐ store_word p w'' }}}.
    Proof.
      iIntros (Hshadow Hinstr Hvpc Hpca' Hwa Hwb Hadd ?? φ)
             "(>HPC & >Hi & >Hsrc & >Hdst & >Hsrca) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iApply (wp_store_imm _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try (intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & _); simplify_map_eq; congruence).
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_store_map_imm with (a := a) (ea := ea); eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     { (* Success *)
       iApply "Hφ".
       destruct H6 as [? [Hadd2 _]]; simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_eq.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hsrc Hdst] ]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       exfalso.
       eapply (Store_failure_impossible _ _ _ _ _ p g b e a ea); eauto.
       - by simplify_map_eq.
       - intros Hnone. rewrite /incrementPC /incrementPC_gen in Hnone.
         simplify_map_eq.

     }
    Qed.

   Lemma wp_store_success_reg_same_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst w'
         p g b e a ea (imm : Z) :
     is_shadow_address ea = false →
     decodeInstrW w = Store dst (inr dst) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a
           ∗ ▷ ea ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ w
              ∗ dst ↦ᵣ WCap true p g b e a
              ∗ ea ↦ₐ store_word p (WCap true p g b e a) }}}.
   Proof.
    iIntros (Hshadow Hinstr Hvpc Hpca' Hwa Hwb Hadd ? φ)
             "(>HPC & >Hi & >Hdst & >Hsrca) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iApply (wp_store_imm _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try (intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & _); simplify_map_eq; congruence).
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_store_map_imm with (a := a) (ea := ea); eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     { (* Success *)
       iApply "Hφ".
       destruct H3 as [Hrr2 [Hadd2 _]]. simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_eq.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hdst]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       exfalso.
       eapply (Store_failure_impossible _ _ _ _ _ p g b e a ea); eauto.
       - by simplify_map_eq.
       - intros Hnone. rewrite /incrementPC /incrementPC_gen in Hnone.
         simplify_map_eq.

     }
    Qed.

   Lemma wp_store_success_z_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst z w'
         p g b e a ea (imm : Z) :
     is_shadow_address ea = false →
     decodeInstrW w = Store dst (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a
           ∗ ▷ ea ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ w
              ∗ dst ↦ᵣ WCap true p g b e a
              ∗ ea ↦ₐ WInt z }}}.
   Proof.
     iIntros (Hshadow Hinstr Hvpc Hpca' Hwa Hwb Hadd ? φ)
             "(>HPC & >Hi & >Hdst & >Hsrca) Hφ".
     have Hstore_word : store_word p (WInt z) = WInt z.
     { apply store_word_canStore, writeAllowed_canStore_int, Hwa. }
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iApply (wp_store_imm _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try (intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & _); simplify_map_eq; congruence).
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_store_map_imm with (a := a) (ea := ea); eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     { (* Success *)
       iApply "Hφ".
       destruct H3 as [Hrr2 [Hadd2 _]]. simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_eq.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hdst]"; eauto.
       all: try rewrite Hstore_word; iFrame. }
     { (* Failure (contradiction) *)
       exfalso.
       eapply (Store_failure_impossible _ _ _ _ _ p g b e a ea); eauto.
       - by simplify_map_eq.
       - intros Hnone. rewrite /incrementPC /incrementPC_gen in Hnone.
         simplify_map_eq.
     }
    Qed.

   Lemma wp_store_success_reg_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src w'
       p g b e a ea (imm : Z) w'' :
     is_shadow_address ea = false →
     decodeInstrW w = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     canStore p w'' = true →
     src ≠ cnull → dst ≠ cnull →
     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ WCap true p g b e a
           ∗ ▷ ea ↦ₐ w' }}}
       Instr Executable @ E
     {{{ RET NextIV;
         PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ w
           ∗ src ↦ᵣ w''
           ∗ dst ↦ᵣ WCap true p g b e a
           ∗ ea ↦ₐ w'' }}}.
   Proof.
     iIntros (Hshadow Hinstr Hvpc Hpca' Hwa Hwb Hadd HcanStore Hsrc Hdst φ) "Hres Hφ".
     iApply (wp_store_success_reg_store_word_imm with "Hres"); eauto.
     iNext. iIntros "(HPC & Hi & Hsrc & Hdst & Ha)".
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Ha".
     iApply "Hφ". iFrame.
   Qed.

   Lemma wp_store_success_same_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst z
         p g b e a (imm : Z) :
     is_shadow_address pc_a = false →
     decodeInstrW w = Store dst (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     (a + imm)%a = Some pc_a →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ (WInt z)
              ∗ dst ↦ᵣ WCap true p g b e a }}}.
    Proof.
     iIntros (Hshadow Hinstr Hvpc Hpca' Hwa Hwb Hadd ? φ)
            "(>HPC & >Hi & >Hdst) Hφ".
     have Hstore_word : store_word p (WInt z) = WInt z.
     { apply store_word_canStore, writeAllowed_canStore_int, Hwa. }
     iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
     iDestruct (memMap_resource_1 with "Hi") as "Hmem".

    iApply (wp_store_imm _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try (intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & _); simplify_map_eq; congruence).
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_eq_implies_allow_store_map_imm; eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     { (* Success *)
       iApply "Hφ".
       destruct H2 as [? [Hadd2 _]]; simplify_map_eq.
       rewrite memMap_resource_1.
       incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto.
       all: try rewrite Hstore_word; iFrame. }
     { (* Failure (contradiction) *)
       exfalso.
       eapply (Store_failure_impossible _ _ _ _ _ p g b e a _); eauto.
       - by simplify_map_eq.
       - intros Hnone. rewrite /incrementPC /incrementPC_gen in Hnone.
         simplify_map_eq.
     }
     Qed.

   Lemma wp_store_success_reg_same'_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst
         p g b e a (imm : Z) :
     is_shadow_address pc_a = false →
     decodeInstrW w = Store dst (inr dst) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     (a + imm)%a = Some pc_a →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ store_word p (WCap true p g b e a)
              ∗ dst ↦ᵣ WCap true p g b e a }}}.
   Proof.
     iIntros (Hshadow Hinstr Hvpc Hpca' Hwa Hwb Hadd ? φ)
            "(>HPC & >Hi & >Hdst) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
     iDestruct (memMap_resource_1 with "Hi") as "Hmem".

    iApply (wp_store_imm _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try (intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & _); simplify_map_eq; congruence).
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_eq_implies_allow_store_map_imm; eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     { (* Success *)
       iApply "Hφ".
       destruct H2 as [? [Hadd2 _]]; simplify_map_eq.
       rewrite memMap_resource_1.
       incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       exfalso.
       eapply (Store_failure_impossible _ _ _ _ _ p g b e a _); eauto.
       - by simplify_map_eq.
       - intros Hnone. rewrite /incrementPC /incrementPC_gen in Hnone.
         simplify_map_eq.
     }
   Qed.

   Lemma wp_store_success_reg_same_a_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src
         p g b e a (imm : Z) w'' :
     is_shadow_address pc_a = false →
      decodeInstrW w = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     (a + imm)%a = Some pc_a →
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ WCap true p g b e a }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ store_word p w''
              ∗ src ↦ᵣ w''
              ∗ dst ↦ᵣ WCap true p g b e a}}}.
   Proof.
     iIntros (Hshadow Hinstr Hvpc Hpca' Hwa Hwb Hadd ?? φ)
             "(>HPC & >Hi & >Hsrc & >Hdst) Hφ".
     iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
     iDestruct (memMap_resource_1 with "Hi") as "Hmem".

    iApply (wp_store_imm _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try (intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & _); simplify_map_eq; congruence).
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_eq_implies_allow_store_map_imm; eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     { (* Success *)
       iApply "Hφ".
       destruct H5 as [? [Hadd2 _]]; simplify_map_eq.
       rewrite memMap_resource_1.
       incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hsrc Hdst] ]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       exfalso.
       eapply (Store_failure_impossible _ _ _ _ _ p g b e a _); eauto.
       - by simplify_map_eq.
       - intros Hnone. rewrite /incrementPC /incrementPC_gen in Hnone.
         simplify_map_eq.
     }
   Qed.

   Lemma wp_store_success_reg_same'_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst
       p g b e a (imm : Z) :
     is_shadow_address pc_a = false →
     decodeInstrW w = Store dst (inr dst) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     (a + imm)%a = Some pc_a →
     canStore p (WCap true p g b e a) = true →
     dst ≠ cnull →
     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a }}}
       Instr Executable @ E
     {{{ RET NextIV;
         PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ WCap true p g b e a
           ∗ dst ↦ᵣ WCap true p g b e a }}}.
   Proof.
     iIntros (Hshadow Hinstr Hvpc Hpca' Hwa Hwb Hadd HcanStore Hdst φ) "Hres Hφ".
     iApply (wp_store_success_reg_same'_store_word_imm with "Hres"); eauto.
     iNext. iIntros "(HPC & Hi & Hdst)".
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Hi".
     iApply "Hφ". iFrame.
   Qed.

   Lemma wp_store_success_reg_same_a_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src
       p g b e a (imm : Z) w'' :
     is_shadow_address pc_a = false →
     decodeInstrW w = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     (a + imm)%a = Some pc_a →
     canStore p w'' = true →
     src ≠ cnull → dst ≠ cnull →
     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ WCap true p g b e a }}}
       Instr Executable @ E
     {{{ RET NextIV;
         PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ w''
           ∗ src ↦ᵣ w''
           ∗ dst ↦ᵣ WCap true p g b e a }}}.
   Proof.
     iIntros (Hshadow Hinstr Hvpc Hpca' Hwa Hwb Hadd HcanStore Hsrc Hdst φ) "Hres Hφ".
     iApply (wp_store_success_reg_same_a_store_word_imm with "Hres"); eauto.
     iNext. iIntros "(HPC & Hi & Hsrc & Hdst)".
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Hi".
     iApply "Hφ". iFrame.
   Qed.

   Lemma wp_store_fail_reg_not_cap_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a w
     dst src wdst wstore :
      decodeInstrW w = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     is_cap wdst = false ->
     src ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ wstore
           ∗ ▷ dst ↦ᵣ wdst
     }}}
       Instr Executable @ E
       {{{ RET FailedV; True}}}.
    Proof.
      iIntros (Hinstr Hvpc Hnot_cap ? φ)
             "(>HPC & >Hi & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (memMap_resource_1 with "Hi") as "Hmem"; auto.

    iApply (wp_store_imm _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try solve [intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & Hwa0 & Hwb0);
        try (destruct (decide (dst = cnull))); simplify_map_eq; try (cbn in Hnot_cap); congruence].
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /allow_store_map_or_true_imm.
      eexists true,_,_,_,_,_,_; eauto.
      simplify_map_eq.
      split; [|split]; eauto.
      - rewrite /read_reg_inr; simplify_map_eq.
        destruct wdst as [| [] | |]; cbn in Hnot_cap; done.
      - rewrite /reg_allows_store_imm.
        destruct (_ + imm)%a; simpl; last done. simplify_map_eq.
        rewrite decide_False; auto.
        intros [].
        destruct (decide (dst = cnull)); first done.
        destruct wdst as [| [] | |]; cbn in Hnot_cap; simplify_eq.
    }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     { (* Success (contradiction) *)
       exfalso.
       rewrite /reg_allows_store_imm in H4.
       destruct H4 as (? & ? & ? & ?); simplify_map_eq.
       destruct (decide (dst = cnull)); first done.
       simplify_map_eq.
     }
     by iApply "Hφ".
     Unshelve. all: done.
    Qed.

    Lemma wp_store_fail_z_not_cap_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a w
     dst z wdst :
      decodeInstrW w = Store dst (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     is_cap wdst = false ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ wdst
     }}}
       Instr Executable @ E
       {{{ RET FailedV; True}}}.
    Proof.
      iIntros (Hinstr Hvpc Hnot_cap ? φ)
             "(>HPC & >Hi & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (memMap_resource_1 with "Hi") as "Hmem"; auto.

    iApply (wp_store_imm _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try solve [intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & Hwa0 & Hwb0);
        try (destruct (decide (dst = cnull))); simplify_map_eq; try (cbn in Hnot_cap); congruence].
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /allow_store_map_or_true_imm.
      eexists true,_,_,_,_,_,_; eauto.
      simplify_map_eq.
      split; [|split]; eauto.
      - rewrite /read_reg_inr; simplify_map_eq.
        destruct wdst as [| [] | |]; cbn in Hnot_cap; done.
      - rewrite /reg_allows_store_imm.
        destruct (_ + imm)%a; simpl; last done. simplify_map_eq.
        rewrite decide_False; auto.
        intros [].
        destruct (decide (dst = cnull)); first done.
        destruct wdst as [| [] | |]; cbn in Hnot_cap; simplify_eq.
    }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     { (* Success (contradiction) *)
       exfalso.
       rewrite /reg_allows_store_imm in H2.
       simplify_map_eq.
       destruct H2 as (? & ? & ? & ?); simplify_map_eq.
     }
     by iApply "Hφ".
     Unshelve. all: done.
    Qed.

   Lemma wp_store_fail_reg_perm_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a w dst src
         p g b e a w'' :
     decodeInstrW w = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     writeAllowed p = false ->
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ WCap true p g b e a
     }}}
       Instr Executable @ E
       {{{ RET FailedV; True}}}.
    Proof.
      iIntros (Hinstr Hvpc Hwa ?? φ)
             "(>HPC & >Hi & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (memMap_resource_1 with "Hi") as "Hmem"; auto.

    iApply (wp_store_imm _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try solve [intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & Hwa0 & Hwb0);
        try (destruct (decide (dst = cnull))); simplify_map_eq; try (cbn in Hnot_cap); congruence].
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /allow_store_map_or_true_imm.
      eexists true,p,g,b,e,a,w''.
      split.
      { rewrite /read_reg_inr.
        by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert_eq.
      }
      split.
      { rewrite /word_of_argument.
        by simplify_map_eq.
      }
      rewrite /reg_allows_store_imm.
      destruct (a + imm)%a eqn:Haddr; simpl; last done.
      rewrite Hwa.
      rewrite decide_False; auto.
      intro; naive_solver.
      }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     { (* Success (contradiction) *)
       exfalso.
       rewrite /reg_allows_store_imm in H5.
       destruct H5 as (? & ? & Hwa' & ?); simplify_map_eq.
       congruence.
     }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; by iApply "Hφ".
     }
    Qed.

    Lemma wp_store_fail_z_perm_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a w dst
         p g b e a z :
      decodeInstrW w = Store dst (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     writeAllowed p = false ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a
     }}}
       Instr Executable @ E
       {{{ RET FailedV; True}}}.
    Proof.
      iIntros (Hinstr Hvpc HcanStore ? φ)
             "(>HPC & >Hi & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (memMap_resource_1 with "Hi") as "Hmem"; auto.

    iApply (wp_store_imm _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try solve [intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & Hwa0 & Hwb0);
        try (destruct (decide (dst = cnull))); simplify_map_eq; try (cbn in Hnot_cap); congruence].
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /allow_store_map_or_true_imm.
      eexists true,p,g,b,e,a,_.
      split.
      { rewrite /read_reg_inr.
        by rewrite lookup_insert_ne // lookup_insert_eq.
      }
      split.
      { rewrite /word_of_argument.
        eauto.
      }
      rewrite /reg_allows_store_imm.
      destruct (a + imm)%a eqn:Haddr; simpl; last done.
      rewrite HcanStore.
      rewrite decide_False; auto.
      intro; naive_solver.
      }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     { (* Success (contradiction) *)
       exfalso.
       rewrite /reg_allows_store_imm in H2.
       destruct H2 as (? & ? & Hwa' & ?); simplify_map_eq.
       congruence.
     }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; by iApply "Hφ".
     }
    Qed.

   Lemma wp_store_fail_reg_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a w dst src
         p g b e a ea w'' :
      decodeInstrW w = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (a + imm)%a = Some ea →
     withinBounds b e ea = false →
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ WCap true p g b e a
     }}}
       Instr Executable @ E
       {{{ RET FailedV; True}}}.
    Proof.
      iIntros (Hinstr Hvpc Hadd Hwb ?? φ)
             "(>HPC & >Hi & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (memMap_resource_1 with "Hi") as "Hmem"; auto.

    iApply (wp_store_imm _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try solve [intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & Hwa0 & Hwb0);
        try (destruct (decide (dst = cnull))); simplify_map_eq; try (cbn in Hnot_cap); congruence].
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /allow_store_map_or_true_imm.
      eexists true,p,g,b,e,a,w''.
      split.
      { rewrite /read_reg_inr.
        by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert_eq.
      }
      split.
      { rewrite /word_of_argument.
        by simplify_map_eq.
      }
      rewrite /reg_allows_store_imm.
      rewrite Hadd Hwb.
      rewrite decide_False; auto.
      intro; naive_solver.
      }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     { (* Success (contradiction) *)
       exfalso.
       rewrite /reg_allows_store_imm in H5.
       destruct H5 as (? & Haddr & ? & Hbounds); simplify_map_eq.
       by rewrite Hbounds in Hwb.
     }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; by iApply "Hφ".
     }
    Qed.

    Lemma wp_store_fail_z_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a w dst
         p g b e a ea z :
      decodeInstrW w = Store dst (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (a + imm)%a = Some ea →
     withinBounds b e ea = false →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a
     }}}
       Instr Executable @ E
       {{{ RET FailedV; True}}}.
    Proof.
      iIntros (Hinstr Hvpc Hadd Hwb ? φ)
             "(>HPC & >Hi & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (memMap_resource_1 with "Hi") as "Hmem"; auto.

    iApply (wp_store_imm _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try solve [intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & Hwa0 & Hwb0);
        try (destruct (decide (dst = cnull))); simplify_map_eq; try (cbn in Hnot_cap); congruence].
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /allow_store_map_or_true_imm.
      eexists true,p,g,b,e,a,_.
      split.
      { rewrite /read_reg_inr.
        by rewrite lookup_insert_ne // lookup_insert_eq.
      }
      split.
      { rewrite /word_of_argument. eauto.
      }
      rewrite /reg_allows_store_imm.
      rewrite Hadd Hwb.
      rewrite decide_False; auto.
      intro; naive_solver.
      }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     { (* Success (contradiction) *)
       exfalso.
       rewrite /reg_allows_store_imm in H2.
       destruct H2 as (? & Haddr & ? & Hbounds); simplify_map_eq.
       by rewrite Hbounds in Hwb.
     }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; by iApply "Hφ".
     }
    Qed.

  Lemma wp_store_fail_tag_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a
      w dst (src : Z + RegName) regs wa :
    decodeInstrW w = Store dst src imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !!ᵣ dst = Some wa →
    get_tag wa = false →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FailedV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Hsrc Htag φ) "(>Hpc_a & >Hmap) Hφ".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "[[[Hr Hsr] Hm] Hst] /=".
    destruct σ1 as [[[r sr] m] st]; cbn.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    have Hsrc' := lookup_reg_weaken _ _ _ _ Hsrc Hregs.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hpc_a; auto.
    iModIntro. iSplitR; first (by iPureIntro; apply normal_always_base_reducible).
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_". iSplitR; auto. eapply step_exec_inv in Hstep; eauto.
    rewrite /exec /= Hsrc' /= in Hstep.
    assert (c = Failed ∧ σ2 = (r, sr, m, st)) as (-> & ->).
    { destruct (word_of_argument r src) eqn:Harg; rewrite Harg in Hstep; cbn in Hstep.
      all: destruct wa as [| [t p g b e a|] | |]; cbn in Htag;
        by simplify_pair_eq. }
    cbn; iFrame; iApply "Hφ"; iFrame. done.
  Qed.

   Lemma wp_store_success_reg_PC_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w src w'
         ea (imm : Z) w'' :
     is_shadow_address ea = false →
      decodeInstrW w = Store PC (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true → withinBounds pc_b pc_e ea = true →
     (pc_a + imm)%a = Some ea →
     src ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ ea ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ w
              ∗ src ↦ᵣ w''
              ∗ ea ↦ₐ store_word pc_p w'' }}}.
    Proof.
      iIntros (Hshadow Hinstr Hvpc Hpca' Hwa Hwb Hadd ? φ)
             "(>HPC & >Hi & >Hsrc & >Hsrca) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hsrc") as "[Hmap %]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iApply (wp_store_imm _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try (intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & _); simplify_map_eq; congruence).
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_store_map_imm with (a := pc_a) (ea := ea); eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as
      [p0 g0 b0 e0 a0 ea0 storev oldv Harg Hallow Hordinary Hold Hmem' Hshadow' Hinc
      |p0 g0 b0 e0 a0 ea0 heap_a z0 old_status Harg Hallow Hshadow_addr Htranslate Hstatus Hmem' Hshadow' Hinc
      |Hmem' Hshadow' Hfail]; try (simplify_map_eq; congruence).
     { (* Success *)
       iApply "Hφ".
       destruct Hallow as [Hrr2 [Hadd2 _]]; simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       try rewrite insert_insert_eq.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       exfalso.
       eapply (Store_failure_impossible _ _ _ _ _ pc_p pc_g pc_b pc_e pc_a _); eauto.
       - by simplify_map_eq.
       - intros Hnone. rewrite /incrementPC /incrementPC_gen in Hnone.
         simplify_map_eq.
     }
    Qed.

   Lemma wp_store_success_reg_PC_same_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w w'
         ea (imm : Z) :
     is_shadow_address ea = false →
     decodeInstrW w = Store PC (inr PC) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true → withinBounds pc_b pc_e ea = true →
     (pc_a + imm)%a = Some ea →

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ ea ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ w
              ∗ ea ↦ₐ store_word pc_p (WCap true pc_p pc_g pc_b pc_e pc_a) }}}.
   Proof.
    iIntros (Hshadow Hinstr Hvpc Hpca' Hwa Hwb Hadd φ)
             "(>HPC & >Hi & >Hsrca) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iApply (wp_store_imm _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try (intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & _); simplify_map_eq; congruence).
    { eapply mem_neq_implies_allow_store_map_imm with (a := pc_a) (ea := ea); eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as
      [p0 g0 b0 e0 a0 ea0 storev oldv Harg Hallow Hordinary Hold Hmem' Hshadow' Hinc
      |p0 g0 b0 e0 a0 ea0 heap_a z0 old_status Harg Hallow Hshadow_addr Htranslate Hstatus Hmem' Hshadow' Hinc
      |Hmem' Hshadow' Hfail]; try (simplify_map_eq; congruence).
     { (* Success *)
       iApply "Hφ".
       destruct Hallow as [Hrr2 [Hadd2 _]]. simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       try rewrite insert_insert_eq.
       iDestruct (regs_of_map_1 with "[$Hmap]") as "HPC"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       exfalso.
       eapply (Store_failure_impossible _ _ _ _ _ pc_p pc_g pc_b pc_e pc_a _); eauto.
       - by simplify_map_eq.
       - intros Hnone. rewrite /incrementPC /incrementPC_gen in Hnone.
         simplify_map_eq.
     }
    Qed.

   Lemma wp_store_success_z_PC_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w z w'
         ea (imm : Z) :
     is_shadow_address ea = false →
     decodeInstrW w = Store PC (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true → withinBounds pc_b pc_e ea = true →
     (pc_a + imm)%a = Some ea →

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ ea ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ w
              ∗ ea ↦ₐ WInt z }}}.
   Proof.
     iIntros (Hshadow Hinstr Hvpc Hpca' Hwa Hwb Hadd φ)
             "(>HPC & >Hi & >Hsrca) Hφ".
     have Hstore_word : store_word pc_p (WInt z) = WInt z.
     { apply store_word_canStore, writeAllowed_canStore_int, Hwa. }
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iApply (wp_store_imm _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try (intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & _); simplify_map_eq; congruence).
    { eapply mem_neq_implies_allow_store_map_imm with (a := pc_a) (ea := ea); eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as
      [p0 g0 b0 e0 a0 ea0 storev oldv Harg Hallow Hordinary Hold Hmem' Hshadow' Hinc
      |p0 g0 b0 e0 a0 ea0 heap_a z0 old_status Harg Hallow Hshadow_addr Htranslate Hstatus Hmem' Hshadow' Hinc
      |Hmem' Hshadow' Hfail]; try (simplify_map_eq; congruence).
     { (* Success *)
       iApply "Hφ".
       destruct Hallow as [Hrr2 [Hadd2 _]]. simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       try rewrite insert_insert_eq.
       iDestruct (regs_of_map_1 with "[$Hmap]") as "HPC"; eauto.
       all: try rewrite Hstore_word; iFrame. }
     { (* Failure (contradiction) *)
       exfalso.
       eapply (Store_failure_impossible _ _ _ _ _ pc_p pc_g pc_b pc_e pc_a _); eauto.
       - by simplify_map_eq.
       - intros Hnone. rewrite /incrementPC /incrementPC_gen in Hnone.
         simplify_map_eq.
     }
    Qed.

   Lemma wp_store_success_reg_same_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst w'
         p g b e a ea (imm : Z) :
     is_shadow_address ea = false →
     decodeInstrW w = Store dst (inr dst) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     dst ≠ cnull ->

     canStore p (WCap true p g b e a) = true →
     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a
           ∗ ▷ ea ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ w
              ∗ dst ↦ᵣ WCap true p g b e a
              ∗ ea ↦ₐ WCap true p g b e a }}}.
   Proof.
     iIntros (Hshadow Hinstr Hvpc Hpca' Hwa Hwb Hadd ? HcanStore φ) "Hres Hφ".
     iApply (wp_store_success_reg_same_store_word_imm with "Hres"); eauto.
     iNext. iIntros "Hpost".
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Hpost".
     iApply "Hφ". iExact "Hpost".
   Qed.

   Lemma wp_store_success_reg_PC_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w src w'
         ea (imm : Z) w'' :
     is_shadow_address ea = false →
      decodeInstrW w = Store PC (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true → withinBounds pc_b pc_e ea = true →
     (pc_a + imm)%a = Some ea →
     src ≠ cnull ->

     canStore pc_p (w'') = true →
     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ ea ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ w
              ∗ src ↦ᵣ w''
              ∗ ea ↦ₐ w'' }}}.
    Proof.
     iIntros (Hshadow Hinstr Hvpc Hpca' Hwa Hwb Hadd ? HcanStore φ) "Hres Hφ".
     iApply (wp_store_success_reg_PC_store_word_imm with "Hres"); eauto.
     iNext. iIntros "Hpost".
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Hpost".
     iApply "Hφ". iExact "Hpost".
   Qed.

   Lemma wp_store_success_reg_PC_same_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w w'
         ea (imm : Z) :
     is_shadow_address ea = false →
     decodeInstrW w = Store PC (inr PC) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true → withinBounds pc_b pc_e ea = true →
     (pc_a + imm)%a = Some ea →

     canStore pc_p (WCap true pc_p pc_g pc_b pc_e pc_a) = true →
     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ ea ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ w
              ∗ ea ↦ₐ WCap true pc_p pc_g pc_b pc_e pc_a }}}.
   Proof.
     iIntros (Hshadow Hinstr Hvpc Hpca' Hwa Hwb Hadd HcanStore φ) "Hres Hφ".
     iApply (wp_store_success_reg_PC_same_store_word_imm with "Hres"); eauto.
     iNext. iIntros "Hpost".
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Hpost".
     iApply "Hφ". iExact "Hpost".
   Qed.

   Lemma wp_store_success_reg_fromPC_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst w'
         p g b e a ea (imm : Z) :
     is_shadow_address ea = false →
     decodeInstrW w = Store dst (inr PC) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a
           ∗ ▷ ea ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ w
              ∗ dst ↦ᵣ WCap true p g b e a
              ∗ ea ↦ₐ store_word p (WCap true pc_p pc_g pc_b pc_e pc_a) }}}.
   Proof.
    iIntros (Hshadow Hinstr Hvpc Hpca' Hwa Hwb Hadd ? φ)
             "(>HPC & >Hi & >Hdst & >Hsrca) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iApply (wp_store_imm _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try (intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & _); simplify_map_eq; congruence).
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_store_map_imm with (a := a) (ea := ea); eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     { (* Success *)
       iApply "Hφ".
       destruct H3 as [Hrr2 [Hadd2 _]]. simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_eq.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hdst]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       exfalso.
       eapply (Store_failure_impossible _ _ _ _ _ p g b e a _); eauto.
       - by simplify_map_eq.
       - intros Hnone. rewrite /incrementPC /incrementPC_gen in Hnone.
         simplify_map_eq.
     }
    Qed.

   Lemma wp_store_success_reg_fromPC_same_a_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst
         p g b e a (imm : Z) :
     is_shadow_address pc_a = false →
     decodeInstrW w = Store dst (inr PC) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     (a + imm)%a = Some pc_a →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ store_word p (WCap true pc_p pc_g pc_b pc_e pc_a)
              ∗ dst ↦ᵣ WCap true p g b e a }}}.
   Proof.
     iIntros (Hshadow Hinstr Hvpc Hpca' Hwa Hwb Hadd ? φ)
            "(>HPC & >Hi & >Hdst) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
     iDestruct (memMap_resource_1 with "Hi") as "Hmem".

    iApply (wp_store_imm _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try (intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & _); simplify_map_eq; congruence).
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_eq_implies_allow_store_map_imm; eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     { (* Success *)
       iApply "Hφ".
       destruct H2 as [? [Hadd2 _]]; simplify_map_eq.
       rewrite memMap_resource_1.
       incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       exfalso.
       eapply (Store_failure_impossible _ _ _ _ _ p g b e a _); eauto.
       - by simplify_map_eq.
       - intros Hnone. rewrite /incrementPC /incrementPC_gen in Hnone.
         simplify_map_eq.
     }
   Qed.

  Lemma wp_store_success_mem E pc_p pc_g pc_b pc_e pc_a
    dst src w regs regs' mem p g b e a storev oldv :
    decodeInstrW w = Store dst src 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Store dst src 0) ⊆ dom regs →
    mem !! pc_a = Some w →
    reg_allows_store regs dst p g b e a →
    word_of_argument regs src = Some storev →
    is_shadow_address a = false →
    mem !! a = Some oldv →
    incrementPC regs = Some regs' →
    {{{ (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        ([∗ map] a↦w ∈ <[a:=store_word p storev]> mem, a ↦ₐ w) ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    intros Hinstr Hvpc HPC Dregs Hmem Hallow Harg Hshadow Hlookup Hinc.
    eapply wp_store_success_mem_imm with (imm := 0) (ea := a); eauto.
    destruct Hallow as (Hdst & Hwa & Hwb).
    unfold reg_allows_store_imm. repeat split; eauto; try by rewrite finz_add_0.
  Qed.

  Lemma wp_store_success_shadow E pc_p pc_g pc_b pc_e pc_a
    dst src w regs regs' mem shadow p g b e a heap_a revoked old_revoked :
    decodeInstrW w = Store dst src 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Store dst src 0) ⊆ dom regs →
    mem !! pc_a = Some w →
    reg_allows_store regs dst p g b e a →
    word_of_argument regs src = Some (WInt (encodeAllocStatus revoked)) →
    is_shadow_address a = true →
    shadow_to_heap a = Some heap_a →
    shadow !! heap_a = Some old_revoked →
    incrementPC regs = Some regs' →
    {{{ (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
        (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ revoked) ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        ([∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
        ([∗ map] a↦revoked ∈ <[heap_a:=revoked]> shadow, a ↦ₛ revoked) ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem Hallow Harg Hshadow Htranslate Hlookup Hinc φ)
      "(>Hmem & >Hshadow & >Hmap) Hφ".
    iApply (wp_store with "[$Hmem $Hshadow $Hmap]"); eauto.
    { intros p0 g0 b0 e0 a0 v0 (Hdst0 & _) Harg0.
      destruct Hallow as (Hdst & _). simplify_eq.
      rewrite Hshadow. intros _. exists heap_a. split; first done. by eexists. }
    iNext. iIntros (regs0 mem0 shadow0 retv) "(%Hspec & Hmem & Hshadow & Hmap)".
    destruct Hallow as (Hdst & Hwa & Hwb).
    destruct Hspec as
      [p0 g0 b0 e0 a0 ea0 v0 oldv0 Harg0 (Hdst0 & Hadd0 & _) Hshadow0 Hlookup0 -> -> Hinc0
      |p0 g0 b0 e0 a0 ea0 heap_a0 z0 old_status0 Harg0 (Hdst0 & Hadd0 & _) Hshadow0 Htranslate0 Hlookup0 -> -> Hinc0
      |Hmem_eq Hshadow_eq Hfail]; simplify_eq.
    - rewrite finz_add_0 in Hadd0. inversion Hadd0; subst ea0. congruence.
    - rewrite finz_add_0 in Hadd0. inversion Hadd0; subst ea0.
      assert (heap_a0 = heap_a) as -> by congruence.
      iApply "Hφ". try rewrite decode_encode_alloc_status_inv. iFrame.
    - destruct Hfail as
        [w0 Hreg0 Hcap0|p0 g0 b0 e0 a0 Htag0|p0 g0 b0 e0 a0 Hreg0 Hadd0 Haddr0|
         p0 g0 b0 e0 a0 ea0 Hreg0 Hadd0 Hbounds0|Hpc0|
         p0 g0 b0 e0 a0 ea0 v0 Hreg0 Hadd0 Hshadow0 Harg0 Hbad0].
      + rewrite Hreg0 in Hdst. inversion Hdst; subst. unfold is_cap in Hcap0. cbn in Hcap0. discriminate.
      + rewrite Htag0 in Hdst. inversion Hdst.
      + rewrite finz_add_0 in Hadd0. discriminate.
      + rewrite finz_add_0 in Hadd0. inversion Hadd0; subst ea0.
        rewrite Hreg0 in Hdst. inversion Hdst; subst. destruct Hbounds0; congruence.
      + congruence.
      + rewrite finz_add_0 in Hadd0. inversion Hadd0; subst ea0.
        rewrite Hreg0 in Hdst. inversion Hdst; subst. congruence.
  Qed.

  Lemma wp_store_success_z_PC E pc_p pc_g pc_b pc_e pc_a pc_a' w z :
     is_shadow_address pc_a = false →
     decodeInstrW w = Store PC (inl z) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ (WInt z) }}}.
  Proof.
    intros. eapply wp_store_success_z_PC_same_a_imm with (imm := 0); eauto.
    by rewrite finz_add_0.
  Qed.

   Lemma wp_store_success_reg_PC_store_word E src wsrc pc_p pc_g pc_b pc_e pc_a pc_a' w :
     is_shadow_address pc_a = false →
     decodeInstrW w = Store PC (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →
     src ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ wsrc }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ store_word pc_p wsrc
              ∗ src ↦ᵣ wsrc }}}.
   Proof.
    intros. eapply wp_store_success_reg_PC_same_a_store_word_imm with (imm := 0); eauto.
    by rewrite finz_add_0.
  Qed.

   Lemma wp_store_success_reg_PC E src wsrc pc_p pc_g pc_b pc_e pc_a pc_a' w :
     is_shadow_address pc_a = false →
     decodeInstrW w = Store PC (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →
     canStore pc_p wsrc = true ->
     src ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ wsrc }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ wsrc
              ∗ src ↦ᵣ wsrc }}}.
  Proof.
    iIntros (Hshadow Hinstr Hvpc Hpca' Hwa HcanStore Hsrc φ) "Hres Hφ".
    iApply (wp_store_success_reg_PC_same_a_store_word_imm with "Hres"); eauto;
      try by rewrite finz_add_0.
    iNext. iIntros "Hpost".
    iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Hpost".
    iApply "Hφ". iExact "Hpost".
  Qed.

   Lemma wp_store_success_reg_PC_same_store_word E pc_p pc_g pc_b pc_e pc_a pc_a' w w' :
     is_shadow_address pc_a = false →
     decodeInstrW w = Store PC (inr PC) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ store_word pc_p (WCap true pc_p pc_g pc_b pc_e pc_a) }}}.
   Proof.
    intros. eapply wp_store_success_reg_PC_same_same_a_store_word_imm with (imm := 0); eauto.
    by rewrite finz_add_0.
  Qed.

   Lemma wp_store_success_reg_PC_same E pc_p pc_g pc_b pc_e pc_a pc_a' w w' :
     is_shadow_address pc_a = false →
     decodeInstrW w = Store PC (inr PC) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →
     canStore pc_p (WCap true pc_p pc_g pc_b pc_e pc_a) = true ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ WCap true pc_p pc_g pc_b pc_e pc_a }}}.
  Proof.
    iIntros (Hshadow Hinstr Hvpc Hpca' Hwa HcanStore φ) "Hres Hφ".
    iApply (wp_store_success_reg_PC_same_same_a_store_word_imm with "Hres"); eauto;
      try by rewrite finz_add_0.
    iNext. iIntros "Hpost".
    iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Hpost".
    iApply "Hφ". iExact "Hpost".
  Qed.

   Lemma wp_store_success_same E pc_p pc_g pc_b pc_e pc_a pc_a' w dst z w'
         p g b e :
     is_shadow_address pc_a = false →
     decodeInstrW w = Store dst (inl z) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ WCap true p g b e pc_a }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ (WInt z)
              ∗ dst ↦ᵣ WCap true p g b e pc_a }}}.
  Proof.
    intros. eapply wp_store_success_same_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_success_reg_same'_store_word E pc_p pc_g pc_b pc_e pc_a pc_a' w dst
         p g b e :
     is_shadow_address pc_a = false →
     decodeInstrW w = Store dst (inr dst) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ WCap true p g b e pc_a }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ store_word p (WCap true p g b e pc_a)
              ∗ dst ↦ᵣ WCap true p g b e pc_a }}}.
   Proof.
    intros. eapply wp_store_success_reg_same'_store_word_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_success_reg_same' E pc_p pc_g pc_b pc_e pc_a pc_a' w dst
         p g b e :
     is_shadow_address pc_a = false →
     decodeInstrW w = Store dst (inr dst) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     canStore p (WCap true p g b e pc_a) = true ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ WCap true p g b e pc_a }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ WCap true p g b e pc_a
              ∗ dst ↦ᵣ WCap true p g b e pc_a }}}.
  Proof.
    intros. eapply wp_store_success_reg_same'_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_success_reg_same_a_store_word E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src
         p g b e w'' :
      is_shadow_address pc_a = false →
     decodeInstrW w = Store dst (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ WCap true p g b e pc_a }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ store_word p w''
              ∗ src ↦ᵣ w''
              ∗ dst ↦ᵣ WCap true p g b e pc_a}}}.
   Proof.
    intros. eapply wp_store_success_reg_same_a_store_word_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_success_reg_same_a E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src
         p g b e w'' :
     is_shadow_address pc_a = false →
      decodeInstrW w = Store dst (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     canStore p w'' = true ->
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ WCap true p g b e pc_a }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ w''
              ∗ src ↦ᵣ w''
              ∗ dst ↦ᵣ WCap true p g b e pc_a}}}.
  Proof.
    intros. eapply wp_store_success_reg_same_a_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_success_reg_store_word E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src w'
         p g b e a w'' :
      is_shadow_address a = false →
     decodeInstrW w = Store dst (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ WCap true p g b e a
           ∗ ▷ a ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ w
              ∗ src ↦ᵣ w''
              ∗ dst ↦ᵣ WCap true p g b e a
              ∗ a ↦ₐ store_word p w'' }}}.
    Proof.
    intros. eapply wp_store_success_reg_store_word_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_success_reg E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src w'
         p g b e a w'' :
     is_shadow_address a = false →
      decodeInstrW w = Store dst (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →
     canStore p w'' = true ->
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ WCap true p g b e a
           ∗ ▷ a ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ w
              ∗ src ↦ᵣ w''
              ∗ dst ↦ᵣ WCap true p g b e a
              ∗ a ↦ₐ w'' }}}.
  Proof.
    intros. eapply wp_store_success_reg_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_success_reg_same_store_word E pc_p pc_g pc_b pc_e pc_a pc_a' w dst w'
         p g b e a :
     is_shadow_address a = false →
     decodeInstrW w = Store dst (inr dst) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a
           ∗ ▷ a ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ w
              ∗ dst ↦ᵣ WCap true p g b e a
              ∗ a ↦ₐ store_word p (WCap true p g b e a) }}}.
   Proof.
    intros. eapply wp_store_success_reg_same_store_word_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_success_reg_same E pc_p pc_g pc_b pc_e pc_a pc_a' w dst w'
         p g b e a :
     is_shadow_address a = false →
     decodeInstrW w = Store dst (inr dst) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →
     canStore p (WCap true p g b e a) = true ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a
           ∗ ▷ a ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ w
              ∗ dst ↦ᵣ WCap true p g b e a
              ∗ a ↦ₐ WCap true p g b e a }}}.
  Proof.
    intros. eapply wp_store_success_reg_same_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_success_z E pc_p pc_g pc_b pc_e pc_a pc_a' w dst z w'
         p g b e a :
     is_shadow_address a = false →
     decodeInstrW w = Store dst (inl z) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a
           ∗ ▷ a ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ w
              ∗ dst ↦ᵣ WCap true p g b e a
              ∗ a ↦ₐ WInt z }}}.
  Proof.
    intros. eapply wp_store_success_z_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_fail_reg_not_cap E pc_p pc_g pc_b pc_e pc_a w
     dst src wdst wstore :
      decodeInstrW w = Store dst (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     is_cap wdst = false ->
     src ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ wstore
           ∗ ▷ dst ↦ᵣ wdst
     }}}
       Instr Executable @ E
       {{{ RET FailedV; True}}}.
  Proof.
    intros. eapply wp_store_fail_reg_not_cap_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

    Lemma wp_store_fail_z_not_cap E pc_p pc_g pc_b pc_e pc_a w
     dst z wdst :
      decodeInstrW w = Store dst (inl z) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     is_cap wdst = false ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ wdst
     }}}
       Instr Executable @ E
       {{{ RET FailedV; True}}}.
  Proof.
    intros. eapply wp_store_fail_z_not_cap_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_fail_reg_perm E pc_p pc_g pc_b pc_e pc_a w dst src
         p g b e a w'' :
      decodeInstrW w = Store dst (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     writeAllowed p = false ->
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ WCap true p g b e a
     }}}
       Instr Executable @ E
       {{{ RET FailedV; True}}}.
  Proof.
    intros. eapply wp_store_fail_reg_perm_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

    Lemma wp_store_fail_z_perm E pc_p pc_g pc_b pc_e pc_a w dst
         p g b e a z :
      decodeInstrW w = Store dst (inl z) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     writeAllowed p = false ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a
     }}}
       Instr Executable @ E
       {{{ RET FailedV; True}}}.
  Proof.
    intros. eapply wp_store_fail_z_perm_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_fail_reg E pc_p pc_g pc_b pc_e pc_a w dst src
         p g b e a w'' :
      decodeInstrW w = Store dst (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     withinBounds b e a = false →
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ WCap true p g b e a
     }}}
       Instr Executable @ E
       {{{ RET FailedV; True}}}.
  Proof.
    intros. eapply wp_store_fail_reg_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

    Lemma wp_store_fail_z E pc_p pc_g pc_b pc_e pc_a w dst
         p g b e a z :
      decodeInstrW w = Store dst (inl z) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     withinBounds b e a = false →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a
     }}}
       Instr Executable @ E
       {{{ RET FailedV; True}}}.
  Proof.
    intros. eapply wp_store_fail_z_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

  Lemma wp_store_success_shadow_z E pc_p pc_g pc_b pc_e pc_a pc_a' w
    dst p g b e a revoked old_revoked heap_a :
    is_shadow_address a = true →
    shadow_to_heap a = Some heap_a →
    decodeInstrW w = Store dst (inl (encodeAllocStatus revoked)) 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    writeAllowed p = true →
    withinBounds b e a = true →
    dst ≠ cnull →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
        ▷ pc_a ↦ₐ w ∗
        ▷ dst ↦ᵣ WCap true p g b e a ∗
        ▷ heap_a ↦ₛ old_revoked }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
        pc_a ↦ₐ w ∗
        dst ↦ᵣ WCap true p g b e a ∗
        heap_a ↦ₛ revoked }}}.
  Proof.
    iIntros (Hshadow Htranslate Hinstr Hvpc Hpca' Hwa Hwb ? φ)
      "(>HPC & >Hi & >Hdst & >Ha) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (memMap_resource_1 with "Hi") as "Hmem".
    iAssert ([∗ map] a0↦rev ∈ {[heap_a:=old_revoked]}, a0 ↦ₛ rev)%I
      with "[Ha]" as "Hshadow".
    { by rewrite big_sepM_singleton. }
    iApply (wp_store_success_shadow _ pc_p pc_g with "[$Hmem $Hshadow $Hmap]");
      eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { unfold reg_allows_store. split; first by simplify_map_eq.
      repeat split; auto. }
    { by rewrite /incrementPC /incrementPC_gen; simplify_map_eq. }
    iNext. iIntros "(Hmem & Hshadow & Hmap)". iApply "Hφ".
    iEval (rewrite insert_insert_eq big_sepM_singleton) in "Hshadow".
    rewrite !insert_insert_eq memMap_resource_1.
    iDestruct (regs_of_map_2 with "Hmap") as "[HPC Hr]"; eauto. iFrame.
  Qed.

  Lemma wp_store_success_shadow_reg E pc_p pc_g pc_b pc_e pc_a pc_a' w
    dst p g b e a src revoked old_revoked heap_a :
    is_shadow_address a = true →
    shadow_to_heap a = Some heap_a →
    decodeInstrW w = Store dst (inr src) 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    writeAllowed p = true →
    withinBounds b e a = true →
    src ≠ cnull →
    dst ≠ cnull →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
        ▷ pc_a ↦ₐ w ∗
        ▷ src ↦ᵣ WInt (encodeAllocStatus revoked) ∗
        ▷ dst ↦ᵣ WCap true p g b e a ∗
        ▷ heap_a ↦ₛ old_revoked }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
        pc_a ↦ₐ w ∗
        src ↦ᵣ WInt (encodeAllocStatus revoked) ∗
        dst ↦ᵣ WCap true p g b e a ∗
        heap_a ↦ₛ revoked }}}.
  Proof.
    iIntros (Hshadow Htranslate Hinstr Hvpc Hpca' Hwa Hwb ? ? φ)
      "(>HPC & >Hi & >Hsrc & >Hdst & >Ha) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (memMap_resource_1 with "Hi") as "Hmem".
    iAssert ([∗ map] a0↦rev ∈ {[heap_a:=old_revoked]}, a0 ↦ₛ rev)%I
      with "[Ha]" as "Hshadow".
    { by rewrite big_sepM_singleton. }
    iApply (wp_store_success_shadow _ pc_p pc_g with "[$Hmem $Hshadow $Hmap]");
      eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { unfold reg_allows_store. split; first by simplify_map_eq.
      repeat split; auto. }
    { by rewrite /incrementPC /incrementPC_gen; simplify_map_eq. }
    iNext. iIntros "(Hmem & Hshadow & Hmap)". iApply "Hφ".
    iEval (rewrite insert_insert_eq big_sepM_singleton) in "Hshadow".
    rewrite !insert_insert_eq memMap_resource_1.
    iDestruct (regs_of_map_3 with "Hmap") as "(HPC & Hsrc & Hdst)"; eauto. iFrame.
  Qed.

  Lemma wp_store_success_shadow_z_PC E pc_p pc_g pc_b pc_e pc_a pc_a' w
    revoked old_revoked heap_a :
    is_shadow_address pc_a = true →
    shadow_to_heap pc_a = Some heap_a →
    decodeInstrW w = Store PC (inl (encodeAllocStatus revoked)) 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    writeAllowed pc_p = true →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
        ▷ pc_a ↦ₐ w ∗
        ▷ heap_a ↦ₛ old_revoked }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
        pc_a ↦ₐ w ∗
        heap_a ↦ₛ revoked }}}.
  Proof.
    iIntros (Hshadow Htranslate Hinstr Hvpc Hpca' Hwa φ)
      "(>HPC & >Hi & >Ha) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iDestruct (memMap_resource_1 with "Hi") as "Hmem".
    iAssert ([∗ map] a0↦rev ∈ {[heap_a:=old_revoked]}, a0 ↦ₛ rev)%I
      with "[Ha]" as "Hshadow".
    { by rewrite big_sepM_singleton. }
    iApply (wp_store_success_shadow _ pc_p pc_g with "[$Hmem $Hshadow $Hmap]");
      eauto; simplify_map_eq; eauto.
    { unfold reg_allows_store. split; first by simplify_map_eq.
      repeat split; auto.
      apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [_ Hwb].
      by apply Is_true_true. }
    { by rewrite /incrementPC /incrementPC_gen; simplify_map_eq. }
    iNext. iIntros "(Hmem & Hshadow & Hmap)". iApply "Hφ".
    iEval (rewrite insert_insert_eq big_sepM_singleton) in "Hshadow".
    rewrite !insert_insert_eq memMap_resource_1.
    iDestruct (regs_of_map_1 with "Hmap") as "HPC"; eauto. iFrame.
  Qed.

  Lemma wp_store_success_shadow_reg_PC E pc_p pc_g pc_b pc_e pc_a pc_a' w
    src revoked old_revoked heap_a :
    is_shadow_address pc_a = true →
    shadow_to_heap pc_a = Some heap_a →
    decodeInstrW w = Store PC (inr src) 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    writeAllowed pc_p = true →
    src ≠ cnull →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
        ▷ pc_a ↦ₐ w ∗
        ▷ src ↦ᵣ WInt (encodeAllocStatus revoked) ∗
        ▷ heap_a ↦ₛ old_revoked }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
        pc_a ↦ₐ w ∗
        src ↦ᵣ WInt (encodeAllocStatus revoked) ∗
        heap_a ↦ₛ revoked }}}.
  Proof.
    iIntros (Hshadow Htranslate Hinstr Hvpc Hpca' Hwa ? φ)
      "(>HPC & >Hi & >Hsrc & >Ha) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hsrc") as "[Hmap %]".
    iDestruct (memMap_resource_1 with "Hi") as "Hmem".
    iAssert ([∗ map] a0↦rev ∈ {[heap_a:=old_revoked]}, a0 ↦ₛ rev)%I
      with "[Ha]" as "Hshadow".
    { by rewrite big_sepM_singleton. }
    iApply (wp_store_success_shadow _ pc_p pc_g with "[$Hmem $Hshadow $Hmap]");
      eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { unfold reg_allows_store. split; first by simplify_map_eq.
      repeat split; auto.
      apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [_ Hwb].
      by apply Is_true_true. }
    { by rewrite /incrementPC /incrementPC_gen; simplify_map_eq. }
    iNext. iIntros "(Hmem & Hshadow & Hmap)". iApply "Hφ".
    iEval (rewrite insert_insert_eq big_sepM_singleton) in "Hshadow".
    rewrite !insert_insert_eq memMap_resource_1.
    iDestruct (regs_of_map_2 with "Hmap") as "[HPC Hr]"; eauto. iFrame.
  Qed.

  Lemma wp_store_fail_shadow_reg E pc_p pc_g pc_b pc_e pc_a w
    dst src storev p g b e a :
    is_shadow_address a = true →
    decodeInstrW w = Store dst (inr src) 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (∀ z : Z, storev ≠ WInt z) →
    src ≠ cnull →
    dst ≠ cnull →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
        ▷ pc_a ↦ₐ w ∗
        ▷ src ↦ᵣ storev ∗
        ▷ dst ↦ᵣ WCap true p g b e a }}}
      Instr Executable @ E
    {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hshadow Hinstr Hvpc Hinvalid ? ? φ)
      "(>HPC & >Hi & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (memMap_resource_1 with "Hi") as "Hmem".
    iApply (wp_store _ pc_p pc_g with "[$Hmem $Hmap]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { intros p0 g0 b0 e0 a0 v0 (Hdst & _) Harg. simplify_map_eq.
      rewrite Hshadow. intros [rev Hrev].
      exfalso. by apply (Hinvalid rev). }
    iNext. iIntros (regs' mem' shadow' retv) "(%Hspec & _ & _ & _)".
    destruct Hspec as
      [p0 g0 b0 e0 a0 ea0 v0 oldv Harg (Hdst & Hadd & _ & _) Hshadow0 Hlookup0 -> -> Hinc0
      |p0 g0 b0 e0 a0 ea0 heap_a0 z0 old_status0 Harg (Hdst & Hadd & _ & _) Hshadow0 Htranslate0 Hlookup0 -> -> Hinc0
      |]; last by iApply "Hφ".
    - rewrite finz_add_0 in Hadd. inversion Hadd; subst ea0.
      simplify_map_eq; congruence.
    - rewrite finz_add_0 in Hadd. inversion Hadd; subst ea0.
      by simplify_map_eq.
  Qed.

  Lemma wp_store_fail_tag E pc_p pc_g pc_b pc_e pc_a
      w dst (src : Z + RegName) regs wa :
    decodeInstrW w = Store dst src 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !!ᵣ dst = Some wa →
    get_tag wa = false →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FailedV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    intros. eapply wp_store_fail_tag_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.
Lemma wp_store_fail_reg_overflow_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a w dst src
         p g b e a w'' :
     decodeInstrW w = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (a + imm)%a = None →
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ WCap true p g b e a
     }}}
       Instr Executable @ E
       {{{ RET FailedV; True}}}.
    Proof.
      iIntros (Hinstr Hvpc Hadd ?? φ)
             "(>HPC & >Hi & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (memMap_resource_1 with "Hi") as "Hmem"; auto.

    iApply (wp_store_imm _ pc_p pc_g pc_b pc_e pc_a dst (inr src) imm w
      with "[$Hmap $Hmem]"); try done; try (by simplify_map_eq).
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /allow_store_map_or_true_imm.
      eexists true,p,g,b,e,a,w''.
      split.
      { rewrite /read_reg_inr.
        by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert_eq.
      }
      split.
      { rewrite /word_of_argument.
        by simplify_map_eq.
      }
      rewrite /reg_allows_store_imm.
      by rewrite Hadd.
      }
    { intros p0 g0 b0 e0 a0 ea (Hdst & Haddr & _).
      simpl_map_regs by eauto. simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     { (* Success (contradiction) *)
       exfalso.
       rewrite /reg_allows_store_imm in H5.
       destruct H5 as (? & Haddr & ? & Hbounds); simplify_map_eq.
     }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; by iApply "Hφ".
     }
    Qed.
Lemma wp_store_fail_z_overflow_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a w dst
         p g b e a z :
     decodeInstrW w = Store dst (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (a + imm)%a = None →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a
     }}}
       Instr Executable @ E
       {{{ RET FailedV; True}}}.
    Proof.
      iIntros (Hinstr Hvpc Hadd ? φ)
             "(>HPC & >Hi & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (memMap_resource_1 with "Hi") as "Hmem"; auto.

    iApply (wp_store_imm _ pc_p pc_g pc_b pc_e pc_a dst (inl z) imm w
      with "[$Hmap $Hmem]"); try done; try (by simplify_map_eq).
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /allow_store_map_or_true_imm.
      eexists true,p,g,b,e,a,_.
      split.
      { rewrite /read_reg_inr.
        by rewrite lookup_insert_ne // lookup_insert_eq.
      }
      split.
      { rewrite /word_of_argument. eauto.
      }
      rewrite /reg_allows_store_imm.
      by rewrite Hadd.
      }
    { intros p0 g0 b0 e0 a0 ea (Hdst & Haddr & _).
      simpl_map_regs by eauto. simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     { (* Success (contradiction) *)
       exfalso.
       rewrite /reg_allows_store_imm in H2.
       destruct H2 as (? & Haddr & ? & Hbounds); simplify_map_eq.
     }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; by iApply "Hφ".
     }
    Qed.


End griotte_lang_rules.
