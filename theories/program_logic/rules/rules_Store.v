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

  Definition reg_allows_store (regs : Reg) (r : RegName) p g b e a :=
    regs !!ᵣ r = Some (WCap true p g b e a) ∧
    writeAllowed p = true ∧ withinBounds b e a = true.

  Inductive Store_failure (regs: Reg) (r1 : RegName)(r2 : Z + RegName) (mem : gmap Addr Word):=
  | Store_fail_const w:
      regs !!ᵣ r1 = Some w ->
      is_cap w = false →
      Store_failure regs r1 r2 mem
  | Store_fail_tag p g b e a:
      regs !!ᵣ r1 = Some (WCap false p g b e a) →
      Store_failure regs r1 r2 mem
  | Store_fail_bounds p g b e a:
      regs !!ᵣ r1 = Some(WCap true p g b e a) ->
      (writeAllowed p = false ∨ withinBounds b e a = false) →
      Store_failure regs r1 r2 mem
  | Store_fail_invalid_PC:
      incrementPC (regs) = None ->
      Store_failure regs r1 r2 mem
  .

  Inductive Store_spec
    (regs: Reg) (r1 : RegName) (r2 : Z + RegName)
    (regs': Reg) (mem mem' : gmap Addr Word) : griotte_lang.val → Prop
  :=
  | Store_spec_success p g b e a storev oldv :
      word_of_argument regs r2 = Some storev ->
      reg_allows_store regs r1 p g b e a →
      mem !! a = Some oldv →
      mem' = (<[a := store_word p storev]> mem) →
      incrementPC(regs) = Some regs' ->
      Store_spec regs r1 r2 regs' mem mem' NextIV
  | Store_spec_failure_store :
      mem' = mem →
      Store_failure regs r1 r2 mem ->
      Store_spec regs r1 r2 regs' mem mem' FailedV.

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

   Lemma wp_store Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 (r2 : Z + RegName) w mem regs :
   decodeInstrW w = Store r1 r2 →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Store r1 r2) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_store_map_or_true r1 r2 regs mem →

   {{{ (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ regs' mem' retv, RET retv;
       ⌜ Store_spec regs r1 r2 regs' mem mem' retv⌝ ∗
         ([∗ map] a↦w ∈ mem', a ↦ₐ w) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
   Proof.
     iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaStore φ) "(>Hmem & >Hmap) Hφ".
     iApply wp_lift_atomic_base_step_no_fork; auto.
     iIntros (σ1 ns l1 l2 nt) "[ [Hr Hsr] Hm ] /=". destruct σ1 as [ [r sr] m]; cbn.
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
       assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
       {
         unfold is_cap in Hr1v.
         destruct_word r1v; by simplify_pair_eq.
       }
       iFailWP "Hφ" Store_fail_const.
     }
     destruct r1v as [ | [t p g b e a | ] | | ]; try inversion Hr1v. clear Hr1v.
     destruct t.
     2: {
       inversion Hstep; subst c σ2.
       iFailWP "Hφ" Store_fail_tag.
     }

     destruct (writeAllowed p && withinBounds b e a) eqn:HWA.
     2 : { (* Failure: r2 is either not within bounds or doesnt allow reading *)
       inversion Hstep.
       apply andb_false_iff in HWA.
       iFailWP "Hφ" Store_fail_bounds.
     }
     apply andb_true_iff in HWA; destruct HWA as (Hwa & Hwb).

     (* Prove that a is in the memory map now, otherwise we cannot continue *)
     pose proof (allow_store_implies_storev r1 r2 mem regs p g b e a storev) as (oldv & Hmema); auto.

     (* Given this, prove that a is also present in the memory itself *)
     iDestruct (gen_mem_valid_inSepM mem m a oldv with "Hm Hmem" ) as %Hma' ; auto.

     destruct (incrementPC regs ) as [ regs' |] eqn:Hregs'.
     2: { (* Failure: the PC could not be incremented correctly *)
       assert (incrementPC r = None).
       { eapply incrementPC_overflow_mono; first eapply Hregs'; eauto. }
       rewrite incrementPC_fail_updatePC /= in Hstep; auto.
       inversion Hstep.
       cbn; iFrame; iApply "Hφ"; iFrame.
       iPureIntro. eapply Store_spec_failure_store;eauto. by constructor.
     }

     iMod ((gen_mem_update_inSepM _ _ a) with "Hm Hmem") as "[Hm Hmem]"; eauto.

     (* Success *)
     rewrite /update_mem /= in Hstep.
     eapply (incrementPC_success_updatePC _ sr (<[a:=store_word p storev]> m)) in Hregs'
         as (t1 & p1 & g1 & b1 & e1 & a1 & a'1 & a_pc1 & HPC'' & HuPC & ->).
     eapply (updatePC_success_incl _ (<[a:=store_word p storev]> m)) in HuPC. 2: by eauto.
     rewrite HuPC in Hstep; clear HuPC; inversion Hstep; clear Hstep; subst c σ2; cbn in *.

     iFrame.
     iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     iFrame. iModIntro. iApply "Hφ". iFrame.
     iPureIntro. eapply Store_spec_success; eauto.
     * split; auto; [exact Hr'1|]; auto.
     * rewrite /incrementPC /incrementPC_gen. rewrite a_pc1 HPC''.
       Unshelve. all: auto.
   Qed.

  Lemma wp_store_success_z_PC E pc_p pc_g pc_b pc_e pc_a pc_a' w z :
     decodeInstrW w = Store PC (inl z) →
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
    iIntros (Hinstr Hvpc Hpca' Hwa φ)
            "(>HPC & >Hi) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iDestruct (memMap_resource_1 with "Hi") as "Hmem".

    iApply (wp_store with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { eapply mem_eq_implies_allow_store_map; eauto. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iApply "Hφ".
       destruct H0 as [Hrr2 _]. simplify_map_eq.
       rewrite memMap_resource_1.
       incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (regs_of_map_1 with "[$Hmap]") as "HPC"; eauto.
       rewrite /store_word (writeAllowed_canStore_int _ _ Hwa).
       iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto.
       - apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [_ Hwb].
         destruct o as [Hwa' | Hbounds]; first congruence.
         apply Is_true_false in Hbounds. done.
       - congruence.
     }
   Qed.

   Lemma wp_store_success_reg_PC_store_word E src wsrc pc_p pc_g pc_b pc_e pc_a pc_a' w :
     decodeInstrW w = Store PC (inr src) →
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
     iIntros (Hinstr Hvpc Hpca' Hwa ? φ)
            "(>HPC & >Hi & >Hsrc) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hsrc") as "[Hmap %]".
     iDestruct (memMap_resource_1 with "Hi") as "Hmem".

    iApply (wp_store with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_eq_implies_allow_store_map; eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iApply "Hφ".
       destruct H2 as (Hrdst & Hwa' & Hbounds).
       simplify_map_eq.
       rewrite memMap_resource_1.
       incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto.
       all: iFrame.
     }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto
       ; try congruence.
       apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [_ Hwb].
       destruct o; last apply Is_true_false in H1; try congruence ; try done.
     }
    Qed.

   Lemma wp_store_success_reg_PC_same_store_word E pc_p pc_g pc_b pc_e pc_a pc_a' w w' :
     decodeInstrW w = Store PC (inr PC) →
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
     iIntros (Hinstr Hvpc Hpca' Hwa φ)
            "(>HPC & >Hi) Hφ".
     iDestruct (map_of_regs_1 with "HPC") as "Hmap".
     iDestruct (memMap_resource_1 with "Hi") as "Hmem".

    iApply (wp_store with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { eapply mem_eq_implies_allow_store_map; eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iApply "Hφ".
       destruct H0 as [Hrr2 _]. simplify_map_eq.
       rewrite memMap_resource_1.
       incrementPC_inv.
       simplify_map_eq.
       do 2 rewrite insert_insert_eq.
       iDestruct (regs_of_map_1 with "[$Hmap]") as "HPC"; eauto.
       all: iFrame. }
      { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; try congruence.
       apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [_ Hwb].
       destruct o; last apply Is_true_false in H; [congruence| done].
     }
    Qed.

   Lemma wp_store_success_same E pc_p pc_g pc_b pc_e pc_a pc_a' w dst z w'
         p g b e :
     decodeInstrW w = Store dst (inl z) →
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
     iIntros (Hinstr Hvpc Hpca' Hwa Hwb ? φ)
            "(>HPC & >Hi & >Hdst) Hφ".
     have Hstore_word : store_word p (WInt z) = WInt z.
     { apply store_word_canStore, writeAllowed_canStore_int, Hwa. }
     iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
     iDestruct (memMap_resource_1 with "Hi") as "Hmem".

    iApply (wp_store _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_eq_implies_allow_store_map; eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iApply "Hφ".
       destruct H2 as [? _]; simplify_map_eq.
       rewrite memMap_resource_1.
       incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto.
       all: try rewrite Hstore_word; iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto.
       - destruct o; congruence.
       - congruence.
     }
     Qed.

   Lemma wp_store_success_reg_same'_store_word E pc_p pc_g pc_b pc_e pc_a pc_a' w dst
         p g b e :
     decodeInstrW w = Store dst (inr dst) →
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
     iIntros (Hinstr Hvpc Hpca' Hwa Hwb ? φ)
            "(>HPC & >Hi & >Hdst) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
     iDestruct (memMap_resource_1 with "Hi") as "Hmem".

    iApply (wp_store _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_eq_implies_allow_store_map; eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iApply "Hφ".
       destruct H2 as [? _]; simplify_map_eq.
       rewrite memMap_resource_1.
       incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; try congruence.
       destruct o; congruence.
     }
   Qed.

   Lemma wp_store_success_reg_same_a_store_word E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src
         p g b e w'' :
      decodeInstrW w = Store dst (inr src) →
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
     iIntros (Hinstr Hvpc Hpca' Hwa Hwb ?? φ)
             "(>HPC & >Hi & >Hsrc & >Hdst) Hφ".
     iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
     iDestruct (memMap_resource_1 with "Hi") as "Hmem".

    iApply (wp_store _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_eq_implies_allow_store_map; eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iApply "Hφ".
       destruct H5 as [? _]; simplify_map_eq.
       rewrite memMap_resource_1.
       incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hsrc Hdst] ]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; try congruence.
       destruct o; congruence.
     }
   Qed.

   Lemma wp_store_success_reg_store_word E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src w'
         p g b e a w'' :
      decodeInstrW w = Store dst (inr src) →
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
      iIntros (Hinstr Hvpc Hpca' Hwa Hwb ?? φ)
             "(>HPC & >Hi & >Hsrc & >Hdst & >Hsrca) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iApply (wp_store _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_store_map with (a := a); eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iApply "Hφ".
       destruct H6 as [? _]; simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_eq.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hsrc Hdst] ]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; try congruence.
       destruct o; congruence.
     }
    Qed.

   Lemma wp_store_success_reg_same_store_word E pc_p pc_g pc_b pc_e pc_a pc_a' w dst w'
         p g b e a :
     decodeInstrW w = Store dst (inr dst) →
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
    iIntros (Hinstr Hvpc Hpca' Hwa Hwb ? φ)
             "(>HPC & >Hi & >Hdst & >Hsrca) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iApply (wp_store _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_store_map with (a := a); eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iApply "Hφ".
       destruct H3 as [Hrr2 _]. simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_eq.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hdst]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; try congruence.
       destruct o; congruence.
     }
    Qed.

   Lemma wp_store_success_z E pc_p pc_g pc_b pc_e pc_a pc_a' w dst z w'
         p g b e a :
     decodeInstrW w = Store dst (inl z) →
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
     iIntros (Hinstr Hvpc Hpca' Hwa Hwb ? φ)
             "(>HPC & >Hi & >Hdst & >Hsrca) Hφ".
     have Hstore_word : store_word p (WInt z) = WInt z.
     { apply store_word_canStore, writeAllowed_canStore_int, Hwa. }
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iApply (wp_store _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_store_map with (a := a); eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iApply "Hφ".
       destruct H3 as [Hrr2 _]. simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_eq.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hdst]"; eauto.
       all: try rewrite Hstore_word; iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; last congruence.
       - destruct o; congruence.
     }
    Qed.

   Lemma wp_store_success_reg_PC E src wsrc pc_p pc_g pc_b pc_e pc_a pc_a' w :
     decodeInstrW w = Store PC (inr src) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →
     canStore pc_p wsrc = true →
     src ≠ cnull →
     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ wsrc }}}
       Instr Executable @ E
     {{{ RET NextIV;
         PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wsrc
           ∗ src ↦ᵣ wsrc }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hwa HcanStore Hsrc φ) "Hres Hφ".
     iApply (wp_store_success_reg_PC_store_word with "Hres"); eauto.
     iNext. iIntros "(HPC & Hi & Hsrc)".
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Hi".
     iApply "Hφ". iFrame.
   Qed.

   Lemma wp_store_success_reg_PC_same E pc_p pc_g pc_b pc_e pc_a pc_a' w w' :
     decodeInstrW w = Store PC (inr PC) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →
     canStore pc_p (WCap true pc_p pc_g pc_b pc_e pc_a) = true →
     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w }}}
       Instr Executable @ E
     {{{ RET NextIV;
         PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ WCap true pc_p pc_g pc_b pc_e pc_a }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hwa HcanStore φ) "Hres Hφ".
     iApply (wp_store_success_reg_PC_same_store_word with "Hres"); eauto.
     iNext. iIntros "(HPC & Hi)".
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Hi".
     iApply "Hφ". iFrame.
   Qed.

   Lemma wp_store_success_reg_same' E pc_p pc_g pc_b pc_e pc_a pc_a' w dst
       p g b e :
     decodeInstrW w = Store dst (inr dst) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     canStore p (WCap true p g b e pc_a) = true →
     dst ≠ cnull →
     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ WCap true p g b e pc_a }}}
       Instr Executable @ E
     {{{ RET NextIV;
         PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ WCap true p g b e pc_a
           ∗ dst ↦ᵣ WCap true p g b e pc_a }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hwa Hwb HcanStore Hdst φ) "Hres Hφ".
     iApply (wp_store_success_reg_same'_store_word with "Hres"); eauto.
     iNext. iIntros "(HPC & Hi & Hdst)".
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Hi".
     iApply "Hφ". iFrame.
   Qed.

   Lemma wp_store_success_reg_same_a E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src
       p g b e w'' :
     decodeInstrW w = Store dst (inr src) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     canStore p w'' = true →
     src ≠ cnull → dst ≠ cnull →
     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ WCap true p g b e pc_a }}}
       Instr Executable @ E
     {{{ RET NextIV;
         PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ w''
           ∗ src ↦ᵣ w''
           ∗ dst ↦ᵣ WCap true p g b e pc_a }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hwa Hwb HcanStore Hsrc Hdst φ) "Hres Hφ".
     iApply (wp_store_success_reg_same_a_store_word with "Hres"); eauto.
     iNext. iIntros "(HPC & Hi & Hsrc & Hdst)".
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Hi".
     iApply "Hφ". iFrame.
   Qed.

   Lemma wp_store_success_reg E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src w'
       p g b e a w'' :
     decodeInstrW w = Store dst (inr src) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →
     canStore p w'' = true →
     src ≠ cnull → dst ≠ cnull →
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
     iIntros (Hinstr Hvpc Hpca' Hwa Hwb HcanStore Hsrc Hdst φ) "Hres Hφ".
     iApply (wp_store_success_reg_store_word with "Hres"); eauto.
     iNext. iIntros "(HPC & Hi & Hsrc & Hdst & Ha)".
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Ha".
     iApply "Hφ". iFrame.
   Qed.

   Lemma wp_store_success_reg_same E pc_p pc_g pc_b pc_e pc_a pc_a' w dst w'
       p g b e a :
     decodeInstrW w = Store dst (inr dst) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →
     canStore p (WCap true p g b e a) = true →
     dst ≠ cnull →
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
     iIntros (Hinstr Hvpc Hpca' Hwa Hwb HcanStore Hdst φ) "Hres Hφ".
     iApply (wp_store_success_reg_same_store_word with "Hres"); eauto.
     iNext. iIntros "(HPC & Hi & Hdst & Ha)".
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Ha".
     iApply "Hφ". iFrame.
   Qed.

   Lemma wp_store_fail_reg_not_cap E pc_p pc_g pc_b pc_e pc_a w
     dst src wdst wstore :
      decodeInstrW w = Store dst (inr src) →
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

    iApply (wp_store _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /allow_store_map_or_true.
      eexists true,_,_,_,_,_,_; eauto.
      simplify_map_eq.
      split; [|split]; eauto.
      - rewrite /read_reg_inr; simplify_map_eq.
        destruct wdst as [| [] | |]; cbn in Hnot_cap; done.
      - rewrite /reg_allows_store; simplify_map_eq.
        rewrite decide_False; auto.
        intros [].
        destruct (decide (dst = cnull)); first done.
        destruct wdst as [| [] | |]; cbn in Hnot_cap; simplify_eq.
    }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /reg_allows_store in H4.
       destruct H4 as (? & ? & ?); simplify_map_eq.
       destruct (decide (dst = cnull)); first done.
       simplify_map_eq.
     }
     by iApply "Hφ".
     Unshelve. all: done.
    Qed.

    Lemma wp_store_fail_z_not_cap E pc_p pc_g pc_b pc_e pc_a w
     dst z wdst :
      decodeInstrW w = Store dst (inl z) →
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

    iApply (wp_store _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /allow_store_map_or_true.
      eexists true,_,_,_,_,_,_; eauto.
      simplify_map_eq.
      split; [|split]; eauto.
      - rewrite /read_reg_inr; simplify_map_eq.
        destruct wdst as [| [] | |]; cbn in Hnot_cap; done.
      - rewrite /reg_allows_store; simplify_map_eq.
        rewrite decide_False; auto.
        intros [].
        destruct (decide (dst = cnull)); first done.
        destruct wdst as [| [] | |]; cbn in Hnot_cap; simplify_eq.
    }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /reg_allows_store in H2.
       simplify_map_eq.
       destruct H2 as (? & ? & ?); simplify_map_eq.
     }
     by iApply "Hφ".
     Unshelve. all: done.
    Qed.

   Lemma wp_store_fail_reg_perm E pc_p pc_g pc_b pc_e pc_a w dst src
         p g b e a w'' :
     decodeInstrW w = Store dst (inr src) →
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

    iApply (wp_store _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /allow_store_map_or_true.
      eexists true,p,g,b,e,a,w''.
      split.
      { rewrite /read_reg_inr.
        by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert_eq.
      }
      split.
      { rewrite /word_of_argument.
        by simplify_map_eq.
      }
      rewrite /reg_allows_store.
      rewrite Hwa.
      rewrite decide_False; auto.
      intro; naive_solver.
      }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /reg_allows_store in H5.
       destruct H5 as (? & Hwa' & ?); simplify_map_eq.
       congruence.
     }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; by iApply "Hφ".
     }
    Qed.

    Lemma wp_store_fail_z_perm E pc_p pc_g pc_b pc_e pc_a w dst
         p g b e a z :
      decodeInstrW w = Store dst (inl z) →
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

    iApply (wp_store _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /allow_store_map_or_true.
      eexists true,p,g,b,e,a,_.
      split.
      { rewrite /read_reg_inr.
        by rewrite lookup_insert_ne // lookup_insert_eq.
      }
      split.
      { rewrite /word_of_argument.
        eauto.
      }
      rewrite /reg_allows_store.
      rewrite HcanStore.
      rewrite decide_False; auto.
      intro; naive_solver.
      }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /reg_allows_store in H2.
       destruct H2 as (? & Hwa' & ?); simplify_map_eq.
       congruence.
     }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; by iApply "Hφ".
     }
    Qed.

   Lemma wp_store_fail_reg E pc_p pc_g pc_b pc_e pc_a w dst src
         p g b e a w'' :
      decodeInstrW w = Store dst (inr src) →
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
      iIntros (Hinstr Hvpc Hwb ?? φ)
             "(>HPC & >Hi & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (memMap_resource_1 with "Hi") as "Hmem"; auto.

    iApply (wp_store _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /allow_store_map_or_true.
      eexists true,p,g,b,e,a,w''.
      split.
      { rewrite /read_reg_inr.
        by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert_eq.
      }
      split.
      { rewrite /word_of_argument.
        by simplify_map_eq.
      }
      rewrite /reg_allows_store.
      rewrite Hwb.
      rewrite decide_False; auto.
      intro; naive_solver.
      }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /reg_allows_store in H5.
       destruct H5 as (? & ? & Hbounds); simplify_map_eq.
       by rewrite Hbounds in Hwb.
     }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; by iApply "Hφ".
     }
    Qed.

    Lemma wp_store_fail_z E pc_p pc_g pc_b pc_e pc_a w dst
         p g b e a z :
      decodeInstrW w = Store dst (inl z) →
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
      iIntros (Hinstr Hvpc Hwb ? φ)
             "(>HPC & >Hi & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (memMap_resource_1 with "Hi") as "Hmem"; auto.

    iApply (wp_store _ pc_p pc_g with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /allow_store_map_or_true.
      eexists true,p,g,b,e,a,_.
      split.
      { rewrite /read_reg_inr.
        by rewrite lookup_insert_ne // lookup_insert_eq.
      }
      split.
      { rewrite /word_of_argument. eauto.
      }
      rewrite /reg_allows_store.
      rewrite Hwb.
      rewrite decide_False; auto.
      intro; naive_solver.
      }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /reg_allows_store in H2.
       destruct H2 as (? & ? & Hbounds); simplify_map_eq.
       by rewrite Hbounds in Hwb.
     }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; by iApply "Hφ".
     }
    Qed.

  (* Untagged authority fails before writing the target memory. *)
  Lemma wp_store_fail_tag E pc_p pc_g pc_b pc_e pc_a
      w dst (src : Z + RegName) regs wa :
    decodeInstrW w = Store dst src →
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
    iIntros (σ1 ns l1 l2 nt) "[[Hr Hsr] Hm] /=".
    destruct σ1 as [[r sr] m]; cbn.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    have Hsrc' := lookup_reg_weaken _ _ _ _ Hsrc Hregs.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hpc_a; auto.
    iModIntro. iSplitR; first (by iPureIntro; apply normal_always_base_reducible).
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_". iSplitR; auto. eapply step_exec_inv in Hstep; eauto.
    rewrite /exec /= Hsrc' /= in Hstep.
    assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
    { destruct (word_of_argument r src) eqn:Harg; rewrite Harg in Hstep; cbn in Hstep.
      all: destruct wa as [| [t p g b e a|] | |]; cbn in Htag;
        by simplify_pair_eq. }
    cbn; iFrame; iApply "Hφ"; iFrame. done.
  Qed.

 End griotte_lang_rules.
