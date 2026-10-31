From iris.proofmode Require Import proofmode.
From griotte Require Export interp.
Import uPred.

Section logrel.

  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ}
    {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    {cthreads : CmptThreads}
    {CL : CritLink Σ}
    `{MP: MachineParameters}
  .
  #[local] Notation E := (interpO Σ).
  #[local] Notation V := (interpO Σ).
  #[local] Notation K := (contO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Lemma interp_cap_regions (W : WORLD) (C : CmptName) p g b e a π :
    isO p = false →
    interp W C (Cap p g b e a @@? π) -∗
    ⌜disjoint_from_mmio b e⌝ ∗ heap_cap_ok p b e π.
  Proof.
    iIntros (HnonO) "Hinterp".
    rewrite interp_unfold interp1_eq HnonO.
    destruct (has_sreg_access p); first done.
    iDestruct "Hinterp" as "[_ [%Hregions #Hok] ]".
    iFrame "Hok". iPureIntro. naive_solver.
  Qed.

  Lemma region_rel_heap_cap_O_key W C k p' P p g :
    persistent_cond P →
    (isWL p = true → g = Local) →
    region_rel W C k p' P p g -∗ heap_cap_O_key W C g k.
  Proof.
    iIntros (Hpers Hwl) "Hrel". rewrite /region_rel /heap_cap_O_key.
    assert (∀ x, Persistent ((safeGC P) x)) as HpersG by (intros x; apply (Hpers (_, _, _))).
    assert (∀ x, Persistent ((safeC P) x)) as HpersL by (intros x; apply Hpers).
    destruct (isWL p) eqn:HWL.
    - rewrite (Hwl eq_refl). iDestruct "Hrel" as "(Hrel & %HT & _)".
      iRight. iExists p', (safeC P). by iFrame "%#".
    - destruct g.
      + iLeft. iExists p', (safeGC P). by iFrame "%#".
      + iDestruct "Hrel" as "[Hrel|(Hrel & %HT & _)]".
        * iLeft. iExists p', (safeGC P). by iFrame "%#".
        * iRight. iExists p', (safeC P). by iFrame "%#".
  Qed.

  Lemma interp_cap_heap_conditions W C p g b e a π :
    interp W C (Cap p g b e a @@? π) -∗
    heap_cap_O_valid W C p g b e π.
  Proof.
    rewrite interp_unfold interp1_eq.
    destruct (isO p); first by iIntros "$".
    destruct (has_sreg_access p); first by iIntros "H".
    iIntros "[#Hlist [%Hconditions #Hok] ]".
    rewrite /heap_cap_O_valid.
    iFrame "Hok".
    iApply (big_sepL_impl with "Hlist").
    iIntros "!>" (i x Hx) "(%q & %P & _ & %Hpers & Hrel & _) _".
    iApply (region_rel_heap_cap_O_key with "Hrel"); first done.
    destruct (isWL p); naive_solver.
  Qed.

  Lemma interp_cap_disjoint (W : WORLD) (C : CmptName) p g b e a π :
    executeAllowed p = true →
    interp W C (Cap p g b e a @@? π) -∗
    ⌜disjoint_from_mmio b e ∧ disjoint_from_heap b e⌝.
  Proof.
    iIntros (Hexec) "Hinterp".
    iDestruct (interp_cap_regions with "Hinterp") as "[%Hshadow #Hheap]";
      first by eapply executeAllowed_nonO.
    iSplit; first done.
    destruct (decide (b < e)%a) as [Hnonempty|Hempty]; last first.
    { iPureIntro. rewrite /disjoint_from_heap finz_seq_between_empty; [set_solver|solve_addr]. }
    iDestruct ("Hheap" with "[%]") as "Hheap'"; first done.
    destruct π as [ι|]; last done.
    iDestruct "Hheap'" as "[%Hconds _]". exfalso.
    destruct Hconds as (_ & Hnonexec & Hnotwl). congruence.
  Qed.

  Lemma interp_cap_disjoint_wl (W : WORLD) (C : CmptName) p g b e a π :
    isWL p = true →
    interp W C (Cap p g b e a @@? π) -∗
    ⌜disjoint_from_mmio b e ∧ disjoint_from_heap b e⌝.
  Proof.
    iIntros (Hwl) "Hinterp".
    iDestruct (interp_cap_regions with "Hinterp") as "[%Hshadow #Hheap]";
      first (apply isWL_nonO; exact Hwl).
    iSplit; first done.
    destruct (decide (b < e)%a) as [Hnonempty|Hempty]; last first.
    { iPureIntro. rewrite /disjoint_from_heap finz_seq_between_empty; [set_solver|solve_addr]. }
    iDestruct ("Hheap" with "[%]") as "Hheap'"; first done.
    destruct π as [ι|]; last done.
    iDestruct "Hheap'" as "[%Hconds _]". exfalso.
    destruct Hconds as (_ & Hnonexec & Hnotwl). congruence.
  Qed.

  Lemma interp_cap_not_shadow (W : WORLD) (C : CmptName) p g b e a a' π :
    isO p = false →
    withinBounds b e a' = true →
    interp W C (Cap p g b e a @@? π) -∗ ⌜is_shadow_address a' = false⌝.
  Proof.
    iIntros (HnonO Hbounds) "Hinterp".
    iDestruct (interp_cap_regions with "Hinterp") as "[%Hshadow _]"; auto.
    iPureIntro. eapply disjoint_from_shadow_not_in; last eauto.
    by apply disjoint_from_mmio_shadow.
  Qed.

  Lemma interp_cap_not_mmio (W : WORLD) (C : CmptName) p g b e a a' π :
    isO p = false →
    withinBounds b e a' = true →
    interp W C (Cap p g b e a @@? π) -∗ ⌜is_mmio_address a' = false⌝.
  Proof.
    iIntros (HnonO Hbounds) "Hinterp".
    iDestruct (interp_cap_regions with "Hinterp") as "[%Hmmio _]"; auto.
    iPureIntro. eapply disjoint_from_mmio_not_in; eauto.
  Qed.

  (* Inversion lemmas about interp  *)
  (** The per-address part of a valid memory capability. *)
  Lemma interp_cap_addr (W : WORLD) (C : CmptName) p g (b e a a' : Addr) π :
    isO p = false →
    (b ≤ a' ∧ a' < e)%Z →
    interp W C (Cap p g b e a @@? π) -∗
    ∃ (p' : Perm) (P:V),
      ⌜PermFlowsTo p p'⌝
      ∗ ⌜persistent_cond P⌝
      ∗ region_rel W C (addr_key π a') p' P p g
      ∗ ▷ zcond P C
      ∗ (if readAllowed p'
         then ▷ (if isGlobal g then rcond_g P C p' (λ t, interp (th := t)) else rcond P C p' interp)
         else True)
      ∗ (if writeAllowed p' then ▷ (if isWL p then wcond P C interp else wcond_nwl P C interp) else True).
  Proof.
    iIntros (HnO Hin) "Hinterp".
    rewrite interp_unfold interp1_eq HnO.
    destruct (has_sreg_access p) eqn:HnXSR; auto.
    iDestruct "Hinterp" as "[Hinterp [%Hloc _] ]".
    iDestruct (extract_from_region_inv with "Hinterp")
      as (p' P' Hfl' Hpers') "(Hrel & Hzcond & Hrcond & Hwcond)"; eauto.
    iExists p', P'. by iFrame "∗%".
  Qed.

  (** The read condition of a capability at the running thread. *)
  Lemma rcond_sel_here g P C p' :
    thread_in th C -∗
    ▷ (if isGlobal g then rcond_g P C p' (λ t, interp (th := t)) else rcond P C p' interp) -∗
    ▷ rcond P C p' interp.
  Proof.
    iIntros "#Hth H". destruct g; cbn; [|done].
    iNext. iApply ("H" $! th with "Hth").
  Qed.

  Lemma read_allowed_inv (W : WORLD) (C : CmptName) (a' a b e: Addr) p g π :
    (b ≤ a' ∧ a' < e)%Z →
    readAllowed p →
    ⊢ thread_in th C -∗
    (interp W C (Cap p g b e a @@? π)) →
    ∃ (p' : Perm) (P:V),
      ⌜ PermFlowsTo p p'⌝
      ∗ ⌜persistent_cond P⌝
      ∗ region_rel W C (addr_key π a') p' P p g
      ∗ ▷ zcond P C
      ∗ ▷ rcond P C p' interp
      ∗ (if writeAllowed p' then ▷ (if isWL p then wcond P C interp else wcond_nwl P C interp) else True)
  .
  Proof.
    iIntros (Hin Ra) "#Hth #Hinterp".
    apply Is_true_eq_true in Ra.
    iDestruct (interp_cap_addr with "Hinterp")
      as (p' P' Hfl' Hpers') "(Hrel & Hzcond & Hrcond & Hwcond)";
      [by eapply readAllowed_nonO|done|].
    pose proof (readAllowed_flowsto _ _ Hfl' Ra) as Ra'.
    rewrite Ra'.
    iDestruct (rcond_sel_here with "Hth Hrcond") as "Hrcond_here".
    iExists p',P'; iFrame "#∗%".
  Qed.

  Lemma read_allowed_inv_many (W : WORLD) (C : CmptName) (a b e: Addr) p g l π :
    readAllowed p →
    Forall (fun a' : Addr => (a' ∈ₐ [b, e)) ) l ->
    ⊢ thread_in th C -∗
    (interp W C (Cap p g b e a @@? π)) →
    [∗ list] a' ∈ l,
          (
            ∃ (p' : Perm) (P:V),
              ⌜ PermFlowsTo p p'⌝
              ∗ ⌜persistent_cond P⌝
              ∗ region_rel W C (addr_key π a') p' P p g
              ∗ ▷ zcond P C
              ∗ ▷ rcond P C p' interp
              ∗ (if writeAllowed p' then ▷ (if isWL p then wcond P C interp else wcond_nwl P C interp) else True)
          ).
  Proof.
    induction l; iIntros (Hra Hin) "#Hth #Hinterp"; first done.
    simpl.
    apply Forall_cons in Hin. destruct Hin as [Hin_a0 Hin].
    iDestruct (read_allowed_inv _ _ a0 with "Hth Hinterp")
      as (p' P) "(%Hperm_flow & %Hpers_P & Hrel_P & Hzcond_P & Hrcond_P & Hwcond_P)"
    ; auto.
    iFrame "%#".
    iApply (IHl with "Hth Hinterp"); eauto.
  Qed.

  Lemma read_allowed_inv_full_cap (W : WORLD) (C : CmptName) (a b e: Addr) p g π :
    readAllowed p →
    ⊢ thread_in th C -∗
    (interp W C (Cap p g b e a @@? π)) →
    [∗ list] a' ∈ (finz.seq_between b e),
          (
            ∃ (p' : Perm) (P:V),
              ⌜ PermFlowsTo p p'⌝
              ∗ ⌜persistent_cond P⌝
              ∗ region_rel W C (addr_key π a') p' P p g
              ∗ ▷ zcond P C
              ∗ ▷ rcond P C p' interp
              ∗ (if writeAllowed p' then ▷ (if isWL p then wcond P C interp else wcond_nwl P C interp) else True)
          ).
  Proof.
    iIntros (Hra) "Hth Hinterp".
    iApply (read_allowed_inv_many with "Hth Hinterp"); eauto.
    apply Forall_forall.
    intros a' Ha'.
    by apply elem_of_finz_seq_between.
  Qed.

  (* Inversion lemmas about about when W-capability *)
  Lemma write_allowed_inv (W : WORLD) (C : CmptName) (a' a b e: Addr) p g π :
    (b ≤ a' ∧ a' < e)%Z →
    writeAllowed p →
    ⊢ (interp W C (Cap p g b e a @@? π)) →
    ∃ (p' : Perm) (P:V),
      ⌜ PermFlowsTo p p'⌝
      ∗ ⌜persistent_cond P⌝
      ∗ region_rel W C (addr_key π a') p' P p g
      ∗ ▷ zcond P C
      ∗ ▷ (if isWL p then wcond P C interp else wcond_nwl P C interp)
      ∗ (if readAllowed p' then ▷ (if isGlobal g then rcond_g P C p' (λ t, interp (th := t)) else rcond P C p' interp) else True)
  .
  Proof.
    iIntros (Hin Ra) "#Hinterp".
    apply Is_true_eq_true in Ra.
    iDestruct (interp_cap_addr with "Hinterp")
      as (p' P' Hfl' Hpers') "(Hrel & Hzcond & Hrcond & Hwcond)";
      [by eapply writeAllowed_nonO|done|].
    pose proof (writeAllowed_flowsto _ _ Hfl' Ra) as Ra'.
    rewrite Ra'.
    iExists p',P'; iFrame "#∗%".
  Qed.

  Lemma write_allowed_inv_many (W : WORLD) (C : CmptName) (a b e: Addr) p g l π :
    writeAllowed p →
    Forall (fun a' : Addr => (a' ∈ₐ [b, e)) ) l ->
    ⊢ (interp W C (Cap p g b e a @@? π)) →
    [∗ list] a' ∈ l,
          (
            ∃ (p' : Perm) (P:V),
              ⌜ PermFlowsTo p p'⌝
              ∗ ⌜persistent_cond P⌝
              ∗ region_rel W C (addr_key π a') p' P p g
              ∗ ▷ zcond P C
              ∗ (if readAllowed p' then ▷ (if isGlobal g then rcond_g P C p' (λ t, interp (th := t)) else rcond P C p' interp) else True)
              ∗ ▷ (if isWL p then wcond P C interp else wcond_nwl P C interp)
          ).
  Proof.
    induction l; iIntros (Hra Hin) "#Hinterp"; first done.
    simpl.
    apply Forall_cons in Hin. destruct Hin as [Hin_a0 Hin].
    iDestruct (write_allowed_inv _ _ a0 with "Hinterp")
      as (p' P) "(%Hperm_flow & %Hpers_P & Hrel_P & Hzcond_P & Hwcond_P & Hrcond_P)"
    ; auto.
    iFrame "%#".
    iApply (IHl with "Hinterp"); eauto.
  Qed.

  Lemma write_allowed_inv_full_cap (W : WORLD) (C : CmptName) (a b e: Addr) p g π :
    writeAllowed p →
    ⊢ (interp W C (Cap p g b e a @@? π)) →
    [∗ list] a' ∈ (finz.seq_between b e),
          (
            ∃ (p' : Perm) (P:V),
              ⌜ PermFlowsTo p p'⌝
              ∗ ⌜persistent_cond P⌝
              ∗ region_rel W C (addr_key π a') p' P p g
              ∗ ▷ zcond P C
              ∗ (if readAllowed p' then ▷ (if isGlobal g then rcond_g P C p' (λ t, interp (th := t)) else rcond P C p' interp) else True)
              ∗ ▷ (if isWL p then wcond P C interp else wcond_nwl P C interp)
          ).
  Proof.
    iIntros (Hra) "Hinterp".
    iApply (write_allowed_inv_many with "Hinterp"); eauto.
    apply Forall_forall.
    intros a' Ha'.
    by apply elem_of_finz_seq_between.
  Qed.

  Lemma interp_cap_cur_addr W C t p g b e a a' π :
    interp W C (WCap t p g b e a @@? π) ≡
    interp W C (WCap t p g b e a' @@? π).
  Proof.
    destruct t.
    - rewrite !interp_unfold !interp1_eq. reflexivity.
    - rewrite !interp_untagged_eq; done.
  Qed.

  (* Inversion lemmas about about when WL-capability *)
  Lemma writeLocalAllowed_valid_cap_implies (W : WORLD) (C : CmptName) p g b e a a' π :
    isWL p = true ->
    withinBounds b e a = true ->
    interp W C (Cap p g b e a' @@? π) -∗
    ⌜std W !! addr_key π a = Some Temporary⌝.
  Proof.
    intros Hp Hb. iIntros "Hinterp".
    eapply withinBounds_le_addr in Hb.
    iDestruct (interp_cap_addr with "Hinterp") as (p' P' Hfl' Hpers') "(Hrel & _)";
      [by eapply isWL_nonO|done|].
    rewrite /region_rel Hp. by iDestruct "Hrel" as "(_ & % & _)".
  Qed.

  Lemma writeLocalAllowed_valid_cap_implies_many (W : WORLD) (C : CmptName) p g b e a l π :
    isWL p = true ->
    Forall (fun a' : Addr => (a' ∈ₐ [b, e)) ) l ->
    ⊢ (interp W C (Cap p g b e a @@? π)) →
    [∗ list] a' ∈ l, ⌜std W !! addr_key π a' = Some Temporary⌝.
  Proof.
    induction l; iIntros (Hra Hin) "#Hinterp"; first done.
    simpl.
    apply Forall_cons in Hin; destruct Hin as [Hin_a0 Hin].
    iDestruct (writeLocalAllowed_valid_cap_implies with "Hinterp") as "$"; auto.
    { rewrite /withinBounds; solve_addr. }
    iApply (IHl with "Hinterp"); eauto.
  Qed.

  Lemma writeLocalAllowed_valid_cap_implies_full_cap (W : WORLD) (C : CmptName) p g b e a π :
    isWL p = true ->
    ⊢ (interp W C (Cap p g b e a @@? π)) →
    [∗ list] a' ∈ (finz.seq_between b e), ⌜std W !! addr_key π a' = Some Temporary⌝.
  Proof.
    iIntros (Hwl) "Hinterp".
    iApply (writeLocalAllowed_valid_cap_implies_many with "Hinterp"); eauto.
    apply Forall_forall.
    intros a' Ha'.
    by apply elem_of_finz_seq_between.
  Qed.

  (* A write-local capability never covers the heap, so its addresses are keyed
     by [LNonHeap]. *)
  Lemma interp_WL_addr_key W C p g b e a π :
    isWL p = true ->
    interp W C (Cap p g b e a @@? π) -∗
    ⌜Forall (λ a', addr_key π a' = LNonHeap a') (finz.seq_between b e)⌝.
  Proof.
    iIntros (Hwl) "Hinterp".
    iDestruct (interp_cap_regions with "Hinterp") as "[_ #Hvalid]";
      first by apply isWL_nonO.
    destruct π as [ι|]; last first.
    { iPureIntro. apply Forall_forall. intros a' Ha'. done. }
    destruct (decide (b < e)%a) as [Hlt|Hge]; last first.
    { iPureIntro. rewrite finz_seq_between_empty; [done|solve_addr]. }
    iDestruct (heap_cap_ok_id with "Hvalid") as %(_ & _ & Hnwl); first done.
    congruence.
  Qed.


  (** The addresses of a write-local capability are non-heap, so its full
      [Temporary] coverage is stated over [LNonHeap] keys. *)
  Lemma writeLocalAllowed_valid_cap_implies_full_cap_nonheap (W : WORLD) (C : CmptName) p g b e a π :
    isWL p = true ->
    ⊢ (interp W C (Cap p g b e a @@? π)) →
    [∗ list] a' ∈ (finz.seq_between b e), ⌜std W !! LNonHeap a' = Some Temporary⌝.
  Proof.
    iIntros (Hwl) "#Hinterp".
    iDestruct (interp_WL_addr_key with "Hinterp") as %Hkeys; first done.
    iDestruct (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp") as "Htmp"; first done.
    iApply (big_sepL_impl with "Htmp"); iIntros "!>" (k a' Ha') "%Htmp".
    by rewrite (Forall_lookup_1 _ _ _ _ Hkeys Ha') in Htmp.
  Qed.


  (** A register file can read (resp. write) the address [a] through a word
      without an identifier, i.e. through the region key [LNonHeap a]. A word
      with an identifier reaches [a] under another key. *)
  Definition readAllowed_a_in_lregs (regs : LReg) (a : Addr) :=
    ∃ r (w : LWord), regs !! r = Some w ∧ w.(lprov) = None ∧
                     readAllowedWord w.(lw) ∧ hasValidAddress w.(lw) a.

  Definition writeAllowed_a_in_lregs (regs : LReg) (a : Addr) :=
    ∃ r (w : LWord), regs !! r = Some w ∧ w.(lprov) = None ∧
                     writeAllowedWord w.(lw) ∧ hasValidAddress w.(lw) a.

  #[global] Instance readAllowed_a_in_lregs_Decidable (regs : LReg) (a : Addr) :
    Decision (readAllowed_a_in_lregs regs a).
  Proof.
    eapply finite.exists_dec.
    intros x. destruct (regs !! x) as [w|] eqn:Hsome;
      last (right; intros [w1 (Heq & _)]; congruence).
    destruct (decide (w.(lprov) = None)), (decide (readAllowedWord w.(lw))),
      (decide (hasValidAddress w.(lw) a));
      try (right; intros [w1 (Heq & ? & ? & ?)]; simplify_eq; contradiction).
    left; eexists _; eauto.
  Qed.

  #[global] Instance writeAllowed_a_in_lregs_Decidable (regs : LReg) (a : Addr) :
    Decision (writeAllowed_a_in_lregs regs a).
  Proof.
    eapply finite.exists_dec.
    intros x. destruct (regs !! x) as [w|] eqn:Hsome;
      last (right; intros [w1 (Heq & _)]; congruence).
    destruct (decide (w.(lprov) = None)), (decide (writeAllowedWord w.(lw))),
      (decide (hasValidAddress w.(lw) a));
      try (right; intros [w1 (Heq & ? & ? & ?)]; simplify_eq; contradiction).
    left; eexists _; eauto.
  Qed.

  (** A valid PC is executable and so carries no identifier. *)
  Lemma interp_pc_noid W C p g b e a π :
    isCorrectPC (Cap p g b e a) ->
    interp W C (Cap p g b e a @@? π) -∗ ⌜π = None⌝.
  Proof.
    iIntros (Hpc) "Hinterp".
    assert (executeAllowed p = true) as Hexec by (by inversion Hpc).
    iDestruct (interp_cap_regions with "Hinterp") as "[_ #Hvalid]";
      first by eapply executeAllowed_nonO.
    destruct π as [ι|]; last done.
    pose proof (isCorrectPC_withinBounds _ _ _ _ _ _ Hpc) as Hwb.
    apply withinBounds_true_iff in Hwb.
    iDestruct (heap_cap_ok_id with "Hvalid") as %(_ & Hnexec & _); first solve_addr.
    congruence.
  Qed.

  (** Two regions of the same key outside the heap have the same
      permission. *)
  Lemma region_rel_part_agree_nonheap W C a ρ1 ρ2 p1 p2 P1 P2 :
    world_interp W C -∗
    region_rel_part ρ1 W C (LNonHeap a) p1 P1 -∗
    region_rel_part ρ2 W C (LNonHeap a) p2 P2 -∗
    world_interp W C ∗ ⌜p1 = p2⌝.
  Proof.
    iIntros "Hw #H1 #H2".
    destruct ρ1, ρ2; cbn.
    - iDestruct (rel_g_agree with "H1 H2") as "[% _]". by iFrame.
    - iDestruct "H2" as "(_ & %HT & _)".
      iDestruct (world_interp_rel_g_not_temporary_nonheap with "Hw H1") as "[_ %]". done.
    - iDestruct "H1" as "(_ & %HT & _)".
      iDestruct (world_interp_rel_g_not_temporary_nonheap with "Hw H2") as "[_ %]". done.
    - iDestruct "H1" as "(H1 & _)". iDestruct "H2" as "(H2 & _)".
      iDestruct (rel_l_agree with "H1 H2") as "[% _]". by iFrame.
  Qed.

  Lemma interp_in_registers
    (W : WORLD) (C : CmptName)
    (regs : leibnizO LReg) (p : Perm) (g : Locality) (b e a : Addr):
      thread_in th C
    -∗ world_interp W C
    -∗ (∀ (r : RegName) (v : LWord), ⌜regs !! r = Some v⌝ → interp W C v)%I
    -∗ (∃ (p' : Perm) (P : V),
        ⌜PermFlowsTo p p'⌝
        ∗ ⌜persistent_cond P⌝
        ∗ region_rel W C (LNonHeap a) p' P p g
        ∗ ▷ zcond P C
        ∗ (if readAllowed p' then ▷ (if isGlobal g then rcond_g P C p' (λ t, interp (th := t)) else rcond P C p' interp) else True)
        ∗ (if writeAllowed p' then ▷ (if isWL p then wcond P C interp else wcond_nwl P C interp) else True)
       )
    -∗ world_interp W C ∗
       (∃ (p' : Perm) (P : V),
        ⌜PermFlowsTo p p'⌝
        ∗ ⌜persistent_cond P⌝
        ∗ region_rel W C (LNonHeap a) p' P p g
        ∗ ▷ zcond P C
        ∗ (if decide (readAllowed_a_in_lregs regs a)
            then ▷ (rcond P C p' interp)
            else emp)
        ∗ (if decide (writeAllowed_a_in_lregs regs a)
            then ▷ (if isWL p then wcond P C interp else wcond_nwl P C interp)
            else emp)
       ).
  Proof.
    iIntros "#Hth Hw #Hreg #H".
    iDestruct "H" as (p0 P0 Hflp0 Hperscond_P0) "(Hrel0 & Hzcond0 & Hrcond0 & Hwcond0)".
    iDestruct (region_rel_parts with "Hrel0") as (ρ0) "#Hpart0".
    (* A register reaching [a] without identifier reaches the region of the PC. *)
    iAssert (□ ∀ r c g' b' e' a', ⌜regs !! r = Some (WCap true c g' b' e' a' @@? None)⌝ →
               ⌜isO c = false⌝ → ⌜hasValidAddress (WCap true c g' b' e' a') a⌝ →
               world_interp W C -∗ world_interp W C ∗ ⌜PermFlowsTo c p0⌝)%I
      as "#Hperm".
    { iIntros "!>" (r c g' b' e' a' Hsome HnO Hvw) "Hw"; cbn in Hvw.
      iDestruct ("Hreg" $! r _ Hsome) as "Hinterp_w".
      apply withinBounds_le_addr in Hvw.
      iDestruct (interp_cap_addr with "Hinterp_w") as (p1 P1 Hfl1 _) "(Hrel1 & _)";
        [done|done|].
      iDestruct (region_rel_parts with "Hrel1") as (ρ1) "Hpart1".
      iDestruct (region_rel_part_agree_nonheap with "Hw Hpart1 Hpart0") as "[$ ->]".
      done. }
    iAssert (world_interp W C ∗ ⌜readAllowed_a_in_lregs regs a → readAllowed p0 = true⌝)%I
      with "[Hw]" as "[Hw %HR]".
    { destruct (decide (readAllowed_a_in_lregs regs a)) as [Hra'|Hra']; [|by iFrame].
      destruct Hra' as (r & [w π] & Hsome & Hπ & Hrar & Hvw); cbn in Hπ, Hrar, Hvw; subst π.
      destruct_word w; try destruct t; cbn in Hrar, Hvw; try done.
      iDestruct ("Hperm" $! r with "[//] [%] [//] Hw") as "[$ %Hfl]".
      { by eapply readAllowed_nonO. }
      iPureIntro. intros _. eapply readAllowed_flowsto; eauto. }
    iAssert (world_interp W C ∗ ⌜writeAllowed_a_in_lregs regs a → writeAllowed p0 = true⌝)%I
      with "[Hw]" as "[Hw %HW]".
    { destruct (decide (writeAllowed_a_in_lregs regs a)) as [Hwa'|Hwa']; [|by iFrame].
      destruct Hwa' as (r & [w π] & Hsome & Hπ & Hwaw & Hvw); cbn in Hπ, Hwaw, Hvw; subst π.
      destruct_word w; try destruct t; cbn in Hwaw, Hvw; try done.
      iDestruct ("Hperm" $! r with "[//] [%] [//] Hw") as "[$ %Hfl]".
      { by eapply writeAllowed_nonO. }
      iPureIntro. intros _. eapply writeAllowed_flowsto; eauto. }
    iFrame "Hw". iExists p0, P0. iFrame "%#". iSplit.
    - destruct (decide (readAllowed_a_in_lregs regs a)) as [Hra'|]; [|done].
      rewrite (HR Hra'). iApply (rcond_sel_here with "Hth Hrcond0").
    - destruct (decide (writeAllowed_a_in_lregs regs a)) as [Hwa'|]; [|done].
      by rewrite (HW Hwa').
  Qed.

  (** A valid executable capability with a non-empty range carries no
      identifier: heap authority is never executable. *)
  Lemma interp_exec_noid W C p g b e a π :
    executeAllowed p = true → (b < e)%a →
    interp W C (Cap p g b e a @@? π) -∗ ⌜π = None⌝.
  Proof.
    iIntros (Hexec Hbe) "Hinterp".
    iDestruct (interp_cap_regions with "Hinterp") as "[_ #Hheap]";
      first by eapply executeAllowed_nonO.
    iDestruct ("Hheap" with "[%]") as "Hheap'"; first done.
    destruct π as [ι|]; last done.
    iDestruct "Hheap'" as "[%Hconds _]". exfalso.
    destruct Hconds as (_ & Hnonexec & _). congruence.
  Qed.

  (** A non-empty capability with an identifier has heap authority. *)
  Lemma interp_cap_has_authority W C p g b e a ea ι :
    isO p = false → withinBounds b e ea = true →
    interp W C (Cap p g b e a @@? Some ι) -∗ ⌜has_authority (Cap p g b e a)⌝.
  Proof.
    iIntros (HnO Hwb) "Hinterp".
    iDestruct (interp_cap_regions with "Hinterp") as "[_ #Hok]"; first done.
    apply withinBounds_true_iff in Hwb.
    iDestruct (heap_cap_ok_id with "Hok") as %(Hb & _ & _); first solve_addr.
    iPureIntro. split; first done. exists b.
    rewrite /heap_authority_base decide_True; last solve_addr.
    by rewrite /heap_cap_base /memory_cap_base /= Hb.
  Qed.

  Lemma interp_lstore_word W C p v :
    interp W C v -∗ interp W C (lstore_word p v).
  Proof.
    iIntros "#Hv".
    destruct (canStore p v.(lw)) eqn:Hcs.
    - by rewrite lstore_word_canStore.
    - assert (lstore_word p v = lclear_tag v) as ->.
      { by rewrite /lstore_word /lclear_tag /lift_word /store_word Hcs. }
      iApply interp_clear_tag.
  Qed.

End logrel.
