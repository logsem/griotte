From iris.proofmode Require Import proofmode.
From griotte Require Export logrel.
From griotte Require Import monotone.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {cthreads : CmptThreads} {CL : CritLink Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  #[local] Notation V := (interpO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

  (** The content of the region of the PC: a Global region holds the
      world-free image of its predicate. *)
  Definition pc_content (ρ : region_part) (W : WORLD) (C : CmptName) (P : V) (w : LWord)
    : iProp Σ :=
    match ρ with
    | InGlobal => P ∅ C w
    | InLocal => P W C w
    end.

  (** The opened region of the PC, at key [k] of part [ρ], holding [w]. *)
  Definition pc_open_def (W : WORLD) (C : CmptName) (k : LAddr) (p' : Perm) (P : V)
      (w : LWord) (ρ : region_part) : iProp Σ :=
    match ρ with
    | InGlobal => ⌜std W !! k ≠ Some Temporary⌝ ∗ PermRes C k p' (safeGC P) w
    | InLocal => TmpRes W C k p' (safeC P) w
    end.
  #[local] Definition pc_open_aux : seal (@pc_open_def). Proof. by eexists. Qed.

  Definition pc_open := pc_open_aux.(unseal).
  #[local] Definition pc_open_unseal : @pc_open = @pc_open_def := pc_open_aux.(seal_eq).

  (** The cell of the PC, with its content. *)
  Lemma pc_open_acc W C k p' P w ρ :
    pc_open W C k p' P w ρ -∗
    (k ↦ₖ w ∗ pc_content ρ W C P w) ∗
    (k ↦ₖ w ∗ pc_content ρ W C P w -∗ pc_open W C k p' P w ρ).
  Proof.
    rewrite pc_open_unseal. destruct ρ; cbn.
    - iIntros "($ & %HpO & $ & $)". iIntros "[$ $]". done.
    - iIntros "(%HpO & $ & $ & #Hmono)". iIntros "[$ $]". by iFrame "#".
  Qed.

  (** Opening the region of the PC. *)
  Lemma pc_open_intro W C k p' (P : V) w ρ :
    (ρ = InGlobal → std W !! k ≠ Some Temporary) →
    match ρ with
    | InGlobal => PermRes C k p' (safeGC P) w
    | InLocal => TmpRes W C k p' (safeC P) w
    end -∗
    pc_open W C k p' P w ρ.
  Proof.
    rewrite pc_open_unseal. iIntros (HnT) "H". destruct ρ; [|done].
    iFrame. iPureIntro. by apply HnT.
  Qed.

  (** Closing the region of the PC. *)
  Lemma pc_close W C k p' P w ρ :
    persistent_cond P →
    world_interp_open W C [k] -∗
    region_rel_part ρ W C k p' P -∗
    pc_open W C k p' P w ρ -∗
    world_interp W C.
  Proof.
    rewrite pc_open_unseal. iIntros (Hpers) "Hw #Hrel Hres".
    assert (∀ x, Persistent (safeGC P x)) as HpersG by (intros x; apply (Hpers (_, _, _))).
    assert (∀ x, Persistent (safeC P x)) as HpersL by (intros x; apply Hpers).
    rewrite open_world_interp_empty.
    destruct ρ; cbn.
    - iDestruct "Hres" as "[%HnT Hres]".
      iDestruct (close_world_interp_permanent W C [] k p' (safeGC P) w
                   with "Hw Hrel Hres") as "[$ _]"; [set_solver|done].
    - iDestruct "Hrel" as "(Hrel & %HT & _)".
      iDestruct (close_world_interp_temporary W C [] k p' (safeC P) w
                   with "Hw Hrel Hres") as "[$ _]"; [set_solver|done].
  Qed.

  (** An opened region is rebuilt from its cell and its content, for any
      word. *)
  Lemma pc_open_rebuild ρ W C k p' P :
    isO p' = false →
    (ρ = InGlobal → std W !! k ≠ Some Temporary) →
    region_rel_part ρ W C k p' P -∗
    □ ∀ w, k ↦ₖ w ∗ pc_content ρ W C P w -∗ pc_open W C k p' P w ρ.
  Proof.
    iIntros (HpO HnT) "#Hpart !>". iIntros (w) "[Hk HP]".
    iApply (pc_open_intro with "[Hk HP]"); first done.
    destruct ρ; cbn.
    - by iFrame "∗%".
    - iDestruct "Hpart" as "(_ & _ & #Hmono)". iFrame "∗%". iApply "Hmono".
  Qed.

  (** The cell of an opened region, with its content, for any new word. *)
  Lemma pc_open_acc_forall W C k p' P w ρ :
    region_rel_part ρ W C k p' P -∗
    pc_open W C k p' P w ρ -∗
    (k ↦ₖ w ∗ pc_content ρ W C P w) ∗
    (∀ w', k ↦ₖ w' ∗ pc_content ρ W C P w' -∗ pc_open W C k p' P w' ρ).
  Proof.
    rewrite pc_open_unseal. iIntros "#Hrel". destruct ρ; cbn.
    - iIntros "(%HnT & %HpO & Hc & HP)". iFrame "Hc HP".
      iIntros (w') "[Hc HP]". by iFrame "∗%".
    - iDestruct "Hrel" as "(_ & _ & #Hmono)".
      iIntros "(%HpO & Hc & HP & _)". iFrame "Hc HP".
      iIntros (w') "[Hc HP]". iFrame "∗%". iApply "Hmono".
  Qed.

  (** Closing an opened region, with other keys open. *)
  Lemma pc_close_next W C s k p' P w ρ :
    k ∉ s →
    persistent_cond P →
    world_interp_open W C ({[k]} ∪ s) -∗
    region_rel_part ρ W C k p' P -∗
    pc_open W C k p' P w ρ -∗
    world_interp_open W C s.
  Proof.
    rewrite pc_open_unseal. iIntros (Hks Hpers) "Hw #Hrel Hres".
    assert (∀ x, Persistent (safeGC P x)) as HpersG by (intros x; apply (Hpers (_, _, _))).
    assert (∀ x, Persistent (safeC P x)) as HpersL by (intros x; apply Hpers).
    destruct ρ; cbn.
    - iDestruct "Hres" as "[%HnT Hres]".
      iDestruct (close_world_interp_permanent W C s k p' (safeGC P) w
                   with "Hw Hrel Hres") as "[$ _]"; done.
    - iDestruct "Hrel" as "(Hrel & %HT & _)".
      iDestruct (close_world_interp_temporary W C s k p' (safeC P) w
                   with "Hw Hrel Hres") as "[$ _]"; done.
  Qed.

  Lemma pc_content_persistent ρ W C P w :
    persistent_cond P → Persistent (pc_content ρ W C P w).
  Proof. intros Hpers. destruct ρ; [apply (Hpers (∅, C, w))|apply (Hpers (W, C, w))]. Qed.

End fundamental.

Section wp_interp.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    {cthreads : CmptThreads}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> (leibnizO LWord) -n> iPropO Σ).
  #[local] Notation V := (interpO Σ).
  #[local] Notation K := (contO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

  (** Reading the content of an opened region: a Global region is read at
      the empty world. *)
  Lemma pc_content_rcond {CL : CritLink Σ} ρ W C P p' w :
    rcond P C p' interp -∗ pc_content ρ W C P w -∗ interp_in_mem_pre W C p' interp w.
  Proof.
    iIntros "#Hrc HP". destruct ρ; cbn.
    - iDestruct ("Hrc" with "HP") as "H". rewrite /interp_in_mem_pre.
      by iApply interp_g_any_world.
    - by iApply "Hrc".
  Qed.

  (** Writing a safe word into an opened region: a Global region is written
      through a capability that is not write-local. *)
  (** A word stored through a capability that is not write-local is not
      local. *)
  Lemma lstore_word_nonlocal p v :
    isWL p = false → isLocalWord (lstore_word p v).(lw) = false.
  Proof.
    intros Hwl. destruct (canStore p v.(lw)) eqn:Hcs.
    - rewrite lstore_word_canStore //. by eapply canStore_global_nonisWL.
    - assert (lstore_word p v = lclear_tag v) as ->.
      { by rewrite /lstore_word /lclear_tag /lift_word /store_word Hcs. }
      rewrite lw_lclear_tag. destruct v as [v ?]; cbn.
      destruct_word v; cbn; try done. by destruct sb.
  Qed.

  Lemma pc_content_wcond {CL : CritLink Σ} ρ W C P p v :
    (ρ = InGlobal → isWL p = false) →
    (if isWL p then wcond P C interp else wcond_nwl P C interp) -∗
    interp W C v -∗ pc_content ρ W C P (lstore_word p v).
  Proof.
    iIntros (Hwl) "#Hwc #Hv". destruct ρ; cbn.
    - rewrite Hwl //. iApply ("Hwc" with "[%]").
      { by apply lstore_word_nonlocal, Hwl. }
      iApply (interp_store_g with "Hv"). by apply Hwl.
    - destruct (isWL p) eqn:Hp.
      + iApply "Hwc". by iApply interp_lstore_word.
      + iApply ("Hwc" with "[%]"); first by apply lstore_word_nonlocal.
        by iApply interp_lstore_word.
  Qed.

  Lemma pc_content_wcond_z {CL : CritLink Σ} ρ W C P p z :
    (if isWL p then wcond P C interp else wcond_nwl P C interp) -∗ pc_content ρ W C P (WInt z).
  Proof.
    iIntros "#Hwc". destruct (isWL p); destruct ρ; cbn;
      iApply "Hwc"; try done; iApply interp_int.
  Qed.

End wp_interp.
