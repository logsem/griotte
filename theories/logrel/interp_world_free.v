From iris.proofmode Require Import proofmode.
From griotte Require Export interp_caps.
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

  (** ** World-free validity

      A word that is not Local is valid in every world: its regions are
      Permanent, its sentries run in every world, and the predicates of Global
      seals are constant. *)
  Lemma interp_global_world_free W W' C w :
    isLocalWord w.(lw) = false →
    interp W C w -∗ interp W' C w.
  Proof.
    intros Hloc.
    destruct (get_tag w.(lw)) eqn:Htag; last (rewrite !interp_untagged_eq //; auto).
    rewrite !interp_unfold.
    destruct w as [w π]; cbn in Htag, Hloc |- *.
    destruct_word w; cbn in Htag, Hloc |- *.
    - done.
    - subst t. destruct g; cbn in Hloc; try done.
      destruct c as [rx wp dl dro]; destruct rx, wp; by iIntros "H".
    - subst t. destruct g; cbn in Hloc; try done. by iIntros "H".
    - subst t. destruct g; cbn in Hloc; try done. by iIntros "H".
    - rewrite Htag /interp_sb.
      iIntros "[(%κ & %P & #Hs & #Hok & HP) $]".
      iExists κ, P. iFrame "Hs Hok".
      destruct κ; cbn.
      + iDestruct "Hok" as "[_ #Hc]". iNext. by iApply ("Hc" $! th th W W').
      + by iDestruct "Hok" as "[_ [] ]".
  Qed.

  (** A word sealed with a Global-kind otype is valid in every world: the
      predicate of the otype does not depend on the world. *)
  Lemma interp_sealed_global_kind_world_free W W' C o P sb π :
    o ↪ₒ{SealGlobal} P -∗
    interp W C (WSealed o sb @@? π) -∗
    interp W' C (WSealed o sb @@? π).
  Proof.
    iIntros "#Hs #Hinterp".
    destruct (get_tag_sealable sb) eqn:Htag;
      last (rewrite !interp_untagged_eq //=; auto).
    rewrite !interp_unfold /= Htag /interp_sb.
    iDestruct "Hinterp" as "[(%κ & %P' & #Hs' & #Hok & #HP) $]".
    iDestruct (seal_pred_agree with "Hs Hs'") as "[<- _]".
    iExists SealGlobal, P'. iFrame "Hs' Hok".
    iDestruct "Hok" as "[_ #Hc]". iNext. by iApply ("Hc" $! th th W W').
  Qed.

  (** ** Sealed words

      A sealed word is valid when the predicate of a Global-kind otype holds
      of its payload made Global. *)
  Lemma interp_sb_intro_global W C o P sb π :
    seal_kind_ok SealGlobal C P -∗
    o ↪ₒ{SealGlobal} P -∗
    ▷ P (th, W, C, lforce_global (WSealable sb @@? π)) -∗
    sealed_payload_ok (WSealable sb @@? π) -∗
    interp W C (WSealed o sb @@? π).
  Proof.
    iIntros "#Hok #Hs HP #Hpayload".
    destruct (get_tag_sealable sb) eqn:Htag;
      last (rewrite interp_untagged_eq //=; auto).
    iDestruct "Hok" as "[%Hpers Hc]".
    rewrite interp_unfold /= Htag /interp_sb.
    iSplit; last done.
    iExists SealGlobal, P. iFrame "Hs". iSplit; first by iFrame "Hc".
    iExact "HP".
  Qed.

  (** The validity of a sealed word gives the predicate of its otype, after
      agreement with the otype's seal predicate. *)
  Lemma interp_sb_elim W C o κ P sb π :
    get_tag_sealable sb = true →
    o ↪ₒ{κ} P -∗
    interp W C (WSealed o sb @@? π) -∗
    ▷ P (th, W, C, norm κ (WSealable sb @@? π)) ∗
    sealed_payload_ok (WSealable sb @@? π).
  Proof.
    iIntros (Htag) "#Hs #Hinterp".
    rewrite interp_unfold /= Htag /interp_sb.
    iDestruct "Hinterp" as "[(%κ' & %P' & #Hs' & _ & #HP) $]".
    iDestruct (seal_pred_agree with "Hs Hs'") as "[<- #Heq]".
    iNext. by iRewrite ("Heq" $! (th, W, C, norm κ (WSealable sb @@? π))).
  Qed.

  (** The validity of a word in every world. *)
  Definition interp_g (C : CmptName) (w : LWord) : iProp Σ := interp ∅ C w.

  #[global] Instance interp_g_persistent C w : Persistent (interp_g C w).
  Proof. apply _. Qed.

  (** A word stored through a capability that is not write-local is valid in
      every world. *)
  Lemma interp_store_g W C p w :
    isWL p = false →
    interp W C w -∗ interp_g C (lstore_word p w).
  Proof.
    iIntros (Hwl) "#Hw". rewrite /interp_g.
    destruct (canStore p w.(lw)) eqn:Hcs.
    - rewrite lstore_word_canStore //.
      iApply (interp_global_world_free with "Hw").
      by eapply canStore_global_nonisWL.
    - assert (lstore_word p w = lclear_tag w) as ->.
      { by rewrite /lstore_word /lclear_tag /lift_word /store_word Hcs. }
      iApply interp_clear_tag.
  Qed.

  (** The region of an address reached through a capability is the PC's
      region exactly when the address is the PC's and the capability has no
      identifier: a capability with an identifier reaches it under another key. *)
  Lemma addr_key_pc π ea pc_a :
    addr_key π ea = LNonHeap pc_a → π = None ∧ ea = pc_a.
  Proof. destruct π; cbn; intros; simplify_eq; done. Qed.

End logrel.

(** Validity across threads: a word that is not local has the same
    validity at every thread and in every world. *)
Section logrel_threads.

  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ}
    {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    {cthreads : CmptThreads}
    {CL : CritLink Σ}
    `{MP: MachineParameters}
  .
  #[local] Notation V := (interpO Σ).
  #[local] Notation TV := (Thread -d> interpO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (** The per-address part of a Global capability that is not write-local
      moves from the thread [t] to the thread [t'], given the validity of
      the words that are not local from [t'] to [t] one step later. *)
  Lemma interp_cap_body_global_thread (I : TV) (t t' : Thread) W W' C p b e π :
    isWL p = false →
    ▷ (□ ∀ W0 w0, ⌜isLocalWord w0.(lw) = false⌝ → I t' W0 C w0 -∗ I t W0 C w0) -∗
    interp_cap_body I t W C p Global b e π -∗
    interp_cap_body I t' W' C p Global b e π.
  Proof.
    iIntros (Hwl) "#IH #Hbody". rewrite !interp_cap_body_eq.
    iApply (big_sepL_impl with "Hbody").
    iIntros "!>" (k a Ha) "(%p' & %P & %Hfl & %Hpers & Hrel & Hz & Hr & Hw)".
    iExists p', P. rewrite /region_rel Hwl /=. iFrame "Hrel Hz Hr %".
    destruct (writeAllowed p'); last done.
    iNext. iDestruct "Hw" as "#Hw". iIntros "!>" (W0 w0 Hl0) "Hw0".
    iApply ("Hw" $! W0 w0 Hl0). iApply ("IH" $! W0 w0 Hl0 with "Hw0").
  Qed.

  (** Factorisation, as a persistent entailment between any two threads and
      worlds, by Löb induction: the write condition of a Global capability
      is at the holder's thread. *)
  Lemma interp_nonlocal_thread_world_free_later C :
    ⊢ □ ∀ (t t' : Thread) (W W' : WORLD) (w : LWord),
        ⌜isLocalWord w.(lw) = false⌝ →
        interp (th := t) W C w -∗ interp (th := t') W' C w.
  Proof.
    iLöb as "IH".
    iIntros "!>" (t t' W W' w Hloc) "#Hw".
    destruct (get_tag w.(lw)) eqn:Htag.
    2: { by rewrite (interp_untagged_eq (th := t')). }
    rewrite (interp_unfold (th := t)) (interp_unfold (th := t')).
    destruct w as [w π]; cbn in Htag, Hloc |- *.
    destruct w as [z | [tg c | tg sr] | k tg sd | e]; cbn in Htag, Hloc.
    - discriminate.
    - subst tg. destruct g; cbn in Hloc; [|discriminate].
      destruct c as [rx wp dl dro]; destruct rx, wp; cbn.
      (* O *)
      1: { iDestruct "Hw" as "[Hok Hl]". iFrame "Hok". iApply (big_sepL_impl with "Hl").
           iIntros "!>" (k x _) "H %Hh". iDestruct ("H" with "[//]") as "[H|[] ]".
           by iLeft. }
      (* The other permissions, one goal each, with explicit arguments. *)
      1: { iDestruct "Hw" as "(Hbody & Hmmio & Hok)". iFrame "Hmmio Hok".
           iApply (interp_cap_body_global_thread (λ t0, interp (th := t0)) t t' W W' C
                     (BPerm Orx permissions.W dl dro) b e π eq_refl with "[] Hbody").
           iNext. iIntros "!>" (W0 w0 Hl0) "Hw0".
           iApply ("IH" $! t' t W0 W0 w0 Hl0 with "Hw0"). }
      1: iDestruct "Hw" as "[]".
      1: { iDestruct "Hw" as "(Hbody & Hmmio & Hok)". iFrame "Hmmio Hok".
           iApply (interp_cap_body_global_thread (λ t0, interp (th := t0)) t t' W W' C
                     (BPerm R Ow dl dro) b e π eq_refl with "[] Hbody").
           iNext. iIntros "!>" (W0 w0 Hl0) "Hw0".
           iApply ("IH" $! t' t W0 W0 w0 Hl0 with "Hw0"). }
      1: { iDestruct "Hw" as "(Hbody & Hmmio & Hok)". iFrame "Hmmio Hok".
           iApply (interp_cap_body_global_thread (λ t0, interp (th := t0)) t t' W W' C
                     (BPerm R permissions.W dl dro) b e π eq_refl with "[] Hbody").
           iNext. iIntros "!>" (W0 w0 Hl0) "Hw0".
           iApply ("IH" $! t' t W0 W0 w0 Hl0 with "Hw0"). }
      1: iDestruct "Hw" as "[]".
      1: { iDestruct "Hw" as "(Hbody & Hmmio & Hok)". iFrame "Hmmio Hok".
           iApply (interp_cap_body_global_thread (λ t0, interp (th := t0)) t t' W W' C
                     (BPerm X Ow dl dro) b e π eq_refl with "[] Hbody").
           iNext. iIntros "!>" (W0 w0 Hl0) "Hw0".
           iApply ("IH" $! t' t W0 W0 w0 Hl0 with "Hw0"). }
      1: { iDestruct "Hw" as "(Hbody & Hmmio & Hok)". iFrame "Hmmio Hok".
           iApply (interp_cap_body_global_thread (λ t0, interp (th := t0)) t t' W W' C
                     (BPerm X permissions.W dl dro) b e π eq_refl with "[] Hbody").
           iNext. iIntros "!>" (W0 w0 Hl0) "Hw0".
           iApply ("IH" $! t' t W0 W0 w0 Hl0 with "Hw0"). }
      all: iDestruct "Hw" as "[]".
    - subst tg. cbn. iExact "Hw".
    - subst tg. destruct g; cbn in Hloc; [|discriminate]. cbn. iExact "Hw".
    - rewrite /= Htag /interp_sb.
      iDestruct "Hw" as "[(%κ & %P & #Hs & #Hok & HP) $]".
      iExists κ, P. iFrame "Hs Hok".
      destruct κ; cbn.
      + iDestruct "Hok" as "[_ #Hc]". iNext. iApply ("Hc" $! t t' W W' with "HP").
      + by iDestruct "Hok" as "[_ [] ]".
  Qed.

  (** Factorisation: the validity of a word that is not local is the same
      at any two threads and in any two worlds. *)
  Lemma interp_global_thread_world_free (t t' : Thread) W W' C w :
    isLocalWord w.(lw) = false →
    interp (th := t) W C w ⊣⊢ interp (th := t') W' C w.
  Proof.
    intros Hloc. iPoseProof (interp_nonlocal_thread_world_free_later C) as "#H".
    iSplit; iIntros "Hw".
    - iApply ("H" $! t t' W W' w Hloc with "Hw").
    - iApply ("H" $! t' t W' W w Hloc with "Hw").
  Qed.

  (** [interp_g] at a thread agrees with the validity at every thread, on
      the words that are not local. *)
  Lemma interp_g_agree (th t : Thread) W C w :
    isLocalWord w.(lw) = false →
    interp_g (th := th) C w ⊣⊢ interp (th := t) W C w.
  Proof.
    intros Hloc. rewrite /interp_g. exact (interp_global_thread_world_free th t ∅ W C w Hloc).
  Qed.

  (** The table part of [top_cmpt_untrusted] does not depend on the
      thread, for words that are not local. *)
  Lemma top_cmpt_untrusted_tbl_thread_free (t t' : Thread) W C pcc cgp :
    isLocalWord pcc.(lw) = false → isLocalWord cgp.(lw) = false →
    (□ ∀ W', ⌜related_sts_priv_world W W'⌝ →
       interp (th := t) W' C pcc ∗ interp (th := t) W' C cgp) ⊣⊢
    (□ ∀ W', ⌜related_sts_priv_world W W'⌝ →
       interp (th := t') W' C pcc ∗ interp (th := t') W' C cgp).
  Proof.
    intros Hpcc Hcgp. iPoseProof (interp_nonlocal_thread_world_free_later C) as "#Hf".
    iSplit; iIntros "#H !>" (W' HW'); iDestruct ("H" $! W' HW') as "[H1 H2]".
    - iSplit; [iApply ("Hf" $! t t' W' W' pcc Hpcc with "H1")
              |iApply ("Hf" $! t t' W' W' cgp Hcgp with "H2")].
    - iSplit; [iApply ("Hf" $! t' t W' W' pcc Hpcc with "H1")
              |iApply ("Hf" $! t' t W' W' cgp Hcgp with "H2")].
  Qed.

  (** A holder of a Global capability that is not write-local, at any
      thread [t], in the compartment's threads or not, writes a word that
      is not local into a Permanent region through the map of Permanent regions
      alone. *)
  Lemma wg_holder_write (t : Thread) W C p (b e a a' : Addr) w :
    isWL p = false → writeAllowed p = true → (b ≤ a' ∧ a' < e)%Z →
    isLocalWord w.(lw) = false →
    interp (th := t) W C (Cap p Global b e a) -∗
    interp (th := t) W C w -∗
    perm_region_map C ∅ -∗
    ▷ ∃ v, LNonHeap a' ↦ₖ v ∗
      (LNonHeap a' ↦ₖ w -∗ perm_region_map C ∅).
  Proof.
    iIntros (Hwl Hwa Hin Hloc) "#Hcap #Hw Hg".
    iDestruct (interp_cap_addr (th := t) W C p Global b e a a' None with "Hcap")
      as (p' P Hfl Hpers) "(Hrel & _ & _ & Hwcond)";
      [by apply writeAllowed_nonO|done|].
    rewrite (writeAllowed_flowsto _ _ Hfl Hwa) /region_rel Hwl /= /region_rel_perm.
    iDestruct (open_perm_region_map C ∅ (LNonHeap a') p' with "Hg Hrel") as "[Hg Hres]";
      first set_solver.
    iNext. iDestruct "Hres" as (v) "(%HpO & Hv & _)".
    iExists v. iFrame "Hv". iIntros "Hv".
    assert (∀ Cv : CmptName * LWord, Persistent (P ∅ Cv.1 Cv.2)) as HpersG
      by (intros Cv; apply (Hpers (∅, Cv.1, Cv.2))).
    iApply (close_perm_region_map C ∅ (LNonHeap a') p' (safeGC P) w with "Hg Hrel");
      first set_solver.
    iFrame "Hv %". iApply ("Hwcond" $! ∅ w Hloc).
    iApply (interp_global_world_free (th := t) W ∅ C w Hloc with "Hw").
  Qed.

End logrel_threads.

(** The trap path of the logical relation, at the core link: trap entry
    and the trap vector are stated with core WPs. *)
Section logrel_trap.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ}
    {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    {cthreads : CmptThreads}
    `{MP: MachineParameters}
  .
  Implicit Types w : (leibnizO LWord).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (** A fault in an untrusted compartment: the topmost frame's compartment
      is untrusted, the faulting registers are safe, and the logical
      relation's resources go to the trap vector, which may resume the
      faulting context or run an untrusted error handler through the FTLR. *)
  Definition untrusted_fault (cstk : CSTK) (regs : LReg) : iProp Σ :=
    untrusted_fault_pre interp interp_continuation cstk regs.

  Lemma untrusted_fault_intro (W : WORLD) (C : CmptName) (cstk : CSTK)
    (Ws : list WORLD) (Cs : list CmptName) (regs : LReg) :
    frame_match Ws Cs cstk W C →
    thread_in th C -∗
    interp_reg interp W C regs -∗
    top_cmpt_untrusted interp W C cstk -∗
    world_resources W C ∗ shared_credit C -∗
    interp_continuation cstk Ws Cs -∗
    untrusted_fault cstk regs.
  Proof.
    iIntros (Hframe) "Hth Hreg Htop [Hworld Hcred] Hcont". iExists W, C, Ws, Cs. by iFrame.
  Qed.

  (** The trap vector [wvec] is safe: after trap entry from any PC [w], with
      any call stack [cstk] and registers [regs], execution from [wvec] is
      safe, for a fault in an untrusted compartment ([untrusted_fault]) or
      a fault that the switcher handles ([trusted_fault], instantiated by
      the switcher with [trap_handler_ok ⊤]). Only a fault in an untrusted
      compartment carries the worlds and the continuation. Trap entry lends
      MEPCC, mcause and mtval to the trap vector ([trap_entry_out w]) and
      holds the trap-entry part [Ntrap] of the non-atomic token. *)
  Definition trap_vector_safe
      (trusted_fault : CSTK → LWord → LReg → iProp Σ) (wvec : LWord) : iProp Σ :=
    trap_vector_safe_pre interp interp_continuation trusted_fault wvec.

  #[global] Instance trap_vector_safe_persistent trusted_fault wvec :
    Persistent (trap_vector_safe trusted_fault wvec).
  Proof. rewrite /trap_vector_safe. apply _. Qed.

  (** A safe trap vector [mtcc_vec] is safe for a fault in an untrusted
      compartment. *)
  Lemma trap_vector_safe_untrusted (trusted_fault : CSTK → LWord → LReg → iProp Σ) :
    trap_vector_safe trusted_fault (lword_of_word mtcc_vec) -∗
    untrusted_trap_safe interp interp_continuation.
  Proof. apply trap_vector_safe_pre_untrusted. Qed.

  (** A fault closes through a safe trap vector: after exception entry, the
      PC holds the trap vector and execution is safe, for a fault in an
      untrusted compartment or one that [trusted_fault] accepts. *)
  Lemma interp_trap (trusted_fault : CSTK → LWord → LReg → iProp Σ)
    (cstk : CSTK) (regs : LReg) (wvec w : LWord) :
    (∀ r, is_Some (regs !! r)) ->
    trap_vector_safe trusted_fault wvec -∗
    (untrusted_fault cstk regs ∨ trusted_fault cstk w regs) -∗
    registers_pointsto regs -∗
    na_own (tpool th) (⊤ ∖ ↑Ntrap) -∗
    ◯(CSTK)[th] cstk -∗
    trap_entry_out w -∗
    (PC ↦ₚ[th] wvec -∗ safe[th]).
  Proof.
    iIntros (Hfull) "#Hsafe Hfault Hregs Hna Hcstk Hout HPC".
    iApply ("Hsafe" with "[//] Hfault HPC Hout Hregs Hna Hcstk").
  Qed.

  (** The fault obligation from a safe trap vector [mtcc_vec]: trap entry
      leads to the trap vector, where execution is safe. The resources and
      the fault's justification come under an update at the time of the fault (for instance,
      to close an invariant); the non-atomic token provides the trap-entry
      token, and the trap vector receives MEPCC, mcause and mtval. *)
  Lemma interp_trap_safe (trusted_fault : CSTK → LWord → LReg → iProp Σ)
    (cstk : CSTK) (regs : LReg) (w : LWord) :
    (∀ r, is_Some (regs !! r)) ->
    trap_vector_safe trusted_fault (lword_of_word mtcc_vec) -∗
    (|={⊤}=>
       registers_pointsto regs ∗
       na_own (tpool th) ⊤ ∗
       ◯(CSTK)[th] cstk ∗
       (untrusted_fault cstk regs ∨ trusted_fault cstk w regs)) -∗
    trap_safe w ⊤ (HO th).
  Proof.
    iIntros (Hfull) "#Hsafe Hres".
    iApply trap_safe_entry_intro.
    iSplit; last by iIntros "!> %Hv".
    iMod "Hres" as "(Hregs & Hna & Hcstk & Hfault)".
    iDestruct (trap_entry_res_split ⊤ with "Hna") as "[Htok Hna]"; first done.
    iModIntro. iFrame "Htok". iIntros "!> Hout HPC".
    by iApply (interp_trap with "Hsafe Hfault Hregs Hna Hcstk Hout HPC").
  Qed.

  (** A fault in an untrusted compartment, from the logical relation: the
      registers are safe and the topmost compartment is untrusted. *)
  Lemma interp_trap_safe_untrusted (trusted_fault : CSTK → LWord → LReg → iProp Σ)
    (W : WORLD) (C : CmptName) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (regs : LReg) (w : LWord) :
    (∀ r, is_Some (regs !! r)) ->
    frame_match Ws Cs cstk W C ->
    trap_vector_safe trusted_fault (lword_of_word mtcc_vec) -∗
    thread_in th C -∗
    interp_reg interp W C regs -∗
    top_cmpt_untrusted interp W C cstk -∗
    (|={⊤}=>
       registers_pointsto regs ∗
       (world_resources W C ∗ shared_credit C) ∗
       interp_continuation cstk Ws Cs ∗
       na_own (tpool th) ⊤ ∗
       ◯(CSTK)[th] cstk) -∗
    trap_safe w ⊤ (HO th).
  Proof.
    iIntros (Hfull Hframe) "Hsafe Hth Hreg Htop Hres".
    iApply (interp_trap_safe with "Hsafe"); first done.
    iMod "Hres" as "(Hregs & Hworld & Hcont & Hna & Hcstk)".
    iModIntro. iFrame "Hregs Hna Hcstk". iLeft.
    iApply (untrusted_fault_intro with "Hth Hreg Htop Hworld Hcont"); done.
  Qed.

End logrel_trap.

Section region_alloc_cmpt.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    {cthreads : CmptThreads}
    `{MP: MachineParameters}
  .
  #[local] Notation V := (interpO Σ).

  (** The predicate of the PCC range of a compartment (its import table and
      code): a word valid at every thread of the compartment. The import
      table holds the Local sentry of the switcher's call, which is not
      valid independently of the thread. *)
  Program Definition interp_cmpt_threads : V :=
    λne W C w, (□ ∀ t', thread_in t' C -∗ interp (th := t') W C w)%I.
  Solve All Obligations with solve_proper.

  #[global] Instance interp_cmpt_threads_persistent W C w :
    Persistent (interp_cmpt_threads W C w).
  Proof. rewrite /interp_cmpt_threads /=. apply _. Qed.

  Lemma persistent_cond_interp_cmpt_threads : persistent_cond interp_cmpt_threads.
  Proof. intros WCw; apply _. Qed.

  Lemma interp_cmpt_threads_int W C z π : ⊢ interp_cmpt_threads W C (WInt z @@? π).
  Proof. rewrite /interp_cmpt_threads /=. iIntros "!>" (t') "_". iApply interp_int. Qed.

  Lemma zcond_interp_cmpt_threads C : ⊢ zcond interp_cmpt_threads C.
  Proof. iIntros "!> %W1 %W2 %z %π _". iApply interp_cmpt_threads_int. Qed.

  (** The predicate of the data range of a compartment (its CGP range) and
      of the heap objects: a valid word that is not local. Its validity
      does not depend on the thread. *)
  Program Definition interp_nonlocal : V :=
    λne W C w, (⌜isLocalWord w.(lw) = false⌝ ∗ interp W C w)%I.
  Solve All Obligations with solve_proper.

  #[global] Instance interp_nonlocal_persistent W C w :
    Persistent (interp_nonlocal W C w).
  Proof. rewrite /interp_nonlocal /=. apply _. Qed.

  Lemma persistent_cond_interp_nonlocal : persistent_cond interp_nonlocal.
  Proof. intros WCw; apply _. Qed.

  Lemma interp_nonlocal_int W C z π : ⊢ interp_nonlocal W C (WInt z @@? π).
  Proof. rewrite /interp_nonlocal /=. iSplit; first done. iApply interp_int. Qed.

  Lemma zcond_interp_nonlocal C : ⊢ zcond interp_nonlocal C.
  Proof. iIntros "!> %W1 %W2 %z %π _". iApply interp_nonlocal_int. Qed.

  Lemma wcond_nwl_interp_nonlocal C : ⊢ wcond_nwl interp_nonlocal C interp.
  Proof. iIntros "!>" (W w Hloc) "#Hw". rewrite /interp_nonlocal /=. by iSplit. Qed.

End region_alloc_cmpt.
