From iris.proofmode Require Import proofmode.
From griotte Require Import named_props_extra.
From griotte Require Export state_interp.

(** * Postures

    The resources a thread holds at an interrupt posture, and the routing
    law of a critical-section link. At InterruptDisabled the thread holds
    [handover_res] (the critical-section token, the unwedged token and the
    volatile registers: MEPCC, mcause, mtval and MPIE) and the part of its
    posture that the link describes ([posture_part]); at InterruptEnabled
    the link holds them. *)

(** The context-switch thread runs at InterruptDisabled only. *)
Definition route_pre (th : Thread) (b : InterruptStatus) : Prop :=
  th = CtxSwitch → b = InterruptDisabled.

(** An optional pin of a value. *)
Definition opt_pin {A} (o : option A) (x : A) : Prop :=
  match o with Some y => y = x | None => True end.

(** MIE and MPIE of a configuration are those of the logical system
    registers it erases to. *)
Lemma erasure_mie_st `{MP : MachineParameters} R C σ lpc lreg ls lmem :
  erasure R C σ lpc lreg (ls_join ls) lmem →
  mie_st σ = ls_mie ls ∧ mpie_st σ = ls_mpie ls.
Proof.
  intros Her.
  destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her (ls_join_mstatus ls))
    as (wst & Hwst & Hrelst).
  apply reg_phys_no_bounds in Hrelst; last done. cbn in Hrelst. subst wst.
  rewrite /mie_st /mpie_st Hwst /= mie_of_mstatus_enc mpie_of_mstatus_enc. done.
Qed.

Section handover.
  Context `{MP : MachineParameters} `{ceriseg : ceriseG Σ}.

  (** The volatile registers, at given values: MEPCC, mcause, mtval (an
      integer) and MPIE. *)
  Definition volatile_csr_at (p c : LWord) (v : Z) (b : InterruptStatus) : iProp Σ :=
    mepcc ↦ₓ p ∗
    mcause ↦ₓ c ∗
    mtval ↦ₓ lword_of_word (WInt v) ∗
    MPIE_frag b.

  (** What a critical section hands over: the critical-section token, the
      unwedged token and the volatile registers. *)
  Definition handover_at (p c : LWord) (v : Z) (b : InterruptStatus) : iProp Σ :=
    na_own crit ⊤ ∗
    unwedged ∗
    volatile_csr_at p c v b.

  Definition handover_res_def : iProp Σ := ∃ p c v b, handover_at p c v b.
  #[local] Definition handover_res_aux : seal (@handover_res_def). Proof. by eexists. Qed.
  Definition handover_res := handover_res_aux.(unseal).
  #[local] Definition handover_res_unseal :
    @handover_res = @handover_res_def := handover_res_aux.(seal_eq).

  #[global] Instance handover_res_timeless : Timeless handover_res.
  Proof. rewrite handover_res_unseal. apply _. Qed.

  Lemma handover_res_unfold : handover_res ⊣⊢ ∃ p c v b, handover_at p c v b.
  Proof. by rewrite handover_res_unseal. Qed.

  Lemma handover_res_intro p c v b : handover_at p c v b -∗ handover_res.
  Proof. rewrite handover_res_unseal. iIntros "H". by iExists p, c, v, b. Qed.

  (** The critical-section token, lent out of [handover_res]. *)
  Lemma handover_res_crit :
    handover_res -∗
    na_own crit ⊤ ∗
    (na_own crit ⊤ -∗ handover_res).
  Proof.
    rewrite handover_res_unseal.
    iIntros "(%p & %c & %v & %b & Hcrit & HU & Hv)". iFrame "Hcrit".
    iIntros "Hcrit". iExists p, c, v, b. by iFrame.
  Qed.

  (** What the thread holds besides its MIE fragment at posture [b], for the
      part [part] of its posture: nothing at InterruptEnabled. *)
  Definition held_of (part : iProp Σ) (b : InterruptStatus) : iProp Σ :=
    if b is InterruptDisabled then (handover_res ∗ part)%I else True%I.

  (** The MIE fragment agrees with the state interpretation. *)
  Lemma SI_mie_st σ b :
    cerise_state_interp σ -∗ MIE_frag b -∗ ⌜mie_st σ = b⌝.
  Proof.
    iIntros "Hσ Hf". iDestruct (SI_open with "Hσ") as "Hσ". iNamed "Hσ".
    iDestruct (sys_interp_mie_agree with "Hsr Hf") as %<-.
    iPureIntro. by destruct (erasure_mie_st _ _ _ _ _ _ _ Her).
  Qed.
End handover.

(** The routing law of a link: take [handover_res] out of the link (at
    InterruptEnabled) or out of what the thread holds (at
    InterruptDisabled), and get a wand that, for any post-state, rebuilds
    the link and the part of the posture from the post-state MIE. At a
    post-state with InterruptEnabled the wand takes [handover_res] back into
    the link; at InterruptDisabled the thread keeps it. *)
Class CritRoute Σ `{MP : MachineParameters} {ceriseg : ceriseG Σ} (th : Thread)
    (CL : CritLink Σ th) := {
  posture_part : iProp Σ;
  crit_route σ :
    route_pre th (mie_st σ) →
    ⊢ @crit_link Σ th CL σ -∗ held_of posture_part (mie_st σ) ==∗
      handover_res ∗
      (∀ σ2, cerise_state_interp σ2 -∗
             (if mie_st σ2 is InterruptEnabled then handover_res else True%I) ==∗
             cerise_state_interp σ2 ∗
             @crit_link Σ th CL σ2 ∗
             (if mie_st σ2 is InterruptEnabled then True%I else posture_part));
}.
#[export] Hint Mode CritRoute + - - + + : typeclass_instances.

Section posture.
  Context `{MP : MachineParameters} `{ceriseg : ceriseG Σ} {th : Thread} {CL : CritLink Σ th}
    {CR : CritRoute Σ th CL}.

  (** What the thread holds besides its MIE fragment at posture [b]. *)
  Definition held (b : InterruptStatus) : iProp Σ := held_of (@posture_part _ _ _ th CL CR) b.

  Lemma held_enabled : held InterruptEnabled ⊣⊢ True.
  Proof. done. Qed.

  Lemma held_disabled : held InterruptDisabled ⊣⊢ handover_res ∗ @posture_part _ _ _ th CL CR.
  Proof. done. Qed.

  (** The whole posture, with optional pins of MPIE, MEPCC, mcause and
      mtval. *)
  Definition posture_res_def (ob : option InterruptStatus) (op oc : option LWord) (ov : option Z)
    : iProp Σ :=
    (∃ p c v b,
       ⌜opt_pin ob b⌝ ∗ ⌜opt_pin op p⌝ ∗ ⌜opt_pin oc c⌝ ∗ ⌜opt_pin ov v⌝ ∗
       handover_at p c v b) ∗
    @posture_part _ _ _ th CL CR.
  #[local] Definition posture_res_aux : seal (@posture_res_def). Proof. by eexists. Qed.
  Definition posture_res_gen := posture_res_aux.(unseal).
  #[local] Definition posture_res_unseal :
    @posture_res_gen = @posture_res_def := posture_res_aux.(seal_eq).

  Lemma posture_res_gen_unfold ob op oc ov :
    posture_res_gen ob op oc ov ⊣⊢
    (∃ p c v b,
       ⌜opt_pin ob b⌝ ∗ ⌜opt_pin op p⌝ ∗ ⌜opt_pin oc c⌝ ∗ ⌜opt_pin ov v⌝ ∗
       handover_at p c v b) ∗
    @posture_part _ _ _ th CL CR.
  Proof. by rewrite posture_res_unseal. Qed.

  (** The posture without the critical-section token, with optional pins
      of MPIE, MEPCC, mcause and mtval. *)
  Definition posture_lent (ob : option InterruptStatus) (op oc : option LWord) (ov : option Z)
    : iProp Σ :=
    (∃ p c v b,
       ⌜opt_pin ob b⌝ ∗ ⌜opt_pin op p⌝ ∗ ⌜opt_pin oc c⌝ ∗ ⌜opt_pin ov v⌝ ∗
       unwedged ∗
       volatile_csr_at p c v b) ∗
    @posture_part _ _ _ th CL CR.

  (** The critical-section token, lent out of the whole posture. *)
  Lemma posture_res_gen_lend ob op oc ov :
    posture_res_gen ob op oc ov ⊣⊢ na_own crit ⊤ ∗ posture_lent ob op oc ov.
  Proof.
    rewrite posture_res_gen_unfold /posture_lent /handover_at. iSplit.
    - iIntros "[(%p & %c & %v & %b & ? & ? & ? & ? & $ & HU & Hv) $]".
      iExists p, c, v, b. by iFrame.
    - iIntros "[Hcrit [(%p & %c & %v & %b & ? & ? & ? & ? & HU & Hv) $] ]".
      iExists p, c, v, b. by iFrame.
  Qed.

  (** The critical-section token, lent out of what the thread holds at
      InterruptDisabled. *)
  Lemma held_lend :
    held InterruptDisabled ⊣⊢ na_own crit ⊤ ∗ posture_lent None None None None.
  Proof.
    rewrite held_disabled handover_res_unfold /posture_lent /handover_at. iSplit.
    - iIntros "[(%p & %c & %v & %b & $ & HU & Hv) $]".
      iExists p, c, v, b. by iFrame.
    - iIntros "[Hcrit [(%p & %c & %v & %b & _ & _ & _ & _ & HU & Hv) $] ]".
      iExists p, c, v, b. by iFrame.
  Qed.

  (** [held_lend] as a wand, for a client that gives the token back. *)
  Lemma held_crit :
    held InterruptDisabled -∗
    na_own crit ⊤ ∗
    (na_own crit ⊤ -∗ held InterruptDisabled).
  Proof. rewrite held_lend. iIntros "[$ Hlent] Hcrit". iFrame. Qed.

  Lemma posture_res_gen_intro p c v b :
    handover_at p c v b -∗
    @posture_part _ _ _ th CL CR -∗
    posture_res_gen (Some b) (Some p) (Some c) (Some v).
  Proof.
    rewrite posture_res_unseal. iIntros "Hh Hp". iFrame "Hp".
    iExists p, c, v, b. by iFrame "Hh".
  Qed.

  (** Forgetting the pins. *)
  Lemma posture_res_gen_unpin ob op oc ov :
    posture_res_gen ob op oc ov -∗ posture_res_gen None None None None.
  Proof.
    rewrite posture_res_unseal. iIntros "[(%p & %c & %v & %b & _ & _ & _ & _ & Hh) $]".
    iExists p, c, v, b. by iFrame "Hh".
  Qed.

  (** The whole posture is what the thread holds at InterruptDisabled. *)
  Lemma posture_res_held ob op oc ov :
    posture_res_gen ob op oc ov -∗ held InterruptDisabled.
  Proof.
    rewrite posture_res_unseal /held /held_of.
    iIntros "[(%p & %c & %v & %b & _ & _ & _ & _ & Hh) $]".
    by iApply handover_res_intro.
  Qed.

  (** A window is open only at InterruptDisabled: at InterruptEnabled, the
      link of a thread that may run there holds [handover_res], so the
      thread holds none of its exclusive parts. *)
  Lemma crit_link_enabled_handover σ :
    route_pre th (mie_st σ) →
    mie_st σ = InterruptEnabled →
    @crit_link Σ th CL σ ==∗ ∃ p c v b, handover_at p c v b.
  Proof.
    iIntros (Hpre Hen) "Hl".
    iMod (crit_route σ with "Hl []") as "[Hho _]"; [done | by rewrite Hen |].
    iModIntro. by iApply handover_res_unfold.
  Qed.

  Lemma window_closed_unwedged σ :
    route_pre th (mie_st σ) →
    mie_st σ = InterruptEnabled →
    @crit_link Σ th CL σ -∗ unwedged ==∗ False.
  Proof.
    iIntros (Hpre Hen) "Hl HU".
    iMod (crit_link_enabled_handover with "Hl") as (p c v b) "(_ & HU' & _)"; [done..|].
    iDestruct (unwedged_excl with "HU HU'") as %[].
  Qed.

  Lemma window_closed_mpie σ (b : InterruptStatus) :
    route_pre th (mie_st σ) →
    mie_st σ = InterruptEnabled →
    @crit_link Σ th CL σ -∗ MPIE_frag b ==∗ False.
  Proof.
    iIntros (Hpre Hen) "Hl Hf".
    iMod (crit_link_enabled_handover with "Hl") as (p c v b') "(_ & _ & _ & _ & _ & Hf')";
      [done..|].
    iDestruct (MPIE_frag_excl with "Hf Hf'") as %[].
  Qed.

  Lemma held_posture_res :
    held InterruptDisabled -∗ posture_res_gen None None None None.
  Proof.
    rewrite posture_res_unseal /held /held_of handover_res_unfold.
    iIntros "[(%p & %c & %v & %b & Hh) $]". iExists p, c, v, b. by iFrame "Hh".
  Qed.
End posture.

Notation posture_res := (posture_res_gen None None None None).
Notation "'posture_res{' b } " := (posture_res_gen (Some b) None None None)
  (at level 0, b at level 200, format "posture_res{ b }") : bi_scope.
Notation "'posture_res{' b , e } " := (posture_res_gen (Some b) (Some e) None None)
  (at level 0, b at level 200, e at level 200, format "posture_res{ b ,  e }") : bi_scope.
Notation "'posture_res{' b , e , c } " := (posture_res_gen (Some b) (Some e) (Some c) None)
  (at level 0, b at level 200, e at level 200, c at level 200,
   format "posture_res{ b ,  e ,  c }") : bi_scope.

(** * The transfer of a link by a step that may change MIE or mtdc

    [link_transfer_si P T1 T2]: for states related by [P], the link of the
    state before the step, with [T1], gives the link of the state after the
    step, with [T2], with the state interpretation of the state after the
    step in hand. *)
Section link_transfer_si.
  Context `{MP : MachineParameters} `{ceriseg : ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.

  Definition link_transfer_si (P : ExecConf → ExecConf → Prop) (T1 T2 : iProp Σ) : Prop :=
    ∀ σ σ', P σ σ' →
      cerise_state_interp σ' ∗ @crit_link Σ th CL σ ∗ T1 ⊢
      |==> cerise_state_interp σ' ∗ @crit_link Σ th CL σ' ∗ T2.

  (** A transfer that does not need the state interpretation. *)
  Lemma link_transfer_si_of P T1 T2 :
    link_transfer P T1 T2 → link_transfer_si P T1 T2.
  Proof.
    iIntros (Htr σ σ' HP) "($ & Hl & HT)". iApply (Htr _ _ HP with "[$Hl $HT]").
  Qed.

  Lemma link_transfer_si_weaken P T1 T2 T1' T2' :
    (T1' ⊢ T1) → (T2 ⊢ T2') →
    link_transfer_si P T1 T2 → link_transfer_si P T1' T2'.
  Proof.
    iIntros (H1 H2 Htr σ σ' HP) "(HSI & Hl & HT)".
    iMod (Htr _ _ HP with "[$HSI $Hl HT]") as "($ & $ & HT)"; first by iApply H1.
    iModIntro. by iApply H2.
  Qed.

  (** A step that keeps MIE and mtdc keeps the link, with any resource. *)
  Lemma link_transfer_si_kept b T :
    link_transfer_si (mie_move b b) T T.
  Proof.
    iIntros (σ σ' (Hb & Hb' & Hmtdc)) "($ & Hl & $)". iModIntro.
    iApply (crit_link_stable with "Hl"); [congruence | done].
  Qed.

  (** The posture moves with MIE, by the routing law. *)
  Lemma link_transfer_si_route `{CR : !CritRoute Σ th CL} b b' :
    route_pre th b →
    link_transfer_si (mie_move b b') (held b) (held b').
  Proof.
    iIntros (Hpre σ σ' (Hb & Hb' & _)) "(HSI & Hl & Hh)".
    iMod (crit_route σ with "Hl [Hh]") as "[Hho Hrestore]"; [by rewrite Hb | by rewrite Hb |].
    rewrite /held /held_of. destruct b'.
    - iMod ("Hrestore" $! σ' with "HSI [Hho]") as "($ & $ & _)"; first by rewrite Hb'.
      done.
    - iMod ("Hrestore" $! σ' with "HSI []") as "($ & $ & Hp)"; first by rewrite Hb'.
      iRevert "Hp". rewrite Hb'. iIntros "Hp". by iFrame.
  Qed.
End link_transfer_si.

(** At the core link, any transfer holds with the same resource. *)
Lemma link_transfer_si_core `{MP : MachineParameters} `{ceriseg : ceriseG Σ} {th : Thread} P
    (T : iProp Σ) :
  link_transfer_si (CL := link_core) P T T.
Proof. iIntros (σ σ' _) "($ & _ & $)". done. Qed.

Section si_mtdc.
  Context `{MP : MachineParameters} `{ceriseg : ceriseG Σ}.

  (** The fragment of mtdc pins the physical mtdc: zero for zero... *)
  Lemma SI_mtdc_zero σ :
    cerise_state_interp σ -∗
    mtdc ↦ₜ ExceptionScratch (lword_of_word (WInt 0)) -∗
    ⌜sreg σ !! mtdc = Some (WInt 0)⌝.
  Proof.
    iIntros "Hσ Hf". iDestruct (SI_open with "Hσ") as "Hσ". iNamed "Hσ".
    iDestruct (sys_interp_mtdc_agree with "Hsr Hf") as %[_ Hm]. cbn in Hm.
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her (ls_join_mtdc lsreg)) as (w & Hw & Hrel).
    rewrite Hm in Hrel. apply reg_phys_no_bounds in Hrel; last done. cbn in Hrel. subst w.
    done.
  Qed.

  (** ... and a capability for a trusted-stack value. *)
  Lemma SI_mtdc_tstack σ p b e a :
    cerise_state_interp σ -∗
    mtdc ↦ₜ (Capₗ p _ b e a) -∗
    ⌜sreg σ !! mtdc ≠ Some (WInt 0)⌝.
  Proof.
    iIntros "Hσ Hf". iDestruct (SI_open with "Hσ") as "Hσ". iNamed "Hσ".
    iDestruct (sys_interp_mtdc_agree with "Hsr Hf") as %[_ [g Hm] ].
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her (ls_join_mtdc lsreg)) as (w & Hw & Hrel).
    rewrite Hm in Hrel. destruct (reg_phys_and_tag _ _ _ Hrel) as [s ->]. rewrite Hw.
    iPureIntro. intros Heq. simplify_eq.
  Qed.
End si_mtdc.
