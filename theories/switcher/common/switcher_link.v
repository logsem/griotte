From iris.proofmode Require Import proofmode.
From griotte Require Import rules.
From griotte Require Export posture switcher.

(** The user-thread number of a thread. The context-switch thread has no
    trusted stack: it gets thread 0's layout, which it never uses. *)
Definition thread_index (th : Thread) : nat :=
  match th with UserThread i => i | CtxSwitch => 0 end.

(** The layout of the section's thread: [b_trusted_stack] in a thread section
    is that thread's. *)
#[global] Instance tlayout_of {swlayout : switcherLayout} (th : Thread) : threadLayout :=
  swl_thread (thread_index th).
#[global] Instance tlayout_wf_of `{MP : MachineParameters}
  {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  (th : Thread) : threadLayoutWf (tlayout := tlayout_of th) := swl_thread_wf _.
#[global] Arguments tlayout_of : simpl never.
#[global] Arguments tlayout_wf_of : simpl never.

(** * The critical-section links of the switcher

    The link of a user thread holds, at InterruptEnabled, what the thread
    hands over ([handover_res]) and the part of its posture that the
    switcher describes: the register save area of its trusted stack but the
    word [hazardPointers] (which [trusted_stack_inv] keeps), and its mtdc
    token. The context-switch thread's part is mtdc holding zero; its link
    holds that part only while the physical mtdc is zero. *)

(** The MIE bit of the word [mstatus] of a register save area [ws] is
    InterruptDisabled. *)
Definition saved_mie_ok (ws : list LWord) : Prop :=
  ∀ w, ws !! Z.to_nat TrustedStack_offset_mstatus = Some w →
       mie_of (get_a w.(lw)) = InterruptDisabled.

Section switcher_link.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}
    {swlayout : switcherLayout}.

  (** The register save area of the trusted stack of [th], holding [ws],
      without its word [hazardPointers]. *)
  Definition save_area_holed (th : Thread) (ws : list LWord) : iProp Σ :=
    [∗ list] k ↦ a;w ∈ finz.seq_between (@b_trusted_stack (tlayout_of th))
                         (@b_trusted_stack (tlayout_of th) ^+ TSTACK_REGFRAME_SZ)%a; ws,
      if decide (k = Z.to_nat TrustedStack_offset_hazardPointers) then emp else a ↦ₐ w.

  (** The save area in the posture: its saved MIE is InterruptDisabled. *)
  Definition save_area_part (th : Thread) : iProp Σ :=
    ∃ ws : list LWord, ⌜saved_mie_ok ws⌝ ∗ save_area_holed th ws.

  Definition posture_part_of (th : Thread) : iProp Σ :=
    match th with
    | UserThread _ => save_area_part th ∗ @mtdc_lent Σ (@cb_mtdc_lent_of Σ ceriseb th)
    | CtxSwitch => mtdc ↦ₜ[CtxSwitch] ExceptionScratch (lword_of_word (WInt 0))
    end.

  (** MIE outermost: at InterruptDisabled the link is [True] at every
      thread. *)
  Definition crit_link_def (th : Thread) (σ : ExecConf) : iProp Σ :=
    (if mie_st σ is InterruptEnabled then
      match th with
      | UserThread _ => @handover_res Σ (ceriseG_of th) ∗ posture_part_of th
      | CtxSwitch =>
          if decide (sreg σ !! mtdc = Some (WInt 0))
          then @handover_res Σ (ceriseG_of CtxSwitch) ∗ posture_part_of CtxSwitch
          else @handover_res Σ (ceriseG_of CtxSwitch)
      end
    else True)%I.

  Lemma crit_link_def_stable th σ σ' :
    mie_st σ = mie_st σ' → sreg σ !! mtdc = sreg σ' !! mtdc →
    crit_link_def th σ ⊢ crit_link_def th σ'.
  Proof. intros Hm Hd. rewrite /crit_link_def Hm Hd. done. Qed.

  (** The full link, above [link_core]'s priority. *)
  #[global] Instance crit_link_full (th : Thread) : CritLink Σ th | 10 :=
    {| crit_link := crit_link_def th; crit_link_stable := crit_link_def_stable th |}.

  Lemma crit_link_full_unfold th σ :
    @crit_link Σ th (crit_link_full th) σ = crit_link_def th σ.
  Proof. done. Qed.

  (** The routing law: a user thread needs no mtdc fact; the context-switch
      thread runs at InterruptDisabled, and its part [MTDC ↦ 0] selects the
      branch of the link in the post-state. *)
  Lemma crit_route_full_law {th : Thread} σ :
    route_pre th (mie_st σ) →
    ⊢ crit_link_def th σ -∗ held_of (posture_part_of th) (mie_st σ) ==∗
      handover_res ∗
      (∀ σ2, cerise_state_interp σ2 -∗
             (if mie_st σ2 is InterruptEnabled then handover_res else True) ==∗
             cerise_state_interp σ2 ∗ crit_link_def th σ2 ∗
             (if mie_st σ2 is InterruptEnabled then True else posture_part_of th)).
  Proof.
    iIntros (Hpre) "Hl Hh". rewrite /crit_link_def /held_of.
    destruct th as [t|].
    - iAssert (@handover_res Σ (ceriseG_of (UserThread t)) ∗ posture_part_of (UserThread t))%I
        with "[Hl Hh]" as "[$ Hpart]".
      { destruct (mie_st σ); [iExact "Hl" | iExact "Hh"]. }
      iIntros "!>" (σ2) "Hsi Hho". destruct (mie_st σ2); by iFrame.
    - rewrite (Hpre eq_refl).
      iDestruct "Hh" as "[$ Hz]". iIntros "!>" (σ2) "Hsi Hho".
      iDestruct (SI_mtdc_zero with "Hsi Hz") as %Hd.
      destruct (mie_st σ2); last by iFrame.
      rewrite decide_True //. by iFrame.
  Qed.

  #[global] Instance crit_route_full (th : Thread) :
    @CritRoute Σ MP (ceriseG_of th) th (crit_link_full th) :=
    {| posture_part := posture_part_of th; crit_route := crit_route_full_law (th := th) |}.

  (** The part of a user thread. *)
  Lemma posture_part_user th :
    th ≠ CtxSwitch →
    @posture_part Σ MP (ceriseG_of th) th (crit_link_full th) (crit_route_full th) ⊣⊢
    save_area_part th ∗ @mtdc_lent Σ (@cb_mtdc_lent_of Σ ceriseb th).
  Proof. intros Hth. destruct th; [done | by destruct Hth]. Qed.

  (** The link of a user thread does not depend on mtdc. *)
  Lemma link_transfer_mtdc_user th (T : iProp Σ) :
    th ≠ CtxSwitch →
    @link_transfer Σ th (crit_link_full th) mtdc_written T T.
  Proof.
    intros Hth σ σ' Hw. rewrite !crit_link_full_unfold /crit_link_def /mtdc_written Hw.
    destruct th; [|done]. by iIntros "[$ $]".
  Qed.

  (** The resuming [mret] of the context-switch thread: mtdc holds the
      trusted stack of the resumed thread, so the link at InterruptEnabled
      is in its branch without [MTDC ↦ 0], and takes only [handover_res]. *)
  Lemma link_transfer_ctx_resume (q : InterruptStatus) p' b e a :
    link_transfer_si (ceriseg := ceriseG_of CtxSwitch) (th := CtxSwitch)
      (CL := crit_link_full CtxSwitch) (mie_move InterruptDisabled q)
      (mtdc ↦ₜ[CtxSwitch] (Capₗ p' _ b e a) ∗ @handover_res Σ (ceriseG_of CtxSwitch))
      (mtdc ↦ₜ[CtxSwitch] (Capₗ p' _ b e a) ∗
       (if q is InterruptEnabled then True else @handover_res Σ (ceriseG_of CtxSwitch))).
  Proof.
    iIntros (σ σ' (_ & Hq & _)) "(Hsi & _ & Hm & Hho)".
    iDestruct (SI_mtdc_tstack with "Hsi Hm") as %Hd.
    rewrite !crit_link_full_unfold /crit_link_def Hq. iModIntro.
    destruct q; last by iFrame.
    rewrite decide_False //. by iFrame.
  Qed.
End switcher_link.

#[global] Arguments crit_link_full : simpl never.
#[global] Arguments crit_route_full : simpl never.
#[global] Arguments posture_part_of : simpl never.
#[global] Arguments crit_link_def : simpl never.

(** * Record checks at the full link

    At InterruptEnabled, the link of a user thread holds its mtdc token: its
    mtdc is at home (the trusted stack, by [trusted_stack_inv]), and the
    mtdc window, which lends the token, is open only at InterruptDisabled. *)
Section switcher_link_pins.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}
    {swlayout : switcherLayout} {th : Thread}.

  Lemma crit_link_user_enabled_mtdc σ m :
    th ≠ CtxSwitch →
    mie_st σ = InterruptEnabled →
    cerise_state_interp σ -∗
    crit_link_def th σ -∗
    mtdc ↦ₜ m -∗
    ⌜m = mtdc_home⌝.
  Proof.
    iIntros (Hth Hen) "Hsi Hl Hf".
    rewrite /crit_link_def Hen.
    destruct th as [t|]; last by destruct Hth.
    rewrite /posture_part_of. iDestruct "Hl" as "(_ & _ & Hlent)".
    iDestruct (SI_open with "Hsi") as "Hsi". iNamed "Hsi".
    iDestruct (sys_interp_mtdc_agree with "Hsr Hf") as %[<- _].
    iApply (sys_interp_mtdc_lent with "Hsr Hlent").
  Qed.

  Lemma crit_link_user_window_closed σ m :
    th ≠ CtxSwitch →
    m ≠ mtdc_home →
    cerise_state_interp σ -∗
    crit_link_def th σ -∗
    mtdc ↦ₜ m -∗
    ⌜mie_st σ = InterruptDisabled⌝.
  Proof.
    iIntros (Hth Hm) "Hsi Hl Hf".
    destruct (mie_st σ) eqn:Hmie; last done.
    by iDestruct (crit_link_user_enabled_mtdc with "Hsi Hl Hf") as %?.
  Qed.
End switcher_link_pins.

(** * Full-link forms of the rules that move a posture *)

Section mtdc_full.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}
    {swlayout : switcherLayout} {th : Thread}.

  (** The mtdc writes of a user thread at the full link: the open, ex and
      close forms of the core rules. *)
  Lemma wp_specialrw_swap_mtdc_open_full E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r (v : LWord)
      m m' dq :
    th ≠ CtxSwitch →
    decodeInstrW w.(lw) = SpecialRW r mtdc (inr r) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    r ≠ cnull →
    m = mtdc_home →
    mtdc_match m' v →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r ↦ᵣ v ∗
        ▷ mtdc ↦ₜ m ∗
        ▷ mtdc_lent }}}
      Instr Executable @ E
      {{{ vm, RET NextIV;
          ⌜mtdc_match m vm⌝ ∗
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          r ↦ᵣ vm ∗
          mtdc ↦ₜ m' }}}.
  Proof.
    iIntros (Hth Hinstr Hvpc Hxsr Hpca' Hr Hhome Hm' φ) "(HPC & Hpc_a & Hr & Hmtdc & HL) Hφ".
    subst m.
    iApply (wp_specialrw_swap_mtdc_link _ _ _ _ _ _ _ _ _ _ _ mtdc_home m' _ True%I True%I
              mtdc_lent True%I with "[$HPC $Hpc_a $Hr $Hmtdc $HL]").
    all: try done.
    { by apply link_transfer_mtdc_user. }
    { apply mtdc_clause_open. }
    iIntros "!>" (vm) "(Hm & HPC & Hpc_a & Hr & Hmtdc & _)". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_specialrw_swap_mtdc_ex_full E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r (v : LWord)
      m m' dq :
    th ≠ CtxSwitch →
    decodeInstrW w.(lw) = SpecialRW r mtdc (inr r) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    r ≠ cnull →
    m ≠ mtdc_home →
    mtdc_match m' v →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r ↦ᵣ v ∗
        ▷ mtdc ↦ₜ m }}}
      Instr Executable @ E
      {{{ vm, RET NextIV;
          ⌜mtdc_match m vm⌝ ∗
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          r ↦ᵣ vm ∗
          mtdc ↦ₜ m' }}}.
  Proof.
    iIntros (Hth Hinstr Hvpc Hxsr Hpca' Hr Hne Hm' φ) "(HPC & Hpc_a & Hr & Hmtdc) Hφ".
    iApply (wp_specialrw_swap_mtdc_link _ _ _ _ _ _ _ _ _ _ _ m m' _ True%I True%I
              True%I True%I with "[$HPC $Hpc_a $Hr $Hmtdc]").
    all: try done.
    { by apply link_transfer_mtdc_user. }
    { by apply mtdc_clause_ex. }
    iIntros "!>" (vm) "(Hm & HPC & Hpc_a & Hr & Hmtdc & _)". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_writesr_mtdc_close_full E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src (v : LWord) m dq :
    th ≠ CtxSwitch →
    decodeInstrW w.(lw) = SpecialRW cnull mtdc (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    m ≠ mtdc_home →
    mtdc_match mtdc_home v →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ v ∗
        ▷ mtdc ↦ₜ m }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          src ↦ᵣ v ∗
          mtdc ↦ₜ mtdc_home ∗
          mtdc_lent }}}.
  Proof.
    iIntros (Hth Hinstr Hvpc Hxsr Hpca' Hsrc Hne Hm' φ) "(HPC & Hpc_a & Hsrc & Hmtdc) Hφ".
    iApply (wp_writesr_mtdc_link _ _ _ _ _ _ _ _ _ _ _ m mtdc_home _ True%I True%I
              True%I mtdc_lent with "[$HPC $Hpc_a $Hsrc $Hmtdc]").
    all: try done.
    { by apply link_transfer_mtdc_user. }
    { by apply mtdc_clause_close. }
    iIntros "!> (HPC & Hpc_a & Hsrc & Hmtdc & _ & Hl)". iApply "Hφ". iFrame.
  Qed.
End mtdc_full.
