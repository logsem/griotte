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
  Implicit Types w : LWord.
  Implicit Types reg : gmap RegName LWord.
  Implicit Types ms : gmap Addr LWord.


  (* The new PC is the source word with its identifier; the link is built
     from the PC and takes the PC's identifier. A [cnull] destination drops
     the link. The link's kind depends on MIE before the jump, which the
     state interpretation holds: the spec quantifies over it. *)
  Inductive Jalr_spec (regs : LReg) pc_p pc_g pc_b pc_e pc_a pc_π (rdst rsrc: RegName) :
    LWord → LReg → griotte_lang.val → Prop :=
  | Jalr_spec_success regs' pc_a' wsrc mie :
    regs !!ₗ rsrc = Some wsrc ->
    jalr_target_ok rdst rsrc wsrc.(lw) = true ->
    (pc_a + 1)%a = Some pc_a' ->
    regs' = (if decide (rdst = cnull) then regs
             else <[rdst := jalr_link rdst mie true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ]ₗ> regs) →
    Jalr_spec regs pc_p pc_g pc_b pc_e pc_a pc_π rdst rsrc (lupdatePcPerm wsrc) regs' NextIV
  | Jalr_spec_failure_target wsrc :
    regs !!ₗ rsrc = Some wsrc ->
    jalr_target_ok rdst rsrc wsrc.(lw) = false ->
    Jalr_spec regs pc_p pc_g pc_b pc_e pc_a pc_π rdst rsrc
      (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs FaultedV
  | Jalr_spec_failure :
    (pc_a + 1)%a = None ->
    Jalr_spec regs pc_p pc_g pc_b pc_e pc_a pc_π rdst rsrc
      (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs FaultedV.

  Lemma wp_Jalr Ep pc_p pc_g pc_b pc_e pc_a pc_π w rdst rsrc regs dq :
    decodeInstrW w.(lw) = Jalr rdst rsrc ->
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Jalr rdst rsrc) ⊆ dom regs →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lpc' regs' retv, RET retv;
        ⌜ Jalr_spec regs pc_p pc_g pc_b pc_e pc_a pc_π rdst rsrc lpc' regs' retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step_link with "HPC Hpc_a Hmap"); eauto.
    iNext; iIntros (r sr m st lreg lsreg lmem R C c σ') "@".
    assert (∃ vst, ls_join lsreg !! mstatus = Some vst) as [vst Hvst'].
    { eexists. apply ls_join_mstatus. }
    rewrite Hinstr in Hstep.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri.
    unfold regs_of, operands_of in Hri, Dregs.
    destruct (Hri rsrc) as [wsrc [H'rsrc _] ]; first by set_solver+.
    destruct (llookup_reg_phys _ _ _ _ _ Hregs H'rsrc) as (s & Hrsrc & Hrel).
    pose proof (erasure_llookup_reg_word _ _ _ _ _ _ _ _ _ _ Her Hlregs H'rsrc) as Hoksrc.
    pose proof (er_pc_word _ _ _ _ _ _ _ Her) as HokPC.
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hvst') as (wst & Hwst & Hrelst).
    assert (get_a wst = get_a vst.(lw)) as Hast.
    { destruct (reg_phys_and_tag _ _ _ Hrelst) as [s' ->]. apply get_a_and_tag. }
    rewrite /exec /= Hrsrc /= jalr_target_checks in Hstep.
    (* The target checks fail on the physical copy exactly when they fail on
       the logical word: a word that passes them is executable, hence
       exact. *)
    destruct (jalr_target_ok rdst rsrc wsrc.(lw)) eqn:Hok; cycle 1.
    { rewrite jalr_target_ok_and_tag Hok andb_false_r in Hstep.
      instr_fail Hstep. by eapply Jalr_spec_failure_target. }
    assert (and_tag s wsrc.(lw) = wsrc.(lw)) as Heq.
    { pose proof Hok as Hok'. apply andb_prop in Hok' as [[Ht _]%andb_prop Hx].
      by apply (reg_phys_executable R C). }
    rewrite Heq in Hstep Hrel. rewrite Hok Hwst /= in Hstep.
    destruct (pc_a + 1)%a as [pc_a'|] eqn:Hpca'; cbn in Hstep.
    2: { instr_fail Hstep. by constructor. }
    rewrite Hast in Hstep.
    injection Hstep as <- <-.
    set (mie := mie_of (get_a vst.(lw))).
    set (link := jalr_link rdst mie true pc_p pc_g pc_b pc_e pc_a').
    pose proof (erasure_pc_no_id _ _ _ _ _ _ _ Her Hvpc) as Hπ. cbn in Hπ.
    assert (reg_word_ok R C (link @@? pc_π)) as Hoklink.
    { rewrite /link /jalr_link. case_decide;
        (apply (reg_word_ok_derive _ _ (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π));
         [by left|done|done|done]). }
    assert (reg_phys R (link @@? pc_π) link) as Hrellink by (by apply reg_phys_no_id).
    (* mstatus, held by the state interpretation: a sentry that sets the
       interrupt status writes MIE. *)
    destruct (jalr_mstatus wsrc.(lw) (get_a vst.(lw))) as [z|] eqn:Hmie.
    - pose proof Hmie as Hz. rewrite /jalr_mstatus in Hz.
      apply fmap_Some in Hz as (mie' & _ & Hzeq).
      pose proof (erasure_insert_sreg _ _ _ _ _ _ _ _ _ _ _ mstatus
                    (lword_of_word (WInt (mstatus_enc mie' (mpie_of (get_a vst.(lw))))))
                    (WInt z) Her) as Her1.
      specialize (Her1 ltac:(apply reg_word_ok_int) ltac:(by intros) ltac:(by intros)
                    ltac:(rewrite Hzeq; apply reg_phys_lword_of_word)).
      rewrite -ls_join_set_mstatus in Her1.
      iMod (sys_interp_set_mstatus _ mie' (mpie_of (get_a vst.(lw))) with "Hsr") as "Hsr".
      destruct (decide (rdst = cnull)) as [Hnull | Hnull].
      + iApply instr_close_core.
        iApply (instr_close_set_pc (Cap pc_p pc_g pc_b pc_e pc_a) r
                  (<[mstatus := WInt z]> sr) m st _ lreg _ lmem R C _ (lupdatePcPerm wsrc)
                  with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap").
        * exact Her1.
        * by apply reg_word_ok_lupdatePcPerm.
        * by apply reg_phys_lupdatePcPerm.
        * by eapply jalr_target_ok_pc_ok.
        * iIntros "HPC Hmap". iApply "Hφ". iFrame. iPureIntro.
          eapply (Jalr_spec_success _ _ _ _ _ _ _ _ _ _ _ _ mie);
            [exact H'rsrc | exact Hok | exact Hpca' |].
          by rewrite decide_True.
      + iApply instr_close_core.
        iApply (instr_close_reg_set_pc (Cap pc_p pc_g pc_b pc_e pc_a) r
                  (<[mstatus := WInt z]> sr) m st _ lreg _ lmem R C _ rdst
                  (link @@? pc_π) link (lupdatePcPerm wsrc)
                  with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap").
        * exact Her1.
        * right. apply Dregs. set_solver.
        * exact Hoklink.
        * exact Hrellink.
        * by apply reg_word_ok_lupdatePcPerm.
        * by apply reg_phys_lupdatePcPerm.
        * by eapply jalr_target_ok_pc_ok.
        * iIntros "HPC Hmap". iApply "Hφ". iFrame. iPureIntro.
          eapply (Jalr_spec_success _ _ _ _ _ _ _ _ _ _ _ _ mie);
            [exact H'rsrc | exact Hok | exact Hpca' |].
          by rewrite decide_False.
    - destruct (decide (rdst = cnull)) as [Hnull | Hnull].
      + iApply instr_close_core.
        iApply (instr_close_set_pc _ _ _ _ _ _ _ _ _ _ _ _ (lupdatePcPerm wsrc)
                  with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap").
        * exact Her.
        * by apply reg_word_ok_lupdatePcPerm.
        * by apply reg_phys_lupdatePcPerm.
        * by eapply jalr_target_ok_pc_ok.
        * iIntros "HPC Hmap". iApply "Hφ". iFrame. iPureIntro.
          eapply (Jalr_spec_success _ _ _ _ _ _ _ _ _ _ _ _ mie);
            [exact H'rsrc | exact Hok | exact Hpca' |].
          by rewrite decide_True.
      + iApply instr_close_core.
        iApply (instr_close_reg_set_pc _ _ _ _ _ _ _ _ _ _ _ _ rdst
                  (link @@? pc_π) link (lupdatePcPerm wsrc)
                  with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap").
        * exact Her.
        * right. apply Dregs. set_solver.
        * exact Hoklink.
        * exact Hrellink.
        * by apply reg_word_ok_lupdatePcPerm.
        * by apply reg_phys_lupdatePcPerm.
        * by eapply jalr_target_ok_pc_ok.
        * iIntros "HPC Hmap". iApply "Hφ". iFrame. iPureIntro.
          eapply (Jalr_spec_success _ _ _ _ _ _ _ _ _ _ _ _ mie);
            [exact H'rsrc | exact Hok | exact Hpca' |].
          by rewrite decide_False.
  Qed.

  (** A jump whose destination is neither [cnull] nor [cra]: the target is
      unsealed or an inheriting sentry, and the link is the unsealed PC. *)
  Lemma wp_jalr_success E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w rsrc wsrc rdst wdst dq :
    decodeInstrW w.(lw) = Jalr rdst rsrc →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    jalr_target_ok rdst rsrc wsrc.(lw) = true →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->
    rdst ≠ cra ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ rsrc ↦ᵣ wsrc
        ∗ ▷ rdst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ lupdatePcPerm wsrc
          ∗ pc_a ↦ₐ{dq} w
          ∗ rsrc ↦ᵣ wsrc
          ∗ rdst ↦ᵣ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Htgt Hcnull Hcnull' Hcra ϕ) "(>HPC & >Hpc_a & >Hrsrc & >Hrdst) Hφ".
    iDestruct (map_of_regs_2 with "Hrsrc Hrdst") as "[Hmap %]".
    iApply (wp_Jalr with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { set_solver. }
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

   destruct Hspec as [ ? ? ? mie | ? Hlook Hfail | Hfail ]; subst.
   { rewrite decide_False // /jalr_link decide_False //.
     iApply "Hφ". iFrame. simplify_lmap_eq.
     iRegsMap "Hmap"; eauto; iFrame. }
   { simplify_lmap_eq. congruence. }
   { congruence. }
  Qed.

  (** A call ([rdst = cra]): the target is unsealed or a forward sentry, and
      the link is a return sentry whose kind restores the interrupt status of
      the caller, which the rule does not expose. *)
  Lemma wp_jalr_success_call E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w rsrc wsrc wcra dq :
    decodeInstrW w.(lw) = Jalr cra rsrc →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    jalr_target_ok cra rsrc wsrc.(lw) = true →
    rsrc ≠ cnull ->
    rsrc ≠ cra ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ rsrc ↦ᵣ wsrc
        ∗ ▷ cra ↦ᵣ wcra
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          ∃ mie,
          PC ↦ₚ lupdatePcPerm wsrc
          ∗ pc_a ↦ₐ{dq} w
          ∗ rsrc ↦ᵣ wsrc
          ∗ cra ↦ᵣ Sentry (ret_kind mie) pc_p pc_g pc_b pc_e pc_a' @@? pc_π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Htgt Hcnull Hcra ϕ) "(>HPC & >Hpc_a & >Hrsrc & >Hrdst) Hφ".
    iDestruct (map_of_regs_2 with "Hrsrc Hrdst") as "[Hmap %]".
    iApply (wp_Jalr with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { set_solver. }
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

   destruct Hspec as [ ? ? ? mie | ? Hlook Hfail | Hfail ]; subst.
   { destruct (decide (cra = cnull)) as [Hc|_]; first done.
     rewrite /jalr_link. destruct (decide (cra = cra)) as [_|Hc]; last done.
     iApply "Hφ". iExists mie. iFrame. simplify_lmap_eq.
     iRegsMap "Hmap"; eauto; iFrame. }
   { simplify_lmap_eq. congruence. }
   { congruence. }
  Qed.

  (** [jalr cra cra]: a call through [cra] itself. *)
  Lemma wp_jalr_success_call_same E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w wcra dq :
    decodeInstrW w.(lw) = Jalr cra cra →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    jalr_target_ok cra cra wcra.(lw) = true →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ cra ↦ᵣ wcra
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          ∃ mie,
          PC ↦ₚ lupdatePcPerm wcra
          ∗ pc_a ↦ₐ{dq} w
          ∗ cra ↦ᵣ Sentry (ret_kind mie) pc_p pc_g pc_b pc_e pc_a' @@? pc_π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Htgt ϕ) "(>HPC & >Hpc_a & >Hrdst) Hφ".
    iDestruct (map_of_regs_1 with "Hrdst") as "Hmap".
    iApply (wp_Jalr with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

   destruct Hspec as [ ? ? ? mie | ? Hlook Hfail | Hfail ]; subst.
   { destruct (decide (cra = cnull)) as [Hc|_]; first done.
     rewrite /jalr_link. destruct (decide (cra = cra)) as [_|Hc]; last done.
     iApply "Hφ". iExists mie. iFrame.
     simplify_lmap_eq.
     iRegsMap "Hmap"; eauto; iFrame. }
   { simplify_lmap_eq. congruence. }
   { congruence. }
  Qed.

  Lemma wp_jalr_success_cnull E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w rsrc wsrc dq :
    decodeInstrW w.(lw) = Jalr cnull rsrc →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    jalr_target_ok cnull rsrc wsrc.(lw) = true →
    rsrc ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ rsrc ↦ᵣ wsrc
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ lupdatePcPerm wsrc
          ∗ pc_a ↦ₐ{dq} w
          ∗ rsrc ↦ᵣ wsrc
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Htgt Hcnull ϕ) "(>HPC & >Hpc_a & >Hrsrc) Hφ".
    iDestruct (map_of_regs_1 with "Hrsrc") as "Hmap".
    iApply (wp_Jalr with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { set_solver. }
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

   destruct Hspec as [ ? ? ? mie | ? Hlook Hfail | Hfail ]; subst.
   { destruct (decide (cnull = cnull)) as [_|Hc]; last done.
     simplify_lmap_eq.
     iApply "Hφ". iFrame. iApply (regs_of_map_1 with "Hmap"). }
   { simplify_lmap_eq. congruence. }
   { congruence. }
  Qed.

  (** [jalr r r] with [r] neither [cnull] nor [cra]. *)
  Lemma wp_jalr_success_rdst E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w wdst rdst dq :
    decodeInstrW w.(lw) = Jalr rdst rdst →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    jalr_target_ok rdst rdst wdst.(lw) = true →
    rdst ≠ cnull ->
    rdst ≠ cra ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ rdst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ lupdatePcPerm wdst
          ∗ pc_a ↦ₐ{dq} w
          ∗ rdst ↦ᵣ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Htgt Hcnull Hcra ϕ) "(>HPC & >Hpc_a & >Hrdst) Hφ".
    iDestruct (map_of_regs_1 with "Hrdst") as "Hmap".
    iApply (wp_Jalr with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { set_solver. }
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

   destruct Hspec as [ ? ? ? mie | ? Hlook Hfail | Hfail ]; subst.
   { rewrite decide_False // /jalr_link decide_False //.
     iApply "Hφ". iFrame.
     simplify_lmap_eq.
     iRegsMap "Hmap"; eauto; iFrame. }
   { simplify_lmap_eq. congruence. }
   { congruence. }
  Qed.

  (** A target that fails the checks makes Jalr fail, before it writes the
      PC or the link register. *)
  Lemma wp_jalr_fail_target E pc_p pc_g pc_b pc_e pc_a pc_π w rsrc wsrc rdst wdst dq :
    decodeInstrW w.(lw) = Jalr rdst rsrc →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    jalr_target_ok rdst rsrc wsrc.(lw) = false →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ rsrc ↦ᵣ wsrc
        ∗ ▷ rdst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET FaultedV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ rsrc ↦ᵣ wsrc
          ∗ rdst ↦ᵣ wdst
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hfail ϕ) "(>HPC & >Hpc_a & >Hrsrc & >Hrdst) Hφ".
    iApply (wp_instr_faulted_2 with "[$HPC $Hrsrc $Hrdst $Hpc_a]"); [done | done | | ].
    - intros r sr m st s1 s2 Hr1 _.
      rewrite /exec /= /lookup_reg /=.
      destruct (decide (rsrc = cnull)) as [->|Hne]; first done.
      rewrite Hr1 /= jalr_target_checks.
      by rewrite jalr_target_ok_and_tag Hfail andb_false_r.
    - iNext. iIntros "(HPC & Hrsrc & Hrdst & Hpc_a)". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_jalr_fail_target_cnull E pc_p pc_g pc_b pc_e pc_a pc_π w rsrc wsrc dq :
    decodeInstrW w.(lw) = Jalr cnull rsrc →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    jalr_target_ok cnull rsrc wsrc.(lw) = false →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ rsrc ↦ᵣ wsrc
    }}}
      Instr Executable @ E
      {{{ RET FaultedV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ rsrc ↦ᵣ wsrc
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hfail ϕ) "(>HPC & >Hpc_a & >Hrsrc) Hφ".
    iApply (wp_instr_faulted_1 with "[$HPC $Hrsrc $Hpc_a]"); [done | done | | ].
    - intros rf sr m st s1 Hr1.
      rewrite /exec /= /lookup_reg /=.
      destruct (decide (rsrc = cnull)) as [->|Hne]; first done.
      rewrite Hr1 /= jalr_target_checks.
      by rewrite jalr_target_ok_and_tag Hfail andb_false_r.
    - iNext. iIntros "(HPC & Hrsrc & Hpc_a)". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_jalr_fail_target_same E pc_p pc_g pc_b pc_e pc_a pc_π w r wr dq :
    decodeInstrW w.(lw) = Jalr r r →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    jalr_target_ok r r wr.(lw) = false →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r ↦ᵣ wr
    }}}
      Instr Executable @ E
      {{{ RET FaultedV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r ↦ᵣ wr
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hfail ϕ) "(>HPC & >Hpc_a & >Hr) Hφ".
    iApply (wp_instr_faulted_1 with "[$HPC $Hr $Hpc_a]"); [done | done | | ].
    - intros rf sr m st s1 Hr1.
      rewrite /exec /= /lookup_reg /=.
      destruct (decide (r = cnull)) as [->|Hne]; first done.
      rewrite Hr1 /= jalr_target_checks.
      by rewrite jalr_target_ok_and_tag Hfail andb_false_r.
    - iNext. iIntros "(HPC & Hr & Hpc_a)". iApply "Hφ". iFrame.
  Qed.

End griotte_lang_rules.
