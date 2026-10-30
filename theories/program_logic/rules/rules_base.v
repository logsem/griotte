From iris.proofmode Require Import proofmode environments spec_patterns.
From iris.base_logic Require Export invariants na_invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.algebra Require Import frac auth gmap.
From griotte Require Export iris_extra stdpp_extra griotte_lang.
From griotte Require Export machine_base state_interp register_file machine_instructions.
From griotte Require Export resource_maps instr_operands.
From griotte Require Export named_props_extra.

(* --------------------------- LTAC DEFINITIONS ----------------------------------- *)

Ltac inv_base_step :=
  repeat match goal with
         | _ => progress simplify_map_eq/= (* simplify memory stuff *)
         | H : to_val _ = Some _ |- _ => apply of_to_val in H
         | H : _ = of_val ?v |- _ =>
           is_var v; destruct v; first[discriminate H|injection H as H]
         | H : griotte_lang.prim_step ?e _ _ _ _ _ |- _ =>
           try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable *)
           (*    and can thus better be avoided. *)
           let φ := fresh "φ" in
           inversion H as [| φ]; subst φ; clear H
         end.

Section griotte_lang_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {CL : CritLink Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : griotte_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
  Implicit Types w : LWord.
  Implicit Types reg : gmap RegName LWord.
  Implicit Types ms : gmap Addr LWord.

  Program Definition wp_lift_atomic_base_step_no_fork_determ {s E Φ} e1 :
    to_val e1 = None →
    (∀ (σ1:griotte_lang.state) ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E}=∗
     ∃ κ e2 (σ2:griotte_lang.state) efs, ⌜griotte_lang.prim_step e1 σ1 κ e2 σ2 efs⌝ ∗
      (▷ |==> (state_interp σ2 (S ns) κs nt ∗ from_option Φ False (to_val e2))))
      ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (?) "H". iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns κ κs nt)  "Hσ1 /=".
    iMod ("H" $! σ1 ns κ κs nt with "[Hσ1]") as "H"; auto.
    iDestruct "H" as (κ' e2 σ2 efs) "[H1 H2]".
    iModIntro. iSplit.
    - rewrite /base_reducible /=.
      iExists κ', e2, σ2, efs. auto.
    - iNext. iIntros (? ? ?) "H".
      iDestruct "H" as %Hs1.
      iDestruct "H1" as %Hs2.
      destruct (griotte_lang_determ _ _ _ _ _ _ _ _ _ _ Hs1 Hs2) as [Heq1 [Heq2 [Heq3 Heq4] ] ].
      subst. iMod "H2". iIntros "_".
      iModIntro. iFrame. inv Hs1; auto.
  Qed.

  (* ------------------------- the state interpretation --------------------------- *)

  (** The common start of every instruction rule: the logical PC and the
      instruction word give the physical ones, and the instruction is decoded
      from the physical copy. The continuation closes the state
      interpretation after the physical step. The system registers are one
      argument [lsreg] and one hypothesis ["Hsr"]; the continuation shows
      that the step keeps MIE and mtdc ([sys_kept]), so that it keeps the
      link. *)
  Lemma wp_instr_step E pc_p pc_g pc_b pc_e pc_a pc_π (w : LWord) dq (regs : LReg) Φ :
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    ▷ PC ↦ₚ (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) -∗
    ▷ pc_a ↦ₐ{dq} w -∗
    ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    ▷ (∀ (r : Reg) (sr : SReg) (m : Mem) (st : ShadowTbl) (lreg : LReg) (lsreg : LSys) (lmem : LMem)
       (R : RegState) (C : gmap Addr AddrClaim) (c : ConfFlag) (σ' : ExecConf),
       ("%Her" ∷ ⌜erasure R C (Cap pc_p pc_g pc_b pc_e pc_a, r, sr, m, st)
                    (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) lreg (ls_join lsreg) lmem⌝ ∗
        "%Hlregs" ∷ ⌜regs ⊆ lreg⌝ ∗
        "%Hregs" ∷ ⌜lregs_phys R regs r⌝ ∗
        "%Hpc_a" ∷ ⌜lmem !! pc_a = Some w⌝ ∗
        "%Hstep" ∷ ⌜exec (decodeInstrW w.(lw)) pc_p
                     (Cap pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) = (c, σ')⌝ ∗
        "HPCa" ∷ PC_auth (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) ∗
        "Hr" ∷ gen_heap_interp lreg ∗
        "Hsr" ∷ sys_interp lsreg ∗
        "Hm" ∷ gen_heap_interp lmem ∗
        "Hst" ∷ gen_heap_interp st ∗
        "HR" ∷ reg_auth R ∗
        "HC" ∷ addr_alloc_auth C ∗
        "HPC" ∷ PC ↦ₚ (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) ∗
        "Hpc_a" ∷ pc_a ↦ₐ{dq} w ∗
        "Hmap" ∷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y))
       ==∗
       ⌜sys_kept (Cap pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) σ'⌝ ∗
       cerise_state_interp σ' ∗ from_option Φ False (to_val (Instr c)))
    -∗ WP Instr Executable @ E {{ Φ }}.
  Proof.
    iIntros (Hvpc) "HPC Hpc_a Hmap Hcont".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "[Hσ Hlink] /=". destruct σ1 as [ [ [ [pc r] sr] m] st]; cbn.
    iDestruct (SI_open with "Hσ") as "Hσ". iNamed "Hσ".
    iMod "HPC". iMod "Hpc_a". iMod "Hmap".
    iDestruct (PC_agree with "HPCa HPC") as %->.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    iDestruct (gen_heap_valid with "Hm Hpc_a") as %Hpc_a.
    pose proof (erasure_regs_incl _ _ _ _ _ _ _ _ Her Hregs) as Hregs'.
    destruct (erasure_lookup_mem _ _ _ _ _ _ _ _ _ Her Hpc_a) as (pw & Hpw & Hok).
    pose proof (erasure_pc_correct _ _ _ _ _ _ _ Her Hvpc) as HPCr. cbn in HPCr. subst pc.
    iModIntro. iSplitR; first (by iPureIntro; apply normal_always_base_reducible).
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_". iSplitR; first done.
    eapply step_exec_inv in Hstep; eauto; cbn in Hstep.
    rewrite (mem_word_ok_decode _ _ _ _ Hok) in Hstep.
    iMod ("Hcont" with "[$HPCa $Hr $Hsr $Hm $Hst $HR $HC $HPC $Hpc_a $Hmap]")
      as "([%Hk1 %Hk2] & $ & $)"; first by iFrame "%".
    iModIntro. iApply (crit_link_stable with "Hlink"); done.
  Qed.

  (** The same for a step that may change MIE or mtdc: the continuation
      receives the link and gives back the link of the new state. *)
  Lemma wp_instr_step_link E pc_p pc_g pc_b pc_e pc_a pc_π (w : LWord) dq (regs : LReg) Φ :
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    ▷ PC ↦ₚ (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) -∗
    ▷ pc_a ↦ₐ{dq} w -∗
    ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    ▷ (∀ (r : Reg) (sr : SReg) (m : Mem) (st : ShadowTbl) (lreg : LReg) (lsreg : LSys) (lmem : LMem)
       (R : RegState) (C : gmap Addr AddrClaim) (c : ConfFlag) (σ' : ExecConf),
       ("%Her" ∷ ⌜erasure R C (Cap pc_p pc_g pc_b pc_e pc_a, r, sr, m, st)
                    (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) lreg (ls_join lsreg) lmem⌝ ∗
        "%Hlregs" ∷ ⌜regs ⊆ lreg⌝ ∗
        "%Hregs" ∷ ⌜lregs_phys R regs r⌝ ∗
        "%Hpc_a" ∷ ⌜lmem !! pc_a = Some w⌝ ∗
        "%Hstep" ∷ ⌜exec (decodeInstrW w.(lw)) pc_p
                     (Cap pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) = (c, σ')⌝ ∗
        "HPCa" ∷ PC_auth (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) ∗
        "Hr" ∷ gen_heap_interp lreg ∗
        "Hsr" ∷ sys_interp lsreg ∗
        "Hm" ∷ gen_heap_interp lmem ∗
        "Hst" ∷ gen_heap_interp st ∗
        "HR" ∷ reg_auth R ∗
        "HC" ∷ addr_alloc_auth C ∗
        "Hlink" ∷ crit_link (Cap pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) ∗
        "HPC" ∷ PC ↦ₚ (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) ∗
        "Hpc_a" ∷ pc_a ↦ₐ{dq} w ∗
        "Hmap" ∷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y))
       ==∗
       (cerise_state_interp σ' ∗ crit_link σ') ∗ from_option Φ False (to_val (Instr c)))
    -∗ WP Instr Executable @ E {{ Φ }}.
  Proof.
    iIntros (Hvpc) "HPC Hpc_a Hmap Hcont".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "[Hσ Hlink] /=". destruct σ1 as [ [ [ [pc r] sr] m] st]; cbn.
    iDestruct (SI_open with "Hσ") as "Hσ". iNamed "Hσ".
    iMod "HPC". iMod "Hpc_a". iMod "Hmap".
    iDestruct (PC_agree with "HPCa HPC") as %->.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    iDestruct (gen_heap_valid with "Hm Hpc_a") as %Hpc_a.
    pose proof (erasure_regs_incl _ _ _ _ _ _ _ _ Her Hregs) as Hregs'.
    destruct (erasure_lookup_mem _ _ _ _ _ _ _ _ _ Her Hpc_a) as (pw & Hpw & Hok).
    pose proof (erasure_pc_correct _ _ _ _ _ _ _ Her Hvpc) as HPCr. cbn in HPCr. subst pc.
    iModIntro. iSplitR; first (by iPureIntro; apply normal_always_base_reducible).
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_". iSplitR; first done.
    eapply step_exec_inv in Hstep; eauto; cbn in Hstep.
    rewrite (mem_word_ok_decode _ _ _ _ Hok) in Hstep.
    iMod ("Hcont" with "[$HPCa $Hr $Hsr $Hm $Hst $HR $HC $Hlink $HPC $Hpc_a $Hmap]")
      as "[ [$ $] $]"; first by iFrame "%".
    done.
  Qed.

  (** Closes a step that keeps MIE and mtdc, under [wp_instr_step_link]. *)
  Lemma instr_close_link_kept σ σ' (X : iProp Σ) :
    crit_link σ -∗
    (|==> ⌜sys_kept σ σ'⌝ ∗ cerise_state_interp σ' ∗ X) -∗
    |==> (cerise_state_interp σ' ∗ crit_link σ') ∗ X.
  Proof.
    iIntros "Hlink >([%Hk1 %Hk2] & $ & $)". iModIntro.
    iApply (crit_link_stable with "Hlink"); done.
  Qed.

  (** At the core link, any closing closes a step that may change MIE or
      mtdc. *)
  Lemma instr_close_core σ1 σ' (X : iProp Σ) :
    (|==> ⌜sys_kept σ1 σ'⌝ ∗ cerise_state_interp σ' ∗ X) -∗
    |==> (cerise_state_interp σ' ∗ @crit_link Σ link_core σ') ∗ X.
  Proof. iIntros ">(_ & $ & $)". done. Qed.

  (** Closes a step that may change MIE or mtdc from [σ0], through a
      closing from [σ1] (the state after the write): the link is
      transferred with [T1] for [T2], which the postcondition receives. *)
  Lemma instr_close_link_transfer (P : ExecConf → ExecConf → Prop) (T1 T2 : iProp Σ)
      σ0 σ1 σ' (Ψ : griotte_lang.val → iProp Σ) (c : ConfFlag) :
    link_transfer P T1 T2 →
    (sys_kept σ1 σ' → P σ0 σ') →
    crit_link σ0 -∗ T1 -∗
    (|==> ⌜sys_kept σ1 σ'⌝ ∗ cerise_state_interp σ' ∗
          from_option (λ v, T2 -∗ Ψ v) False (to_val (Instr c))) -∗
    |==> (cerise_state_interp σ' ∗ crit_link σ') ∗ from_option Ψ False (to_val (Instr c)).
  Proof.
    iIntros (Htr HP) "Hlink HT >(%Hk & $ & HΨ)".
    iMod (Htr _ σ' (HP Hk) with "[$Hlink $HT]") as "[$ HT]". iModIntro.
    destruct (to_val (Instr c)); cbn; [by iApply "HΨ" | done].
  Qed.

  (** A closing that keeps MIE and mtdc from a state that keeps them. *)
  Lemma instr_close_kept_trans σ0 σ1 σ' (X : iProp Σ) :
    sys_kept σ0 σ1 →
    (|==> ⌜sys_kept σ1 σ'⌝ ∗ X) -∗
    |==> ⌜sys_kept σ0 σ'⌝ ∗ X.
  Proof.
    iIntros (Hk) ">[%Hk' $]". iPureIntro. by eapply sys_kept_trans.
  Qed.

  (* ----------------------------------- FAIL RULES ---------------------------------- *)
  (* Bind Scope expr_scope with language.expr griotte_lang. *)

  Lemma wp_notCorrectPC:
    forall E (w : LWord),
      ~ isCorrectPC w.(lw) ->
      {{{ PC ↦ₚ w }}}
         Instr Executable @ E
        {{{ RET FaultedV; PC ↦ₚ w }}}.
  Proof.
    intros *. intros Hnpc.
    iIntros (ϕ) "HPC Hϕ".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 nt l1 l2 ns) "[Hσ1 Hlink] /="; destruct σ1 as [ [ [ [pc r] sr] m] st]; simpl.
    iDestruct (SI_open with "Hσ1") as "Hσ1". iNamed "Hσ1".
    iDestruct (PC_agree with "HPCa HPC") as %->.
    pose proof (erasure_pc_not_correct _ _ _ _ _ _ _ Her Hnpc) as Hnpc'. cbn in Hnpc'.
    iApply fupd_frame_l.
    iSplit; first (by iPureIntro; apply normal_always_base_reducible).
    iModIntro. iIntros (e1 σ2 efs Hstep).
    apply prim_step_exec_inv in Hstep as (-> & -> & (c & -> & Hstep)).
    eapply step_fail_inv in Hstep as [-> ->]; eauto.
    iNext. iIntros "_".
    iModIntro. iSplitR; auto. iSplitR "Hϕ HPC"; last by iApply "Hϕ".
    iFrame "Hlink". iApply (SI_close _ _ _ _ _ _ _ Her with "HPCa Hr Hsr Hm Hst HR HC").
  Qed.

  Lemma wp_notCorrectPC_tag E (w : LWord) :
    get_tag w.(lw) = false →
    {{{ PC ↦ₚ w }}}
      Instr Executable @ E
    {{{ RET FaultedV; PC ↦ₚ w }}}.
  Proof.
    iIntros (Htag φ) "HPC Hφ".
    iApply (wp_notCorrectPC with "HPC").
    { by apply not_isCorrectPC_untagged. }
    iNext. iIntros "HPC". by iApply "Hφ".
  Qed.

  (* ----------------------------------- ATOMIC RULES -------------------------------- *)

  Lemma wp_halt E pc_p pc_g pc_b pc_e pc_a pc_π w dq :
    decodeInstrW w.(lw) = Halt →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →

    {{{ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ pc_a ↦ₐ{dq} w }}}
      Instr Executable @ E
    {{{ RET HaltedV; PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ pc_a ↦ₐ{dq} w }}}.
  Proof.
    intros Hinstr Hvpc.
    iIntros (φ) "[Hpc Hpca] Hφ".
    iApply (wp_instr_step _ _ _ _ _ _ _ _ _ ∅ with "Hpc Hpca [] "); eauto.
    iNext; iIntros (r sr m st lreg lsreg lmem R C c σ') "@".
    rewrite Hinstr /exec /= in Hstep. simplify_eq.
    iModIntro. iSplit; first (iPureIntro; apply sys_kept_refl).
    iSplitR "Hφ HPC Hpc_a"; last (cbn; iApply "Hφ"; iFrame).
    iApply (SI_close _ _ _ _ _ _ _ Her with "HPCa Hr Hsr Hm Hst HR HC").
  Qed.

  Lemma wp_fail E pc_p pc_g pc_b pc_e pc_a pc_π w dq :
    decodeInstrW w.(lw) = Fail →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →

    {{{ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ pc_a ↦ₐ{dq} w }}}
      Instr Executable @ E
    {{{ RET FaultedV; PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ pc_a ↦ₐ{dq} w }}}.
  Proof.
    intros Hinstr Hvpc.
    iIntros (φ) "[Hpc Hpca] Hφ".
    iApply (wp_instr_step _ _ _ _ _ _ _ _ _ ∅ with "Hpc Hpca [] "); eauto.
    iNext; iIntros (r sr m st lreg lsreg lmem R C c σ') "@".
    rewrite Hinstr /exec /= in Hstep. simplify_eq.
    iModIntro. iSplit; first (iPureIntro; apply sys_kept_refl).
    iSplitR "Hφ HPC Hpc_a"; last (cbn; iApply "Hφ"; iFrame).
    iApply (SI_close _ _ _ _ _ _ _ Her with "HPCa Hr Hsr Hm Hst HR HC").
  Qed.

  (* ----------------------------------- PURE RULES ---------------------------------- *)

  #[local] Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
  #[local] Ltac solve_exec_puredet := simpl; intros; by inv_base_step.
  #[local] Ltac solve_exec_pure := intros ?; apply nsteps_once, pure_base_step_pure_step;
                                constructor; [solve_exec_safe|]; intros;
                                (match goal with
                                | H : base_step _ _ _ _ _ _ |- _ => inversion H end).

  #[global] Instance pure_seq_halted :
    PureExec True 1 (Seq (Instr Halted)) (Instr Halted).
  Proof. by solve_exec_pure. Qed.

  #[global] Instance pure_seq_done :
    PureExec True 1 (Seq (Instr NextI)) Exec.
  Proof. by solve_exec_pure. Qed.

  (** The register [cnull] holds the null word: read from the state
      interpretation, in front of any expression that is not a value. *)
  Lemma wp_reg_cnull_lnull E e Φ r w :
    to_val e = None →
    r ↦ᵣ w -∗
    (⌜r = cnull → w = lnull⌝ -∗ r ↦ᵣ w -∗ WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros (He) "Hr' HΦ".
    rewrite wp_unfold /wp_pre He.
    iIntros (σ1 ns κ κs nt) "[Hσ Hlink] /=".
    iDestruct (SI_open with "Hσ") as "Hσ". iNamed "Hσ".
    iDestruct (gen_heap_valid with "Hr Hr'") as %Hlookup.
    iSpecialize ("HΦ" with "[%] Hr'").
    { intros ->. by eapply er_cnull. }
    iApply ("HΦ" $! σ1 ns κ κs nt). iFrame "Hlink".
    iApply (SI_close _ _ _ _ _ _ _ Her with "HPCa Hr Hsr Hm Hst HR HC").
  Qed.

End griotte_lang_rules.

Section instruction_closing.
  Context `{MP : MachineParameters} `{ceriseg : ceriseG Σ}.

  (** The closing lemmas below conclude that the step keeps MIE and mtdc
      ([sys_kept]): they do not change the system registers. *)

  (** Closes a failed instruction: the state is unchanged. *)
  Lemma instr_close_fail pc (r : Reg) sr m st lpc (lreg : LReg) lsreg lmem R C
      (regs : LReg) (Φ : griotte_lang.val → iProp Σ) :
    erasure R C (pc, r, sr, m, st) lpc lreg (ls_join lsreg) lmem →
    PC_auth lpc -∗
    gen_heap_interp lreg -∗ sys_interp lsreg -∗ gen_heap_interp lmem -∗
    gen_heap_interp st -∗ reg_auth R -∗ addr_alloc_auth C -∗
    PC ↦ₚ lpc -∗
    ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    (PC ↦ₚ lpc -∗ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗ Φ FaultedV) ==∗
    ⌜sys_kept (pc, r, sr, m, st) (pc, r, sr, m, st)⌝ ∗
    cerise_state_interp (pc, r, sr, m, st) ∗ from_option Φ False (to_val (Instr Faulted)).
  Proof.
    iIntros (Her) "HPCa Hr Hsr Hm Hst HR HC HPC Hmap Hφ". iModIntro.
    iSplit; first (iPureIntro; apply sys_kept_refl).
    iSplitR "Hφ HPC Hmap"; last by iApply ("Hφ" with "HPC").
    iApply (SI_close _ _ _ _ _ _ _ Her with "HPCa Hr Hsr Hm Hst HR HC").
  Qed.

  (** Closes an instruction that only moves the PC by [n], as the physical
      [advancePC φ n]. The spec [P] holds of the new PC on success, and of
      the old one on failure. *)
  Lemma instr_close_pc_update pc (r : Reg) sr m st lpc (lreg : LReg) lsreg lmem R C
      (regs : LReg) n c σ' (Φ : griotte_lang.val → iProp Σ)
      (P : LWord → griotte_lang.val → Prop) :
    erasure R C (pc, r, sr, m, st) lpc lreg (ls_join lsreg) lmem →
    (match advancePC (pc, r, sr, m, st) n with
     | Some conf => conf | None => (Faulted, (pc, r, sr, m, st)) end) = (c, σ') →
    (∀ lpc', incrementPC_gen lpc n = Some lpc' → P lpc' NextIV) →
    (incrementPC_gen lpc n = None → P lpc FaultedV) →
    PC_auth lpc -∗
    gen_heap_interp lreg -∗ sys_interp lsreg -∗ gen_heap_interp lmem -∗
    gen_heap_interp st -∗ reg_auth R -∗ addr_alloc_auth C -∗
    PC ↦ₚ lpc -∗
    ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    (∀ lpc' retv, ⌜P lpc' retv⌝ -∗ PC ↦ₚ lpc' -∗
       ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗ Φ retv) ==∗
    ⌜sys_kept (pc, r, sr, m, st) σ'⌝ ∗
    cerise_state_interp σ' ∗ from_option Φ False (to_val (Instr c)).
  Proof.
    iIntros (Her Hstep HPs HPf) "HPCa Hr Hsr Hm Hst HR HC HPC Hmap Hφ".
    destruct (incrementPC_gen lpc n) as [lpc'|] eqn:Hi.
    - destruct (erasure_incrementPC_gen _ _ _ _ _ _ _ _ _ _ _ _ _ Her Hi) as (pc' & Hu & Her2).
      rewrite Hu in Hstep. simplify_eq.
      iMod (PC_update _ _ lpc' with "HPCa HPC") as "[HPCa HPC]".
      iModIntro. iSplit; first (iPureIntro; by apply sys_kept_same_sreg).
      iSplitR "Hφ HPC Hmap".
      + iApply (SI_close _ _ _ _ _ _ _ Her2 with "HPCa Hr Hsr Hm Hst HR HC").
      + iApply ("Hφ" with "[%] HPC Hmap"). by apply HPs.
    - rewrite (erasure_incrementPC_fail _ _ _ _ _ _ _ _ _ _ _ _ Her Hi) in Hstep.
      simplify_eq. iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); first done.
      iIntros "HPC Hmap". iApply ("Hφ" with "[%] HPC Hmap"). by apply HPf.
  Qed.

  (** Writes the logical register [dst], owned unless it is [cnull]. *)
  Lemma lreg_update (lreg regs : LReg) dst v :
    (dst = cnull ∨ dst ∈ dom regs) →
    gen_heap_interp lreg -∗ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ==∗
    gen_heap_interp (<[dst := v]ₗ> lreg) ∗ [∗ map] k↦y ∈ <[dst := v]ₗ> regs, k ↦ᵣ y.
  Proof.
    iIntros (Hdst) "Hr Hmap".
    destruct (decide (dst = cnull)) as [->|Hne].
    { rewrite !linsert_reg_cnull. by iFrame. }
    destruct Hdst as [->|Hdst]; first done.
    rewrite !linsert_reg_not_cnull //.
    iApply (gen_heap_update_inSepM with "Hr Hmap"). by apply elem_of_dom.
  Qed.

  (** Closes an instruction that writes one register then increments the PC,
      as the physical [nextPC (update_reg φ dst v)]. The spec [P] holds of
      the new PC and owned registers on success, and of the old ones on
      failure. *)
  Lemma instr_close_reg_update pc (r : Reg) sr m st lpc (lreg : LReg) lsreg lmem R C
      (regs : LReg) dst (v : LWord) (w : Word) c σ' (Φ : griotte_lang.val → iProp Σ)
      (P : LWord → LReg → griotte_lang.val → Prop) :
    erasure R C (pc, r, sr, m, st) lpc lreg (ls_join lsreg) lmem →
    regs ⊆ lreg →
    dst = cnull ∨ dst ∈ dom regs →
    reg_word_ok R C v →
    (match nextPC (update_reg (pc, r, sr, m, st) dst w) with
     | Some conf => conf | None => (Faulted, (pc, r, sr, m, st)) end) = (c, σ') →
    reg_phys R v w →
    (∀ lpc', incrementPC lpc = Some lpc' → P lpc' (<[dst := v]ₗ> regs) NextIV) →
    (incrementPC lpc = None → P lpc regs FaultedV) →
    PC_auth lpc -∗
    gen_heap_interp lreg -∗ sys_interp lsreg -∗ gen_heap_interp lmem -∗
    gen_heap_interp st -∗ reg_auth R -∗ addr_alloc_auth C -∗
    PC ↦ₚ lpc -∗
    ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    (∀ lpc' regs' retv, ⌜P lpc' regs' retv⌝ -∗ PC ↦ₚ lpc' -∗
       ([∗ map] k↦y ∈ regs', k ↦ᵣ y) -∗ Φ retv) ==∗
    ⌜sys_kept (pc, r, sr, m, st) σ'⌝ ∗
    cerise_state_interp σ' ∗ from_option Φ False (to_val (Instr c)).
  Proof.
    iIntros (Her Hlregs Hdst Hok Hstep Hw HPs HPf) "HPCa Hr Hsr Hm Hst HR HC HPC Hmap Hφ".
    pose proof (erasure_linsert_reg _ _ _ _ _ _ _ _ _ _ _ dst v w Her Hok Hw) as Her1.
    rewrite /update_reg /= in Hstep.
    destruct (incrementPC lpc) as [lpc'|] eqn:Hi.
    - destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hi) as (pc' & Hu & Her2).
      rewrite Hu in Hstep. simplify_eq.
      iMod (lreg_update _ _ dst v Hdst with "Hr Hmap") as "[Hr Hmap]".
      iMod (PC_update _ _ lpc' with "HPCa HPC") as "[HPCa HPC]".
      iModIntro. iSplit; first (iPureIntro; by apply sys_kept_same_sreg).
      iSplitR "Hφ HPC Hmap".
      + iApply (SI_close _ _ _ _ _ _ _ Her2 with "HPCa Hr Hsr Hm Hst HR HC").
      + iApply ("Hφ" with "[%] HPC Hmap"). by apply HPs.
    - pose proof (erasure_incrementPC_fail _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hi) as Hfail.
      rewrite /nextPC Hfail in Hstep.
      simplify_eq. iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); first done.
      iIntros "HPC Hmap". iApply ("Hφ" with "[%] HPC Hmap"). by apply HPf.
  Qed.

  (** Closes an instruction that sets the PC to [lpc'] and writes one
      register, as the physical [update_reg (update_pcc φ pc') dst w]. *)
  Lemma instr_close_reg_set_pc pc (r : Reg) sr m st lpc (lreg : LReg) lsreg lmem R C
      (regs : LReg) dst (v : LWord) (w : Word) (lpc' : LWord) (pc' : Word)
      (Φ : griotte_lang.val → iProp Σ) :
    erasure R C (pc, r, sr, m, st) lpc lreg (ls_join lsreg) lmem →
    dst = cnull ∨ dst ∈ dom regs →
    reg_word_ok R C v →
    reg_phys R v w →
    reg_word_ok R C lpc' →
    reg_phys R lpc' pc' →
    pc_ok lpc'.(lw) →
    PC_auth lpc -∗
    gen_heap_interp lreg -∗ sys_interp lsreg -∗ gen_heap_interp lmem -∗
    gen_heap_interp st -∗ reg_auth R -∗ addr_alloc_auth C -∗
    PC ↦ₚ lpc -∗
    ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    (PC ↦ₚ lpc' -∗ ([∗ map] k↦y ∈ <[dst := v]ₗ> regs, k ↦ᵣ y) -∗ Φ NextIV) ==∗
    ⌜sys_kept (pc, r, sr, m, st) (update_reg (update_pcc (pc, r, sr, m, st) pc') dst w)⌝ ∗
    cerise_state_interp (update_reg (update_pcc (pc, r, sr, m, st) pc') dst w) ∗
    from_option Φ False (to_val (Instr NextI)).
  Proof.
    iIntros (Her Hdst Hok Hw Hokpc Hwpc Hpcok)
      "HPCa Hr Hsr Hm Hst HR HC HPC Hmap Hφ".
    pose proof (erasure_linsert_reg _ _ _ _ _ _ _ _ _ _ _ dst v w Her Hok Hw) as Her1.
    pose proof (erasure_set_pc _ _ _ _ _ _ _ _ _ _ _ lpc' pc' Her1 Hokpc Hwpc Hpcok) as Her2.
    iMod (lreg_update _ _ dst v Hdst with "Hr Hmap") as "[Hr Hmap]".
    iMod (PC_update _ _ lpc' with "HPCa HPC") as "[HPCa HPC]".
    iModIntro. iSplit; first (iPureIntro; by apply sys_kept_same_sreg).
    iSplitR "Hφ HPC Hmap".
    - iApply (SI_close _ _ _ _ _ _ _ Her2 with "HPCa Hr Hsr Hm Hst HR HC").
    - iApply ("Hφ" with "HPC Hmap").
  Qed.

  (** Closes a step that only sets the PC. *)
  Lemma instr_close_set_pc pc (r : Reg) sr m st lpc (lreg : LReg) lsreg lmem R C
      (regs : LReg) (lpc' : LWord) (pc' : Word)
      (Φ : griotte_lang.val → iProp Σ) :
    erasure R C (pc, r, sr, m, st) lpc lreg (ls_join lsreg) lmem →
    reg_word_ok R C lpc' →
    reg_phys R lpc' pc' →
    pc_ok lpc'.(lw) →
    PC_auth lpc -∗
    gen_heap_interp lreg -∗ sys_interp lsreg -∗ gen_heap_interp lmem -∗
    gen_heap_interp st -∗ reg_auth R -∗ addr_alloc_auth C -∗
    PC ↦ₚ lpc -∗
    ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    (PC ↦ₚ lpc' -∗ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗ Φ NextIV) ==∗
    ⌜sys_kept (pc, r, sr, m, st) (update_pcc (pc, r, sr, m, st) pc')⌝ ∗
    cerise_state_interp (update_pcc (pc, r, sr, m, st) pc') ∗
    from_option Φ False (to_val (Instr NextI)).
  Proof.
    iIntros (Her Hokpc Hwpc Hpcok) "HPCa Hr Hsr Hm Hst HR HC HPC Hmap Hφ".
    pose proof (erasure_set_pc _ _ _ _ _ _ _ _ _ _ _ lpc' pc' Her Hokpc Hwpc Hpcok) as Her'.
    iMod (PC_update _ _ lpc' with "HPCa HPC") as "[HPCa HPC]".
    iModIntro. iSplit; first (iPureIntro; by apply sys_kept_same_sreg).
    iSplitR "Hφ HPC Hmap".
    - iApply (SI_close _ _ _ _ _ _ _ Her' with "HPCa Hr Hsr Hm Hst HR HC").
    - iApply ("Hφ" with "HPC Hmap").
  Qed.

End instruction_closing.

(** Closes the failing branch of a general rule with [instr_close_fail], then
    the rule's continuation ["Hφ"], and leaves the spec as a pure goal. A
    tactic rather than a lemma: it passes the state hypotheses that
    [wp_instr_step] (and the lifting of the Load and Store rules) introduce
    under fixed names. *)
Ltac instr_fail_close :=
  try iApply bupd_fupd;
  try iApply (instr_close_link_kept with "Hlink");
  iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); [done|];
  iIntros "HPC Hmap"; iApply "Hφ"; iFrame; iPureIntro.

(** The same, after substituting the faulted configuration given by
    [Hstep : (Faulted, φ) = (c, σ')]. *)
Ltac instr_fail Hstep :=
  first [injection Hstep as <- <- | simplify_eq]; instr_fail_close.

(** Pure side conditions of the map-form rules ([wp_Get_next], …) applied to
    register maps built by [map_of_regs_k]: a small closed set of goals
    (instruction decoding, register lookups and domains, the PC increment).
    A tactic because the goals vary with the instruction class. *)
Ltac solve_next_side :=
  first [ done
        | by apply incrementPC_add
        | by rewrite /regs_of /operands_of /regs_of_argument ?dom_insert_L ?dom_singleton_L; set_solver+
        | by simplify_map_eq
        | by apply llookup_reg_cnull
        | by rewrite /lz_of_argument /=; simplify_map_eq ].

Section instruction_outcomes.

  Context `{MP : MachineParameters} `{ceriseg : ceriseG Σ} {CL : CritLink Σ}.

  (* A failed instruction rolls back every tentative write. The premise is
     about all physical register files that include the erased owned
     registers, so no absent register or memory address can be mistaken for
     evidence of runtime failure. *)
  #[local] Lemma wp_instr_faulted_map E pc_p pc_g pc_b pc_e pc_a pc_π (w : LWord) i (regs : LReg) dq :
    decodeInstrW w.(lw) = i →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (∀ R r sr m st, lregs_phys R regs r →
       exec i pc_p (Cap pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) =
         (Faulted, (Cap pc_p pc_g pc_b pc_e pc_a, r, sr, m, st))) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FaultedV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Hfailed φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
    iNext; iIntros (r sr m st lreg lsreg lmem R C c σ') "@".
    rewrite Hinstr (Hfailed R r sr m st Hregs) in Hstep. simplify_eq.
    iModIntro. iSplit; first (iPureIntro; apply sys_kept_refl).
    iSplitR "Hφ HPC Hpc_a Hmap"; last (cbn; iApply "Hφ"; iFrame).
    iApply (SI_close _ _ _ _ _ _ _ Her with "HPCa Hr Hsr Hm Hst HR HC").
  Qed.

  (* Failure with PC alone; all resources are returned unchanged. *)
  Lemma wp_instr_faulted_0 E pc_p pc_g pc_b pc_e pc_a pc_π w i dq :
    decodeInstrW w.(lw) = i →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (∀ r sr m st,
       exec i pc_p (Cap pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) =
         (Faulted, (Cap pc_p pc_g pc_b pc_e pc_a, r, sr, m, st))) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ{dq} w }}}
      Instr Executable @ E
    {{{ RET FaultedV; PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ pc_a ↦ₐ{dq} w }}}.
  Proof.
    iIntros (Hinstr Hvpc Hfailed φ) "(>HPC & >Hmem) Hφ".
    iApply (wp_instr_faulted_map _ _ _ _ _ _ _ _ _ ∅ with "[$HPC $Hmem]").
    - exact Hinstr.
    - exact Hvpc.
    - intros R r sr m st _. apply Hfailed.
    - by rewrite big_sepM_empty.
    - iNext. iIntros "(HPC & Hmem & _)".
      iApply "Hφ". iFrame.
  Qed.

  (* Failure with PC and 1 explicit register; all resources are returned unchanged. *)
  Lemma wp_instr_faulted_1 E pc_p pc_g pc_b pc_e pc_a pc_π w i r1 w1 dq :
    decodeInstrW w.(lw) = i →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (∀ r sr m st s1, r !! r1 = Some (and_tag s1 w1.(lw)) →
       exec i pc_p (Cap pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) =
         (Faulted, (Cap pc_p pc_g pc_b pc_e pc_a, r, sr, m, st))) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ r1 ↦ᵣ w1 ∗ ▷ pc_a ↦ₐ{dq} w }}}
      Instr Executable @ E
    {{{ RET FaultedV; PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ r1 ↦ᵣ w1 ∗ pc_a ↦ₐ{dq} w }}}.
  Proof.
    iIntros (Hinstr Hvpc Hfailed φ) "(>HPC & >Hr1 & >Hmem) Hφ".
    iDestruct (map_of_regs_1 with "Hr1") as "Hmap".
    iApply (wp_instr_faulted_map _ _ _ _ _ _ _ _ _ (<[r1 := w1]> ∅)
      with "[$HPC $Hmap $Hmem]").
    - exact Hinstr.
    - exact Hvpc.
    - intros R r sr m st Hincl.
      destruct (lregs_phys_lookup _ _ r r1 w1 Hincl) as [s1 Hl1]; first by simplify_map_eq.
      by eapply Hfailed.
    - iNext. iIntros "(HPC & Hmem & Hmap)".
      iDestruct (regs_of_map_1 with "Hmap") as "Hr1"; eauto.
      iApply "Hφ". iFrame.
  Qed.

  (* Failure with PC and 2 explicit registers; all resources are returned unchanged. *)
  Lemma wp_instr_faulted_2 E pc_p pc_g pc_b pc_e pc_a pc_π w i r1 w1 r2 w2 dq :
    decodeInstrW w.(lw) = i →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (∀ r sr m st s1 s2, r !! r1 = Some (and_tag s1 w1.(lw)) →
       r !! r2 = Some (and_tag s2 w2.(lw)) →
       exec i pc_p (Cap pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) =
         (Faulted, (Cap pc_p pc_g pc_b pc_e pc_a, r, sr, m, st))) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ r1 ↦ᵣ w1 ∗ ▷ r2 ↦ᵣ w2 ∗ ▷ pc_a ↦ₐ{dq} w }}}
      Instr Executable @ E
    {{{ RET FaultedV; PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ r1 ↦ᵣ w1 ∗ r2 ↦ᵣ w2 ∗ pc_a ↦ₐ{dq} w }}}.
  Proof.
    iIntros (Hinstr Hvpc Hfailed φ) "(>HPC & >Hr1 & >Hr2 & >Hmem) Hφ".
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %Hne]".
    iApply (wp_instr_faulted_map _ _ _ _ _ _ _ _ _ (<[r1 := w1]> (<[r2 := w2]> ∅))
      with "[$HPC $Hmap $Hmem]").
    - exact Hinstr.
    - exact Hvpc.
    - intros R r sr m st Hincl.
      destruct (lregs_phys_lookup _ _ r r1 w1 Hincl) as [s1 Hl1]; first by simplify_map_eq.
      destruct (lregs_phys_lookup _ _ r r2 w2 Hincl) as [s2 Hl2]; first by simplify_map_eq.
      by eapply Hfailed.
    - iNext. iIntros "(HPC & Hmem & Hmap)".
      iDestruct (regs_of_map_2 with "Hmap") as "(Hr1 & Hr2)"; eauto.
      iApply "Hφ". iFrame.
  Qed.

  (* Failure with PC and 3 explicit registers; all resources are returned unchanged. *)
  Lemma wp_instr_faulted_3 E pc_p pc_g pc_b pc_e pc_a pc_π w i r1 w1 r2 w2 r3 w3 dq :
    decodeInstrW w.(lw) = i →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (∀ r sr m st s1 s2 s3, r !! r1 = Some (and_tag s1 w1.(lw)) →
       r !! r2 = Some (and_tag s2 w2.(lw)) →
       r !! r3 = Some (and_tag s3 w3.(lw)) →
       exec i pc_p (Cap pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) =
         (Faulted, (Cap pc_p pc_g pc_b pc_e pc_a, r, sr, m, st))) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
          ▷ r1 ↦ᵣ w1 ∗
          ▷ r2 ↦ᵣ w2 ∗
          ▷ r3 ↦ᵣ w3 ∗
          ▷ pc_a ↦ₐ{dq} w }}}
      Instr Executable @ E
    {{{ RET FaultedV; PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
          r1 ↦ᵣ w1 ∗
          r2 ↦ᵣ w2 ∗
          r3 ↦ᵣ w3 ∗
          pc_a ↦ₐ{dq} w }}}.
  Proof.
    iIntros (Hinstr Hvpc Hfailed φ) "(>HPC & >Hr1 & >Hr2 & >Hr3 & >Hmem) Hφ".
    iDestruct (map_of_regs_3 with "Hr1 Hr2 Hr3") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (wp_instr_faulted_map _ _ _ _ _ _ _ _ _
      (<[r1 := w1]> (<[r2 := w2]> (<[r3 := w3]> ∅)))
      with "[$HPC $Hmap $Hmem]").
    - exact Hinstr.
    - exact Hvpc.
    - intros R r sr m st Hincl.
      destruct (lregs_phys_lookup _ _ r r1 w1 Hincl) as [s1 Hl1]; first by simplify_map_eq.
      destruct (lregs_phys_lookup _ _ r r2 w2 Hincl) as [s2 Hl2]; first by simplify_map_eq.
      destruct (lregs_phys_lookup _ _ r r3 w3 Hincl) as [s3 Hl3]; first by simplify_map_eq.
      by eapply Hfailed.
    - iNext. iIntros "(HPC & Hmem & Hmap)".
      iDestruct (regs_of_map_3 with "Hmap") as "(Hr1 & Hr2 & Hr3)"; eauto.
      iApply "Hφ". iFrame.
  Qed.
End instruction_outcomes.
