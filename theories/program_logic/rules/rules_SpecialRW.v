From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.

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
  Implicit Types sreg : gmap SRegName LWord.
  Implicit Types ms : gmap Addr LWord.

  (** The system registers after [SpecialRW _ sr src]: the source [inr cnull]
      does not write [sr], any other source writes its legalised value. *)
  Definition specialrw_sregs (regs : LReg) (sregs : LSReg) (sr : SRegName)
      (src : Z + RegName) : option LSReg :=
    match src with
    | inr r =>
        if decide (r = cnull) then Some sregs
        else v ← regs !!ₗ r; Some (<[sr := llegalise sr v]> sregs)
    | inl z => Some (<[sr := llegalise sr (WInt z)]> sregs)
    end.

  (** The registers after [SpecialRW dst _ _] with old value [vold]: the
      destination [cnull] drops it. *)
  Definition specialrw_regs (regs : LReg) (dst : RegName) (vold : LWord) : LReg :=
    if decide (dst = cnull) then regs else <[dst := vold]> regs.

  Lemma specialrw_regs_cnull regs vold : specialrw_regs regs cnull vold = regs.
  Proof. rewrite /specialrw_regs. by case_decide. Qed.

  Lemma specialrw_regs_ne regs dst vold :
    dst ≠ cnull → specialrw_regs regs dst vold = <[dst := vold]> regs.
  Proof. rewrite /specialrw_regs. by case_decide. Qed.

  Inductive SpecialRW_failure (lpc : LWord) : Prop :=
  | SpecialRW_fail_nonxsr p g b e a π :
      lpc = Cap p g b e a @@? π →
      has_sreg_access p = false →
      SpecialRW_failure lpc
  | SpecialRW_fail_incrPC :
      incrementPC lpc = None →
      SpecialRW_failure lpc.

  Inductive SpecialRW_spec
    (lpc : LWord) (regs : LReg) (sregs : LSReg) (dst : RegName) (sr : SRegName)
    (src : Z + RegName) (lpc' : LWord) (regs' : LReg) (sregs' : LSReg)
    : griotte_lang.val → Prop :=
  | SpecialRW_spec_success p g b e a π vold :
      lpc = Cap p g b e a @@? π →
      has_sreg_access p = true →
      sregs !! sr = Some vold →
      specialrw_sregs regs sregs sr src = Some sregs' →
      incrementPC lpc = Some lpc' →
      regs' = specialrw_regs regs dst vold →
      SpecialRW_spec lpc regs sregs dst sr src lpc' regs' sregs' NextIV
  | SpecialRW_spec_failure :
      regs' = regs →
      sregs' = sregs →
      SpecialRW_failure lpc →
      lpc' = lpc →
      SpecialRW_spec lpc regs sregs dst sr src lpc' regs' sregs' FaultedV.

  (** The physical system registers after the write, and the erasure of the
      new logical ones. *)
  Lemma specialrw_sregs_phys R C pc (r : Reg) psr m st lpc lreg lsreg lmem regs sregs sr src vold :
    erasure R C (pc, r, psr, m, st) lpc lreg lsreg lmem →
    regs ⊆ lreg →
    lregs_phys R regs r →
    sregs ⊆ lsreg →
    regs_of_argument src ∖ {[ cnull ]} ⊆ dom regs →
    sregs !! sr = Some vold →
    ∃ sregs' psr' lsreg',
      specialrw_sregs regs sregs sr src = Some sregs' ∧
      (match src with
       | inr rs =>
           if decide (rs = cnull) then Some (pc, r, psr, m, st)
           else wsrc ← r !!ᵣ rs; Some (update_sreg (pc, r, psr, m, st) sr (legalise sr wsrc))
       | inl z => Some (update_sreg (pc, r, psr, m, st) sr (legalise sr (WInt z)))
       end) = Some (pc, r, psr', m, st) ∧
      erasure R C (pc, r, psr', m, st) lpc lreg lsreg' lmem ∧
      ((sregs' = sregs ∧ lsreg' = lsreg) ∨
       ∃ nv, sregs' = <[sr := nv]> sregs ∧ lsreg' = <[sr := nv]> lsreg).
  Proof.
    intros Her Hlregs Hregs Hlsregs Dsrc Hvold.
    assert (∀ (v : LWord) pw, reg_word_ok R C v → reg_phys R v pw →
      ∃ psr' lsreg',
        update_sreg (pc, r, psr, m, st) sr (legalise sr pw) = (pc, r, psr', m, st) ∧
        erasure R C (pc, r, psr', m, st) lpc lreg lsreg' lmem ∧
        lsreg' = <[sr := llegalise sr v]> lsreg) as Hwrite.
    { intros v pw Hok Hw. eexists _, _. split; first done.
      split; last done. by apply erasure_write_sreg. }
    destruct src as [z|rs]; cbn.
    - destruct (Hwrite (lword_of_word (WInt z)) (WInt z)) as (psr' & lsreg' & Hu & Her' & ->).
      { apply reg_word_ok_int. } { apply reg_phys_lword_of_word. }
      eexists _, psr', _. split; first done. rewrite Hu. split; first done.
      split; first done. right. by eexists.
    - case_decide as Hrs.
      { eexists sregs, psr, lsreg. split_and!; try done. by left. }
      assert (is_Some (regs !!ₗ rs)) as [v Hv].
      { apply elem_of_dom_lreg. apply Dsrc. set_solver. }
      destruct (llookup_reg_phys _ _ _ _ _ Hregs Hv) as (s & Hrs' & Hrel).
      destruct (Hwrite v (and_tag s v.(lw))) as (psr' & lsreg' & Hu & Her' & ->).
      { by eapply (erasure_llookup_reg_word _ _ _ _ _ _ _ regs). }
      { done. }
      eexists _, psr', _. rewrite Hv Hrs' /= Hu. split; first done. split; first done.
      split; first done. right. by eexists.
  Qed.

  (** The physical write of [SpecialRW] to a register other than MTDC and
      mstatus keeps MIE and mtdc. *)
  Lemma specialrw_sys_kept pc (r : Reg) psr m st psr' sr src :
    sr ≠ mtdc → sr ≠ mstatus →
    (match src with
     | inr rs =>
         if decide (rs = cnull) then Some (pc, r, psr, m, st)
         else wsrc ← r !!ᵣ rs; Some (update_sreg (pc, r, psr, m, st) sr (legalise sr wsrc))
     | inl z => Some (update_sreg (pc, r, psr, m, st) sr (legalise sr (WInt z)))
     end) = Some (pc, r, psr', m, st) →
    sys_kept (pc, r, psr, m, st) (pc, r, psr', m, st).
  Proof.
    intros H1 H2 Hφ. destruct src as [z|rs]; cbn in Hφ.
    - simplify_eq. by apply sys_kept_insert_sreg.
    - case_decide; first by simplify_eq.
      destruct (r !!ᵣ rs); cbn in Hφ; simplify_eq. by apply sys_kept_insert_sreg.
  Qed.

  Lemma wp_SpecialRW Ep pc_p pc_g pc_b pc_e pc_a pc_π w dst sr src regs sregs dq :
    decodeInstrW w.(lw) = SpecialRW dst sr src →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (SpecialRW dst sr src) ⊆ dom regs →
    (if has_sreg_access pc_p
     then sregs_of (SpecialRW dst sr src) ⊆ dom sregs
     else True) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        ▷ ([∗ map] k↦y ∈ sregs, k ↦ₓ y)
    }}}
      Instr Executable @ Ep
    {{{ lpc' regs' sregs' retv, RET retv;
        ⌜ SpecialRW_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs sregs dst sr src
            lpc' regs' sregs' retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        ([∗ map] k↦y ∈ regs', k ↦ᵣ y) ∗
        ([∗ map] k↦y ∈ sregs', k ↦ₓ y)
    }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Dsregs φ) "(>HPC & >Hpc_a & >Hmap & >Hsmap) Hφ".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
    iNext; iIntros (r psr m st lreg lsreg lmem R C c σ') "@".
    iDestruct (sys_interp_valid with "Hsr Hsmap") as %[Hlsregs Hdomsys].
    rewrite Hinstr /exec in Hstep.
    destruct (has_sreg_access pc_p) eqn:Hxsr; cycle 1.
    { cbn in Hstep. rewrite Hxsr in Hstep. instr_fail Hstep.
      apply SpecialRW_spec_failure; [done|done| |done]. by eapply SpecialRW_fail_nonxsr. }
    destruct (indom_sregs_incl _ _ _ Dsregs Hlsregs sr) as (vold & Hvold & Hvold');
      first (rewrite /sregs_of; set_solver).
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hvold') as (wold & Hwold & Hrelold).
    destruct (Hdomsys sr) as [Hsr_mtdc Hsr_mst]; first by eapply elem_of_dom_2.
    destruct (specialrw_sregs_phys R C _ r psr m st _ lreg (ls_join lsreg) lmem regs sregs sr src
                vold Her Hlregs Hregs Hlsregs)
      as (sregs' & psr' & lsreg' & Hsregs' & Hφ1 & Her1 & Hup).
    { rewrite /regs_of /operands_of in Dregs. set_solver. } { done. }
    cbn in Hstep. rewrite Hxsr Hwold /= Hφ1 /= in Hstep.
    destruct (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π)) as [lpc'|] eqn:Hi;
      cycle 1.
    { (* The PC increment fails: the state is unchanged. *)
      pose proof (erasure_incrementPC_fail _ _ _ _ _ _ _ _ _ _ _ _ Her Hi) as Hfail.
      rewrite /nextPC /advancePC /= in Hfail.
      destruct (pc_a + 1)%a as [pc_a'|] eqn:Hpca'; first done.
      assert (∀ φ', pcc φ' = Cap pc_p pc_g pc_b pc_e pc_a → nextPC φ' = None) as Hfail'.
      { intros φ' Hpc. by rewrite /nextPC /advancePC Hpc Hpca'. }
      rewrite Hfail' in Hstep; last by case_decide.
      instr_fail Hstep.
      apply SpecialRW_spec_failure; [done|done| |done]. by apply SpecialRW_fail_incrPC. }
    (* The ghost system registers *)
    iAssert (|==> ∃ ls', ⌜ls_join ls' = lsreg'⌝ ∗ sys_interp ls' ∗
                         [∗ map] k↦y ∈ sregs', k ↦ₓ y)%I
      with "[Hsr Hsmap]" as ">(%ls' & %Hls' & Hsr & Hsmap)".
    { destruct Hup as [ [-> ->] | (nv & -> & ->)]; first by iFrame.
      iMod (sys_interp_update _ _ sr nv with "Hsr Hsmap") as "[Hsr Hsmap]"; first by eexists.
      iModIntro. iExists (ls_insert_sh lsreg sr nv). iFrame. iPureIntro.
      by rewrite ls_join_insert_sh. }
    rewrite -Hls' in Her1.
    pose proof (specialrw_sys_kept _ _ _ _ _ _ _ _ Hsr_mtdc Hsr_mst Hφ1) as Hkept.
    pose proof (er_sreg_words _ _ _ _ _ _ _ Her _ _ Hvold') as Hokold.
    case_decide as Hdst.
    - (* The old value is dropped. *)
      destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hi) as (pc' & Hu & _).
      iApply (instr_close_kept_trans _ _ _ _ Hkept).
      iApply (instr_close_pc_update _ _ _ _ _ _ _ _ _ _ _ _ 1 _ _ _
        (λ lpc' retv, SpecialRW_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs sregs
           dst sr src lpc' regs sregs' retv)
        with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hsmap]").
      { exact Her1. } { rewrite /nextPC in Hu Hstep. by rewrite Hu in Hstep |- *. }
      { intros lpc'' Hi'. rewrite /incrementPC in Hi. simplify_eq.
        eapply SpecialRW_spec_success; eauto.
        all: by rewrite specialrw_regs_cnull. }
      { intros Hi'. rewrite /incrementPC in Hi. congruence. }
      iIntros (lpc'' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
    - (* [dst] receives the old value. *)
      destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _
        (erasure_linsert_reg _ _ _ _ _ _ _ _ _ _ _ dst vold wold Her1 Hokold Hrelold) Hi)
        as (pc' & Hu & _).
      iApply (instr_close_kept_trans _ _ _ _ Hkept).
      iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ dst vold wold _ _ _
        (λ lpc' regs' retv, SpecialRW_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs
           sregs dst sr src lpc' regs' sregs' retv)
        with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hsmap]").
      { exact Her1. } { exact Hlregs. }
      { right. apply Dregs. rewrite /regs_of /operands_of. set_solver. }
      { exact Hokold. }
      { rewrite /update_reg /= in Hu Hstep |- *. by rewrite Hu in Hstep |- *. }
      { exact Hrelold. }
      { intros lpc'' Hi'. rewrite Hi in Hi'. simplify_eq.
        eapply SpecialRW_spec_success; eauto.
        all: by rewrite specialrw_regs_ne // linsert_reg_not_cnull. }
      { intros Hi'. congruence. }
      iIntros (lpc'' regs'' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
  Qed.

  (** Inverts a [SpecialRW_spec] whose PC increment succeeds and whose PC has
      the system-register permission: the failure case is absurd. *)
  Lemma SpecialRW_spec_success_inv pc_p pc_g pc_b pc_e pc_a pc_π pc_a' regs sregs dst sr src
      lpc' regs' sregs' retv :
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    SpecialRW_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs sregs dst sr src
      lpc' regs' sregs' retv →
    retv = NextIV ∧ lpc' = Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∧
    ∃ vold, sregs !! sr = Some vold ∧
      specialrw_sregs regs sregs sr src = Some sregs' ∧
      regs' = specialrw_regs regs dst vold.
  Proof.
    intros Hxsr Hpca' Hspec.
    destruct Hspec as [p g b e a π vold Hpc Hx Hvold Hsr' Hi -> | -> -> Hfail].
    - simplify_eq. rewrite (incrementPC_add _ _ _ _ _ _ _ _ Hpca') in Hi. simplify_eq.
      split_and!; try done. by eexists.
    - exfalso. destruct Hfail as [p g b e a π Hpc Hx | Hi].
      + simplify_eq. by rewrite Hxsr in Hx.
      + by rewrite (incrementPC_add _ _ _ _ _ _ _ _ Hpca') in Hi.
  Qed.

  Lemma wp_readsr_success E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst wdst src (wsrc : Word) dq :
    decodeInstrW w.(lw) = SpecialRW dst src (inr cnull) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ wdst
        ∗ ▷ src ↦ₓ wsrc }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ dst ↦ᵣ lword_of_word wsrc
          ∗ src ↦ₓ wsrc }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hcnull φ) "(>HPC & >Hpc_a & >Hdst & >Hsrc) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iDestruct (map_of_sregs_1 with "Hsrc") as "Hsmap".
    iApply (wp_SpecialRW with "[$HPC $Hmap $Hsmap $Hpc_a]"); eauto.
    { rewrite /regs_of /operands_of /regs_of_argument dom_singleton_L. set_solver. }
    { rewrite Hxsr /sregs_of dom_singleton_L. set_solver. }
    iNext. iIntros (lpc' regs' sregs' retv) "(%Hspec & HPC & Hpc_a & Hmap & Hsmap)".
    destruct (SpecialRW_spec_success_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hxsr Hpca' Hspec)
      as (-> & -> & vold & Hvold & Hsr' & ->).
    rewrite /specialrw_sregs /= in Hsr'. case_decide as Hc; last done. simplify_map_eq.
    rewrite specialrw_regs_ne // insert_singleton_eq.
    iApply "Hφ". iFrame.
    iDestruct (regs_of_map_1 with "Hmap") as "$".
    iApply (sregs_of_map_1 with "Hsmap").
  Qed.

  Lemma wp_writesr_success E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst wdst src (wsrc : Word) dq :
    decodeInstrW w.(lw) = SpecialRW cnull dst (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ₓ wdst
        ∗ ▷ src ↦ᵣ lword_of_word wsrc }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ dst ↦ₓ legalise dst wsrc
          ∗ src ↦ᵣ lword_of_word wsrc }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hcnull φ) "(>HPC & >Hpc_a & >Hdst & >Hsrc) Hφ".
    iDestruct (map_of_regs_1 with "Hsrc") as "Hmap".
    iDestruct (map_of_sregs_1 with "Hdst") as "Hsmap".
    iApply (wp_SpecialRW with "[$HPC $Hmap $Hsmap $Hpc_a]"); eauto.
    { rewrite /regs_of /operands_of /regs_of_argument dom_singleton_L. set_solver. }
    { rewrite Hxsr /sregs_of dom_singleton_L. set_solver. }
    iNext. iIntros (lpc' regs' sregs' retv) "(%Hspec & HPC & Hpc_a & Hmap & Hsmap)".
    destruct (SpecialRW_spec_success_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hxsr Hpca' Hspec)
      as (-> & -> & vold & Hvold & Hsr' & ->).
    rewrite /specialrw_sregs /= in Hsr'. case_decide as Hc; first done.
    rewrite llookup_reg_not_cnull // in Hsr'.
    simplify_map_eq. rewrite insert_singleton_eq.
    rewrite specialrw_regs_cnull.
    iApply "Hφ". iFrame.
    iDestruct (regs_of_map_1 with "Hmap") as "$".
    iApply (sregs_of_map_1 with "Hsmap").
  Qed.

  (** The swap of a register with a system register. *)
  Lemma wp_specialrw_swap E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r sr (v vold : LWord) dq :
    decodeInstrW w.(lw) = SpecialRW r sr (inr r) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    r ≠ cnull →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r ↦ᵣ v
        ∗ ▷ sr ↦ₓ vold }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r ↦ᵣ vold
          ∗ sr ↦ₓ llegalise sr v }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hcnull φ) "(>HPC & >Hpc_a & >Hr & >Hsr) Hφ".
    iDestruct (map_of_regs_1 with "Hr") as "Hmap".
    iDestruct (map_of_sregs_1 with "Hsr") as "Hsmap".
    iApply (wp_SpecialRW with "[$HPC $Hmap $Hsmap $Hpc_a]"); eauto.
    { rewrite /regs_of /operands_of /regs_of_argument dom_singleton_L. set_solver. }
    { rewrite Hxsr /sregs_of dom_singleton_L. set_solver. }
    iNext. iIntros (lpc' regs' sregs' retv) "(%Hspec & HPC & Hpc_a & Hmap & Hsmap)".
    destruct (SpecialRW_spec_success_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hxsr Hpca' Hspec)
      as (-> & -> & vold' & Hvold & Hsr' & ->).
    rewrite /specialrw_sregs /= in Hsr'. case_decide as Hc; first done.
    rewrite llookup_reg_not_cnull // in Hsr'.
    simplify_map_eq. rewrite insert_singleton_eq.
    rewrite specialrw_regs_ne // insert_singleton_eq.
    iApply "Hφ". iFrame.
    iDestruct (regs_of_map_1 with "Hmap") as "$".
    iApply (sregs_of_map_1 with "Hsmap").
  Qed.

  (** A swap between two different registers. *)
  Lemma wp_specialrw_success E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst wdst sr src
      (v vold : LWord) dq :
    decodeInstrW w.(lw) = SpecialRW dst sr (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    src ≠ cnull →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ wdst
        ∗ ▷ src ↦ᵣ v
        ∗ ▷ sr ↦ₓ vold }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ dst ↦ᵣ vold
          ∗ src ↦ᵣ v
          ∗ sr ↦ₓ llegalise sr v }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hdst Hsrc φ) "(>HPC & >Hpc_a & >Hdst & >Hsrc & >Hsr) Hφ".
    iDestruct (map_of_regs_2 with "Hdst Hsrc") as "[Hmap %Hne]".
    iDestruct (map_of_sregs_1 with "Hsr") as "Hsmap".
    iApply (wp_SpecialRW with "[$HPC $Hmap $Hsmap $Hpc_a]"); eauto.
    { rewrite /regs_of /operands_of /regs_of_argument !dom_insert_L. set_solver. }
    { rewrite Hxsr /sregs_of dom_singleton_L. set_solver. }
    iNext. iIntros (lpc' regs' sregs' retv) "(%Hspec & HPC & Hpc_a & Hmap & Hsmap)".
    destruct (SpecialRW_spec_success_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hxsr Hpca' Hspec)
      as (-> & -> & vold' & Hvold & Hsr' & ->).
    rewrite /specialrw_sregs /= in Hsr'. case_decide as Hc; first done.
    rewrite llookup_reg_not_cnull // in Hsr'.
    simplify_map_eq. rewrite insert_singleton_eq.
    rewrite specialrw_regs_ne // insert_insert_eq.
    iApply "Hφ". iFrame.
    iDestruct (regs_of_map_2 with "Hmap") as "[$ $]"; first done.
    iApply (sregs_of_map_1 with "Hsmap").
  Qed.

  (** The write of an immediate, as [csrw sr, z]. *)
  Lemma wp_specialrw_imm_success E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w sr (z : Z) vold dq :
    decodeInstrW w.(lw) = SpecialRW cnull sr (inl z) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ sr ↦ₓ vold }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ sr ↦ₓ legalise sr (WInt z) }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' φ) "(>HPC & >Hpc_a & >Hsr) Hφ".
    iDestruct (map_of_sregs_1 with "Hsr") as "Hsmap".
    iApply (wp_SpecialRW _ _ _ _ _ _ _ _ _ _ _ ∅ with "[$HPC $Hsmap $Hpc_a]"); eauto.
    { rewrite Hxsr /sregs_of dom_singleton_L. set_solver. }
    iNext. iIntros (lpc' regs' sregs' retv) "(%Hspec & HPC & Hpc_a & Hmap & Hsmap)".
    destruct (SpecialRW_spec_success_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hxsr Hpca' Hspec)
      as (-> & -> & vold' & Hvold & Hsr' & ->).
    rewrite /specialrw_sregs in Hsr'. simplify_map_eq. rewrite insert_singleton_eq.
    iApply "Hφ". iFrame.
    iApply (sregs_of_map_1 with "Hsmap").
  Qed.

  (** ** mtdc

      mtdc is a per-thread register with its own ghost state: the fragment
      [mtdc ↦ₜ m] of the thread holds a ghost value [m] that stands for the
      logical word of mtdc ([mtdc_match]). A read gives a word that [m]
      stands for; a write relabels the ghost value with any [m'] that stands
      for the written word, and has a link-transfer premise. *)

  (** [cspecialr dst, mtdc]. *)
  Lemma wp_readsr_mtdc E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst wdst m dq :
    decodeInstrW w.(lw) = SpecialRW dst mtdc (inr cnull) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ wdst ∗
        ▷ mtdc ↦ₜ m }}}
      Instr Executable @ E
      {{{ vm, RET NextIV;
          ⌜mtdc_match m vm⌝ ∗
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          dst ↦ᵣ vm ∗
          mtdc ↦ₜ m }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hdst φ) "(>HPC & >Hpc_a & >Hdst & >Hmtdc_f) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); first done.
    iNext; iIntros (r psr mm st lreg lsreg lmem R C c σ') "@".
    iDestruct (sys_interp_mtdc_agree with "Hsr Hmtdc_f") as %[Hmeq Hmatch].
    pose proof (ls_join_mtdc lsreg) as Hv.
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hv) as (wold & Hwold & Hrel).
    pose proof (er_sreg_words _ _ _ _ _ _ _ Her _ _ Hv) as Hok.
    rewrite Hinstr /exec in Hstep. cbn in Hstep. rewrite Hxsr Hwold /= in Hstep.
    destruct (decide (cnull = cnull)) as [_|Hc]; last done.
    destruct (decide (dst = cnull)) as [Hc|_]; first done. cbn in Hstep.
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ dst (ls_vmtdc lsreg) wold _ _ _
      (λ lpc' regs' retv, lpc' = Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∧
                          regs' = <[dst := ls_vmtdc lsreg]ₗ> {[dst := wdst]} ∧ retv = NextIV)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hmtdc_f]").
    { exact Her. } { exact Hlregs. } { right. set_solver. } { exact Hok. } { exact Hstep. }
    { exact Hrel. }
    { intros lpc' Hi. rewrite (incrementPC_add _ _ _ _ _ _ _ _ Hpca') in Hi. by simplify_eq. }
    { intros Hi. by rewrite (incrementPC_add _ _ _ _ _ _ _ _ Hpca') in Hi. }
    iIntros (lpc' regs' retv (-> & -> & ->)) "HPC Hmap".
    rewrite linsert_reg_not_cnull // insert_singleton_eq.
    iApply "Hφ". iFrame. iDestruct (regs_of_map_1 with "Hmap") as "$".
    iPureIntro. done.
  Qed.

  (** [cspecialw mtdc, src]: the ghost value becomes any [m'] that stands
      for the written word. *)
  Lemma wp_writesr_mtdc_link E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src (v : LWord) m m' dq
      (T1 T2 : iProp Σ) :
    decodeInstrW w.(lw) = SpecialRW cnull mtdc (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    mtdc_match m' v →
    link_transfer mtdc_written T1 T2 →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ v ∗
        ▷ mtdc ↦ₜ m ∗
        ▷ T1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          src ↦ᵣ v ∗
          mtdc ↦ₜ m' ∗
          T2 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hsrc Hm' Htr φ) "(>HPC & >Hpc_a & >Hsrc & >Hmtdc_f & HT) Hφ".
    iDestruct (map_of_regs_1 with "Hsrc") as "Hmap".
    iApply (wp_instr_step_link with "HPC Hpc_a Hmap"); first done.
    iNext; iIntros (r psr mm st lreg lsreg lmem R C c σ') "@".
    pose proof (ls_join_mtdc lsreg) as Hv.
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hv) as (wold & Hwold & _).
    assert ({[src := v]} !!ₗ src = Some v) as Hsv.
    { rewrite llookup_reg_not_cnull // lookup_singleton_eq //. }
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hsv) as (s & Hrs & Hrel).
    pose proof (erasure_llookup_reg_word _ _ _ _ _ _ _ _ _ _ Her Hlregs Hsv) as Hok.
    rewrite Hinstr /exec in Hstep. cbn in Hstep. rewrite Hxsr Hwold /= in Hstep.
    destruct (decide (src = cnull)) as [Hc|_]; first done.
    rewrite Hrs /= in Hstep.
    destruct (decide (cnull = cnull)) as [_|Hc]; last done.
    pose proof (erasure_write_sreg _ _ _ _ _ _ _ _ _ _ _ mtdc v (and_tag s (lw v)) Her Hok Hrel)
      as Her1.
    rewrite llegalise_mtdc -(ls_join_set_mtdc lsreg m' v) in Her1. cbn [legalise] in Her1, Hstep.
    iMod (sys_interp_set_mtdc _ m m' v Hm' with "Hsr Hmtdc_f") as "[Hsr Hmtdc_f]".
    iApply (instr_close_link_transfer _ _ _ _
              (Cap pc_p pc_g pc_b pc_e pc_a, r, <[mtdc := and_tag s (lw v)]> psr, mm, st)
              with "Hlink HT"); [exact Htr | |].
    { intros Hk. eapply mtdc_written_kept; last exact Hk.
      by rewrite /mtdc_written /mie_st /= lookup_insert_ne. }
    destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ Her1
                (incrementPC_add _ _ _ _ _ _ _ _ Hpca')) as (pc' & Hu & _).
    iApply (instr_close_pc_update _ _ _ _ _ _ _ _ _ _ _ _ 1 _ _ _
      (λ lpc' retv, lpc' = Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∧ retv = NextIV)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hmtdc_f]").
    { exact Her1. } { rewrite /nextPC in Hu Hstep. by rewrite Hu in Hstep |- *. }
    { intros lpc' Hi. rewrite /incrementPC_gen /= Hpca' in Hi. by simplify_eq. }
    { intros Hi. by rewrite /incrementPC_gen /= Hpca' in Hi. }
    iIntros (lpc' retv [-> ->]) "HPC Hmap HT".
    iApply "Hφ". iFrame. iApply (regs_of_map_1 with "Hmap").
  Qed.

  (** [cspecialrw r, mtdc, r]: the swap of a register with mtdc; [r]
      receives a word that [m] stands for, and the ghost value becomes any
      [m'] that stands for the word written. *)
  Lemma wp_specialrw_swap_mtdc_link E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r (v : LWord) m m' dq
      (T1 T2 : iProp Σ) :
    decodeInstrW w.(lw) = SpecialRW r mtdc (inr r) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    r ≠ cnull →
    mtdc_match m' v →
    link_transfer mtdc_written T1 T2 →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r ↦ᵣ v ∗
        ▷ mtdc ↦ₜ m ∗
        ▷ T1 }}}
      Instr Executable @ E
      {{{ vm, RET NextIV;
          ⌜mtdc_match m vm⌝ ∗
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          r ↦ᵣ vm ∗
          mtdc ↦ₜ m' ∗
          T2 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hr Hm' Htr φ) "(>HPC & >Hpc_a & >Hr & >Hmtdc_f & HT) Hφ".
    iDestruct (map_of_regs_1 with "Hr") as "Hmap".
    iApply (wp_instr_step_link with "HPC Hpc_a Hmap"); first done.
    iNext; iIntros (rf psr mm st lreg lsreg lmem R C c σ') "@".
    iDestruct (sys_interp_mtdc_agree with "Hsr Hmtdc_f") as %[Hmeq Hmatch].
    pose proof (ls_join_mtdc lsreg) as Hv.
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hv) as (wold & Hwold & Hrelold).
    pose proof (er_sreg_words _ _ _ _ _ _ _ Her _ _ Hv) as Hokold.
    assert ({[r := v]} !!ₗ r = Some v) as Hsv.
    { rewrite llookup_reg_not_cnull // lookup_singleton_eq //. }
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hsv) as (s & Hrs & Hrel).
    pose proof (erasure_llookup_reg_word _ _ _ _ _ _ _ _ _ _ Her Hlregs Hsv) as Hok.
    rewrite Hinstr /exec in Hstep. cbn in Hstep. rewrite Hxsr Hwold /= in Hstep.
    destruct (decide (r = cnull)) as [Hc|_]; first done.
    rewrite Hrs /= in Hstep.
    pose proof (erasure_write_sreg _ _ _ _ _ _ _ _ _ _ _ mtdc v (and_tag s (lw v)) Her Hok Hrel)
      as Her1.
    rewrite llegalise_mtdc -(ls_join_set_mtdc lsreg m' v) in Her1. cbn [legalise] in Her1, Hstep.
    iMod (sys_interp_set_mtdc _ m m' v Hm' with "Hsr Hmtdc_f") as "[Hsr Hmtdc_f]".
    iApply (instr_close_link_transfer _ _ _ _
              (Cap pc_p pc_g pc_b pc_e pc_a, rf, <[mtdc := and_tag s (lw v)]> psr, mm, st)
              with "Hlink HT"); [exact Htr | |].
    { intros Hk. eapply mtdc_written_kept; last exact Hk.
      by rewrite /mtdc_written /mie_st /= lookup_insert_ne. }
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ r (ls_vmtdc lsreg) wold _ _ _
      (λ lpc' regs' retv, lpc' = Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∧
                          regs' = <[r := ls_vmtdc lsreg]ₗ> {[r := v]} ∧ retv = NextIV)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hmtdc_f]").
    { exact Her1. } { exact Hlregs. } { right. set_solver. } { exact Hokold. }
    { destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _
        (erasure_linsert_reg _ _ _ _ _ _ _ _ _ _ _ r (ls_vmtdc lsreg) wold Her1 Hokold Hrelold)
        (incrementPC_add _ _ _ _ _ _ _ _ Hpca')) as (pc' & Hu & _).
      rewrite /update_reg /= in Hu Hstep |- *. by rewrite Hu in Hstep |- *. }
    { exact Hrelold. }
    { intros lpc' Hi. rewrite (incrementPC_add _ _ _ _ _ _ _ _ Hpca') in Hi. by simplify_eq. }
    { intros Hi. by rewrite (incrementPC_add _ _ _ _ _ _ _ _ Hpca') in Hi. }
    iIntros (lpc' regs' retv (-> & -> & ->)) "HPC Hmap HT".
    rewrite linsert_reg_not_cnull // insert_singleton_eq.
    iApply "Hφ". iFrame. iDestruct (regs_of_map_1 with "Hmap") as "$".
    iPureIntro. done.
  Qed.

  (** [cspecialw mtdc, z]: the write of an immediate. *)
  Lemma wp_specialrw_imm_mtdc_link E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w (z : Z) m m' dq
      (T1 T2 : iProp Σ) :
    decodeInstrW w.(lw) = SpecialRW cnull mtdc (inl z) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    mtdc_match m' (lword_of_word (WInt z)) →
    link_transfer mtdc_written T1 T2 →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ mtdc ↦ₜ m ∗
        ▷ T1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          mtdc ↦ₜ m' ∗
          T2 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hm' Htr φ) "(>HPC & >Hpc_a & >Hmtdc_f & HT) Hφ".
    iAssert ([∗ map] k↦y ∈ (∅ : LReg), k ↦ᵣ y)%I as "Hmap0"; first by rewrite big_sepM_empty.
    iApply (wp_instr_step_link _ _ _ _ _ _ _ _ _ ∅ with "HPC Hpc_a Hmap0"); first done.
    iNext; iIntros (r psr mm st lreg lsreg lmem R C c σ') "@".
    pose proof (ls_join_mtdc lsreg) as Hv.
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hv) as (wold & Hwold & _).
    rewrite Hinstr /exec in Hstep. cbn in Hstep. rewrite Hxsr Hwold /= in Hstep.
    destruct (decide (cnull = cnull)) as [_|Hc]; last done.
    pose proof (erasure_write_sreg _ _ _ _ _ _ _ _ _ _ _ mtdc (lword_of_word (WInt z)) (WInt z)
                  Her (reg_word_ok_int _ _ _ _) (reg_phys_lword_of_word _ _)) as Her1.
    rewrite llegalise_mtdc -(ls_join_set_mtdc lsreg m' (lword_of_word (WInt z))) in Her1.
    cbn [legalise] in Her1, Hstep.
    iMod (sys_interp_set_mtdc _ m m' _ Hm' with "Hsr Hmtdc_f") as "[Hsr Hmtdc_f]".
    iApply (instr_close_link_transfer _ _ _ _
              (Cap pc_p pc_g pc_b pc_e pc_a, r, <[mtdc := WInt z]> psr, mm, st)
              with "Hlink HT"); [exact Htr | |].
    { intros Hk. eapply mtdc_written_kept; last exact Hk.
      by rewrite /mtdc_written /mie_st /= lookup_insert_ne. }
    destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ Her1
                (incrementPC_add _ _ _ _ _ _ _ _ Hpca')) as (pc' & Hu & _).
    iApply (instr_close_pc_update _ _ _ _ _ _ _ _ _ _ _ _ 1 _ _ _
      (λ lpc' retv, lpc' = Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∧ retv = NextIV)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hmtdc_f]").
    { exact Her1. } { rewrite /nextPC in Hu Hstep. by rewrite Hu in Hstep |- *. }
    { intros lpc' Hi. rewrite /incrementPC_gen /= Hpca' in Hi. by simplify_eq. }
    { intros Hi. by rewrite /incrementPC_gen /= Hpca' in Hi. }
    iIntros (lpc' retv [-> ->]) "HPC Hmap HT".
    iApply "Hφ". iFrame.
  Qed.

End griotte_lang_rules.

(** The core corollaries of the mtdc writers: at the core link, the premise
    holds with [True]. *)
Section griotte_lang_rules_core.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ}.
  Implicit Types w : LWord.

  Lemma wp_writesr_mtdc E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src (v : LWord) m m' dq :
    decodeInstrW w.(lw) = SpecialRW cnull mtdc (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    mtdc_match m' v →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ v ∗
        ▷ mtdc ↦ₜ m }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          src ↦ᵣ v ∗
          mtdc ↦ₜ m' }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hsrc Hm' φ) "(>HPC & >Hpc_a & >Hsrc & >Hmtdc_f) Hφ".
    iApply (wp_writesr_mtdc_link _ _ _ _ _ _ _ _ _ _ _ _ _ _ True%I True%I
             with "[$HPC $Hpc_a $Hsrc $Hmtdc_f]").
    all: try done.
    { apply link_transfer_core. }
    iNext. iIntros "(HPC & Hpc_a & Hsrc & Hmtdc_f & _)". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_specialrw_swap_mtdc E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r (v : LWord) m m' dq :
    decodeInstrW w.(lw) = SpecialRW r mtdc (inr r) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    r ≠ cnull →
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
    iIntros (Hinstr Hvpc Hxsr Hpca' Hr Hm' φ) "(>HPC & >Hpc_a & >Hr & >Hmtdc_f) Hφ".
    iApply (wp_specialrw_swap_mtdc_link _ _ _ _ _ _ _ _ _ _ _ _ _ _ True%I True%I
             with "[$HPC $Hpc_a $Hr $Hmtdc_f]").
    all: try done.
    { apply link_transfer_core. }
    iNext. iIntros (vm) "(Hmatch & HPC & Hpc_a & Hr & Hmtdc_f & _)". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_specialrw_imm_mtdc E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w (z : Z) m m' dq :
    decodeInstrW w.(lw) = SpecialRW cnull mtdc (inl z) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    mtdc_match m' (lword_of_word (WInt z)) →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ mtdc ↦ₜ m }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          mtdc ↦ₜ m' }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hm' φ) "(>HPC & >Hpc_a & >Hmtdc_f) Hφ".
    iApply (wp_specialrw_imm_mtdc_link _ _ _ _ _ _ _ _ _ _ _ _ _ True%I True%I
             with "[$HPC $Hpc_a $Hmtdc_f]").
    all: try done.
    { apply link_transfer_core. }
    iNext. iIntros "(HPC & Hpc_a & Hmtdc_f & _)". iApply "Hφ". iFrame.
  Qed.

End griotte_lang_rules_core.
