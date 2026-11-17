From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import proofmode.
From griotte Require Import named_props_extra.
From griotte Require Export resources crit_link thread_langs.

(** The logical system registers of a step, in one argument: the shared
    heap [ls_sh] (without MTDC, mstatus, MSHWM and MSHWMB), the ghost value
    [ls_mtdc] of the thread's mtdc and its logical word [ls_vmtdc], MIE and
    MPIE, the thread's MSHWMB [ls_hwmb] and MSHWM [ls_hwm], its HWM
    restore window [ls_pend] and its lent set [ls_lent]. *)
Record LSys := MkLSys {
  ls_sh : LSReg;
  ls_mtdc : mtdc_val;
  ls_vmtdc : LWord;
  ls_mie : InterruptStatus;
  ls_mpie : InterruptStatus;
  ls_hwmb : Z;
  ls_hwm : Z;
  ls_pend : option Z;
  ls_lent : gset Addr;
}.

(** The logical system registers of [erasure]. *)
Definition ls_join (ls : LSys) : LSReg :=
  lsregs_join (ls_sh ls) (ls_vmtdc ls) (ls_hwmb ls) (ls_hwm ls) (ls_mie ls) (ls_mpie ls).

Definition ls_set_mstatus (ls : LSys) (mie mpie : InterruptStatus) : LSys :=
  MkLSys (ls_sh ls) (ls_mtdc ls) (ls_vmtdc ls) mie mpie
    (ls_hwmb ls) (ls_hwm ls) (ls_pend ls) (ls_lent ls).
Definition ls_set_mtdc (ls : LSys) (m : mtdc_val) (vm : LWord) : LSys :=
  MkLSys (ls_sh ls) m vm (ls_mie ls) (ls_mpie ls)
    (ls_hwmb ls) (ls_hwm ls) (ls_pend ls) (ls_lent ls).
Definition ls_insert_sh (ls : LSys) (sr : SRegName) (v : LWord) : LSys :=
  MkLSys (<[sr := v]> (ls_sh ls)) (ls_mtdc ls) (ls_vmtdc ls) (ls_mie ls) (ls_mpie ls)
    (ls_hwmb ls) (ls_hwm ls) (ls_pend ls) (ls_lent ls).
Definition ls_set_hwmb (ls : LSys) (mshwmb_v : Z) : LSys :=
  MkLSys (ls_sh ls) (ls_mtdc ls) (ls_vmtdc ls) (ls_mie ls) (ls_mpie ls)
    mshwmb_v (ls_hwm ls) (ls_pend ls) (ls_lent ls).
Definition ls_set_hwm (ls : LSys) (mshwm_v : Z) : LSys :=
  MkLSys (ls_sh ls) (ls_mtdc ls) (ls_vmtdc ls) (ls_mie ls) (ls_mpie ls)
    (ls_hwmb ls) mshwm_v (ls_pend ls) (ls_lent ls).
(** The window and the lent set, which [erasure] does not see. *)
Definition ls_set_win (ls : LSys) (o : option Z) (L : gset Addr) : LSys :=
  MkLSys (ls_sh ls) (ls_mtdc ls) (ls_vmtdc ls) (ls_mie ls) (ls_mpie ls)
    (ls_hwmb ls) (ls_hwm ls) o L.

Lemma ls_join_mstatus ls :
  ls_join ls !! mstatus = Some (lword_of_word (WInt (mstatus_enc (ls_mie ls) (ls_mpie ls)))).
Proof. apply lsregs_join_mstatus. Qed.

Lemma ls_join_mtdc ls : ls_join ls !! mtdc = Some (ls_vmtdc ls).
Proof. apply lsregs_join_mtdc. Qed.

Lemma ls_join_set_mstatus ls mie mpie :
  ls_join (ls_set_mstatus ls mie mpie) =
  <[mstatus := lword_of_word (WInt (mstatus_enc mie mpie))]> (ls_join ls).
Proof. by rewrite /ls_join /lsregs_join /= insert_insert_eq. Qed.

Lemma ls_join_set_mtdc ls m vm :
  ls_join (ls_set_mtdc ls m vm) = <[mtdc := vm]> (ls_join ls).
Proof.
  by rewrite /ls_join /lsregs_join /= (insert_insert_ne _ mtdc mstatus) // insert_insert_eq.
Qed.

Lemma ls_join_insert_sh ls sr v :
  sr ≠ mtdc → sr ≠ mstatus → sr ≠ mshwm → sr ≠ mshwmb →
  ls_join (ls_insert_sh ls sr v) = <[sr := v]> (ls_join ls).
Proof.
  intros H1 H2 H3 H4. rewrite /ls_join /lsregs_join /=.
  rewrite (insert_insert_ne _ sr mstatus) // (insert_insert_ne _ sr mtdc) //.
  rewrite (insert_insert_ne _ sr mshwmb) // (insert_insert_ne _ sr mshwm) //.
Qed.

Lemma ls_join_mshwmb ls : ls_join ls !! mshwmb = Some (lword_of_word (WInt (ls_hwmb ls))).
Proof. apply lsregs_join_mshwmb. Qed.

Lemma ls_join_mshwm ls : ls_join ls !! mshwm = Some (lword_of_word (WInt (ls_hwm ls))).
Proof. apply lsregs_join_mshwm. Qed.

Lemma ls_join_set_hwmb ls mshwmb_v :
  ls_join (ls_set_hwmb ls mshwmb_v) = <[mshwmb := lword_of_word (WInt mshwmb_v)]> (ls_join ls).
Proof.
  rewrite /ls_join /lsregs_join /=.
  rewrite (insert_insert_ne _ mshwmb mstatus) // (insert_insert_ne _ mshwmb mtdc) //.
  by rewrite insert_insert_eq.
Qed.

Lemma ls_join_set_hwm ls mshwm_v :
  ls_join (ls_set_hwm ls mshwm_v) = <[mshwm := lword_of_word (WInt mshwm_v)]> (ls_join ls).
Proof.
  rewrite /ls_join /lsregs_join /=.
  rewrite (insert_insert_ne _ mshwm mstatus) // (insert_insert_ne _ mshwm mtdc) //.
  rewrite (insert_insert_ne _ mshwm mshwmb) //. by rewrite insert_insert_eq.
Qed.

Lemma ls_join_set_win ls o L : ls_join (ls_set_win ls o L) = ls_join ls.
Proof. done. Qed.

(** The state interpretation: a part shared by the threads and the part of
    the running thread, related to the machine state by their erasures. *)
Section state_interp.
  Context `{MP : MachineParameters}.
  Context `{!pcG Σ,
            !gen_heapGS RegName LWord Σ, !gen_heapGS SRegName LWord Σ,
            !gen_heapGS Addr LWord Σ, !gen_heapGS Addr AllocStatus Σ,
            !allocRegistryG Σ, !addrAllocG Σ, !trapVector, !cerise_na_invs Σ,
            !mtdcG Σ, !mieG Σ, !mpieG Σ, !postureG Σ, !mtdcLentG Σ, !hwmG Σ}.

  (** The zone of the thread covers [hc, mshwm_v) with its own cells and the
      lent halves [L], and the state interpretation holds half of each cell
      of both, at some integer: the cell's value, shared with the other half.
      [hc] is the cover base ([hc_of]). *)
  Definition hwm_zone (hc mshwm_v : Z) (L : gset Addr) : iProp Σ :=
    ∃ zone : gset Addr,
      "%Hzone_cover" ∷ ⌜∀ a : Addr, (hc ≤ a < mshwm_v)%Z → a ∈ zone ∪ L⌝ ∗
      "Hzone_auth" ∷ zone_auth zone ∗
      "Hzone_cells" ∷ zone_halves zone ∗
      "Hlent_cells" ∷ zone_halves L.

  #[global] Instance hwm_zone_timeless hc mshwm_v L : Timeless (hwm_zone hc mshwm_v L).
  Proof. apply _. Qed.

  (** MTCC: it holds the trap vector [mtcc_vec] while the one-shot ghost is
      pending; once wedged, it holds an untagged word and the state
      interpretation holds the unwedged token. No client holds its
      points-to. *)
  Definition SI_mtcc : iProp Σ :=
    (mtcc ↦ₓ lword_of_word mtcc_vec ∗ mtcc_pending) ∨
    (∃ w : LWord, mtcc ↦ₓ w ∗ ⌜get_tag w.(lw) = false⌝ ∗ unwedged ∗ mtcc_wedged).

  (** The shared part: the shared system registers (MTCC as [SI_mtcc]),
      memory, the shadow table, the registry, the address claims, and the
      authority of MPIE. The volatile registers (MEPCC, mcause, mtval) and
      the fragment of MPIE are held by the clients. *)
  Definition SI_shared R C (σ : ExecConf) : iProp Σ :=
    ∃ (lsh : LSReg) (lmem : LMem) (mpie : InterruptStatus),
      "Hsr" ∷ gen_heap_interp lsh ∗
      "Hmtcc" ∷ SI_mtcc ∗
      "Hm" ∷ gen_heap_interp lmem ∗
      "Hst" ∷ gen_heap_interp (shadowtbl σ) ∗
      "HR" ∷ reg_auth R ∗
      "HC" ∷ addr_alloc_auth C ∗
      "Hmpie" ∷ MPIE_auth mpie ∗
      "%Hersh" ∷ ⌜erasure_sh R C σ lsh lmem mpie⌝.

  (** The part of the running thread: its PC, its registers, the authority
      of its mtdc ghost and the clause of its mtdc token, the authority of
      MIE (the fragment is held by the thread's code), the authorities of
      its MSHWMB and MSHWM, the state interpretation's half of its HWM
      restore window, the authority of its lent set, and its zone at the
      cover base. The erasure is exact on the physical MSHWMB and MSHWM. *)
  Definition SI_th R C (σ : ExecConf) : iProp Σ :=
    ∃ (lpc : LWord) (lreg : LReg) (m : mtdc_val) (vm : LWord) (mie : InterruptStatus)
      (mshwmb_v mshwm_v : Z) (o : option Z) (L : gset Addr),
      "HPCa" ∷ PC_auth lpc ∗
      "Hr" ∷ gen_heap_interp lreg ∗
      "Hmtdc" ∷ mtdc_auth m ∗
      "%Hmtdc_m" ∷ ⌜mtdc_match m vm⌝ ∗
      "Hlent" ∷ mtdc_clause m ∗
      "Hmie" ∷ MIE_auth mie ∗
      "Hmshwmb_a" ∷ mshwmb_auth mshwmb_v ∗
      "Hmshwm_a" ∷ mshwm_auth mshwm_v ∗
      "Hpend_si" ∷ pend_si o ∗
      "Hlent_a" ∷ lent_auth L ∗
      "Hzone" ∷ hwm_zone (hc_of mshwmb_v o) mshwm_v L ∗
      "%Herth" ∷ ⌜erasure_th R C σ lpc lreg vm mie mshwmb_v mshwm_v⌝.

  (** One [∃ R C] for both parts. *)
  Definition cerise_state_interp (σ : ExecConf) : iProp Σ :=
    ∃ R C, SI_shared R C σ ∗ SI_th R C σ.

  #[global] Instance cerise_state_interp_timeless σ : Timeless (cerise_state_interp σ).
  Proof. apply _. Qed.

  (** The system registers of a step, as one hypothesis: the shared heap,
      MTCC, MPIE, the thread's mtdc with its clause, MIE, and its MSHWMB,
      MSHWM, window, lent set and zone. *)
  Definition sys_interp (ls : LSys) : iProp Σ :=
    "Hsr" ∷ gen_heap_interp (ls_sh ls) ∗
    "Hmtcc" ∷ SI_mtcc ∗
    "Hmpie" ∷ MPIE_auth (ls_mpie ls) ∗
    "Hmtdc" ∷ mtdc_auth (ls_mtdc ls) ∗
    "%Hmtdc_m" ∷ ⌜mtdc_match (ls_mtdc ls) (ls_vmtdc ls)⌝ ∗
    "Hlent" ∷ mtdc_clause (ls_mtdc ls) ∗
    "Hmie" ∷ MIE_auth (ls_mie ls) ∗
    "%Hlsh" ∷ ⌜ls_sh ls !! mtdc = None ∧ ls_sh ls !! mstatus = None⌝ ∗
    "Hmshwmb_a" ∷ mshwmb_auth (ls_hwmb ls) ∗
    "Hmshwm_a" ∷ mshwm_auth (ls_hwm ls) ∗
    "Hpend_si" ∷ pend_si (ls_pend ls) ∗
    "Hlent_a" ∷ lent_auth (ls_lent ls) ∗
    "Hzone" ∷ hwm_zone (hc_of (ls_hwmb ls) (ls_pend ls)) (ls_hwm ls) (ls_lent ls) ∗
    "%Hlsh_hwm" ∷ ⌜ls_sh ls !! mshwm = None ∧ ls_sh ls !! mshwmb = None⌝.
End state_interp.

(** The context-switch thread's interrupt clause. At [CtxK], interrupts are
    disabled, or half of the PC fragment is parked there (after a resuming
    [mret]); at [UserK], [True]. *)
Definition ctx_irq_si `{MachineParameters} {Σ} {ceriseg : ceriseG Σ} (k : kind)
    (σ : ExecConf) : iProp Σ :=
  match k with
  | UserK => True
  | CtxK => ⌜mie_st σ = InterruptDisabled⌝ ∨ ∃ lpc, PC_fragq (DfracOwn (1/2)) lpc
  end.

(** * The HWM restore window of the context-switch thread

    The window between the two writes of the resume path
    ([csrw mshwm, ra] at [a1], [csrw mshwmb, ra] at [a3]): MSHWMB is still
    the parked thread's, MSHWM the resumed thread's, and the zone is stated
    at the target base. While it is open, the PC is at the load [a2] or at
    the closing write [a3 = a2 + 1], both read-only, and the PCC and [csp]
    make both succeed. The addresses are existentials: the program logic
    needs no switcher parameter. *)

(** The decoded [csrw mshwmb, ra]. *)
Definition csrw_mshwmb_ra : instr := SpecialRW cnull mshwmb (inr cra).

(** [i] writes MSHWMB: a [csrw] to MSHWMB from a register other than
    [cnull], or from an immediate. *)
Definition writes_mshwmb (i : instr) : bool :=
  match i with
  | SpecialRW _ sr (inr r) => bool_decide (sr = mshwmb) && bool_decide (r ≠ cnull)
  | SpecialRW _ sr (inl _) => bool_decide (sr = mshwmb)
  | _ => false
  end.

(** The two instructions of the open window: a load, or a write to
    MSHWMB. *)
Definition hwm_window_instr (i : instr) : Prop :=
  (∃ dst src off, i = CLoad dst src off) ∨ writes_mshwmb i = true.

(** The PC of [σ] is at [a2] or [a3 = a2 + 1], with a correct PCC that has
    the system-register permission and bounds over [a2] and [a3], and [a3]
    has a successor. *)
Definition pc_in_window (σ : ExecConf) (a2 a3 : Addr) : Prop :=
  ∃ (p : Perm) (g : Locality) (b e a a4 : Addr),
    pcc σ = Cap p g b e a ∧
    (a2 + 1)%a = Some a3 ∧ (a3 + 1)%a = Some a4 ∧
    (a = a2 ∨ a = a3) ∧
    isCorrectPC (Cap p g b e a2) ∧ isCorrectPC (Cap p g b e a3) ∧
    has_sreg_access p = true.

(** [csp] of [σ] is a tagged, unsealed capability with the load permission,
    [csp + off] is in its bounds, mapped in memory, not a memory-mapped
    device, and a loaded heap capability has a shadow entry. *)
Definition csp_load_ok `{MachineParameters} (σ : ExecConf) (off : Z) : Prop :=
  ∃ (p : Perm) (g : Locality) (b e a ea : Addr) (w : Word),
    reg σ !!ᵣ csp = Some (Cap p g b e a) ∧
    readAllowed p = true ∧ (a + off)%a = Some ea ∧ withinBounds b e ea = true ∧
    is_mmio_address ea = false ∧ mem σ !! ea = Some w ∧
    (∀ base, heap_cap_base w = Some base → is_Some (shadowtbl σ !! base)).

(** The capability [wcsp] loads at [ea], [off] past its address: tagged,
    unsealed, with the load permission, [ea] in its bounds. *)
Definition csp_cap_load_ok (wcsp : LWord) (off : Z) (ea : Addr) : Prop :=
  ∃ (p : Perm) (g : Locality) (b e a : Addr),
    wcsp.(lw) = Cap p g b e a ∧
    readAllowed p = true ∧ (a + off)%a = Some ea ∧ withinBounds b e ea = true.

(** The integer of the physical MSHWMB of [σ]. *)
Definition phys_mshwmb (σ : ExecConf) : Z :=
  match sreg σ !! mshwmb with
  | Some w => get_a w
  | None => 0
  end.

(** * The window clause across a step

    A step keeps MSHWMB unless it writes it with the system-register
    permission. While the window is open, the instruction at the PC is the
    load at [a2] or the closing write at [a3]. The load cannot fault: the
    window's PCC and [csp] facts make it succeed, with the PC at [a3] and the
    facts kept. *)
Section window_step.
  Context `{MP: MachineParameters}.

  Lemma exec_mshwmb_kept i p φ :
    (has_sreg_access p = true → writes_mshwmb i = false) →
    sreg (exec i p φ).2 !! mshwmb = sreg φ !! mshwmb.
  Proof.
    intros Hw. rewrite /exec. destruct (exec_opt i p φ) as [c|] eqn:Hexec; last done.
    rewrite /exec_opt /exec_jcond /mmio_load /mmio_store in Hexec.
    destruct i; cbn -[enter_exc] in Hexec.
    all: repeat (case_match || simplify_option_eq); simplify_eq/=; try done.
    all: try match goal with
      | Hup : advancePC _ _ = Some _ |- _ => rewrite (advancePC_sreg _ _ _ Hup) /=
      | Hup : nextPC _ = Some _ |- _ => rewrite (advancePC_sreg _ _ _ Hup) /=
      end.
    all: try done.
    all: rewrite ?lookup_insert_ne ?lookup_hwm_update_ne //.
    (* The write to MSHWMB, with the permission. *)
    all: exfalso; by specialize (Hw eq_refl).
  Qed.

  Lemma exec_phys_mshwmb i p φ :
    (has_sreg_access p = true → writes_mshwmb i = false) →
    phys_mshwmb (exec i p φ).2 = phys_mshwmb φ.
  Proof. intros Hw. by rewrite /phys_mshwmb exec_mshwmb_kept. Qed.

  Lemma window_load_step (σ σ' : ExecConf) (c : ConfFlag) p g b e a2 a3 off :
    pcc σ = Cap p g b e a2 →
    pc_in_window σ a2 a3 →
    csp_load_ok σ off →
    exec (CLoad cra csp off) p σ = (c, σ') →
    c = NextI ∧ pc_in_window σ' a2 a3 ∧ csp_load_ok σ' off ∧ sreg σ' = sreg σ.
  Proof.
    intros Hpc (p' & g' & b' & e' & a & a4 & Hpc' & Ha23 & Ha34 & Ha & Hc2 & Hc3 & Hx)
      (pc & gc & bc & ec & ac & ea & wl & Hcsp & Hra & Hea & Hwb & Hmmio & Hm & Hsh) Hexec.
    rewrite Hpc in Hpc'. simplify_eq.
    rewrite /exec /= Hcsp /= Hea /= Hra Hwb /= Hmmio Hm /= in Hexec.
    assert (∃ wd, (NextI, (σ .[cra :=ᵣ wd]) .[PC := Cap p' g' b' e' a3]) = (c, σ'))
      as [wd Hst].
    { destruct (heap_cap_base wl) as [base|] eqn:Hbase.
      - destruct (Hsh base eq_refl) as [stb Hstb]. rewrite Hstb /= in Hexec.
        rewrite /nextPC /advancePC /= Hpc Ha23 in Hexec. by eexists.
      - rewrite /nextPC /advancePC /= Hpc Ha23 in Hexec. by eexists. }
    simplify_eq. split; first done. split_and!.
    - exists p', g', b', e', a3, a4. cbn. split_and!; try done. by right.
    - exists pc, gc, bc, ec, ac, ea, wl. cbn. split_and!; try done.
      rewrite /update_reg /=. by rewrite lookup_reg_insert_reg_ne.
    - done.
  Qed.

  Lemma phys_mshwmb_enter_exc cv σ : phys_mshwmb (enter_exc cv σ) = phys_mshwmb σ.
  Proof. rewrite /phys_mshwmb /enter_exc /=. by rewrite !lookup_insert_ne. Qed.

End window_step.

(** The window is open at [σ]. *)
Definition hwm_window `{MachineParameters} {Σ} {ceriseg : ceriseG Σ} (σ : ExecConf) : iProp Σ :=
  ∃ (a2 a3 : Addr) (off : Z) (w2 w3 : LWord),
    "%Hdec_w" ∷ ⌜decodeInstrW w2.(lw) = CLoad cra csp off ∧ decodeInstrW w3.(lw) = csrw_mshwmb_ra⌝ ∗
    "#Ha2" ∷ a2 ↦ₐ□ w2 ∗
    "#Ha3" ∷ a3 ↦ₐ□ w3 ∗
    "%Hpc_win" ∷ ⌜pc_in_window σ a2 a3⌝ ∗
    "%Hcsp_ok" ∷ ⌜csp_load_ok σ off⌝.

(** The window clause, kind-keyed as [ctx_irq_si]. At [UserK]: the other
    half of the window, closed, the fragment of the lent set, empty (a user
    thread never opens a window nor holds lent halves), and the stack base
    of the thread, its physical MSHWMB. At [CtxK]: a
    quarter of the window, and the facts of [hwm_window] while it is
    open. *)
Definition hwm_win_si `{MachineParameters} {Σ} {ceriseg : ceriseG Σ} (k : kind)
    (σ : ExecConf) : iProp Σ :=
  match k with
  | UserK => pend_half None ∗ lent_frag ∅ ∗ hwm_base (phys_mshwmb σ)
  | CtxK => ∃ o, pend_cl o ∗ (if o is Some _ then hwm_window σ else True)
  end.

(** The PC [w] is not in an HWM window: it is not a capability with the
    system-register permission. *)
Definition pc_nosr (w : Word) : bool :=
  match w with
  | WSealable (SCap _ p _ _ _ _) => negb (has_sreg_access p)
  | _ => true
  end.

(** From a PC without the system-register permission, the window of the
    context-switch thread is closed: an open window holds a PC with it. *)
Lemma hwm_win_si_ctx_nosr `{MachineParameters} {Σ} {ceriseg : ceriseG Σ} σ :
  pc_nosr (pcc σ) = true →
  hwm_win_si CtxK σ ⊢ pend_cl None.
Proof.
  intros Hnsr. rewrite /hwm_win_si /=. iIntros "(%o & Hcl & Hwin)".
  destruct o as [hbT|]; last by iFrame.
  iNamed "Hwin".
  destruct Hpc_win as (p & g & b & e & a & a4 & Hpc & _ & _ & _ & _ & _ & Hsr).
  exfalso. rewrite Hpc /= Hsr in Hnsr. done.
Qed.

(** The window is closed, for the code of thread kind [k]: [True] at
    [UserK], the code's quarter at [None] at [CtxK]. *)
Definition hwm_closed {Σ} `{!hwmG Σ} (k : kind) : iProp Σ :=
  match k with
  | UserK => True
  | CtxK => pend_frag None
  end.

(** At a user thread, the window is closed. *)
Lemma hwm_closed_user {Σ} `{!hwmG Σ} (th : Thread) :
  th ≠ CtxSwitch → ⊢@{iPropI Σ} hwm_closed (kind_of th).
Proof. intros Hth. destruct th as [n|]; last done. done. Qed.

(** The Iris instance of thread [th], over its thread language: invariants
    for memory, and a state interpretation for (mem,reg), with the total
    register file, the link of the critical sections, the context-switch
    thread's interrupt clause, and the window clause. *)
#[global] Instance memG_irisG `{MachineParameters} {Σ} {th : Thread} {ceriseg : ceriseG Σ}
    {CL : CritLink Σ th} :
  irisGS (tlang (kind_of th)) Σ := {
  iris_invGS := cerise_invG;
  state_interp σ _ κs _ :=
    (cerise_state_interp σ ∗ ⌜dom (reg σ) = all_registers_s⌝ ∗ @crit_link Σ th CL σ ∗
     ctx_irq_si (kind_of th) σ ∗ hwm_win_si (kind_of th) σ)%I;
  fork_post _ := True%I;
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.

(** * The WP of a thread

    [WP e @[th] E {{ Φ }}] is Iris's WP at the instance of thread [th], so
    the rule library and the proof mode apply to it unchanged. *)
Notation "'WP' e '@[' th ] E {{ Φ } }" :=
  (@wp _ _ _ _ (@wp' _ _ _ (memG_irisG (th := th) (ceriseg := ceriseG_of th)))
     NotStuck E e%E Φ)
  (at level 20, th custom thread, e, Φ at level 200,
   format "'[hv' 'WP'  e  '/' '@[' th ]  E  '/' {{  Φ  } } ']'") : bi_scope.
Notation "'WP' e '@[' th ] {{ Φ } }" :=
  (@wp _ _ _ _ (@wp' _ _ _ (memG_irisG (th := th) (ceriseg := ceriseG_of th)))
     NotStuck ⊤ e%E Φ)
  (at level 20, th custom thread, e, Φ at level 200,
   format "'[hv' 'WP'  e  '/' '@[' th ]  '/' {{  Φ  } } ']'") : bi_scope.
Notation "'WP' e '@[' th ] E {{ v , Q } }" :=
  (@wp _ _ _ _ (@wp' _ _ _ (memG_irisG (th := th) (ceriseg := ceriseG_of th)))
     NotStuck E e%E (λ v, Q))
  (at level 20, th custom thread, e, Q at level 200, v at level 200 as pattern,
   format "'[hv' 'WP'  e  '/' '@[' th ]  E  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e '@[' th ] {{ v , Q } }" :=
  (@wp _ _ _ _ (@wp' _ _ _ (memG_irisG (th := th) (ceriseg := ceriseG_of th)))
     NotStuck ⊤ e%E (λ v, Q))
  (at level 20, th custom thread, e, Q at level 200, v at level 200 as pattern,
   format "'[hv' 'WP'  e  '/' '@[' th ]  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

(** A fancy update stated with only a base in scope is at the base's
    [cb_invG]. Iris's [elim_modal_fupd_wp] states the update at the WP's
    [iris_invGS], which typeclass search does not unify with [cb_invG]:
    this instance eliminates such an update in the WP of any thread. *)
#[global] Instance elim_modal_base_fupd_wp `{MP : MachineParameters} {Σ}
    {ceriseb : ceriseBaseG Σ} (th : Thread) {CL : CritLink Σ th} p E e (P : iProp Σ) Φ :
  ElimModal True p false
    (@fupd _ (@bi_fupd_fupd _ (@uPred_bi_fupd HasLc Σ (@cb_invG Σ ceriseb))) E E P) P
    (WP e @[th] E {{ Φ }}) (WP e @[th] E {{ Φ }}).
Proof.
  exact (elim_modal_fupd_wp (irisGS_gen0 := memG_irisG (th := th) (ceriseg := ceriseG_of th))
           p NotStuck E e P Φ).
Qed.

(** The same for a fancy update at the invariants of an instance [ceriseg],
    in a WP of the thread at [ceriseg]. Not an instance: a file that needs it
    declares it locally. *)
Lemma elim_modal_cerise_fupd_wp `{MP : MachineParameters} `{ceriseg : ceriseG Σ} {th : Thread}
    {CL : CritLink Σ th} p E e (P : iProp Σ) Φ :
  ElimModal True p false
    (@fupd _ (@bi_fupd_fupd _ (@uPred_bi_fupd HasLc Σ (@cerise_invGS Σ ceriseg))) E E P) P
    (WP e @ E {{ Φ }}) (WP e @ E {{ Φ }}).
Proof.
  exact (elim_modal_fupd_wp (irisGS_gen0 := memG_irisG (th := th)) p NotStuck E e P Φ).
Qed.

(** Texan triples of thread [th], as Iris's. *)
Notation "'{{{' P } } } e '@[' th ] E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @[th] E {{ Φ }})%I
  (at level 20, th custom thread, x closed binder, y closed binder,
   format "'[hv' {{{  '[' P ']'  } } }  '/  ' e  '/' '@[' th ]  E  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q ']'  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e '@[' th ] {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @[th] {{ Φ }})%I
  (at level 20, th custom thread, x closed binder, y closed binder,
   format "'[hv' {{{  '[' P ']'  } } }  '/  ' e  '/' '@[' th ]  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q ']'  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e '@[' th ] E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @[th] E {{ Φ }})%I
  (at level 20, th custom thread,
   format "'[hv' {{{  '[' P ']'  } } }  '/  ' e  '/' '@[' th ]  E  '/' {{{  '[' RET  pat ;  '/' Q ']'  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e '@[' th ] {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @[th] {{ Φ }})%I
  (at level 20, th custom thread,
   format "'[hv' {{{  '[' P ']'  } } }  '/  ' e  '/' '@[' th ]  '/' {{{  '[' RET  pat ;  '/' Q ']'  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e '@[' th ] E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @[th] E {{ Φ }})
  (at level 20, th custom thread, x closed binder, y closed binder,
   format "'[hv' {{{  '[' P ']'  } } }  '/  ' e  '/' '@[' th ]  E  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q ']'  } } } ']'") : stdpp_scope.
Notation "'{{{' P } } } e '@[' th ] {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @[th] {{ Φ }})
  (at level 20, th custom thread, x closed binder, y closed binder,
   format "'[hv' {{{  '[' P ']'  } } }  '/  ' e  '/' '@[' th ]  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q ']'  } } } ']'") : stdpp_scope.
Notation "'{{{' P } } } e '@[' th ] E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @[th] E {{ Φ }})
  (at level 20, th custom thread,
   format "'[hv' {{{  '[' P ']'  } } }  '/  ' e  '/' '@[' th ]  E  '/' {{{  '[' RET  pat ;  '/' Q ']'  } } } ']'") : stdpp_scope.
Notation "'{{{' P } } } e '@[' th ] {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @[th] {{ Φ }})
  (at level 20, th custom thread,
   format "'[hv' {{{  '[' P ']'  } } }  '/  ' e  '/' '@[' th ]  '/' {{{  '[' RET  pat ;  '/' Q ']'  } } } ']'") : stdpp_scope.

