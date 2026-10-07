From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From griotte Require Import sts_multiple_updates.
From griotte Require Import logrel_binary memory_region memory_region_binary rules proofmode_binary.
From griotte Require Import region_invariants_revocation_binary.
From griotte Require Import bitblast.
From griotte Require Export switcher.
From griotte Require Export clear_stack_spec_binary clear_registers_spec_binary.

(** * Switcher invariant and entry points of the binary model

    Both runs execute the same switcher, at the same addresses, with the same
    trusted stack layout. Each run has its own switcher state: its own
    [mtdc] system register, its own trusted stack, and its own logical call
    stack. The switcher invariant of the binary model holds both of them,
    see [switcher_inv] (implementation run) and [switcher_inv_spec]
    (specification run).

    The entry points sealed by the switcher's otype are described by pairs
    of words, but only identical pairs are considered for now: both runs
    load the same export tables. *)

Section Switcher_preamble.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO (Word * Word)) -n> iPropO Σ).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Lemma is_switcher_entry_point_call :
    is_switcher_entry_point (WSentry XSRW_ Local b_switcher e_switcher a_switcher_call) = true.
  Proof.
    rewrite /is_switcher_entry_point.
    rewrite bool_decide_eq_true_2; first done.
    by left.
  Qed.

  Lemma is_switcher_entry_point_return :
    is_switcher_entry_point (WSentry XSRW_ Local b_switcher e_switcher a_switcher_return) = true.
  Proof.
    rewrite /is_switcher_entry_point.
    rewrite bool_decide_eq_true_2; first done.
    by right.
  Qed.

  Lemma encode_entry_point_eq_nargs nargs off_entry :
    (0 ≤ nargs ≤ 7)%Z -> ( (Z.land (encode_entry_point nargs off_entry) 7)) = nargs.
  Proof.
    intros.
    rewrite /encode_entry_point.
    bitblast.
    destruct (decide (nargs = 0)%Z); simplify_eq; first bitblast.
    destruct (decide (nargs = 1)%Z); simplify_eq; first bitblast.
    destruct (decide (nargs = 2)%Z); simplify_eq; first bitblast.
    destruct (decide (nargs = 3)%Z); simplify_eq; first bitblast.
    destruct (decide (nargs = 4)%Z); simplify_eq; first bitblast.
    destruct (decide (nargs = 5)%Z); simplify_eq; first bitblast.
    destruct (decide (nargs = 6)%Z); simplify_eq; first bitblast.
    destruct (decide (nargs = 7)%Z); simplify_eq; first bitblast.
    lia.
  Qed.

  Lemma encode_entry_point_eq_off nargs off_entry :
    ( (encode_entry_point nargs off_entry ≫ 3)%Z) = off_entry.
  Proof.
    intros.
    rewrite /encode_entry_point.
    bitblast.
  Qed.

  (** Namespaces of the invariants of the export tables *)
  Definition export_tableN (Cname : namespace) : namespace := nroot .@ "export_tableN" .@ Cname.
  Definition export_table_PCCN (Cname : namespace) : namespace := (export_tableN Cname) .@ "PCC".
  Definition export_table_CGPN (Cname : namespace) : namespace := (export_tableN Cname) .@ "CGP".
  Definition export_table_entryN (Cname : namespace) (a : Addr) : namespace :=
    (export_tableN Cname) .@ "entry" .@ a.

  (** [execute_entry_point_register] describes the register files of both
      runs after jumping to the callee, at the end of the switcher-call.
      [PC] and [cgp] contain the callee compartment's code and data
      capabilities, [wpcc] and [wcgp], given separately for each run.
      [csp] contains the callee's stack frame [wstk], the same in both runs:
      the stack pointer always comes from a caller that is either untrusted,
      or calls an untrusted compartment.
      The argument registers are related, and all other registers contain
      zeroes in both runs. *)
  Program Definition execute_entry_point_register (wpcc wcgp : Word * Word) (wstk : Word) (nargs : nat) :
    (WORLD -n> (leibnizO CmptName) -n> (leibnizO (Reg * Reg)) -n> iPropO Σ) :=
    λne (W : WORLD) (C : CmptName) (regs : leibnizO (Reg * Reg)),
      (full_map regs.1
       ∧ full_map regs.2
       ∧ ⌜ regs.1 !! PC = Some wpcc.1 ⌝
       ∧ ⌜ regs.2 !! PC = Some wpcc.2 ⌝
       ∧ ⌜ regs.1 !! cgp = Some wcgp.1 ⌝
       ∧ ⌜ regs.2 !! cgp = Some wcgp.2 ⌝
       ∧ ⌜ regs.1 !! cra = Some (WSentry XSRW_ Local b_switcher e_switcher a_switcher_return) ⌝
       ∧ ⌜ regs.2 !! cra = Some (WSentry XSRW_ Local b_switcher e_switcher a_switcher_return) ⌝
       ∧ ⌜ regs.1 !! csp = Some wstk ⌝
       ∧ ⌜ regs.2 !! csp = Some wstk ⌝
       ∗ interp W C (wstk, wstk)
       ∗ (∀ (r : RegName) (v1 v2 : Word),
            ⌜r ∈ (dom_arg_rmap nargs)⌝ → ⌜regs.1 !! r = Some v1⌝ → ⌜regs.2 !! r = Some v2⌝ →
            interp W C (v1, v2))
       ∗ (∀ (r : RegName) (v : Word),
            ⌜r ∉ ({[PC; cra; cgp; csp]} ∪ (dom_arg_rmap nargs) : gset RegName)⌝ →
            ⌜regs.1 !! r = Some v⌝ → ⌜ v = WInt 0 ⌝)
       ∗ (∀ (r : RegName) (v : Word),
            ⌜r ∉ ({[PC; cra; cgp; csp]} ∪ (dom_arg_rmap nargs) : gset RegName)⌝ →
            ⌜regs.2 !! r = Some v⌝ → ⌜ v = WInt 0 ⌝)
      )%I.
  Solve All Obligations with solve_proper.

  (** [csp_sync] relates the stack pointer of the caller with the stack
      pointer of the callee, in both runs: the topmost pair of frames records
      the caller's stack pointer [a_stk'] and the end of its stack [e_stk']. *)
  Definition csp_sync (stk : cstack_pair) (a_stk' e_stk' : Addr) :=
    match stk with
    | frm::_ =>
        frm.1.(a_stk) = a_stk'
        ∧ frm.1.(e_stk) = e_stk'
        ∧ frm.2.(a_stk) = a_stk'
        ∧ frm.2.(e_stk) = e_stk'
    | _ => True
    end
  .

  (** [execute_entry_point] matches the states of both machines after the
      execution of the switcher-call routine. It is the binary counterpart of
      the unary [execute_entry_point]: the callee receives the stack frame
      [[a_stk+4, e_stk)] in both runs, the pair of call stacks [stk], and
      both runs are ready to execute the callee. *)
  Program Definition execute_entry_point (wpcc wcgp : Word * Word) (nargs : nat) :
    (WORLD -n> (leibnizO CmptName) -n> iPropO Σ) :=
    (λne (W : WORLD) (C : CmptName),
      ∀ (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName) (regs1 regs2 : Reg) (a_stk e_stk : Addr),
       let a_stk4 := (a_stk ^+4)%a in
       ( spec_ctx
         ∗ interp_continuation stk Ws Cs
         ∗ ⌜frame_match Ws Cs stk W C⌝
         ∗ (execute_entry_point_register wpcc wcgp (WCap RWL Local a_stk4 e_stk a_stk4) nargs W C
              (regs1, regs2))
         ∗ registers_pointsto regs1
         ∗ spec_registers_pointsto regs2
         ∗ ⤇ Seq (Instr Executable)
         ∗ world_interp W C
         ∗ ⌜csp_sync stk a_stk e_stk ∧ a_stk = (a_stk4 ^+ -4)%a⌝
         ∗ cstack_frag (map fst stk)
         ∗ cstack_frag_spec (map snd stk)
         ∗ na_own cerise_nais ⊤
           -∗ interp_conf W C)
    )%I.
  Solve All Obligations with solve_proper.

  (** [ot_switcher_prop] is the sealing predicate for the switcher's otype.
      It relates two identical entry points: read-only capabilities pointing
      to an entry of a compartment's export table, which holds the same
      words in both runs. The invariants of the export table hold the
      points-to predicates of both runs. *)
  Program Definition ot_switcher_prop : V :=
    λne (W : WORLD) (C : CmptName) (ww : leibnizO (Word * Word)),
       (∃ (g_tbl : Locality) (b_tbl e_tbl a_tbl : Addr)
          (bpcc epcc : Addr)
          (bcgp ecgp : Addr)
          (nargs : nat) (off : Z)
          (Cname : namespace)
         ,
           ⌜ ww.1 = WCap RO g_tbl b_tbl e_tbl a_tbl ⌝
           ∗ ⌜ ww.2 = ww.1 ⌝
           ∗ ⌜ (b_tbl <= a_tbl < e_tbl)%a ⌝
           ∗ ⌜ (b_tbl < (b_tbl ^+1))%a ⌝
           ∗ ⌜ ((b_tbl ^+1) < a_tbl)%a ⌝
           ∗ ⌜ (0 <= nargs <= 7 )%nat ⌝
           ∗ inv (export_table_PCCN Cname)
               (b_tbl ↦ₐ WCap RX Global bpcc epcc bpcc ∗ b_tbl ↣ₐ WCap RX Global bpcc epcc bpcc)
           ∗ inv (export_table_CGPN Cname)
               ((b_tbl ^+ 1)%a ↦ₐ WCap RW Global bcgp ecgp bcgp
                ∗ (b_tbl ^+ 1)%a ↣ₐ WCap RW Global bcgp ecgp bcgp)
           ∗ inv (export_table_entryN Cname a_tbl)
               (a_tbl ↦ₐ WInt (encode_entry_point (Z.of_nat nargs) off)
                ∗ a_tbl ↣ₐ WInt (encode_entry_point (Z.of_nat nargs) off))
           ∗ (seal_capability ww.1 ot_switcher) ↦□ₑ nargs
           ∗ □ ( ∀ W', ⌜related_sts_priv_world W W'⌝ →
                   ▷ (execute_entry_point
                            (WCap RX Global bpcc epcc (bpcc ^+ off)%a, WCap RX Global bpcc epcc (bpcc ^+ off)%a)
                            (WCap RW Global bcgp ecgp bcgp, WCap RW Global bcgp ecgp bcgp)
                            nargs
                            W' C))
      )%I.
  Solve All Obligations with solve_proper.

  Definition ot_switcher_propC : (WORLD * CmptName * (Word * Word)) -> iPropI Σ :=
    safeC ot_switcher_prop.

  Lemma persistent_cond_ot_switcher :
    persistent_cond ot_switcher_prop.
  Proof. intros [ [] ] ; cbn; apply _. Qed.

  Lemma mono_priv_ot_switcher (C : CmptName) (ww : Word * Word) :
    ⊢ future_priv_mono C ot_switcher_propC ww.
  Proof.
    iIntros (W W' Hrelated_W_W').
    iModIntro.
    iIntros "Hot_switcher".
    iEval (cbn) in "Hot_switcher".
    iEval (cbn).
    iDestruct "Hot_switcher" as
      (g_tbl b_tbl e_tbl a_tbl bpcc epcc bcgp ecgp nargs off CNAME Hww1 Hww2
       Hatbl Hbtbl Hbtbl1 Hnargs) "(Hinvpcc & Hinvcgp & Hinventry & #Hentry & #Hcont)".
    iFrame "Hinvpcc Hinvcgp Hinventry Hentry".
    iExists _,_.
    repeat (iSplit ; first done).
    iModIntro.
    iIntros (W'' Hrelated_W'_W'').
    iSpecialize ("Hcont" $! W'').
    iApply "Hcont".
    iPureIntro.
    by eapply related_sts_priv_trans_world.
  Qed.

  (** ** Interpretation of the call stacks *)

  (** [cframe_stk_own] and [cframe_interp] link the topmost frame of the
      implementation call stack with the state of the implementation run,
      as in the unary model. *)
  Definition cframe_stk_own (frm : cframe) : iProp Σ :=
    let a_stk := frm.(a_stk) in
    (if (is_untrusted_caller_frm frm)
    then True
    else
      a_stk ↦ₐ frm.(wcs0)
      ∗ (a_stk ^+ 1)%a ↦ₐ frm.(wcs1)
      ∗ (a_stk ^+ 2)%a ↦ₐ frm.(wret)
      ∗ (a_stk ^+ 3)%a ↦ₐ frm.(wcgp))%I.

  Definition cframe_interp (frm : cframe) (a_tstk : Addr) : iProp Σ :=
    let b_stk := frm.(b_stk) in
    let a_stk := frm.(a_stk) in
    let e_stk := frm.(e_stk) in
    a_tstk ↦ₐ WCap RWL Local b_stk e_stk (a_stk ^+ 4)%a ∗
    ⌜ (b_stk <= a_stk)%a ∧ (a_stk ^+ 3 < e_stk)%a ∧ is_Some (a_stk + 4)%a ⌝ ∗
    cframe_stk_own frm%I.

  Fixpoint cstack_interp (cstk : cstack) (a_tstk : Addr) : iProp Σ :=
    (match cstk with
    | [] => a_tstk ↦ₐ WInt 0
    | frm::cstk' => cstack_interp cstk' (a_tstk ^+ -1)%a
                  ∗ cframe_interp frm a_tstk
    end)%I.

  (** Same definitions for the specification run. *)
  Definition cframe_stk_own_spec (frm : cframe) : iProp Σ :=
    let a_stk := frm.(a_stk) in
    (if (is_untrusted_caller_frm frm)
    then True
    else
      a_stk ↣ₐ frm.(wcs0)
      ∗ (a_stk ^+ 1)%a ↣ₐ frm.(wcs1)
      ∗ (a_stk ^+ 2)%a ↣ₐ frm.(wret)
      ∗ (a_stk ^+ 3)%a ↣ₐ frm.(wcgp))%I.

  Definition cframe_interp_spec (frm : cframe) (a_tstk : Addr) : iProp Σ :=
    let b_stk := frm.(b_stk) in
    let a_stk := frm.(a_stk) in
    let e_stk := frm.(e_stk) in
    a_tstk ↣ₐ WCap RWL Local b_stk e_stk (a_stk ^+ 4)%a ∗
    ⌜ (b_stk <= a_stk)%a ∧ (a_stk ^+ 3 < e_stk)%a ∧ is_Some (a_stk + 4)%a ⌝ ∗
    cframe_stk_own_spec frm%I.

  Fixpoint cstack_interp_spec (cstk : cstack) (a_tstk : Addr) : iProp Σ :=
    (match cstk with
    | [] => a_tstk ↣ₐ WInt 0
    | frm::cstk' => cstack_interp_spec cstk' (a_tstk ^+ -1)%a
                  ∗ cframe_interp_spec frm a_tstk
    end)%I.

  (** ** Switcher invariants *)

  (** [switcher_inv] is the state of the switcher in the implementation run:
      the [mtdc] system register pointing to the trusted stack, the code of
      the switcher, the switcher's sealing capability, the trusted stack in
      sync with the logical call stack (authoritative view [cstack_full]),
      and the sealing predicate of the switcher's otype. *)
  Definition switcher_inv : iProp Σ :=
    ∃ (a_tstk : Addr) (cstk : CSTK) (tstk_next : list Word),
     mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk
     ∗ ⌜ (ot_switcher < (ot_switcher ^+1) )%ot ⌝
     ∗ codefrag a_switcher_call switcher_instrs
     ∗ b_switcher ↦ₐ WSealRange (true,true) Global ot_switcher (ot_switcher^+1)%ot ot_switcher
     ∗ [[ (a_tstk ^+1)%a, e_trusted_stack ]] ↦ₐ [[ tstk_next ]]
     ∗ ⌜ (b_trusted_stack <= a_tstk)%a ∧ (a_tstk <= e_trusted_stack)%a ⌝
     ∗ cstack_full cstk
     ∗ ⌜ (b_trusted_stack + length cstk)%a = Some a_tstk ⌝
     ∗ cstack_interp cstk a_tstk
     ∗ seal_pred ot_switcher ot_switcher_propC.

  (** [switcher_inv_spec] is the state of the switcher in the specification
      run. The address [a_tstk] of the top of the trusted stack is linked to
      the length of the specification call stack, as in [switcher_inv]:
      whenever both call stacks have the same length, both runs have the
      same [a_tstk]. *)
  Definition switcher_inv_spec : iProp Σ :=
    ∃ (a_tstk : Addr) (cstk : CSTK) (tstk_next : list Word),
     mtdc ↣ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk
     ∗ spec_codefrag a_switcher_call switcher_instrs
     ∗ b_switcher ↣ₐ WSealRange (true,true) Global ot_switcher (ot_switcher^+1)%ot ot_switcher
     ∗ [[ (a_tstk ^+1)%a, e_trusted_stack ]] ↣ₐ [[ tstk_next ]]
     ∗ ⌜ (b_trusted_stack <= a_tstk)%a ∧ (a_tstk <= e_trusted_stack)%a ⌝
     ∗ cstack_full_spec cstk
     ∗ ⌜ (b_trusted_stack + length cstk)%a = Some a_tstk ⌝
     ∗ cstack_interp_spec cstk a_tstk.

  (** Both runs reach the same trusted stack address whenever their call
      stacks have the same length. *)
  Lemma a_tstk_eq (cstk1 cstk2 : cstack) (a_tstk1 a_tstk2 : Addr) :
    length cstk1 = length cstk2 →
    (b_trusted_stack + length cstk1)%a = Some a_tstk1 →
    (b_trusted_stack + length cstk2)%a = Some a_tstk2 →
    a_tstk1 = a_tstk2.
  Proof. intros Hlen H1 H2. rewrite Hlen in H1. congruence. Qed.

End Switcher_preamble.

(** The switcher invariant of the binary model: one non-atomic invariant
    holding the switcher state of both runs. *)
Notation switcher_inv_binary := (switcher_inv ∗ switcher_inv_spec)%I.
