From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte Require Export fetch assert_compiled.

(** * Specification of the compiled assert library

    The library [griotte_assert] as compiled by the CHERIoT compiler
    ([assert_compiled]), on its own memory: its PCC region holds the
    import table (the switcher slot, then the capability to the flag),
    then the code, entered at the word [2] through a [Sentry Inherit]. The
    arguments are in [ca0] and [ca1]; it returns through [cra] ([ret]).
    When they differ, it sets the flag to [1]. *)

(** The layout of the compiled library: its PCC region [[b, e)] and its
    flag. *)
Class assertCompiledLayout : Type :=
  mkAssertCompiledLayout {
      b_assert_compiled : Addr ;
      e_assert_compiled : Addr ;
      a_flag_compiled : Addr ;
    }.

(** The sentry of the entry of the compiled library, which its callers
    import. *)
Definition assert_compiled_entry_of (g : Locality) (b_lib e_lib : Addr) : Word :=
  Sentry Inherit RX g b_lib e_lib (b_lib ^+ Z.of_nat assert_compiled_griotte_assert_offset).

Definition assert_compiled_entry `{assertCompiledLayout} : Word :=
  assert_compiled_entry_of Global b_assert_compiled e_assert_compiled.

Section Assert_compiled_call.
  Context `{MP: MachineParameters}.

  (** The assembled call sequence of a caller: [fetch_asm sym rdst ++
      [jalr cra rdst]], where [off] is the resolved offset of the import
      [sym] from the address of the first instruction. *)
  Definition assert_compiled_call (off : Z) (rdst : RegName) : list instr :=
    fetch off rdst ++ [Jalr cra rdst].
  Definition assert_compiled_call_instrs (off : Z) (rdst : RegName) : list Word :=
    encodeInstrsW (assert_compiled_call off rdst).
End Assert_compiled_call.

Section Assert_compiled_spec.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ}
      {MP: MachineParameters}
      {th : Thread} {CL : CritLink Σ th} {CR : CritRoute Σ th CL}
  .

  (** The read-only part of the compiled library: the import table (some
      word in the switcher slot, the capability to the flag) and the code,
      after it. *)
  Definition assert_compiled_static (b_lib e_lib a_flag : Addr) : iProp Σ :=
    ⌜is_heap_address b_lib = false⌝ ∗
    ⌜disjoint_from_shadow b_lib e_lib⌝ ∗
    ⌜(b_lib + (Z.of_nat assert_compiled_griotte_assert_offset
                + length assert_compiled_code))%a = Some e_lib⌝ ∗
    ⌜is_Some (a_flag + 1)%a⌝ ∗
    ⌜is_heap_address a_flag = false⌝ ∗
    ⌜is_shadow_address a_flag = false⌝ ∗
    (∃ w_switcher, b_lib ↦ₐ□ w_switcher) ∗
    (b_lib ^+ 1) ↦ₐ□ Cap RW Global a_flag (a_flag ^+ 1) a_flag ∗
    codefrag_pers (b_lib ^+ Z.of_nat assert_compiled_griotte_assert_offset)
      assert_compiled_code.

  #[global] Instance assert_compiled_static_persistent b_lib e_lib a_flag :
    Persistent (assert_compiled_static b_lib e_lib a_flag).
  Proof. apply _. Qed.

  (** The library, entered at its entry with equal arguments: it returns
      through [cra], the flag untouched. *)
  Lemma assert_compiled_success_spec
    (pc_g : Locality) (b_lib e_lib a_flag : Addr)
    (n1 n2 : Z) (wret : Word) (b : InterruptStatus)
    (φ : tval (kind_of th) → iProp Σ) :
    n1 = n2 →
    jalr_target_ok cnull cra wret = true →
    route_pre th (default b (jalr_target_mie wret)) →
    route_pre th b →
    assert_compiled_static b_lib e_lib a_flag ∗
    PC ↦ₚ Cap RX pc_g b_lib e_lib (b_lib ^+ Z.of_nat assert_compiled_griotte_assert_offset) ∗
    cra ↦ᵣ wret ∗
    ca0 ↦ᵣ WInt n1 ∗
    ca1 ↦ᵣ WInt n2 ∗
    MIE ↦ₜ b ∗
    held b ∗
    ▷ (PC ↦ₚ updatePcPerm wret ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ WInt n1 ∗
       ca1 ↦ᵣ WInt n2 ∗
       MIE ↦ₜ default b (jalr_target_mie wret) ∗
       held (default b (jalr_target_mie wret)) -∗
       WP Exec {{ φ }})
    ⊢ WP Exec {{ φ }}.
  Proof.
    iIntros (Heq Htgt Hroute' Hpre)
      "(#Hassert & HPC & Hcra & Hca0 & Hca1 & Hmie & Hheld & Hφ)".
    iDestruct "Hassert" as "(%Hnot_heap & %Hshadow & %He_lib & %Hflag_end & %Hflag_not_heap
      & %Hflag_not_shadow & _ & _ & Hprog)".
    rewrite /assert_compiled_griotte_assert_offset.
    iEval (rewrite /assert_compiled_code /assert_compiled_instrs_n /assert_compiled_assembled /=)
      in "Hprog".
    codefrag_facts "Hprog".
    assert ((b_lib + 8)%a = Some e_lib) as He_lib' by (rewrite -He_lib; reflexivity).
    assert (SubBounds b_lib e_lib (b_lib ^+ 2%nat) (b_lib ^+ 2%nat ^+ 6%nat))
      as HsubBounds by solve_addr.
    subst n2.
    (* Jeq 5 ca0 ca1. *)
    iInstr "Hprog".
    (* Jalr cnull cra. *)
    iInstr "Hprog".
    1: { intros _. exact Hroute'. }
    iApply "Hφ"; iFrame "∗".
  Qed.

  (** The library, entered at its entry with different arguments: it sets
      the flag to [1] and returns through [cra]. *)
  Lemma assert_compiled_failure_spec
    (pc_g : Locality) (b_lib e_lib a_flag : Addr)
    (n1 n2 : Z) (wret : Word) (wflag : LWord) (b : InterruptStatus)
    (φ : tval (kind_of th) → iProp Σ) :
    n1 ≠ n2 →
    jalr_target_ok cnull cra wret = true →
    route_pre th (default b (jalr_target_mie wret)) →
    route_pre th b →
    assert_compiled_static b_lib e_lib a_flag ∗
    PC ↦ₚ Cap RX pc_g b_lib e_lib (b_lib ^+ Z.of_nat assert_compiled_griotte_assert_offset) ∗
    cra ↦ᵣ wret ∗
    ca0 ↦ᵣ WInt n1 ∗
    ca1 ↦ᵣ WInt n2 ∗
    a_flag ↦ₐ wflag ∗
    MIE ↦ₜ b ∗
    held b ∗
    ▷ (PC ↦ₚ updatePcPerm wret ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ Cap RW Global a_flag (a_flag ^+ 1) a_flag ∗
       ca1 ↦ᵣ WInt 1 ∗
       a_flag ↦ₐ WInt 1 ∗
       MIE ↦ₜ default b (jalr_target_mie wret) ∗
       held (default b (jalr_target_mie wret)) -∗
       WP Exec {{ φ }})
    ⊢ WP Exec {{ φ }}.
  Proof.
    iIntros (Hneq Htgt Hroute' Hpre)
      "(#Hassert & HPC & Hcra & Hca0 & Hca1 & Hflag & Hmie & Hheld & Hφ)".
    iDestruct "Hassert" as "(%Hnot_heap & %Hshadow & %He_lib & %Hflag_end & %Hflag_not_heap
      & %Hflag_not_shadow & _ & Hcap & Hprog)".
    rewrite /assert_compiled_griotte_assert_offset.
    iEval (rewrite /assert_compiled_code /assert_compiled_instrs_n /assert_compiled_assembled /=)
      in "Hprog".
    codefrag_facts "Hprog".
    assert ((b_lib + 8)%a = Some e_lib) as He_lib' by (rewrite -He_lib; reflexivity).
    assert (SubBounds b_lib e_lib (b_lib ^+ 2%nat) (b_lib ^+ 2%nat ^+ 6%nat))
      as HsubBounds by solve_addr.
    assert ((n1 =? n2)%Z = false) as Hneqb by lia.
    (* Jeq 5 ca0 ca1. *)
    iInstr "Hprog".
    assert (is_shadow_address (b_lib ^+ 1) = false) as Hcap_shadow.
    { eapply disjoint_from_shadow_not_in; eauto. solve_addr. }
    (* Auipcc ca0 (-2). *)
    iInstr "Hprog".
    1: { instantiate (1 := b_lib ^+ 1). solve_addr. }
    (* CLoad ca0 ca0 0. *)
    iInstr "Hprog".
    1: { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hflag_not_heap /=.
         reflexivity. }
    1: { solve_addr. }
    iEval (cbn) in "Hca0".
    (* Mov ca1 1. *)
    iInstr "Hprog".
    (* Store ca0 ca1 0. *)
    iInstr "Hprog".
    (* Jalr cnull cra. *)
    iInstr "Hprog".
    1: { intros _. exact Hroute'. }
    iApply "Hφ"; iFrame "∗".
  Qed.

  (** The call sequence of a caller, [fetch_asm sym rdst ++ [jalr cra
      rdst]], with equal integer arguments in [ca0] and [ca1]: it fetches
      the entry of the library from the import table of the caller, calls
      it, and the library returns right after the call, the flag
      untouched. [cra] holds the return sentry written by [jalr], [rdst]
      the entry. *)
  Lemma assert_compiled_call_success_spec
    (n off : Z) (rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (g_lib : Locality) (b_lib e_lib a_flag : Addr)
    (n1 n2 : Z) (wdst wcra : LWord) (dq : dfrac) (b : InterruptStatus)
    (φ : tval (kind_of th) → iProp Σ) :

    let call := assert_compiled_call_instrs off rdst in
    let a_last := (pc_a ^+ length call) in
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a a_last →
    (pc_a + off)%a = Some (pc_b ^+ n) →
    withinBounds pc_b pc_e (pc_b ^+ n) = true →
    disjoint_from_shadow pc_b pc_e →
    rdst ≠ cnull →

    n1 = n2 →
    route_pre th b →
    assert_compiled_static b_lib e_lib a_flag ∗
    PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a ∗
    rdst ↦ᵣ wdst ∗
    cra ↦ᵣ wcra ∗
    ca0 ↦ᵣ WInt n1 ∗
    ca1 ↦ᵣ WInt n2 ∗
    MIE ↦ₜ b ∗
    held b ∗
    codefrag_pers pc_a call ∗
    (pc_b ^+ n) ↦ₐ{dq} assert_compiled_entry_of g_lib b_lib e_lib ∗
    ▷ (PC ↦ₚ Cap pc_p pc_g pc_b pc_e a_last ∗
       rdst ↦ᵣ load_word pc_p (assert_compiled_entry_of g_lib b_lib e_lib) ∗
       cra ↦ᵣ Sentry (ret_kind b) pc_p pc_g pc_b pc_e a_last ∗
       ca0 ↦ᵣ WInt n1 ∗
       ca1 ↦ᵣ WInt n2 ∗
       MIE ↦ₜ b ∗
       held b ∗
       codefrag_pers pc_a call ∗
       (pc_b ^+ n) ↦ₐ{dq} assert_compiled_entry_of g_lib b_lib e_lib -∗
       WP Exec {{ φ }})
    ⊢ WP Exec {{ φ }}.
  Proof.
    intros call a_last; subst call a_last.
    iIntros (Hpc_exec HsubBounds Hoff Hinbounds Hcode_shadow Hrdst_cnull Heq Hpre)
      "(#Hassert & HPC & Hrdst & Hcra & Hca0 & Hca1 & Hmie & Hheld & #Hcode
        & Hpc_bn & Hφ)".
    iAssert (⌜is_heap_address b_lib = false⌝)%I as %Hlib_not_heap.
    { by iDestruct "Hassert" as "[$ _]". }
    codefrag_facts "Hcode".
    assert (is_shadow_address (pc_b ^+ n) = false) as Himport_shadow.
    { eapply disjoint_from_shadow_not_in; eauto. }
    (* Auipcc rdst off. *)
    iInstr "Hcode".
    (* CLoad rdst rdst 0. *)
    iInstr "Hcode".
    1: { rewrite /assert_compiled_entry_of /is_heap_cap /heap_cap_base /memory_cap_base /=
           Hlib_not_heap /=.
         reflexivity. }
    (* The entry, loaded through the PC: a deep-local PC makes it local. *)
    assert (load_word pc_p (assert_compiled_entry_of g_lib b_lib e_lib) =
              Sentry Inherit RX (if isDL pc_p then Local else g_lib) b_lib e_lib
                (b_lib ^+ Z.of_nat assert_compiled_griotte_assert_offset)) as Hentry.
    { rewrite /load_word /assert_compiled_entry_of. by destruct (isDL pc_p), (isDRO pc_p). }
    iEval (rewrite /lload_word /lift_word Hentry) in "Hrdst".
    iEval (rewrite Hentry) in "Hφ".
    iDestruct (regname_neq with "Hrdst Hcra") as %Hrdst_cra.
    (* Jalr cra rdst. *)
    iInstr "Hcode".
    iEval (cbn) in "HPC".
    rewrite (_ : default b (jalr_target_mie
                              (Sentry Inherit RX (if isDL pc_p then Local else g_lib) b_lib e_lib
                                 (b_lib ^+ Z.of_nat assert_compiled_griotte_assert_offset)))
                 = b); last by destruct b.
    iApply (assert_compiled_success_spec with "[-]"); last iFrame "∗ Hassert"; try done.
    all: try (by destruct b).
    iNext; iIntros "(HPC & Hcra & Hca0 & Hca1 & Hmie & Hheld)".
    (* The return sentry restores the posture [b]. *)
    rewrite (_ : default b (jalr_target_mie (Sentry (ret_kind b) pc_p pc_g pc_b pc_e (pc_a ^+ 3)))
                 = b); last by destruct b.
    replace (pc_a ^+ length (assert_compiled_call_instrs off rdst)) with (pc_a ^+ 3)
      by (cbn; solve_addr).
    iEval (cbn) in "HPC".
    iApply "Hφ"; iFrame "∗ Hcode".
  Qed.

End Assert_compiled_spec.

Section assert_compiled_thread_indep.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}.

  (** The static part of the compiled library is the same at any two
      threads. *)
  Lemma assert_compiled_static_thread_indep (t t' : Thread) (b_lib e_lib a_flag : Addr) :
    assert_compiled_static (ceriseg := ceriseG_of t) b_lib e_lib a_flag ⊣⊢
    assert_compiled_static (ceriseg := ceriseG_of t') b_lib e_lib a_flag.
  Proof.
    rewrite /assert_compiled_static.
    setoid_rewrite (codefrag_pers_thread_indep t t').
    setoid_rewrite (pointsto_pers_thread_indep t t').
    reflexivity.
  Qed.
End assert_compiled_thread_indep.
