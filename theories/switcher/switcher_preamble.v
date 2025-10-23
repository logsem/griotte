From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel memory_region rules proofmode.
From cap_machine Require Import multiple_updates region_invariants_revocation.
From cap_machine Require Export switcher.

Section Switcher_preamble.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {cstackg : CSTACKG Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (** Property of capability sealed by the switcher's otype *)
  Definition export_tableN (C : CmptName) : namespace := nroot .@ "export_tableN" .@ C.
  Definition export_table_PCCN (C : CmptName) : namespace := (export_tableN C) .@ "PCC".
  Definition export_table_CGPN (C : CmptName) : namespace := (export_tableN C) .@ "CGP".
  Definition export_table_entryN (C : CmptName) (a : Addr) : namespace :=
    (export_tableN C) .@ "entry" .@ a.

  (** [execute_entry_point_register] describes the register state of the machine
      after jumping to the callee, at the end of the switcher-call.
      [PC] and [cgp] contain the callee compartment's code and data capabilities.
      They don't have to be [interp], and are _not_ [interp]
      when the compartment is one of the trusted ones.

      [cps] contains the callee's stack frame. It has to be [interp] because it always comes from the caller,
      which is usually untrusted.

      Finally, all the register contain some (1) safe values.

      (1) Although we know that they contain zeroes due to the caller's clearing,
          it makes the proofs more annoying, and we never rely on this information anyway.
   *)
  Program Definition execute_entry_point_register (wpcc wcgp wstk : Word) :
    (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ) :=
    λne (W : WORLD) (C : CmptName) (reg : leibnizO Reg),
      (full_map reg
       ∧ ⌜ reg !! PC = Some wpcc ⌝
       ∧ ⌜ reg !! cgp = Some wcgp ⌝
       ∧ ⌜ reg !! cra = Some (WSentry XSRW_ Local b_switcher e_switcher a_switcher_return) ⌝
       ∧ ⌜ reg !! csp = Some wstk ⌝
       ∗ interp W C wstk
       ∗ (∀ (r : RegName) (v : Word), (⌜r ∉ ({[PC; cra; cgp; csp]} : gset RegName)⌝ → ⌜reg !! r = Some v⌝ → interp W C v))
      )%I.
  Solve All Obligations with solve_proper.

  (** [csp_sync] is a small pure side-condition that relates the stack pointer of the caller,
      with the stack pointer of the callee.
      See [execute_entry_point] to understand how they are related.
   *)
  Definition csp_sync (cstk : CSTK) (a_stk e_stk : Addr) :=
    match cstk with
    | frm::_ =>
        get_a frm.(wstk) = Some a_stk
        ∧ get_e frm.(wstk) = Some e_stk
    | _ => True
    end
  .

  (** [execute_entry_point] provides a WP rule matching the state of the machine
      after the execution of call-switcher.

      [execute_entry_point] is somewhat the dual of [interp_cont_exec]:
      - [execute_entry_point] matches the state of the machine after the execution of call-switcher
      - [interp_cont_exec] matches the state of the machine after the execution of return-to-switcher

      It is the WP rule to prove to show that the execution of an entry point is valid.
      In case of known code entry point, it contains all the information available when invoked.
      In case of unknown code entry point, we can show this by validity of
      the code and data capability (see the use of [fundamental] in [ot_switcher_interp]).

      An important point is the use of [csp_sync] and the stack capability [WCap RWL Local a_stk4 e_stk a_stk4].
      If the call stack is not empty, we know that the caller's stack looks like
      [WCap RWL Local b_stk e_stk a_stk] (it is tested by the switcher's call routine).
      The switcher reserves the area `[a_stk, a_stk+4)` for the callee-saved area,
      and passes the rest, i.e. `[a_stk+4, e_stk)`  to the callee.

      [csp_sync] synchronises the caller's stack pointer with the callee stack pointer.
      It's important when proving the functional specification of the return-to-switcher routine,
      because the switcher uses the caller stack pointer to clear (and therefore re-instate) the stack.
      But the caller gives the `revoked_resources` of its own stack pointer.
      Synchronising the caller and callee is important for using the caller's `revoked_resources`
      to re-instate validity of the caller's stack.
      This will become clearer in the proof of [switcher_ret_specification].
   *)
  Program Definition execute_entry_point
    (wpcc wcgp : Word) (regs : Reg) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    : (WORLD -n> (leibnizO CmptName) -n> iPropO Σ) :=
    (λne (W : WORLD) (C : CmptName),
      ∀ a_stk e_stk,
       let a_stk4 := (a_stk ^+4)%a in
       ( interp_continuation cstk Ws Cs
         ∗ ⌜frame_match Ws Cs cstk W C⌝
         ∗ (execute_entry_point_register wpcc wcgp (WCap RWL Local a_stk4 e_stk a_stk4) W C regs)
         ∗ registers_pointsto regs
         ∗ region W C
         ∗ sts_full_world W C
         (* The 2nd condition [a_stk = (a_stk4 ^+ -4)%a] is necessary,
            because ((a_stk ^+4)%a ^+ -4)%a is not necessarily [a_stk] due to finite integers. *)
         ∗ ⌜csp_sync cstk a_stk e_stk ∧ a_stk = (a_stk4 ^+ -4)%a⌝
         ∗ cstack_frag cstk
         ∗ na_own logrel_nais ⊤
           -∗ interp_conf W C)
    )%I.
  Solve All Obligations with solve_proper.

  Definition seal_capability ( w : Word ) (ot : OType) :=
    match w with
    | WCap p g b e a => WSealed ot (SCap p g b e a)
    | _ => w
    end.

  (** [ot_switcher_prop] is the sealing predicate for the switcher's otype, used for sealing entry points.
      Any (regular) compartment's are sealed with this otype, and must therefore respect this predicate.
      Only the switcher can unseal this otype.

      Operationally, a compartment entry point is a RO-capability pointing to
      an entry in the compartment's export table.
      The compartment's export table always starts with the compartment's PCC and CGP,
      and then a list of entries of the form [(nargs,offset)],
      where [nargs] is the number of argument (up-to 7),
      and [offset] is the offset of the function in the code,
      from the first address of the PCC (i.e., we must take account for the RO global data, like the imports).

      For the most of the definition, [ot_switcher_prop] describes the logical state of the physical state described above.
      In addition, it contains the resources [(seal_capability w ot_switcher) ↦□ₑ nargs],
      which states that entry point uses [nargs] (the others are cleared by the switcher).
      It's a [Persistent] knowledge, and is used by the functional spec of the switcher's call
      for requiring the caller to only show [interp] of the actual arguments.

      Finally, [execute_entry_point] is called, with [PCC+off] in the [PC].
      It is guarded by a □-modality, because the entry point can be invoked at any time.
      Similarly, [related_sts_priv_world].
   *)
  Program Definition ot_switcher_prop :
    (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ):=
    λne (W : WORLD) (C : CmptName) (w : Word),
       (∃ (g_tbl : Locality) (b_tbl e_tbl a_tbl : Addr)
          (bpcc epcc : Addr)
          (bcgp ecgp : Addr)
          (nargs : nat) (off : Z),
           ⌜ w = WCap RO g_tbl b_tbl e_tbl a_tbl ⌝
           ∗ ⌜ (b_tbl <= a_tbl < e_tbl)%a ⌝
           ∗ ⌜ (b_tbl < (b_tbl ^+1))%a ⌝
           ∗ ⌜ ((b_tbl ^+1) < a_tbl)%a ⌝
           ∗ ⌜ (0 <= nargs <= 7 )%nat ⌝
           ∗ inv (export_table_PCCN C) ( b_tbl ↦ₐ WCap RX Global bpcc epcc bpcc)
           ∗ inv (export_table_CGPN C) ( (b_tbl ^+ 1)%a ↦ₐ WCap RW Global bcgp ecgp bcgp)
           ∗ inv (export_table_entryN C a_tbl) ( a_tbl ↦ₐ WInt (encode_entry_point (Z.of_nat nargs) off))
           ∗ (seal_capability w ot_switcher) ↦□ₑ nargs
           ∗ □ ( ∀ regs cstk Ws Cs W', ⌜related_sts_priv_world W W'⌝ →
                   ▷ (execute_entry_point
                            (WCap RX Global bpcc epcc (bpcc ^+ off)%a)
                            (WCap RW Global bcgp ecgp bcgp)
                            regs cstk Ws Cs W' C))
      )%I.
  Solve All Obligations with solve_proper.

  Definition ot_switcher_propC : (WORLD * CmptName * Word) -> iPropI Σ :=
    safeC ot_switcher_prop.

  Lemma persistent_cond_ot_switcher :
    persistent_cond ot_switcher_prop.
  Proof. intros [ [] ] ; cbn; apply _. Qed.

  (** [cframe_interp] interprets a call-frame, i.e.,
      describes how the physical call-frame is linked to the logical call-frame [frm : cframe].
      We have 2 situations to take into account:
      - If the caller is untrusted, the points-to predicate of the callee-save region
        are stored in the region invariant, which means that their content is controlled by adversary,
        and does not have to match with the call-frame.
      - If the caller is trusted, the switcher controls the callee-save region,
        and the content should match the words of the call-frame.
   *)
  Definition cframe_interp (frm : cframe) (a_tstk : Addr) : iProp Σ :=
    ∃ (wtstk4 : Word),
      a_tstk ↦ₐ wtstk4 ∗
      match frm.(wstk) with
      | WCap RWL Local b_stk e_stk a_stk =>
          (⌜ (b_stk <= a_stk)%a ∧ (a_stk ^+ 3 < e_stk)%a ∧ is_Some (a_stk + 4)%a ⌝
           ∗ ⌜ wtstk4 = WCap RWL Local b_stk e_stk (a_stk ^+ 4)%a ⌝
           ∗ if frm.(is_untrusted_caller)
             then True
             else
               a_stk ↦ₐ frm.(wcs0)
               ∗ (a_stk ^+ 1)%a ↦ₐ frm.(wcs1)
               ∗ (a_stk ^+ 2)%a ↦ₐ frm.(wret)
               ∗ (a_stk ^+ 3)%a ↦ₐ frm.(wcgp))%I
      (* Constraints WFness of the register save area *)
      | _ => False
      end.

  (** [cstack_interp] interprets a call-stack.
      It simply interpret the topmost stack frame,
      as well as the rest of the call-stack.
   *)
  Fixpoint cstack_interp (cstk : cstack) (a_tstk : Addr) : iProp Σ :=
    (match cstk with
    | [] => a_tstk ↦ₐ WInt 0
    | frm::cstk' => cstack_interp cstk' (a_tstk ^+ -1)%a
                  ∗ cframe_interp frm a_tstk
    end)%I.

  (** [switcher_inv] describes the invariant of the switcher,
      and describe the private state of the switcher.

      [mtdc] is the a privileged register, than only the switcher can access.
      It contains a pointer to the _trusted stack_
      (also called _physical call stack_ or _switcher's private state_).
      The trusted stack stores the compartment's stack pointer of all calls.

      The _trusted stack_ must be in sync with the logical call stack [cstk],
      for which the switcher's invariant holds the authoritative view [cstack_full].
      As a reminder, the fragmental view [cstack_frag] is given by the expression relation
      (or any of its variants).

      The invariant also contains the code of the switcher,
      as well as the unsealing capability of the switcher's otype.

      Finally, it holds the points-to predicates of the trusted stack.
      The unused part `[a_tstk+1, e_trusted_stack)` contains some unknown values.
      The used part is contained in the definition of [stack_interp].
   *)
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
     ∗ cstack_interp cstk a_tstk (* link the topmost frame of cstk to the state *)
     ∗ seal_pred ot_switcher ot_switcher_propC.

End Switcher_preamble.
