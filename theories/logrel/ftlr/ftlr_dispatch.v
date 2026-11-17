From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre.
From griotte Require Import ftlr_base ftlr_contract ftlr_shapes shapes.memory_access ftlr_mem_access Jalr
  Ecall.
Import CoreWPNotations.

(** * The fundamental theorem by shapes: the classification

    Every instruction gets a shape. An instruction with a dedicated proof
    is matched by name; any other instruction is tried against the shapes
    of [ftlr_shapes.v] and [ftlr_mem_access.v], on its operands as they
    are, then on each integer-or-register operand split into its two
    cases. *)

Section dispatch.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {cthreads : CmptThreads} {CL : ∀ t, CritLink Σ t}
    `{MP: MachineParameters}
    {CR : ∀ t, CritRoute Σ t (CL t)}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  #[local] Notation D := (interpO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (D).

  (** The shapes: stop, register step, memory (a load or a store).
      [ShapeDedicated] has a dedicated proof. *)
  Inductive instr_shape := ShapeStop | ShapeRegs | ShapeMem | ShapeDedicated.

  (** Membership of a shape. For [ShapeDedicated], it is the case of the
      contract of the fundamental theorem itself. *)
  Definition shape_member (k : instr_shape) (i : instr) : Prop :=
    match k with
    | ShapeStop => stop_member exec_opt i
    | ShapeRegs => regs_member exec_opt i ∧ not_switch_instr i
    | ShapeMem => mem_member exec_opt i ∧ not_switch_instr i
    | ShapeDedicated => ∀ m W C regs p p' g b e a w ρ P,
        ftlr_contract m W C regs p p' g b e a w i ρ P
    end.

End dispatch.

(** ** The classification tactics *)

Ltac no_shape i := fail 0 "no shape fits" i "and it has no dedicated proof".

(** The three shapes other than [ShapeDedicated], in a goal
    [{ k | shape_member k i }]. *)
Ltac try_shapes :=
  first
    [ solve [exists ShapeStop; cbn [shape_member]; solve_stop_member]
    | solve [exists ShapeRegs; cbn [shape_member]; split; [solve_regs_member | solve_not_switch_instr] ]
    | solve [exists ShapeMem; cbn [shape_member]; split;
             [solve_mem_member | solve_not_switch_instr] ] ].

(** The shapes, on the operands as they are, then with an
    integer-or-register operand split into its two cases, each tried in
    turn: a step that a shape tactic proves only for an integer, or only
    for a register, operand. *)
Ltac try_shapes_split :=
  first
    [ try_shapes
    | lazymatch goal with
      | |- { _ | shape_member _ ?i } =>
          match i with
          | context [?x] =>
              is_var x;
              lazymatch type of x with (Z + RegName)%type => idtac end;
              destruct x; try_shapes_split
          end
      end ].

(** The classification of one instruction, in a goal [{ k | shape_member k i }].
    An instruction with a dedicated proof is matched by name: [Jalr] sees
    the interrupt posture and the volatile registers; [Ecall] hands off to
    the switcher. Any other instruction is tried against the three other
    shapes; if none fits, the tactic fails with an error naming the
    instruction ([debug_classify] then says why each shape rejects
    it). *)
Ltac classify_instr :=
  lazymatch goal with
  | |- { k | shape_member k (Jalr _ _) } =>
      exists ShapeDedicated; cbn [shape_member]; intros; apply jalr_case
  | |- { k | shape_member k Ecall } =>
      exists ShapeDedicated; cbn [shape_member]; intros; apply ecall_case
  | |- { k | shape_member k ?i } =>
      tryif try_shapes_split then idtac else no_shape i
  end.

(** Runs each shape tactic on [i] and prints, for each, that it fits or
    why it was rejected. The operands are not split. Use in a goal with
    [MachineParameters] in the context, e.g.
    [Goal ∀ `{MachineParameters} r1 r2, True. intros.
    debug_classify (Lea r1 r2 (inl 0%Z)). Abort.] *)
Ltac debug_shape name P tac :=
  idtac name;
  tryif (let H := fresh in assert P as H by tac; clear H)
  then idtac "    fits" else idtac.

Ltac debug_classify i :=
  let Hdbg := fresh "Hdbg" in
  pose proof DebugShapes as Hdbg;
  idtac "debug_classify" i;
  debug_shape "ShapeStop: stop_member" (stop_member exec_opt i) solve_stop_member;
  debug_shape "ShapeRegs: regs_member" (regs_member exec_opt i) solve_regs_member;
  debug_shape "ShapeMem: mem_member, load"
    (∃ dst r imm, load_member exec_opt griotte_load_filter i dst r imm)
    ltac:(idtac; do 3 eexists; solve_load_member);
  debug_shape "ShapeMem: mem_member, store"
    (∃ r imm, store_member exec_opt store_source i r imm)
    ltac:(idtac; do 2 eexists; solve_store_member);
  debug_shape "ShapeMem: mem_member, store: not an instruction of the HWM window"
    (¬ hwm_window_instr i) solve_not_hwm_window_instr;
  debug_shape "ShapeRegs, ShapeMem: not_switch_instr" (not_switch_instr i)
    solve_not_switch_instr;
  idtac "ShapeDedicated";
  lazymatch i with
  | Jalr _ _ => idtac "    fits (jalr_case)"
  | Ecall => idtac "    fits (ecall_case)"
  | _ => idtac "    rejected: no dedicated proof"
  end;
  clear Hdbg.

Section shapes.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {cthreads : CmptThreads} {CL : ∀ t, CritLink Σ t}
    `{MP: MachineParameters}
    {CR : ∀ t, CritRoute Σ t (CL t)}
  .

  (** The classification, by instruction. This table is documentation
      only: [classify_shape] below is authoritative (it derives the shape of
      each instruction by the tactics above).

      | Instruction                              | Shape          | Why dedicated                     |
      |------------------------------------------|----------------|-----------------------------------|
      | Jmp, Jeq, Jne, Jlt, Jle                  | ShapeRegs      |                                   |
      | Mov                                      | ShapeRegs      |                                   |
      | Lt, Le, machine_instructions.Add, Sub,   | ShapeRegs      |                                   |
      |   Mul, LAnd, LOr, LShiftL, LShiftR       |                |                                   |
      | Lea, SetA, Restrict, Subseg              | ShapeRegs      |                                   |
      | GetB, GetE, GetLen, GetA, GetP, GetL,    | ShapeRegs      |                                   |
      |   GetWType, GetOType, GetTag             |                |                                   |
      | Seal, UnSeal, ClearTag, Auipcc           | ShapeRegs      |                                   |
      | SpecialRW, SetMIE, Mret                  | ShapeStop      | (fault without system-register    |
      |                                          |                |  access)                          |
      | Fail, Halt                               | ShapeStop      |                                   |
      | CLoad, Store                             | ShapeMem       |                                   |
      | Jalr                                     | ShapeDedicated | interrupt posture, volatile       |
      |                                          |                | registers, sentries               |
      | Ecall                                    | ShapeDedicated | hands off to the switcher         |
  *)
  Definition classify_shape (i : instr) : { k | shape_member (th := th) k i }.
  Proof. destruct i; classify_instr. Defined.

  Definition shape_of (i : instr) : instr_shape := proj1_sig (classify_shape i).

  (** The case of every instruction: the contract that the step lemma
      consumes. *)
  Lemma ftlr_case :
    ∀ W C regs p p' g b e a w i ρ P m,
      ftlr_contract (th := th) m W C regs p p' g b e a w i ρ P.
  Proof.
    intros W C regs p p' g b e a w i ρ P m.
    destruct (classify_shape i) as [k Hmember].
    destruct k; cbn in Hmember.
    - (* ShapeStop *) by apply stop_case.
    - (* ShapeRegs *)
      destruct Hmember as [Hregs Hsw].
      by apply regs_case.
    - (* ShapeMem *)
      destruct Hmember as [Hmem Hsw].
      by apply mem_case.
    - (* ShapeDedicated *) apply Hmember.
  Qed.

End shapes.
