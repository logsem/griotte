From griotte Require Import machine_parameters assembler.

Section ClearStackMacro.
  Import Asm_Griotte.
  #[local] Coercion Z.of_nat : nat >-> Z.
  Context `{MP: MachineParameters}.

  (** CHERIoT's [zero_stack base top]: zero the words from the address of
      the capability in [rbase] up to the address [rtop], one word at a
      time. [rtop] counts the words left, negated. *)
  Definition clear_stack_asm (rbase rtop : RegName) : list asm_code :=
    macro: [
      sub rtop rbase rtop;
      #"loop_start";
      jnez ("loop_body")%asm rtop;
      jmp ("loop_end")%asm;
      #"loop_body";
      store rbase 0;
      lea rbase rbase 1;
      add rtop rtop 1;
      jmp ("loop_start")%asm;
      #"loop_end"
    ].
  Lemma clear_stack_assembles (r1 r2 : RegName) :
    asm_ok (assemble_check (clear_stack_asm r1 r2)).
  Proof. asm_check. Qed.

  Definition clear_stack (r1 r2 : RegName) : list instr :=
    Eval compute in assemble (clear_stack_asm r1 r2).
  Definition clear_stack_instrs (r1 r2 : RegName) : list Word :=
    encodeInstrsW (clear_stack r1 r2).
End ClearStackMacro.
