From griotte Require Import machine_parameters assembler.

Section ClearStackMacro.
  Import Asm_Griotte.
  #[local] Coercion Z.of_nat : nat >-> Z.
  Context `{MP: MachineParameters}.

  (** CHERIoT's [zero_stack base top scratch]: zero from the address of
      [rbase] up to the address [rtop]. *)
  Definition clear_stack_asm (rbase rtop : RegName) : list asm_code :=
    macro: [
      (* [deviation] one word per iteration, no scratch register *)
      (* bgt base, scratch, 1f *)
      jge ("loop_end")%asm rbase rtop;
      #"loop_body";
      (* csc cnull, 0(c\base) *)
      store rbase 0;
      (* cincoffset c\base, c\base, 32 *)
      lea rbase rbase 1;
      (* ble base, scratch, 0b *)
      jlt ("loop_body")%asm rbase rtop;
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
