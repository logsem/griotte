From cap_machine Require Import machine_parameters assembler.

Section ClearStackMacro.
  Import Asm_Griotte.
  Local Coercion Z.of_nat : nat >-> Z.
  Context `{MP: MachineParameters}.

  Definition clear_registers_pre_call_skip_asm : list asm_code :=
    [ jmp ct2;
      mov ca0 0;
      mov ca1 0;
      mov ca2 0;
      mov ca3 0;
      mov ca4 0;
      mov ca5 0;
      mov ct0 0
    ].
  Definition clear_registers_pre_call_skip : list instr :=
    Eval compute in assemble clear_registers_pre_call_skip_asm.
  Definition clear_registers_pre_call_skip_instrs : list Word :=
    encodeInstrsW clear_registers_pre_call_skip.

  Definition clear_registers_pre_call_asm : list asm_code :=
    [
      mov cnull 0;
      mov ctp 0;
      mov ct1 0;
      mov ct2 0;
      mov cs0 0;
      mov cs1 0;
      mov ca6 0;
      mov ca7 0;
      mov cs2 0;
      mov cs3 0;
      mov cs4 0;
      mov cs5 0;
      mov cs6 0;
      mov cs7 0;
      mov cs8 0;
      mov cs9 0;
      mov cs10 0;
      mov cs11 0;
      mov ct3 0;
      mov ct4 0;
      mov ct5 0;
      mov ct6 0
    ].
  Definition clear_registers_pre_call : list instr :=
    Eval compute in assemble clear_registers_pre_call_asm.
  Definition clear_registers_pre_call_instrs : list Word :=
    encodeInstrsW clear_registers_pre_call.

  Definition clear_registers_post_call_asm : list asm_code :=
    [
        mov ct0 0;
        mov cnull 0;
        mov ctp 0;
        mov ct1 0;
        mov ct2 0;
        mov ct3 0;
        mov ct4 0;
        mov ct5 0;
        mov ct6 0;
        mov ca2 0;
        mov ca3 0;
        mov ca4 0;
        mov ca5 0;
        mov ca6 0;
        mov ca7 0;
        mov cs2 0;
        mov cs3 0;
        mov cs4 0;
        mov cs5 0;
        mov cs6 0;
        mov cs7 0;
        mov cs8 0;
        mov cs9 0;
        mov cs10 0;
        mov cs11 0
      ].
  Definition clear_registers_post_call : list instr :=
    Eval compute in assemble clear_registers_post_call_asm.
  Definition clear_registers_post_call_instrs : list Word :=
    encodeInstrsW clear_registers_post_call.
End ClearStackMacro.
