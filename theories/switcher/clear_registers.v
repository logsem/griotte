From cap_machine Require Import machine_parameters assembler.

Section ClearStackMacro.
  Import Asm_Griotte.
  Local Coercion Z.of_nat : nat >-> Z.
  Context `{MP: MachineParameters}.

  Definition rclear_asm (l : list RegName) : list asm_code :=
  (fun r => mov r 0) <$> l.
  Definition rclear (l : list RegName) : list instr :=
    Eval cbn in assemble (rclear_asm l).
  Definition rclear_instrs (l : list RegName) : list Word :=
    encodeInstrsW (rclear l).
  Definition rclear_instrs' (l : list RegName) : list Word
    := (fun r => (encodeInstrW (machine_base.Mov r (inl 0%Z)))) <$> l.

  Definition registers_pre_call_skip : list RegName :=
    [ca0;ca1;ca2;ca3;ca4;ca5;ct0].
  Definition clear_registers_pre_call_skip_asm : list asm_code :=
    [ jmp ct2 ] ++ rclear_asm registers_pre_call_skip.
  Definition clear_registers_pre_call_skip : list instr :=
    Eval compute in assemble clear_registers_pre_call_skip_asm.
  Definition clear_registers_pre_call_skip_instrs : list Word :=
    encodeInstrsW clear_registers_pre_call_skip.

  Definition registers_pre_call : list RegName :=
    [cnull;
     ctp; ct1; ct2; cs0; cs1; ca6; ca7;
     cs2; cs3; cs4; cs5; cs6; cs7; cs8; cs9; cs10; cs11;
     ct3; ct4; ct5; ct6
    ].
  Definition clear_registers_pre_call_asm : list asm_code :=
    rclear_asm registers_pre_call.
  Definition clear_registers_pre_call : list instr :=
    Eval compute in assemble clear_registers_pre_call_asm.
  Definition clear_registers_pre_call_instrs : list Word :=
    encodeInstrsW clear_registers_pre_call.

  Definition registers_post_call : list RegName :=
    [ct0; cnull;
     ctp; ct1; ct2; ct3; ct4; ct5; ct6;
     ca2; ca3; ca4; ca5; ca6; ca7;
     cs2; cs3; cs4; cs5; cs6; cs7; cs8; cs9; cs10; cs11
    ].
  Definition clear_registers_post_call_asm : list asm_code :=
    rclear_asm registers_post_call.
  Definition clear_registers_post_call : list instr :=
    Eval compute in assemble clear_registers_post_call_asm.
  Definition clear_registers_post_call_instrs : list Word :=
    encodeInstrsW clear_registers_post_call.
End ClearStackMacro.
