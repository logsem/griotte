From griotte Require Import machine_parameters assembler.

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
    := (fun r => (encodeInstrW (machine_instructions.Mov r (inl 0%Z)))) <$> l.

  Definition registers_pre_call_skip : list RegName :=
    [ca0;ca1;ca2;ca3;ca4;ca5;ct0].
  Definition clear_registers_pre_call_skip_asm : list asm_code :=
    [ jmp ct2 ] ++ rclear_asm registers_pre_call_skip.
  Definition clear_registers_pre_call_skip : list instr :=
    Eval compute in assemble clear_registers_pre_call_skip_asm.
  Lemma clear_registers_pre_call_skip_assembles : asm_ok (assemble_check clear_registers_pre_call_skip_asm).
  Proof. asm_check. Qed.
  Definition clear_registers_pre_call_skip_instrs : list Word :=
    encodeInstrsW clear_registers_pre_call_skip.

  Definition registers_pre_call : list RegName :=
    [cnull; ctp; ct1; ct2; cs0; cs1].
  Definition clear_registers_pre_call_asm : list asm_code :=
    rclear_asm registers_pre_call.
  Definition clear_registers_pre_call : list instr :=
    Eval compute in assemble clear_registers_pre_call_asm.
  Lemma clear_registers_pre_call_assembles : asm_ok (assemble_check clear_registers_pre_call_asm).
  Proof. asm_check. Qed.
  Definition clear_registers_pre_call_instrs : list Word :=
    encodeInstrsW clear_registers_pre_call.

  Definition registers_post_call : list RegName :=
    [ct0; cnull; ctp; ct1; ct2; ca2; ca3; ca4; ca5].
  Definition clear_registers_post_call_asm : list asm_code :=
    rclear_asm registers_post_call.
  Definition clear_registers_post_call : list instr :=
    Eval compute in assemble clear_registers_post_call_asm.
  Lemma clear_registers_post_call_assembles : asm_ok (assemble_check clear_registers_post_call_asm).
  Proof. asm_check. Qed.
  Definition clear_registers_post_call_instrs : list Word :=
    encodeInstrsW clear_registers_post_call.
End ClearStackMacro.
