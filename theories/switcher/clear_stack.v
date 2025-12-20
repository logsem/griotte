From cap_machine Require Import machine_parameters assembler.

Section ClearStackMacro.
  Import Asm_Griotte.
  Local Coercion Z.of_nat : nat >-> Z.
  Context `{MP: MachineParameters}.

  (* Expects r1 := e_stk ; r2 := a_stk *)
  Definition clear_stack_asm_pre (r1 r2 : RegName) : list asm_code :=
    [
      sub r1 r2 r1;
      mov r2 csp;
      #"loop_start";
      jnz ("loop_body")%asm r1;
      jmp ("loop_end")%asm;
      #"loop_body";
      store r2 0;
      lea r2 1;
      add r1 r1 1;
      jmp ("loop_start")%asm;
      #"loop_end"
    ].

  Definition clear_stack_asm_env :=
    Eval vm_compute in (compute_asm_code_env (clear_stack_asm_pre PC PC)).2.
  Definition clear_stack_asm (r1 r2 : RegName) :=
    Eval compute in resolve_labels_macros (clear_stack_asm_pre r1 r2) clear_stack_asm_env.
  Definition clear_stack (r1 r2 : RegName) : list instr :=
    Eval compute in assemble (clear_stack_asm r1 r2).
  Definition clear_stack_instrs (r1 r2 : RegName) : list Word :=
    encodeInstrsW (clear_stack r1 r2).
End ClearStackMacro.
