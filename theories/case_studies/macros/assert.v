From cap_machine Require Import machine_parameters assembler.
From cap_machine Require Import fetch.

Section Assert_Code.
  Import Asm_Griotte.
  Local Coercion Z.of_nat : nat >-> Z.
  Context `{MP: MachineParameters}.

  (* Maintains a flag storing whether an assert has failed. *)

  (* Asserts (ct0 == ct1). Jumps back to cra.
     Clobbers cra, ct0, ct1.
   *)
  Definition assert_subroutine_asm_pre :=
    [
      sub ct0 ct0 ct1;
      jnz ("assert_fail")%asm ct0;
      #"assert_success";
      mov ct0 0;
      mov ct1 0;
      jmpcap cra; (* return *)
      #"assert_fail";
      mov ct1 PC;
      lea ct1 ("cap_flag"+1)%asm; (* pointer to cap: *)
      load ct1 ct1;
      store ct1 1;
      mov ct0 0;
      mov ct1 0;
      jmpcap cra;
      #"cap_flag"
       (* cap: (RW, flag, end, flag) *)
       (* flag: <0 or 1> *)
       (* end*)
    ].

  Definition assert_subroutine_asm_env :=
    Eval vm_compute in (compute_asm_code_env (assert_subroutine_asm_pre)).2.
  Definition assert_subroutine_asm :=
    Eval compute in resolve_labels_macros assert_subroutine_asm_pre assert_subroutine_asm_env.
  Definition assert_subroutine : list instr :=
    Eval compute in assemble assert_subroutine_asm.
  Definition assert_subroutine_instrs : list Word :=
    encodeInstrsW assert_subroutine.

  (* assert macros:
   - fetch the assert entry point an the n-th position in the import table
   - execute the assert subroutine

   - rdst, rscratch1 and rscratch2 are all clobbered
   *)
  Definition assert_asm (n : Z) (rdst rscratch1 rscratch2 : RegName) :=
    [ fetch_asm n rdst rscratch1 rscratch2
      ;
      [
        mov rscratch1 cra;
        jalr cra rdst;
        mov cra rscratch1;
        mov rscratch1 0;
        mov rdst 0
      ]
    ].

  Definition assembled_assert (n : Z) (rdst rscratch1 rscratch2 : RegName) :=
    Eval compute in assemble_block (assert_asm n rdst rscratch1 rscratch2).
  Definition assert_instrs (n : Z) (rdst rscratch1 rscratch2 : RegName) : list Word :=
    concat (encodeInstrsW <$> (assembled_assert n rdst rscratch1 rscratch2)).
End Assert_Code.
