From griotte Require Import machine_parameters assembler.

Section CopyContextMacro.
  Import Asm_Griotte.
  #[local] Coercion Z.of_nat : nat >-> Z.
  Context `{MP: MachineParameters}.

  (** CHERIoT's [copyContext]: copy the 15 words at [src] to [dst], one word
      per iteration, with [scratch] and the counter [counter]. A word is one
      address: CHERIoT's [cincoffset …, 8] is [lea … 1]. *)
  Definition copy_context_asm (dst src scratch counter : RegName) : list asm_code :=
    macro: [
      (* addi counter, zero, 15 *)
      mov counter 15;
      #"copy_loop";
      (* clc scratch, 0(src) *)
      load scratch src;
      (* csc scratch, 0(dst) *)
      store dst scratch;
      (* addi counter, counter, -1 *)
      add counter counter (-1)%Z;
      (* cincoffset dst, dst, 8 *)
      lea dst dst 1;
      (* cincoffset src, src, 8 *)
      lea src src 1;
      (* bnez counter, 1b *)
      jnez ("copy_loop")%asm counter
    ].
  Lemma copy_context_assembles (dst src scratch counter : RegName) :
    asm_ok (assemble_check (copy_context_asm dst src scratch counter)).
  Proof. asm_check. Qed.

  Definition copy_context (dst src scratch counter : RegName) : list instr :=
    Eval compute in assemble (copy_context_asm dst src scratch counter).
  Definition copy_context_instrs (dst src scratch counter : RegName) : list Word :=
    encodeInstrsW (copy_context dst src scratch counter).
End CopyContextMacro.
