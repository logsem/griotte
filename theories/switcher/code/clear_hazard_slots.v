From griotte Require Import machine_parameters assembler.

Section ClearHazardSlotsMacro.
  Import Asm_Griotte.
  #[local] Coercion Z.of_nat : nat >-> Z.
  Context `{MP: MachineParameters}.

  (** The word of the register save area of the trusted stack that holds the
      capability to the two hazard slots of the thread (CHERIoT's
      [hazardPointers]), counted in words, as the other offsets of the
      trusted stack in [switcher]. *)
  Definition TrustedStack_offset_hazardPointers : Z := 16.

  (** CHERIoT's [clear_hazard_slots trustedStack, scratch]: load the
      store-only capability to the hazard slots of the thread from the
      trusted stack [ts], and clear both slots, with [scratch]. CHERIoT's
      slots take 8 bytes each, a Griotte word: the byte offsets 0 and 8 are
      the words 0 and 1. A whole-word store of 0 replaces CHERIoT's 32-bit
      [csw zero], which clears the tag of the slot. *)
  Definition clear_hazard_slots_asm (ts scratch : RegName) : list asm_code :=
    macro: [
      (* clc scratch, TrustedStack_offset_hazardPointers(trustedStack) *)
      load_imm scratch ts TrustedStack_offset_hazardPointers;
      (* csw zero, 0(scratch) *)
      store_imm scratch 0 0;
      (* csw zero, 8(scratch) *)
      store_imm scratch 0 1
    ].
  Lemma clear_hazard_slots_assembles (ts scratch : RegName) :
    asm_ok (assemble_check (clear_hazard_slots_asm ts scratch)).
  Proof. asm_check. Qed.

  Definition clear_hazard_slots (ts scratch : RegName) : list instr :=
    Eval compute in assemble (clear_hazard_slots_asm ts scratch).
  Definition clear_hazard_slots_instrs (ts scratch : RegName) : list Word :=
    encodeInstrsW (clear_hazard_slots ts scratch).
End ClearHazardSlotsMacro.
