(* Spec instruction rules of the binary model, one
   file per instruction, mirroring [rules.v]. Each file provides the generic
   rule [step_X], the determinism lemma [X_spec_determ], and the derived rules
   [step_X_*] used by the spec proof mode. *)
From griotte Require Export
     rules_base_binary
     rules_Get_binary rules_Load_binary rules_Store_binary rules_BinOp_binary
     rules_Lea_binary rules_Mov_binary rules_Restrict_binary rules_Subseg_binary
     rules_Jmp_binary rules_Jnz_binary rules_Jalr_binary
     rules_Seal_binary rules_UnSeal_binary
     rules_ReadSR_binary rules_WriteSR_binary.
