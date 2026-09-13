From iris.proofmode Require Import coq_tactics.
From iris.bi Require Import bi.
Import bi.
From griotte Require Import rules solve_pure machine_instructions
  proofmode_instr_support.
From Ltac2 Require Import Ltac2 Option.
Set Default Proof Mode "Classic".

Ltac dispatch_Get r1 r2 cont :=
  let p := constr:((r1, r2)) in
  lazymatch p with
  | (_, PC) => cont (@wp_Get_PC_success)
  | (?r, ?r) => cont (@wp_Get_same_success)
  | _ => cont (@wp_Get_success)
  end.

Ltac dispatch_BinOp r1 x1 x2 cont :=
  let p := constr:((r1, x1, x2)) in
  lazymatch p with
  | (?r, (inr ?r), (inr ?r)) => cont (@wp_binop_success_dst_dst)
  | (?dst, (inr ?r), (inr ?dst)) => cont (@wp_binop_success_r_dst)
  | (?dst, (inr ?dst), (inr ?r)) => cont (@wp_binop_success_dst_r)
  | (?dst, (inl _), (inr ?dst)) => cont (@wp_binop_success_z_dst)
  | (?dst, (inr ?dst), (inl _)) => cont (@wp_binop_success_dst_z)
  | (?dst, (inr ?r), (inr ?r)) => cont (@wp_binop_success_r_r_same)
  | (?dst, (inr ?r), (inl _)) => cont (@wp_binop_success_r_z)
  | (?dst, (inl _), (inr _)) =>
    (cont (@wp_binop_success_z_r) ||
     cont (@wp_binop_fail_z_r))
  | (?dst, (inr _), (inr _)) => cont (@wp_binop_success_r_r)
  | (?dst, (inl _), (inl _)) => cont (@wp_binop_success_z_z)
  end.

Ltac dispatch_instr_rule instr cont :=
  let instr := eval unfold register_file.regn, register_file.cst in instr in
  lazymatch instr with
  (* Mov *)
  | Mov PC (inr PC) => cont (@wp_move_success_reg_samePC)
  | Mov PC (inr _) => cont (@wp_move_success_reg_toPC)
  | Mov _ (inr PC) => cont (@wp_move_success_reg_fromPC)
  | Mov ?r (inr ?r) => cont (@wp_move_success_reg_same)
  | Mov _ (inr _) => cont (@wp_move_success_reg)
  | Mov _ (inl _) => cont (@wp_move_success_z_gen)
  (* Get *)
  | GetL ?r1 ?r2 => dispatch_Get r1 r2 cont
  | GetP ?r1 ?r2 => dispatch_Get r1 r2 cont
  | GetB ?r1 ?r2 => dispatch_Get r1 r2 cont
  | GetE ?r1 ?r2 => dispatch_Get r1 r2 cont
  | GetA ?r1 ?r2 => dispatch_Get r1 r2 cont
  | GetOType ?r1 ?r2 => dispatch_Get r1 r2 cont
  | GetWType ?r1 ?r2 => dispatch_Get r1 r2 cont
  | GetTag PC PC => cont (@wp_GetTag_PC_failure)
  | GetTag PC cnull => cont (@wp_GetTag_cnull_toPC)
  | GetTag PC _ => cont (@wp_GetTag_toPC_failure)
  | GetTag cnull cnull => cont (@wp_GetTag_cnull)
  | GetTag cnull PC => cont (@wp_GetTag_PC_to_cnull)
  | GetTag cnull _ => cont (@wp_GetTag_to_cnull)
  | GetTag _ cnull => cont (@wp_GetTag_from_cnull)
  | GetTag ?r1 ?r2 => dispatch_Get r1 r2 cont
  (* ClearTag *)
  | ClearTag PC PC => cont (@wp_ClearTag_PC)
  | ClearTag PC cnull => cont (@wp_ClearTag_cnull_toPC)
  | ClearTag PC _ =>
    (cont (@wp_ClearTag_toPC) || cont (@wp_ClearTag_toPC_failure))
  | ClearTag cnull cnull => cont (@wp_ClearTag_cnull)
  | ClearTag cnull PC => cont (@wp_ClearTag_PC_to_cnull)
  | ClearTag cnull _ => cont (@wp_ClearTag_to_cnull)
  | ClearTag _ cnull => cont (@wp_ClearTag_from_cnull)
  | ClearTag _ PC => cont (@wp_ClearTag_fromPC)
  | ClearTag ?r ?r => cont (@wp_ClearTag_same_success)
  | ClearTag _ _ => cont (@wp_ClearTag_success)
  (* BinOp *)
  | Add ?x1 ?x2 ?x3 => dispatch_BinOp x1 x2 x3 cont
  | Sub ?x1 ?x2 ?x3 => dispatch_BinOp x1 x2 x3 cont
  | Mul ?x1 ?x2 ?x3 => dispatch_BinOp x1 x2 x3 cont
  | LAnd ?x1 ?x2 ?x3 => dispatch_BinOp x1 x2 x3 cont
  | LOr ?x1 ?x2 ?x3 => dispatch_BinOp x1 x2 x3 cont
  | LShiftL ?x1 ?x2 ?x3 => dispatch_BinOp x1 x2 x3 cont
  | LShiftR ?x1 ?x2 ?x3 => dispatch_BinOp x1 x2 x3 cont
  | Lt ?x1 ?x2 ?x3 => dispatch_BinOp x1 x2 x3 cont
  (* Lea *)
  | Lea PC (inr _) => cont (@wp_lea_success_reg_PC)
  | Lea PC (inl _) => cont (@wp_lea_success_z_PC)
  | Lea _ (inr _) => (cont (@wp_lea_success_reg) || cont (@wp_lea_success_reg_sr))
  | Lea _ (inl _) => (cont (@wp_lea_success_z) || cont (@wp_lea_success_z_sr))
  (* Load *)
  | Load PC _ => cont (@wp_load_success_PC)
  | Load _ PC => cont (@wp_load_success_fromPC)
  | Load ?r ?r =>
    (cont (@wp_load_success_same_notinstr) ||
     cont (@wp_load_success_same_frominstr))
  | Load _ _ =>
    (cont (@wp_load_success_notinstr) ||
     cont (@wp_load_success_frominstr))
  (* Store *)
  | Store PC (inl _) => cont (@wp_store_success_z_PC)
  | Store PC (inr PC) => cont (@wp_store_success_reg_PC_same_store_word)
  | Store PC (inr _) => cont (@wp_store_success_reg_PC_store_word)
  | Store _ (inl _) =>
    (cont (@wp_store_success_same) ||
     cont (@wp_store_success_z))
  (* | Store _ (inr PC) => *)
  (*   (cont (@wp_store_success_reg_frominstr_same) || *)
  (*    cont (@wp_store_success_reg_frominstr)) *)
  | Store ?r (inr ?r) =>
    (cont (@wp_store_success_reg_same'_store_word) ||
     cont (@wp_store_success_reg_same_store_word))
  | Store _ (inr _) =>
    (cont (@wp_store_success_reg_same_a_store_word) ||
     cont (@wp_store_success_reg_store_word))
  (* Jnz *)
  (* | Jnz PC PC => cont (@wp_jnz_success_jmpPC) *) (* FAIL *)
  | Jnz (inl _) PC => cont (@wp_jnz_success_jmpPC_z)
  | Jnz (inr _) PC => cont (@wp_jnz_success_jmpPC_reg)
  | Jnz (inl _) _ => (cont (@wp_jnz_success_next_z) || cont (@wp_jnz_success_jmp_z) )
  | Jnz (inr ?r) ?r => cont (@wp_jnz_success_jmp_same)
  | Jnz (inl _) _ => (cont (@wp_jnz_success_next_reg) || cont (@wp_jnz_success_jmp_reg) )
  (* Jmp *)
  | Jmp (inl _) => cont (@wp_jmp_success_z)
  | Jmp (inr _) => cont (@wp_jmp_success_reg)
  (* | Jmp (inr PC) => cont (@wp_jmp_success_z) *) (* FAIL *)
  (* Jalr *)
  | Jalr _ PC => cont (@wp_jalr_successPC)
  | Jalr cnull _ => cont (@wp_jalr_success_cnull)
  | Jalr ?r ?r => cont (@wp_jalr_success_rdst)
  | Jalr _ _ => cont (@wp_jalr_success)
  (* Subseg *)
  | Subseg PC (inr ?r) (inr ?r) => cont (@wp_subseg_success_pc_same)
  | Subseg PC (inr _) (inr _) => cont (@wp_subseg_success_pc)
  | Subseg PC (inl _) (inr _) => cont (@wp_subseg_success_pc_l)
  | Subseg PC (inr _) (inl _) => cont (@wp_subseg_success_pc_r)
  | Subseg PC (inl _) (inl _) => cont (@wp_subseg_success_pc_lr)
  | Subseg _ (inr ?r) (inr ?r) => (cont (@wp_subseg_success_same) || cont (@wp_subseg_success_same_sr)) (* TODO: improve using register values? *)
  | Subseg _ (inr _) (inr _) => (cont (@wp_subseg_success) || cont (@wp_subseg_success_sr))
  | Subseg _ (inl _) (inr _) => (cont (@wp_subseg_success_l) || cont (@wp_subseg_success_l_sr))
  | Subseg _ (inr _) (inl _) => (cont (@wp_subseg_success_r) || cont (@wp_subseg_success_r_sr))
  | Subseg _ (inl _) (inl _) => (cont (@wp_subseg_success_lr) || cont (@wp_subseg_success_lr_sr))
  (* Restrict *)
  | Restrict PC (inr _) => cont (@wp_restrict_success_reg_PC)
  | Restrict _ (inr _) => cont (@wp_restrict_success_reg)
  | Restrict PC (inl _) => cont (@wp_restrict_success_z_PC)
  | Restrict _ (inl _) => cont (@wp_restrict_success_z)
  (* Seal *)
  | Seal ?r ?r PC => cont (@wp_seal_PC_eq)
  | Seal _ _ PC => cont (@wp_seal_PC)
  | Seal ?r _ ?r => cont (@wp_seal_r2)
  | Seal ?r ?r _ => cont (@wp_seal_r1)
  | Seal _ _ _ => cont (@wp_seal_success)
  (* UnSeal *)
  | UnSeal PC _ _ => cont (@wp_unseal_PC)
  | UnSeal ?r _ ?r => cont (@wp_unseal_r2)
  | UnSeal ?r ?r _ => cont (@wp_unseal_r1)
  | UnSeal _ _ _ => cont (@wp_unseal_success)
  (* readsr *)
  | ReadSR PC _ => cont (@wp_readsr_success_toPC)
  | ReadSR _ _ => cont (@wp_readsr_success)
  (* writesr *)
  | WriteSR _ PC => cont (@wp_writesr_success_fromPC)
  | WriteSR _ _ => cont (@wp_writesr_success)
  (* Fail *)
  | Fail => cont (@wp_fail)
  (* Halt *)
  | Halt => cont (@wp_halt)
  (* not found *)
  | _ => fail "No suitable rule found for instruction" instr
  end.

Ltac dispatch_generic_failure instr cont :=
  let regs := instr_failure_registers instr in
  lazymatch goal with
  | |- context [ Esnoc _ _ (PC ↦ᵣ WCap true ?p ?g ?b ?e ?a)%I ] =>
    lazymatch regs with
    | [] => cont (fun E => @wp_instr_failed_0 _ _ _ E p g b e a
                            (encodeInstrW instr) instr)
    | [(?r1, ?w1)] => cont (fun E => @wp_instr_failed_1 _ _ _ E p g b e a
                                     (encodeInstrW instr) instr r1 w1)
    | [(?r1, ?w1); (?r2, ?w2)] =>
        cont (fun E => @wp_instr_failed_2 _ _ _ E p g b e a
                         (encodeInstrW instr) instr r1 w1 r2 w2)
    | [(?r1, ?w1); (?r2, ?w2); (?r3, ?w3)] =>
        cont (fun E => @wp_instr_failed_3 _ _ _ E p g b e a
                         (encodeInstrW instr) instr r1 w1 r2 w2 r3 w3)
    end
  end.

Ltac dispatch_instr_failure instr cont :=
  first [ dispatch_generic_failure instr cont
        | fail "No immediate-failure provider found for instruction" instr ].

(* Like ordinary success dispatch, invalidation selects explicit-resource
   lemmas. Add an instruction case and its necessary alias/operand variants;
   resource preparation and side-condition handling belong to the caller. *)
Ltac dispatch_instr_invalidation instr cont :=
  let instr := eval cbv [regn cst] in instr in
  lazymatch instr with
  (* Lea: reuse the existing overflow rules. *)
  | Lea PC (inr _) => cont (@wp_lea_overflow_reg_PC)
  | Lea PC (inl _) => cont (@wp_lea_overflow_z_PC)
  | Lea _ (inr _) => (cont (@wp_lea_overflow_reg) || cont (@wp_lea_overflow_reg_sr))
  | Lea _ (inl _) => (cont (@wp_lea_overflow_z) || cont (@wp_lea_overflow_z_sr))
  (* Restrict *)
  | Restrict PC (inr _) => cont (@wp_restrict_invalidated_reg_PC)
  | Restrict PC (inl _) => cont (@wp_restrict_invalidated_z_PC)
  | Restrict _ (inr _) =>
      (cont (@wp_restrict_invalidated_reg) || cont (@wp_restrict_invalidated_reg_sr))
  | Restrict _ (inl _) =>
      (cont (@wp_restrict_invalidated_z) || cont (@wp_restrict_invalidated_z_sr))
  (* Subseg: conversion overflow has priority over representable rejection.
     The explicit-mode caller requires overflow evidence before committing. *)
  | Subseg PC (inr ?r) (inr ?r) =>
      (cont (@wp_subseg_unrepresentable_pc_same) ||
       cont (@wp_subseg_invalidated_pc_same))
  | Subseg PC (inr _) (inr _) =>
      (cont (@wp_subseg_unrepresentable_pc) ||
       cont (@wp_subseg_invalidated_pc))
  | Subseg PC (inl _) (inr _) =>
      (cont (@wp_subseg_unrepresentable_pc_l) ||
       cont (@wp_subseg_invalidated_pc_l))
  | Subseg PC (inr _) (inl _) =>
      (cont (@wp_subseg_unrepresentable_pc_r) ||
       cont (@wp_subseg_invalidated_pc_r))
  | Subseg PC (inl _) (inl _) =>
      (cont (@wp_subseg_unrepresentable_pc_lr) ||
       cont (@wp_subseg_invalidated_pc_lr))
  | Subseg _ (inr ?r) (inr ?r) =>
      (cont (@wp_subseg_unrepresentable_same) ||
       cont (@wp_subseg_unrepresentable_same_sr) ||
       cont (@wp_subseg_invalidated_same) ||
       cont (@wp_subseg_invalidated_same_sr))
  | Subseg _ (inr _) (inr _) =>
      (cont (@wp_subseg_unrepresentable) ||
       cont (@wp_subseg_unrepresentable_sr) ||
       cont (@wp_subseg_invalidated) ||
       cont (@wp_subseg_invalidated_sr))
  | Subseg _ (inl _) (inr _) =>
      (cont (@wp_subseg_unrepresentable_l) ||
       cont (@wp_subseg_unrepresentable_l_sr) ||
       cont (@wp_subseg_invalidated_l) ||
       cont (@wp_subseg_invalidated_l_sr))
  | Subseg _ (inr _) (inl _) =>
      (cont (@wp_subseg_unrepresentable_r) ||
       cont (@wp_subseg_unrepresentable_r_sr) ||
       cont (@wp_subseg_invalidated_r) ||
       cont (@wp_subseg_invalidated_r_sr))
  | Subseg _ (inl _) (inl _) =>
      (cont (@wp_subseg_unrepresentable_lr) ||
       cont (@wp_subseg_unrepresentable_lr_sr) ||
       cont (@wp_subseg_invalidated_lr) ||
       cont (@wp_subseg_invalidated_lr_sr))
  (* Seal *)
  | Seal ?r ?r PC => cont (@wp_seal_invalidated_PC_eq)
  | Seal _ _ PC => cont (@wp_seal_invalidated_PC)
  | Seal ?r ?r ?r => cont (@wp_seal_invalidated_all)
  | Seal _ ?r ?r => cont (@wp_seal_invalidated_same)
  | Seal ?r ?r _ => cont (@wp_seal_invalidated_r1)
  | Seal ?r _ ?r => cont (@wp_seal_invalidated_r2)
  | Seal _ _ _ => cont (@wp_seal_invalidated)
  (* UnSeal *)
  | UnSeal PC _ _ => cont (@wp_unseal_invalidated_PC)
  | UnSeal ?r ?r _ => cont (@wp_unseal_invalidated_r1)
  | UnSeal ?r _ ?r => cont (@wp_unseal_invalidated_r2)
  | UnSeal _ _ _ => cont (@wp_unseal_invalidated)
  | _ => fail "No invalidation rule found for instruction" instr
  end.
